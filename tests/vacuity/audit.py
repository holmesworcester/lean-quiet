"""Build evidence and verify each report names a proof that uses its theorem.
Kernel proofs must be closed Prop terms using only standard axioms. Runtime
certificates and conditional bridges are recorded separately, never promoted.
"""
import importlib.util
from pathlib import Path
import re
import subprocess
from runtime import run_checked

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('vacuity', ROOT / 'ci/vacuity.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
checks = audit.load_checks()
RUNNERS = {
    'tests.vacuity.Bootstrap': 'vacuity_bootstrap',
    'tests.vacuity.ProductionBootstrap': 'vacuity_production_bootstrap',
    'tests.vacuity.StorageEffects': 'vacuity_storage_effects',
    'tests.vacuity.ConnectionProgress': 'vacuity_connection_progress',
    'tests.vacuity.ClosureDelivery': 'vacuity_closure_delivery',
    'tests.vacuity.RoundExchange': 'vacuity_round_exchange',
    'tests.vacuity.Identity': 'vacuity_identity',
    'tests.vacuity.IdentityTrust': 'vacuity_identity_trust',
    'tests.vacuity.IdentityPeople': 'vacuity_identity_people',
    'tests.vacuity.IdentityMessages': 'vacuity_identity_messages',
    'tests.vacuity.IdentityConnection': 'vacuity_identity_connection',
    'tests.vacuity.IdentityLifecycle': 'vacuity_identity_lifecycle',
    'tests.vacuity.IdentityFrames': 'vacuity_identity_frames',
    'tests.vacuity.IdentityRejoin': 'vacuity_identity_rejoin',
    'tests.vacuity.IdentityPreadmit': 'vacuity_identity_preadmit',
    'tests.vacuity.ChatPresentation': 'vacuity_chat_presentation',
    'tests.vacuity.Contracts': 'vacuity_contracts',
    'tests.vacuity.SealAudit': 'vacuity_seal_audit',
    'tests.vacuity.CoreRuntime': 'vacuity_core',
    'tests.vacuity.RendererRuntime': 'vacuity_renderer_runtime',
    'tests.vacuity.RendererSupplement': 'vacuity_renderer_runtime',
    'tests.vacuity.Attachment': 'vacuity_attachment',
}
runtime_modules = {e['module'] for e in checks.values()
                   if e['status'] in {'runtime-witness', 'counterexample'}}
runtime_modules |= {e['module'] for e in checks.values() if e.get('exercise')}
unknown = runtime_modules - RUNNERS.keys()
if unknown:
    raise SystemExit(f'No executable registered for runtime evidence: {sorted(unknown)}')
modules = sorted({e['module'] for e in checks.values()})
subprocess.run(['lake', 'build', *modules], cwd=ROOT, check=True)
out = ROOT / 'out/vacuity'
out.mkdir(parents=True, exist_ok=True)
# Names become Lean identifiers, so reject anything except identifier segments.
for e in checks.values():
    for field in ['witness', 'theorem', 'module']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', e[field]):
            raise SystemExit(f'invalid Lean name: {e[field]}')
code = 'import Lean\n' + ''.join(f'import {m}\n' for m in modules)
code += '''
open Lean Meta
-- Follow proof bodies as well as data definitions. A successful example that
-- never applies the advertised theorem cannot satisfy this check.
def reaches (env : Environment) (root target : Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut i := 0
  while i < todo.size do
    let n := todo[i]!
    i := i + 1
    if n == target then return true
    if seen.contains n then continue
    seen := seen.insert n
    if let some info := env.find? n then
      if let some value := info.value? (allowOpaque := true) then
        for c in value.getUsedConstants do
          if !seen.contains c then todo := todo.push c
  return false

def inspect (w t : Name) (kernel predicate : Bool) : MetaM Unit := do
  let info ← getConstInfo w
  let target ← getConstInfo t
  let isDefinition := match target with | .thmInfo _ => false | _ => true
  if kernel then
    unless ← isProp info.type do throwError "kernel witness {w} is not a proof"
    if info.type.hasFVar || info.type.hasMVar then throwError "open witness {w}"
  unless reaches (← getEnv) w t || ((predicate || isDefinition) && info.type.getUsedConstants.contains t) do throwError "{w} does not apply {t}"
  IO.println s!"witness {w} applies {t}"
'''
for e in checks.values():
    is_kernel = 'true' if e['status'] == 'kernel-witness' else 'false'
    predicate = "true" if e["status"] == "counterexample" else "false"
    code += f'#eval inspect ``{e["witness"]} ``{e["theorem"]} {is_kernel} {predicate}\n'
    code += f'#print axioms {e["witness"]}\n'
code += """
def rejected (w t : Name) : MetaM Bool := do
  try
    inspect w t true false
    return false
  catch _ => return true
#eval show MetaM Unit from do
  unless ← rejected ``Vacuity.Pictures.small ``Pic.fit_pos do
    throwError "unrelated theorem negative control escaped"
  unless ← rejected ``Vacuity.Core.payload ``Engine.Codec.decode_encode do
    throwError "non-proof negative control escaped"
  IO.println "audit negative controls rejected"
"""
for e in checks.values():
    if e['status'] in {'runtime-witness', 'counterexample'} or e.get('exercise'):
        runner = e['witness'].rsplit('.', 1)[0] + '.main'
        code += f'#eval show MetaM Unit from do\n  unless reaches (← getEnv) ``{runner} ``{e["witness"]} do throwError "runtime certificate is not exercised: {e["witness"]}"\n'
probe = out / 'Audit.lean'
probe.write_text(code)
r = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=ROOT, text=True, capture_output=True)
(out / 'audit.log').write_text(r.stdout + r.stderr)
if r.returncode:
    raise SystemExit(r.stdout + r.stderr)
reports = re.findall(r'depends on axioms: \[(.*?)\]|does not depend on any axioms', r.stdout, re.S)
if len(reports) != len(checks):
    raise SystemExit(f'expected {len(checks)} axiom reports, got {len(reports)}')
for report in reports:
    axioms = set(re.sub(r'\s', '', report).split(',')) - {''}
    if not axioms <= {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit(f'nonstandard axiom in fixture: {axioms}')
print(f'{len(checks)} witness dependency and axiom checks passed; details in {out / "audit.log"}')

if 'tests.vacuity.RendererRuntime' in runtime_modules:
    if not (ROOT / 'assets/font.bin').exists():
        subprocess.run(['tools/fetch_assets.sh'], cwd=ROOT, check=True)
    subprocess.run(['tools/noto_assets.sh'], cwd=ROOT, check=True)
targets = sorted({RUNNERS[m] for m in runtime_modules})
if targets:
    subprocess.run(['lake', 'build', *targets], cwd=ROOT, check=True)
for target in targets:
    print(run_checked([str(ROOT / '.lake/build/bin' / target)], ROOT,
                      out / f'{target}.log'), end='')
