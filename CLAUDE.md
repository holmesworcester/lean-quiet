# CLAUDE.md: Lean verification for Vibecheck hackathon

The hackathon's judging rules: [docs/VIBECHECK-RULES.md](docs/VIBECHECK-RULES.md).

## 1. Approaches

- **Write the program in Lean and prove it there.** Nothing to translate, nothing extra to trust.
- **Write it in a Lean DSL with a verified compiler.** Prove properties at the DSL level; the compiler's correctness proof carries them to the target.
- **Translate existing code (C, Rust, ...) into Lean.** Tools usually translate a compiler IR, not source text. You trust the translation and the compiler below that IR, and only the supported subset of the language works.
- **Verify the binary.** The compiler is out of the trusted base; you trust the ISA model instead. Proofs need a way to reason above single instructions: a program logic for machine code, or disassembling and lifting the code into a higher-level form and proving things about that.

## 2. Toolchain and versions

- Pin `lean-toolchain` and every dependency's git rev; commit `lake-manifest.json`. Mathlib must match the toolchain exactly. Translation tools pin their own Lean and library versions: use theirs.
- Pick the toolchain from the libraries you need, before writing code. Libraries lag core Lean, and two libraries pinned to different versions can't share a project.
- `lake update` bumps everything. Run it only on purpose.
- Mathlib: fetch the build cache with `lake exe cache get`; building it from source takes hours. Not depending on Mathlib at all keeps builds light and upgrades easy, and core plus Batteries is often enough for program verification.
- What breaks across versions: proofs that rely on reduction (`rfl`, `decide`, `simp` closing a goal by computing), definitions by well-founded recursion (they don't unfold by `rfl`), renamed lemmas, changed simp sets.

## 3. Builds

- Build one module per edit (`lake build My.Module`, or `lake env lean File.lean`).
- Never run two `lake` processes, or lake and a REPL, in one checkout at once.
- A successful build can still contain `sorry`. Read the warnings.
- Raise `maxHeartbeats` only on the declaration that needs it, with a comment. Needing much more usually means the proof should be split.
- A proof is only considered final once it passes Comparator.  This is built into Lean 4.35., which is what you should use.

## 4. Specs people can review

- **Know the trusted surface.** A theorem means what its statement says, and the statement means what every definition it mentions means, transitively. List those definitions for each main theorem (`#spec_surface` in the appendix), review them, and keep the list short. It's tempting to make comments here that are sloppy -- they use way too much technical jargon, go on and on trying to sound fancy, but don't explain anything. Don't do this. Make your properties, and the comments explaining them, cogent, lucid, short, and non-jargon-y.
- **Write specs to be read.** Meaningful names, explicit pre- and postconditions, a docstring per definition, a named example next to it. Keep specs in their own files. Don't use unnecessary math vocabulary. Write specs that would make sense, in [simplified technical english][1], for the average reader.
- **Hypotheses must be satisfiable.** A theorem with contradictory hypotheses proves nothing. Instantiate each main theorem on a concrete input with every hypothesis discharged, as an `example`. Likewise, any kinds of models you use should be executable ... although in general, you should avoid models and try to use the actual code under test/analysis.
- **The spec must reject bad behaviour.** Prove `¬ Spec input badOutput` for a few known-bad outputs.
- **Compare against a reference.** "The implementation computes the same as this simple function" is easier to review than a list of properties.
- **Functions without a body** become an `opaque` with a stated contract, not an `axiom`. The contracts are part of the trusted surface.

## 5. Testing the spec

- **Unit tests**: `#eval` on concrete inputs; `#guard cond` fails the build if `cond` is false; `example : f 3 = 7 := by decide` (or `rfl`).
- **Property-based testing** (`plausible`): run it on a statement before proving it, and again when a proof stalls, since the statement may be false. Random inputs rarely meet narrow preconditions (sorted lists, well-formed states): write a generator for the precondition instead of filtering. Specimen derives generators from inductive relations.
- **Differential testing**: run the Lean model against the real system (production code, a reference interpreter, an existing test suite) on many inputs. This checks the model is the system you meant. Antithesis does deterministic simulation testing of whole systems.

## 6. Proofs

- **Skeleton first.** State the intermediate lemmas with `sorry`, check the main theorem follows from them, then prove them one at a time.
- **Lemmas over unfolding.** Don't `unfold` or `simp` through large generated or monadic code; prove a lemma per helper and use it at each call.
- **Recursion.** `partial def` can't be reasoned about. Use structural recursion, `termination_by`/`decreasing_by`, or `partial_fixpoint`.
- **Arithmetic.** `Nat` subtraction truncates (`2 - 3 = 0`), `Nat` division floors, and casts between `UInt64`, `BitVec`, `Nat` and `Int` cause many stuck goals.
- **Slow `decide`.** It evaluates in the kernel. For large finite checks `native_decide` runs compiled code instead; it trusts the compiler and adds an axiom per use. Decide early whether you accept that.
- **Odd failures.** `set_option pp.all true`, `#print` and `#reduce` show hidden coercions, instances and implicit arguments.
- **Repetition.** A macro or small tactic for a repeated proof step, and a simp set per layer.

## 7. Checking the result

- Reject `sorry`, `admit`, new `axiom`s, `debug.skipKernelTC`, `implemented_by`/`unsafe` used to change meaning, `maxHeartbeats 0`; also edits to the spec or its definitions, theorems about a copy of the code, and weakened statements.
- On every change: build, then audit the axioms of each main theorem (`#print axioms`, or `#audit_axioms` in the appendix). Allowed: `propext`, `Classical.choice`, `Quot.sound`, plus any native-computation axioms you accepted.
- `Classical.choice` among a theorem's axioms is fine for proofs. Definitions that have to run (the implementation, a reference model used for differential testing) can't use it: classical choice, or decidability from `open Classical` in an `if`, makes a definition `noncomputable`, so it can't be `#eval`ed or compiled. `#eval` each definition you need to execute.
- Since Lean v4.35, `lake check` replays the build through the kernel and fails on other axioms, and `lake comparator` checks a solution against a trusted file of statements. Both sandbox the project (Linux only).
- Never edit generated files by hand; regenerate them.
- List what is trusted in the README: translation tools, ISA models, `opaque` contracts, accepted axioms, external solvers.

## 8. Working with models

- Strong at proofs of well-stated lemmas, trying many tactics, boilerplate, translating code, finding lemmas.
- Weak at choosing the right spec (they drift to what is easy to prove), noticing vacuous statements, and giving up gracefully: when stuck they may reach for `sorry` or change a definition.
- Humans own the spec and the trusted surface; models write proofs; the check accepts or rejects them.
- Give the model goal states without rebuilding: lean-lsp-mcp (diagnostics, goals, search) or the Lean REPL (leanprover-community/repl, tag matching your toolchain). A finished proof in the REPL still has to build in the file.
- Search: `exact?`, `apply?`, `simp?` (prints the `simp only` call), `try?`, Loogle, LeanSearch.

## 9. Tools

Check each README for the supported subset, maturity and pinned Lean version (ideally 4.53).

- **Programs written in Lean**: Velvet (Dafny-style contracts and loop invariants, contract tester); core `vcgen` (v4.35, experimental, replaces `mvcgen`); iris-lean (separation logic).
- **Protocols, state machines**: Veil (SMT invariant checking, model checking, interactive proofs; set `veil.smt.trust false` to get checked proofs).
- **Testing**: plausible, Specimen, LSpec.
- **Verified compilers in Lean**: Verity (Ethereum contracts to EVM), powdr-labs' yul-compiler (Yul to EVM), VerifiedJS (JavaScript to Wasm, research), Axon (research). Outside Lean: CompCert (Rocq), CakeML (HOL4), vyper-hol (Vyper semantics in HOL4, the basis for a verified Vyper compiler).
- **Rust**: Aeneas (safe Rust; not `RefCell`/`Cell`, `unsafe`, most `dyn`, async); hax (experimental Lean backend). Outside Lean: Verus, Creusot, Kani.
- **C**: Clift (AutoCorres-style lifting, work in progress); an experimental CompCert fork exporting Clight to Lean; Aristotle (C and Verilog). Outside Lean: Frama-C, VST (Rocq), CN.
- **Binaries**: Sail RISC-V model (Lean output), LNSym (Arm64). In Rocq: Theorem's OSS Verify (RISC-V).
- **WebAssembly**: lean-wasm, Talos. **LLVM/MLIR**: lean-mlir.
- **Ethereum semantics**: EVMYulLean; powdr-labs' evm-semantics. But do you need to do this? Blockchain shit is so 2010.
- **Cryptography**: VCVio, ArkLib.
- **Scientific computing**: Lanyon. They're here! Talk to them!
- **Agents and agent tooling**: Gauss 2 (Math Inc), Aristotle (Harmonic), Axiom's AXLE, Astrio's Forall, lean4-skills (Claude Code / Codex plugin), lean-lsp-mcp, the Lean REPL.
- **Worked examples**: cedar-spec (model, proofs, differential testing against production Rust), SampCert.

## Appendix: snippets

Tested on Lean v4.30 with core only. `#spec_surface` lists definitions from the current file; in a multi-file project, change the filter to keep names from your own modules (for example by module name prefix).

```lean
import Lean
open Lean Elab Command

/-- Definitions a theorem's statement mentions, followed transitively through
their bodies. The proof is not followed. -/
partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- `#spec_surface thm`: list the project's own definitions the statement of `thm` depends on. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toList.filter fun c =>
    (env.getModuleIdxFor? c).isNone && !c.isInternal && !Meta.isMatcherCore env c
  logInfo m!"{own}"

/-- `#audit_axioms thm`: print the axioms `thm` depends on. -/
elab "#audit_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  logInfo m!"{thm}: {axs.toList}"

-- demo
def IsSorted : List Nat → Prop
  | a :: b :: rest => a ≤ b ∧ IsSorted (b :: rest)
  | _ => True

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def Spec (_x : Nat) (l out : List Nat) : Prop := IsSorted l → IsSorted out ∧ out.length = l.length + 1

theorem insert_spec (x : Nat) (l : List Nat) : Spec x l (insertSorted x l) := by sorry

#spec_surface insert_spec
#audit_axioms insert_spec

-- hypotheses are satisfiable: a concrete instance
example : IsSorted [1, 2, 3] := by simp [IsSorted]
-- the spec rejects a bad output
example : ¬ Spec 0 [1] [2, 1] := by
  intro h; have := (h (by simp [IsSorted])).1; simp [IsSorted] at this

#guard insertSorted 2 [1, 3] == [1, 2, 3]
```

Output of the demo: `#spec_surface insert_spec` prints `[IsSorted, insertSorted, Spec]`; `#audit_axioms insert_spec` prints `[propext, sorryAx]`, the `sorryAx` showing the proof is unfinished.

Property-based testing with plausible (add the `plausible` package), before proving:

```lean
example : ∀ (x : Nat) (l : List Nat), (insertSorted x l).length = l.length + 1 := by
  plausible
```

[1](https://en.wikipedia.org/wiki/Simplified_Technical_English)
