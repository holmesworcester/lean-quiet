#!/usr/bin/env python3
"""Prepare exact-source, test-only native barriers and allocation failures."""
from pathlib import Path
import argparse

p=argparse.ArgumentParser()
p.add_argument('--out',type=Path,required=True)
p.add_argument('--reuse-ir',action='store_true',help='private diagnostic only; require already compiled exact local IR')
p.add_argument('--control',choices=['latest-snapshot','empty-read','empty-latest','forget-consumed','consumed-readmit'])
p.add_argument('--app-c',type=Path,help='compiled actual App mutation for a negative control')
args=p.parse_args()
root=Path(__file__).resolve().parents[4]
out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
def once(s,old,new):
    if s.count(old)!=1:raise RuntimeError('test overlay anchor changed: '+old)
    return s.replace(old,new)
s=(root/'platforms/android/twin/quiet_android.c').read_text()
s=s.replace('#include "../../native/translate.h"',f'#include "{root}/platforms/native/translate.h"')
s=once(s,'static void lq_pump(void) {','''
#include <stdatomic.h>
static _Atomic bool input_probe_hold, input_probe_release, input_probe_view_hold;
static _Atomic uint64_t input_probe_blocks;
__attribute__((visibility("default"))) void lq_input_probe_gate(bool hold) {
  if(hold){atomic_store(&input_probe_release,false);atomic_store(&input_probe_hold,true);}
  else atomic_store(&input_probe_release,true);
}
__attribute__((visibility("default"))) uint64_t lq_input_probe_blocked(void) {return atomic_load(&input_probe_blocks);}
__attribute__((visibility("default"))) void lq_input_probe_view(bool hold) {atomic_store(&input_probe_view_hold,hold);}
static void lq_pump(void) {
  if(atomic_load(&input_probe_hold)) {
    if(atomic_exchange(&input_probe_release,false)) {
      atomic_store(&input_probe_hold,false);atomic_store(&input_probe_view_hold,false);
    } else {atomic_fetch_add(&input_probe_blocks,1);return;}
  }
''')
s=once(s,'  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(13));','''
  // Retain a previously observed actual viewport until the queued action is
  // delivered. This forces resize and Send into the same actual App turn.
  static uint32_t input_probe_last_view[13];static bool input_probe_has_view;
  if(atomic_load(&input_probe_view_hold)&&input_probe_has_view)memcpy(v,input_probe_last_view,sizeof v);
  else {memcpy(input_probe_last_view,v,sizeof v);input_probe_has_view=true;}
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(13));''')
if args.control in ['empty-read','empty-latest']:
    ignored=8 if args.control=='empty-read' else 12
    s=once(s,'  if(!text&&length){meta=&error;n=1;length=0;}',f'  if(!text&&length&&n!={ignored}){{meta=&error;n=1;length=0;}}')
(out/'quiet_android.c').write_text(s)
s=(root/'platforms/android/twin/activity.c').read_text()
s=s.replace('#include "../../native/photo.h"',f'#include "{root}/platforms/native/photo.h"')
s=once(s,'#include "../../native/editor_action.h"',f'''
#include <stdatomic.h>
#include <stdlib.h>
#include <stdint.h>
static _Atomic int input_probe_fail_site=-1;
static _Atomic uint64_t input_probe_failures[3];
__attribute__((visibility("default"))) void lq_input_probe_fail_copy(int site) {{atomic_store(&input_probe_fail_site,site);}}
__attribute__((visibility("default"))) uint64_t lq_input_probe_copy_failures(int site) {{return site>=0&&site<3?atomic_load(&input_probe_failures[site]):0;}}
static void *input_probe_allocate(size_t n,unsigned site) {{
  if(atomic_load(&input_probe_fail_site)==(int)site) {{
    if(site!=1)atomic_store(&input_probe_fail_site,-1);
    atomic_fetch_add(&input_probe_failures[site],1);return NULL;
  }}
  return malloc(n);
}}
#define LQ_EDITOR_ALLOC(n,site) input_probe_allocate(n,site)
#include "{root}/platforms/native/editor_action.h"
''')
if args.control=='latest-snapshot':
    s=once(s,'*size=ba_action_slot.length;value=lq_editor_copy(ba_action_slot.text,*size,2);',
           '*size=ba_txt_n;value=lq_editor_copy(ba_txt?ba_txt:"",*size,2);')
elif args.control=='forget-consumed':
    s=once(s,'    ba_editor_ready=false;lq_action_retire(&ba_action_slot);\n',
           '    ba_editor_ready=false;lq_action_retire(&ba_action_slot);ba_action_slot.consumed_owner=0;ba_action_slot.consumed_revision=0;\n')
if args.control=='consumed-readmit':
    header=(root/'platforms/native/editor_action.h').read_text()
    header=once(header,'  if(lq_action_consumed(s,owner,revision))return LQ_ACTION_STALE;','')
    (out/'editor_action.h').write_text(header)
    s=once(s,f'#include "{root}/platforms/native/editor_action.h"',f'#include "{out}/editor_action.h"')
(out/'activity.c').write_text(s)
s=(root/'platforms/android/twin/build_apk.sh').read_text()
s=once(s,'set -euo pipefail','''set -euo pipefail
# This diagnostic may read shared pinned runtime archives. Their maintainer
# takes the exclusive lock while rebuilding; native readers hold this lock.
if [ "${OWNED_NATIVE_RUNTIME_LOCKED:-0}" != 1 ]; then
  exec flock -s /mnt/storage/holmes-tmp/android-runtime-prerequisites.lock \
    env OWNED_NATIVE_RUNTIME_LOCKED=1 bash "$0" "$@"
fi''')
s=once(s,'here=$(cd "$(dirname "$0")" && pwd)',f'here={root}/platforms/android/twin')
s=once(s,'  for c in activity scroll layer quiet_android ctl; do\n    "$cc"',f'''  for c in activity scroll layer quiet_android ctl; do
    source="$here/$c.c"
    case "$c" in activity|quiet_android) source={out}/"$c.c";; esac
    "$cc"''')
s=once(s,'-c "$here/$c.c" -o "$o/twin_$c.o"','-c "$source" -o "$o/twin_$c.o"')
old='''  i=0
  for c in "${cfiles[@]}"; do
    i=$((i + 1))
    if [ "$c" = "$root/.lake/build/ir/${main//./\\/}.c" ]; then
      "$cc" "${flags[@]}" -Dmain=lean_app_main -c "$c" -o "$o/m$i.o" &
    else
      "$cc" "${flags[@]}" -c "$c" -o "$o/m$i.o" &
    fi
  done'''
new='''  # Reuse only exact compiler inputs. Mutated App C gets a distinct object;
  # all compiler exits are checked before linking. This cache is private to
  # this source tree and ABI, never a copied build target from another tree.
  module_cache="$root/out/owned-input-module-cache/$abi"
  mkdir -p "$module_cache"
  header_tag=$(rg --files "$rt/include" | sort | xargs sha256sum | sha256sum)
  compiler_tag=$("$cc" --version)
  compile_module() {
    local source=$1 object=$2 is_main=$3 key cached
    local extra=()
    [ "$is_main" != 1 ] || extra=(-Dmain=lean_app_main)
    key=$({ sha256sum < "$source"; printf '%s\\n' "$header_tag" "$compiler_tag" "${flags[@]}" "${extra[@]}"; } | sha256sum | cut -d' ' -f1)
    cached="$module_cache/$key.o"
    if [ ! -f "$cached" ]; then
      "$cc" "${flags[@]}" "${extra[@]}" -c "$source" -o "$cached.partial.$BASHPID"
      mv "$cached.partial.$BASHPID" "$cached"
    fi
    cp "$cached" "$object"
  }
  i=0; module_jobs=$(nproc); module_pids=()
  for c in "${cfiles[@]}"; do
    i=$((i + 1))
    is_main=0
    [ "$c" != "$root/.lake/build/ir/${main//./\\/}.c" ] || is_main=1
    compile_module "$c" "$o/m$i.o" "$is_main" &
    module_pids+=("$!")
    if [ "${#module_pids[@]}" -ge "$module_jobs" ]; then
      for pid in "${module_pids[@]}"; do wait "$pid"; done
      module_pids=()
    fi
  done
  for pid in "${module_pids[@]}"; do wait "$pid"; done'''
s=once(s,old,new)
if args.app_c:
    # Keep Main's compiler treatment unchanged; only substitute the compiled
    # actual app.Screen module for its source-level mutation.
    s=once(s,'  for c in "${cfiles[@]}"; do\n    i=$((i + 1))',
           f'  for c in "${{cfiles[@]}}"; do\n    [ "$c" != "$root/.lake/build/ir/app/Screen.c" ] || c={args.app_c.resolve()}\n    i=$((i + 1))')
if args.reuse_ir:
    s=once(s,'if [ "${OWNED_NATIVE_RUNTIME_LOCKED:-0}" != 1 ]; then',
           f'while [ -f {root}/out/owned-input-native-paused ]; do sleep 1; done\nif [ "${{OWNED_NATIVE_RUNTIME_LOCKED:-0}}" != 1 ]; then')
    s=once(s,'(cd "$root" && "$lake" build $targets >/dev/null)', '# Private diagnostic: exact local IR was compiled separately under its memory scope.')
    a='''      if [ ! -f "$c" ]; then
        mkdir -p "$(dirname "$c")"
        (cd "$toolchain/src/lean" && "$toolchain/bin/lean" -c "$c" "${mod//./\\/}.lean")
      fi'''
    s=once(s,a,'      [ -f "$c" ] || { echo "missing exact cached IR: $c" >&2; exit 2; }')
    s=once(s,'  (cd "$engine/native/crypto" && CARGO_TARGET_DIR="$cache/rust" cargo build --release --quiet --target "$rtgt")',
           '  # Read the already built native crypto archive; never mutate shared prerequisites.')
(out/'build_app.sh').write_text(s)
