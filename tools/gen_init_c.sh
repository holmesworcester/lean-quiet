#!/bin/sh
# Emit C for every Init module of the installed Lean toolchain (from its
# own .oleans), for cross-compiling a program's whole closure: Android has
# no prebuilt libInit. Output: $1/<Module/Path>.c
set -eu
out=$1
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
T=$(ELAN_HOME=$ELAN_HOME "$ELAN_HOME/bin/lean" --print-prefix)
cd "$T/src/lean"
find Init -name '*.lean' | sed 's/\.lean$//' > "$out.list"
echo Init >> "$out.list"
xargs -P "$(nproc)" -I{} sh -c 'mkdir -p "$(dirname "'"$out"'/{}")" && "'"$T"'/bin/lean" -c "'"$out"'/{}.c" "{}.lean"' < "$out.list"
rm "$out.list"
