#!/usr/bin/env bash
# leanquiet:// links on the Linux desktop (links.py): build the shell and a
# real invite, then install and drive them on a private X display.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
export TMPDIR=${TMPDIR:-/mnt/storage/holmes-tmp}
bash platforms/linux/build.sh
lake build invite_link
mkdir -p out/linux
cc -std=gnu11 -O1 -Wall -Wextra -Werror platforms/linux/active_watch.c -lxcb -o out/linux/active_watch
python3 platforms/linux/links.py
