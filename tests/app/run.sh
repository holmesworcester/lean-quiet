#!/usr/bin/env bash
# The app on the headless twin (platforms/headless): its own session
# (host: chaos, cold open, a fling to the top, send and react), two apps
# joined by link (two_nodes) and over real TCP on loopback (net_join), two
# communities named alike (cross), a photo arriving chunk by chunk
# (arrival), and photos over TCP (attach); a picture whose chunks land
# while its retry waits (pic_retry, with its negative controls); the
# dogfood UX regressions on both scroll seams (ux, with its negative
# controls). Also
# drives host.c's actual externs (host_twin_demo.sh), and checks the
# shipped SQLite and glue (tests/shipped). Screens, replies and databases
# in out/.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME=${ELAN_HOME:-/mnt/storage/elan}
export PATH="$ELAN_HOME/bin:$PATH"
# Its checks are tests/app/parts.txt: stage, part, command.
#   tests/app/run.sh                every stage, in order
#   tests/app/run.sh --part P [C]   just part P (its case C), as ci/local.sh
#                                   --full runs each in its own copy
#   tests/app/run.sh --cases P      part P's cases, if it has them
parts=tests/app/parts.txt
if [ "${1:-}" = --cases ]; then
  cmd=$(awk -F'\t' -v n="$2" '$2 == n { print $3 }' "$parts")
  [ -n "$cmd" ] || { echo "no app part $2" >&2; exit 2; }
  exec bash -c "$cmd --list"
fi
# Resume a failed stage during local iteration. The default always runs all
# stages; the explicit resume is printed so it cannot look like a full run.
start=${APP_TEST_FROM:-fonts}
case "$start" in fonts|input|network|desktop|navigation|lifecycle|appearance|safety|components) ;;
  *) echo "unknown APP_TEST_FROM stage: $start" >&2; exit 2 ;;
esac
active=false
# APP_TEST_ONLY="fonts input …" runs just those stages: ci/local.sh runs
# the stages in groups, each group in its own copy of the tree, at once.
only=${APP_TEST_ONLY:-}
for s in $only; do
  case "$s" in fonts|input|network|desktop|navigation|lifecycle|appearance|safety|components) ;;
    *) echo "unknown APP_TEST_ONLY stage: $s" >&2; exit 2 ;;
  esac
done
stage() {
  if [ -n "$only" ]; then
    case " $only " in *" $1 "*) echo "app stage: $1"; return 0 ;; esac
    echo "SKIP app stage: $1 (APP_TEST_ONLY=$only)"
    return 1
  fi
  if [ "$1" = "$start" ]; then active=true; fi
  if "$active"; then echo "app stage: $1"; return 0; fi
  echo "SKIP previously tested app stage: $1 (APP_TEST_FROM=$start)"
  return 1
}
(cd engine/native/crypto && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
[ -f assets/font.bin ] || tools/fetch_assets.sh
tools/noto_assets.sh
lake build host two_nodes net_join cross arrival attach inkless nodequeue pic_retry ux
# One part, timed; a case, if given, goes to its command.
part() {
  local name=$1 cmd t0
  shift
  cmd=$(awk -F'\t' -v n="$name" '$2 == n { print $3 }' "$parts")
  [ -n "$cmd" ] || { echo "no app part $name" >&2; return 2; }
  echo "app part: $name${1:+ ($1)}"
  t0=$(date +%s)
  if [ $# -gt 0 ]; then bash -c "$cmd \"\$@\"" app-part "$@"; else bash -c "$cmd"; fi
  echo "app part: $name${1:+ ($1)} ok ($(( $(date +%s) - t0 )) s)"
}
if [ "${1:-}" = --part ]; then shift; part "$@"; exit $?; fi
for st in fonts input network desktop navigation lifecycle appearance safety components; do
  stage "$st" || continue
  for p in $(awk -F'\t' -v s="$st" '$1 == s { print $2 }' "$parts"); do part "$p"; done
done
