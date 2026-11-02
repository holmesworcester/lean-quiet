# Sourced by negative controls that run mutants at once. The box is shared:
# `slot_hold`, in a subshell, takes one of MUTANT_SLOTS (12) slots, lock
# files in $TMPDIR/lean-quiet-slots that every run on the box takes from
# (tests/mutants.py's too), and holds it until the subshell exits; so the
# box never builds more mutants at once than that, however many runs.
slot_hold() {
  local n=${MUTANT_SLOTS:-12} dir=${TMPDIR:-/tmp}/lean-quiet-slots i
  mkdir -p "$dir"
  while :; do
    for i in $(shuf -i 0-$((n - 1))); do
      exec 8>>"$dir/$i.lock"
      if flock -n 8; then return 0; fi
      exec 8>&-
    done
    sleep 0.5
  done
}
