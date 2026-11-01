#!/usr/bin/env bash
# Item 6's negative controls (docs/SYNC.md, "Windows and order"). Each
# mutant changes the code that runs so that one law is false; building
# the module that proves the law must then fail inside that law. Runs in
# a scratch copy, never in this tree.
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="${ELAN_HOME:-/mnt/storage/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/window-nc.XXXXXX")
artifacts="$PWD/out/window-negative"
mkdir -p "$artifacts"
trap 'rm -rf -- "$tmp"' EXIT
. tests/snapshot.sh
snapshot "$tmp/base" engine/core engine/wire engine/renderer engine/sync app tests/engine
targets=(app.community.channel.message.attachment.Proofs engine.sync.NewestLaws)
cp -a "$tmp/base" "$tmp/w"
(cd "$tmp/w" && lake build "${targets[@]}" >/dev/null 2>&1) || { echo "FAIL: the unmutated copy does not build"; exit 1; }

# A mutant is refused by its law: the build must fail, and with an error
# inside that law's declaration (law: file:name; for NoDerive, its
# command), not merely somewhere: a proof script that breaks around a
# law still true is not a refusal.
mutant() {  # what target law files old new [old new ...]: files a,b; each old occurs once in them
  local what=$1 target=$2 law=$3 files=$4
  shift 4
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w" "$files" "$@" <<'PY'
import sys
w, files, *pairs = sys.argv[1:]
src = {f: open(f"{w}/{f}").read() for f in files.split(",")}
for old, new in zip(pairs[::2], pairs[1::2]):
    hits = [f for f, s in src.items() if old in s]
    assert len(hits) == 1 and src[hits[0]].count(old) == 1, f"mutant target not found once: {old!r}"
    src[hits[0]] = src[hits[0]].replace(old, new)
for f, s in src.items():
    open(f"{w}/{f}", "w").write(s)
PY
  if (cd "$tmp/w" && lake build "$target" > "$tmp/log" 2>&1); then
    echo "FAIL: mutant survived: $what"; exit 1
  fi
  cp "$tmp/log" "$artifacts/${law##*:}.log"
  if python3 - "$tmp/w" "$law" "$tmp/log" <<'PY'
import re, sys
w, law, log = sys.argv[1:]
path, name = law.rsplit(":", 1)
lines = open(f"{w}/{path}").read().split("\n")
top = re.compile(r"^(theorem|def|lemma|instance|structure|inductive|abbrev|@\[|/--|/-!|#|end\b|section|namespace|variable|open|elab|omit)")
start = next(i for i, l in enumerate(lines)
             if re.match(rf"^(@\[csimp\] )?theorem {re.escape(name)}\b", l) or l.startswith(name))
end = next((i for i in range(start + 1, len(lines)) if top.match(lines[i])), len(lines))
errs = [int(m.group(1)) for m in re.finditer(rf"^error: {re.escape(path)}:(\d+):", open(log).read(), re.M)]
sys.exit(0 if any(start < e <= end for e in errs) else 1)
PY
  then echo "refused by ${law##*:}: $what"
  else echo "FAIL: refused, but not by ${law##*:}: $what"; grep -m3 '^error' "$tmp/log"; exit 1
  fi
}

# A mutant the suite catches: it builds, and running the suite fails.
caught() {  # what exe files old new [old new ...]
  local what=$1 exe=$2 files=$3
  shift 3
  rm -rf -- "$tmp/w"
  cp -a "$tmp/base" "$tmp/w"
  python3 - "$tmp/w" "$files" "$@" <<'PY'
import sys
w, files, *pairs = sys.argv[1:]
src = {f: open(f"{w}/{f}").read() for f in files.split(",")}
for old, new in zip(pairs[::2], pairs[1::2]):
    hits = [f for f, s in src.items() if old in s]
    assert len(hits) == 1 and src[hits[0]].count(old) == 1, f"mutant target not found once: {old!r}"
    src[hits[0]] = src[hits[0]].replace(old, new)
for f, s in src.items():
    open(f"{w}/{f}", "w").write(s)
PY
  if ! (cd "$tmp/w" && lake build "$exe" > "$tmp/log" 2>&1); then
    echo "FAIL: mutant does not build, so the suite cannot catch it: $what"; grep -m3 '^error' "$tmp/log"; exit 1
  fi
  if (cd "$tmp/w" && ".lake/build/bin/$exe" > "$tmp/run.log" 2>&1); then
    echo "FAIL: mutant survived the suite: $what"; tail -5 "$tmp/run.log"; exit 1
  fi
  cp "$tmp/run.log" "$artifacts/$exe-${what// /-}.log"
  echo "caught by $exe: $what"
}

## Chunks sort with their message (chunks_in_window)

# chunk_of_attachment (so chunks_in_window, which rests on it) is false:
# chunks are left at time 0, the structure range every window includes.
mutant "chunks left at time 0" app.community.channel.message.attachment.Proofs \
  app/community/channel/message/attachment/chunk/Proofs.lean:chunk_of_attachment app/community/Family.lean \
  "  | some (.ofChunk b) => b.time
" ""
# check_chunk (so chunk_of_attachment and chunks_in_window) is false: a
# chunk may claim any time, not its attachment's.
mutant "a chunk whose time is not checked" app.community.channel.message.attachment.Proofs \
  app/community/channel/message/attachment/chunk/Proofs.lean:check_chunk \
  app/community/channel/message/attachment/chunk/Validate.lean \
  "r = r2 ∧ l = l2 ∧ tm = tm2 ∧ Merkle.verify" "r = r2 ∧ l = l2 ∧ Merkle.verify"
# check_attach (so attach_order and chunks_in_window) is false: an
# attachment may claim another time than its message's.
mutant "an attachment whose time is not its message's" app.community.channel.message.attachment.Proofs \
  app/community/channel/message/attachment/Proofs.lean:check_attach \
  app/community/channel/message/attachment/Validate.lean \
  "c2 = c ∧ u2 = u ∧ tm = tm2 ∧ r.size = 32" "c2 = c ∧ u2 = u ∧ r.size = 32"

## Newest first (answer_newest_first, window_first, newest_first)

# answer_newest_first is false: an answer's haves go oldest first.
mutant "haves oldest first" engine.sync.NewestLaws engine/sync/NewestLaws.lean:answer_newest_first \
  engine/sync/Round.lean \
  "    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident).reverse," \
  "    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident),"
# answer_newest_first is false: an answer claims its pieces oldest first.
mutant "pieces oldest first" engine.sync.NewestLaws engine/sync/NewestLaws.lean:answer_newest_first \
  engine/sync/Round.lean \
  "    else (pieces r (cutsOf key P x)).reverse.map fun q =>" "    else (pieces r (cutsOf key P x)).map fun q =>"
# window_first is false: the structure range last.
mutant "a window with the structure range last" engine.sync.NewestLaws engine/sync/NewestLaws.lean:window_first \
  engine/sync/Conn.lean \
  "  [⟨⟨0, 0⟩, some ⟨1, 0⟩⟩, ⟨⟨max f 1, 0⟩, none⟩]" "  [⟨⟨max f 1, 0⟩, none⟩, ⟨⟨0, 0⟩, some ⟨1, 0⟩⟩]"
# The suite: with haves oldest first, a fresh node gets the oldest
# photos first, and `newest` fails.
caught "rounds oldest first" newest engine/sync/Round.lean \
  "    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident).reverse," \
  "    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident),"

echo "window negative controls: every mutant refused by its law or caught by its suite"
