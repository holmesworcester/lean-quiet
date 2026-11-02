# Sourced by the negative controls, from the repository's root.
# `snapshot dest dir...` copies into dest what a mutant of those
# directories builds from: the package's lakefile, the directories'
# sources and their part of the built tree (.lake/build), so that only
# what a mutant touches is rebuilt, and the C every executable links (the
# Rust crypto through a link, read-only).
#
# The app imports whichever parts of the engine's Lean library it needs,
# so a snapshot that lists app (or any of it) carries every part of it
# (engine/*, but not engine/native), listed or not: a new import from the
# app into the engine needs no caller to change. And every module a
# snapshotted app file imports, if this tree has it, must be in the
# snapshot; if not, `snapshot` fails here, naming each one.
snapshot() {
  local dest=$1 d b
  shift
  local dirs=("$@")
  if printf '%s\n' "$@" | grep -qE '^app(/|$)'; then
    for d in engine/*/; do
      d=${d%/}
      [ "$d" = engine/native ] || snapshot_listed "$d" "${dirs[@]}" || dirs+=("$d")
    done
  fi
  mkdir -p "$dest"
  cp lakefile.lean lake-manifest.json lean-toolchain "$dest/"
  # Into the parent, so that a directory listed twice, or with a part of
  # it, merges rather than nesting.
  for d in "${dirs[@]}" engine/native/glue.c engine/native/crypto.c engine/native/listener.h tests/engine/listener_fixture.c platforms/headless/host.c platforms/native third_party/sqlite; do
    mkdir -p "$dest/$(dirname "$d")"
    cp -a "$d" "$dest/$(dirname "$d")/"
  done
  for d in "${dirs[@]}"; do
    for b in .lake/build/lib/lean .lake/build/ir; do
      if [ -d "$b/$d" ]; then
        mkdir -p "$dest/$b/$(dirname "$d")"
        cp -a "$b/$d" "$dest/$b/$(dirname "$d")/"
      fi
    done
  done
  for b in native host; do
    [ -d ".lake/build/$b" ] && mkdir -p "$dest/.lake/build" && cp -a ".lake/build/$b" "$dest/.lake/build/"
  done
  mkdir -p "$dest/.lake/build/lib"
  cp -a .lake/build/lib/lib*.a* "$dest/.lake/build/lib/" 2>/dev/null || true
  mkdir -p "$dest/engine/native/crypto/target/release"
  ln -s "$PWD/engine/native/crypto/target/release/liblq_crypto.a" "$dest/engine/native/crypto/target/release/"
  snapshot_imports "$dest"
}

# Whether directory d is listed, itself or within a listed directory.
snapshot_listed() {
  local d=$1 x
  shift
  for x in "$@"; do
    case $d in "$x"|"$x"/*) return 0 ;; esac
  done
  return 1
}

# Every module a snapshotted app file imports that this tree has is in
# the snapshot; otherwise fail, naming each.
snapshot_imports() {
  local dest=$1 m f missing=
  [ -d "$dest/app" ] || return 0
  for m in $(grep -rhoP '^import \K\S+' --include='*.lean' "$dest/app" | sort -u); do
    f=${m//.//}.lean
    if [ -f "$f" ] && [ ! -f "$dest/$f" ]; then missing="$missing $m"; fi
  done
  if [ -n "$missing" ]; then
    echo "snapshot: $dest lacks what its app imports:$missing (list them, tests/snapshot.sh)" >&2
    return 1
  fi
}
