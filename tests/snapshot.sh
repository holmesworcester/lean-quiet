# Sourced by the negative controls, from the repository's root.
# `snapshot dest dir...` copies into dest what a mutant of those
# directories builds from: the package's lakefile, the directories'
# sources and their part of the built tree (.lake/build), so that only
# what a mutant touches is rebuilt, and the C every executable links (the
# Rust crypto through a link, read-only).
snapshot() {
  local dest=$1 d b
  shift
  mkdir -p "$dest"
  cp lakefile.lean lake-manifest.json lean-toolchain "$dest/"
  for d in "$@" engine/native/glue.c engine/native/crypto.c platforms/headless/host.c; do
    mkdir -p "$dest/$(dirname "$d")"
    cp -a "$d" "$dest/$d"
  done
  for d in "$@"; do
    for b in .lake/build/lib/lean .lake/build/ir; do
      if [ -d "$b/$d" ]; then
        mkdir -p "$dest/$b/$(dirname "$d")"
        cp -a "$b/$d" "$dest/$b/$d"
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
}
