#!/usr/bin/env bash
# The clean-room test of `make install && make run` and `make demo`: for
# each image, a fresh container clones the committed tree (HEAD, as a git
# bundle), installs and builds from nothing as a user with sudo, and opens
# the app under Xvfb; a screenshot must show the window painted. Then
# make demo's e2e runs from the clone: two windows joined, a message each
# way (tests/make/clean_room_inner.sh).
#
#   tests/make/clean_room.sh [image...]   default: ubuntu:24.04 ubuntu:22.04 debian:12
#
# Setup: the pinned assets tarball is packed from assets/ (made first by
# tools/fetch_assets.sh if missing) and must have the pinned sha256; the
# container downloads it by file://. CLEAN_ROOM_ASSETS=published downloads
# it from the GitHub release instead, as a judge would.
#
# Needs: Docker (the user in the docker group), network access in the
# containers (apt, Lean and Rust downloads, crates.io), about 10 GB of disk
# under Docker's root per image while it runs. Each container gets
# CLEAN_ROOM_CPUS (8) CPUs and CLEAN_ROOM_MEMORY (24g) of memory, without
# swap; images run one after another unless CLEAN_ROOM_PARALLEL=1.
# Only committed files are tested. Artifacts (logs, screenshots, result.txt,
# demo-e2e/) stay in out/make/clean-room/<image>/. Removes its containers.
set -euo pipefail
top=$(cd "$(dirname "$0")/../.." && pwd)
cd "$top"
export TMPDIR=${TMPDIR:-/tmp}
images=("$@")
[ ${#images[@]} -gt 0 ] || images=(ubuntu:24.04 ubuntu:22.04 debian:12)
cpus=${CLEAN_ROOM_CPUS:-8} mem=${CLEAN_ROOM_MEMORY:-24g}
logs=$top/out/make/clean-room
mkdir -p "$logs"
w=$(mktemp -d "$TMPDIR/lq-clean-room.XXXXXX")
names=$w/containers
: > "$names"
cleanup() {
  while read -r n; do docker rm -f "$n" > /dev/null 2>&1 || true; done < "$names"
  rm -rf "$w"
}
trap cleanup EXIT
trap 'exit 130' INT TERM

command -v docker > /dev/null || { echo "clean-room: needs Docker" >&2; exit 2; }
[ -z "$(git status --porcelain --untracked-files=no)" ] ||
  echo "clean-room: uncommitted changes are NOT tested; testing HEAD $(git rev-parse --short HEAD)"

. tools/make/assets.pin
mounts=()
url=
if [ "${CLEAN_ROOM_ASSETS:-local}" = published ]; then
  echo "clean-room: assets from https://github.com/$LQ_ASSETS_REPO/releases/download/$LQ_ASSETS_TAG/$LQ_ASSETS_NAME"
else
  tarball=out/make/$LQ_ASSETS_NAME
  if [ ! -f "$tarball" ]; then
    if ! (cd assets 2>/dev/null && sha256sum -c --status "$top/tools/make/assets.sha256"); then
      echo "clean-room: making assets/ (tools/fetch_assets.sh)"
      tools/fetch_assets.sh
    fi
    python3 tools/make/assets.py pack --against-pin
  fi
  [ "$(sha256sum "$tarball" | cut -d' ' -f1)" = "$LQ_ASSETS_SHA256" ] ||
    { echo "clean-room: $tarball does not have the pinned sha256" >&2; exit 1; }
  mounts+=(-v "$top/$tarball:/srv/assets.tar.gz:ro")
  url=file:///srv/assets.tar.gz
fi
git bundle create "$w/repo.bundle" HEAD 2> "$w/bundle.log"

one() {
  local image=$1 slot=$2 dir name code=0
  dir=$logs/${image//[:\/]/-}
  name=lq-make-clean-room-${image//[:\/]/-}-$$
  rm -rf "$dir"; mkdir -p "$dir"
  echo "$name" >> "$names"
  echo "clean-room: $image (container $name, $cpus CPUs, $mem)"
  docker run --rm --name "$name" --cpuset-cpus "$((slot * cpus))-$((slot * cpus + cpus - 1))" \
    --memory "$mem" --memory-swap "$mem" \
    -e ASSETS_URL="$url" -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
    -v "$w/repo.bundle:/srv/repo.bundle:ro" -v "$top/tests/make/clean_room_inner.sh:/srv/inner.sh:ro" \
    "${mounts[@]}" -v "$dir:/out" \
    "$image" bash /srv/inner.sh > "$dir/container.log" 2>&1 || code=$?
  # a container killed before its own chown leaves root's files in out/
  [ -z "$(find "$dir" ! -user "$(id -u)" -print -quit)" ] ||
    docker run --rm -v "$dir:/out" "$image" chown -R "$(id -u):$(id -g)" /out
  if [ "$code" = 0 ] && grep -qx 'step=pass' "$dir/result.txt"; then
    echo "ok   $image: $(grep "^install_summary=" "$dir/result.txt" | cut -d= -f2-); screenshots $dir/shot-run.png, shot-online.png, demo-e2e/7-reply.png"
  else
    echo "FAIL $image (exit $code): $(grep '^fail=' "$dir/result.txt" 2>/dev/null | cut -d= -f2-) - see $dir"
    return 1
  fi
}

fails=0 slot=0
if [ "${CLEAN_ROOM_PARALLEL:-0}" = 1 ]; then
  pids=()
  for image in "${images[@]}"; do one "$image" "$slot" & pids+=($!); slot=$((slot + 1)); done
  for p in "${pids[@]}"; do wait "$p" || fails=$((fails + 1)); done
else
  for image in "${images[@]}"; do one "$image" 0 || fails=$((fails + 1)); done
fi
[ "$fails" = 0 ] || { echo "clean-room: $fails of ${#images[@]} images failed"; exit 1; }
echo "clean-room: ${images[*]} pass"
