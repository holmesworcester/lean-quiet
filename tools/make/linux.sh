#!/bin/sh
# `make install`, `make run`, `make online`, `make check` and `make assets`
# on Linux: x86-64, Debian, Ubuntu and their kin. The Makefile calls this.
#
# install  1. system packages: lists the missing ones, says it will install
#             them, then runs apt-get (with sudo unless root);
#          2. Lean: elan into $ELAN_HOME, then the toolchain in
#             lean-toolchain; Rust: rustup into $CARGO_HOME and $RUSTUP_HOME,
#             unless rustc $rust_min or newer is already there;
#          3. the app's assets (tools/make/assets.sh);
#          4. the Rust crypto's crates (cargo fetch), then the build
#             (platforms/linux/build.sh): .lake/build/bin/linux.
#          Run again, it redoes nothing that is done.
# run      the app with --demo: an empty database is seeded with two
#          communities and networking is off (out/make/demo.db)
# online   the app with networking on (out/make/quiet.db)
# check    what install would still need; installs nothing; fails if
#          system packages are missing
set -eu
top=$(cd "$(dirname "$0")/../.." && pwd)
cd "$top"
: "${ELAN_HOME:=$HOME/.elan}" "${CARGO_HOME:=$HOME/.cargo}" "${RUSTUP_HOME:=$HOME/.rustup}" "${TMPDIR:=/tmp}"
export ELAN_HOME CARGO_HOME RUSTUP_HOME TMPDIR
PATH=$CARGO_HOME/bin:$ELAN_HOME/bin:$PATH
export PATH

app=.lake/build/bin/linux
# the newest rust-version among engine/native/crypto's locked crates (sha2)
rust_min=1.88
# what the build needs from the system, as Debian and Ubuntu packages
# (shell.c includes xcb's headers and X11's cursorfont.h and keysym.h)
pkgs="gcc libc6-dev curl ca-certificates python3 libxcb1-dev libxcb-shm0-dev libxcb-sync-dev libx11-dev"
# the libraries the lakefile links, by these paths
libs="libc.so.6 libxcb.so.1 libxcb-shm.so.0 libxcb-sync.so.1"

say() { printf '==> %s\n' "$*"; }
die() { printf 'make: %s\n' "$*" >&2; exit 1; }
mins() { printf '%dm %02ds' $(($1 / 60)) $(($1 % 60)); }

platform() {
  [ "$(uname -m)" = x86_64 ] || die "make install builds for x86-64 Linux; this machine is $(uname -m)"
}

# The missing packages (or, without dpkg, the missing files), one line.
missing() {
  if command -v dpkg-query >/dev/null 2>&1; then
    for p in $pkgs; do
      dpkg-query -W -f='${db:Status-Abbrev}' "$p" 2>/dev/null | grep -q '^ii' || printf '%s ' "$p"
    done
  else
    for c in cc curl python3; do command -v "$c" >/dev/null 2>&1 || printf '%s ' "$c"; done
    for h in xcb/xcb.h xcb/shm.h xcb/sync.h X11/cursorfont.h X11/keysym.h; do
      [ -f "/usr/include/$h" ] || printf '%s ' "/usr/include/$h"; done
    for l in $libs; do [ -e "/usr/lib/x86_64-linux-gnu/$l" ] || printf '%s ' "/usr/lib/x86_64-linux-gnu/$l"; done
  fi
}

rust_ok() {
  v=$(rustc --version 2>/dev/null | cut -d' ' -f2) || return 1
  [ -n "$v" ] && command -v cargo >/dev/null 2>&1 &&
    [ "$(printf '%s\n%s\n' "$rust_min" "${v%%-*}" | sort -V | head -n 1)" = "$rust_min" ]
}

packages() {
  need=$(missing)
  if [ -z "$need" ]; then say "system packages: all there"; return; fi
  command -v apt-get >/dev/null 2>&1 ||
    die "missing: $need
Install them with your package manager, then run make install again. (The build links
xcb from /usr/lib/x86_64-linux-gnu, Debian's and Ubuntu's library folder.)"
  if [ "$(id -u)" = 0 ]; then sudo=
  elif command -v sudo >/dev/null 2>&1; then sudo=sudo
  else die "missing packages: $need
As root, run: apt-get install $need"; fi
  say "These system packages are missing: $need"
  say "Installing them now: ${sudo:+sudo }apt-get update; ${sudo:+sudo }apt-get install $need"
  [ -z "$sudo" ] || say "(sudo may ask for your password. To install them yourself instead, stop here; make check lists them.)"
  $sudo env DEBIAN_FRONTEND=noninteractive apt-get update -q || say "apt-get update failed; trying the install anyway"
  $sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends $need ||
    die "apt-get could not install them. Install them yourself, then run make install again:
  sudo apt-get install $need"
  need=$(missing)
  [ -z "$need" ] || die "still missing after apt-get: $need"
}

toolchains() {
  if ! command -v elan >/dev/null 2>&1; then
    say "Installing elan, Lean's toolchain manager, into $ELAN_HOME"
    curl --proto '=https' --tlsv1.2 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$tmp/elan-init.sh"
    sh "$tmp/elan-init.sh" -y --default-toolchain none --no-modify-path
  fi
  say "Lean $(cat lean-toolchain) (lean-toolchain; elan downloads it once)"
  lake --version
  if rust_ok; then say "Rust: $(rustc --version)"; return; fi
  if command -v rustup >/dev/null 2>&1; then
    say "Rust: rustc $rust_min or newer is needed; installing rustup's stable toolchain"
    rustup toolchain install stable --profile minimal
    RUSTUP_TOOLCHAIN=stable; export RUSTUP_TOOLCHAIN
  else
    say "Installing Rust (rustup, stable) into $CARGO_HOME and $RUSTUP_HOME"
    curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs -o "$tmp/rustup-init.sh"
    RUSTUP_INIT_SKIP_PATH_CHECK=yes sh "$tmp/rustup-init.sh" -y --profile minimal --default-toolchain stable --no-modify-path
  fi
  rust_ok || die "rustc $rust_min or newer is needed; found: $(rustc --version 2>&1)"
  say "Rust: $(rustc --version)"
}

install() {
  platform
  tmp=$(mktemp -d "$TMPDIR/lq-make.XXXXXX")
  trap 'rm -rf "$tmp"' EXIT INT TERM
  t0=$(date +%s)
  packages; t1=$(date +%s)
  toolchains; t2=$(date +%s)
  tools/make/assets.sh; t3=$(date +%s)
  say "Fetching the Rust crypto's crates (engine/native/crypto/Cargo.lock)"
  (cd engine/native/crypto && cargo fetch --locked)
  say "Building (platforms/linux/build.sh: the Rust crypto, then lake build linux)"
  platforms/linux/build.sh; t4=$(date +%s)
  [ -x "$app" ] || die "the build finished without $app"
  say "Built $app in $(mins $((t4 - t0))): packages $(mins $((t1 - t0))), Lean and Rust $(mins $((t2 - t1))), assets $(mins $((t3 - t2))), build $(mins $((t4 - t3)))"
  say "Now: make run"
}

open_app() {
  [ -x "$app" ] || die "the app isn't built yet: run make install first"
  [ -n "${DISPLAY:-}" ] || die "no X display (DISPLAY is unset). Lean Quiet's Linux window needs X11 or XWayland."
  mkdir -p out/make
}

case ${1:-} in
  install) install ;;
  run) shift; open_app
    db=${QUIET_DB:-out/make/demo.db}
    say "Lean Quiet with a demo: two seeded communities, networking off ($db)"
    QUIET_DB=$db exec "$app" --demo "$@" ;;
  online) shift; open_app
    db=${QUIET_DB:-out/make/quiet.db}
    say "Lean Quiet with networking on ($db)"
    QUIET_DB=$db exec "$app" "$@" ;;
  assets) tools/make/assets.sh ;;
  check) platform
    need=$(missing)
    if command -v elan >/dev/null 2>&1; then say "Lean: elan $(elan --version | cut -d' ' -f2)"
    else say "Lean: no elan yet (make install puts it in $ELAN_HOME)"; fi
    if rust_ok; then say "Rust: $(rustc --version)"
    else say "Rust: no rustc $rust_min or newer yet (make install puts rustup in $CARGO_HOME)"; fi
    if [ -x "$app" ]; then say "app: built ($app)"; else say "app: not built yet"; fi
    if [ -n "$need" ]; then
      say "system packages: missing $need"
      say "make install would run: sudo apt-get install $need"
      exit 1
    fi
    say "system packages: all there" ;;
  *) die "usage: $0 install|run|online|check|assets" ;;
esac
