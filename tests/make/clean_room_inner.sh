#!/usr/bin/env bash
# Inside a fresh Debian or Ubuntu container (tests/make/clean_room.sh runs
# this as root): what a judge does, as a user with sudo.
#   1. Install only what a judge already has (git, make, sudo) and the
#      test's own tools (Xvfb, xwd, ImageMagick), then forget apt's lists.
#   2. git clone the repository (a bundle of the commit under test).
#   3. make check must fail and name the missing packages, installing none.
#   4. make install, timed (cold: no Lean, Rust, crates or packages), then
#      make install again, which must redo nothing.
#   5. make run under Xvfb (1600x1000, 24-bit TrueColor); a screenshot of
#      the empty screen must fail the content check (the control), and one
#      of the app's window must pass it while the app is still running.
# Writes /out: logs, shots and result.txt (key=value). Needs ASSETS_URL
# (empty: the URL the pin names) and HOST_UID/HOST_GID for /out's owner.
set -uo pipefail
out=/out
res=$out/result.txt
: > "$res"
finish() {
  local code=$?
  echo "exit=$code" >> "$res"
  [ -r /sys/fs/cgroup/memory.peak ] && echo "memory_peak_bytes=$(cat /sys/fs/cgroup/memory.peak)" >> "$res"
  chown -R "${HOST_UID:-0}:${HOST_GID:-0}" "$out" 2>/dev/null
  exit "$code"
}
trap finish EXIT
step() { echo "step=$1" >> "$res"; echo "== $1"; }
die() { echo "fail=$*" >> "$res"; echo "FAIL $*" >&2; exit 1; }
judge() { su - judge -c "cd ~/lean-quiet && $1"; }

step setup
export DEBIAN_FRONTEND=noninteractive
{ apt-get update -q && apt-get install -y -q --no-install-recommends git make sudo xvfb x11-apps imagemagick procps; } \
  > "$out/setup.log" 2>&1 || die "the test's own packages did not install (setup.log)"
rm -rf /var/lib/apt/lists/*
useradd -m -s /bin/bash judge
echo 'judge ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/judge
su - judge -c 'git clone -q /srv/repo.bundle lean-quiet' > "$out/clone.log" 2>&1 || die "git clone failed"
echo "commit=$(su - judge -c 'git -C lean-quiet rev-parse --short HEAD')" >> "$res"
. /etc/os-release; echo "os=$PRETTY_NAME" >> "$res"

step check
if judge 'make check' > "$out/check-before.log" 2>&1; then die "make check passed on a machine missing the build's packages"; fi
grep -q 'missing.*libxcb-shm0-dev' "$out/check-before.log" || die "make check did not name the missing packages"
dpkg-query -W -f='${db:Status-Abbrev}' libxcb1-dev 2>/dev/null | grep -q '^ii' && die "make check installed packages"

step install
url=${ASSETS_URL:+LQ_ASSETS_URL=$ASSETS_URL }
t0=$(date +%s)
judge "${url}make install" > "$out/install.log" 2>&1
code=$?
t1=$(date +%s)
echo "install_seconds=$((t1 - t0))" >> "$res"
grep '^==> Built' "$out/install.log" | sed 's/^==> /install_summary=/' >> "$res"
[ "$code" = 0 ] || die "make install exited $code (install.log)"
grep -q 'apt-get install' "$out/install.log" || die "make install did not say it would install packages"

step install-again
t0=$(date +%s)
judge "${url}make install" > "$out/install-again.log" 2>&1 || die "a second make install failed (install-again.log)"
echo "install_again_seconds=$(($(date +%s) - t0))" >> "$res"
grep -q 'system packages: all there' "$out/install-again.log" || die "the second make install reinstalled packages"
grep -q 'files in place' "$out/install-again.log" || die "the second make install downloaded the assets again"
if grep -q 'Installing elan\|Installing Rust' "$out/install-again.log"; then die "the second make install reinstalled Lean or Rust"; fi

step run
Xvfb :99 -screen 0 1600x1000x24 -nolisten tcp -ac > "$out/xvfb.log" 2>&1 &
for _ in $(seq 50); do [ -S /tmp/.X11-unix/X99 ] && break; sleep 0.2; done
[ -S /tmp/.X11-unix/X99 ] || die "Xvfb did not start (xvfb.log)"
shot() { xwd -root -display :99 -silent | convert xwd:- "png:$1"; }
colors() { identify -format '%k' "$1"; }
min_colors=64
# The control: the empty screen has one colour, and fails the check.
shot "$out/shot-empty.png"
[ "$(colors "$out/shot-empty.png")" -lt "$min_colors" ] || die "the content check passed an empty screen"
echo "empty_colors=$(colors "$out/shot-empty.png")" >> "$res"
setsid su - judge -c 'cd ~/lean-quiet && DISPLAY=:99 exec make run' > "$out/run.log" 2>&1 &
run_pid=$!
t0=$(date +%s) n=0 painted=0
while [ $(($(date +%s) - t0)) -lt 180 ]; do
  sleep 3
  kill -0 "$run_pid" 2>/dev/null || die "make run exited early (run.log)"
  shot "$out/shot.png" || continue
  n=$(colors "$out/shot.png")
  [ "$n" -ge "$min_colors" ] && { painted=1; break; }
done
echo "shot_colors=$n" >> "$res"
echo "first_paint_seconds=$(($(date +%s) - t0))" >> "$res"
[ "$painted" = 1 ] || die "the window never painted: $n colours after 180 s (shot.png)"
# a few seconds more: the demo's seeding settles, and the app stays up
sleep 5
shot "$out/shot.png"
echo "shot_colors=$(colors "$out/shot.png")" >> "$res"
pgrep -u judge -x linux > /dev/null || die "the app exited after painting (run.log)"
kill -TERM -- -"$run_pid" 2>/dev/null
step pass
