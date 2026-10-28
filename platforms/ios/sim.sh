#!/bin/sh
# The Simulator side, on the Mac: a simulator of its own (an iPhone 16e on
# the newest iOS runtime, named $SIM_NAME, default lean-quiet-ios; made on
# first use, its UDID kept in work_dir/sim.udid) booted headless, the app
# installed and launched in it, screenshots, and its removal.
#
#   sim.sh work_dir udid               the simulator's UDID (made, booted)
#   sim.sh work_dir install APP        installs the .app afresh (its data too)
#   sim.sh work_dir launch [PORT] [TOKEN]  (re)launches the app, the
#                                      control channel on PORT (default
#                                      7417) with TOKEN (else the app's own), its
#                                      stdout and stderr to work_dir/app.log
#   sim.sh work_dir shot FILE.png      a screenshot of the simulator
#   sim.sh work_dir data               the app's data container (quiet.db)
#   sim.sh work_dir delete             shuts the simulator down, deletes it
#
# Needs Xcode at $DEVELOPER_DIR (default Xcode 26.3; never xcode-select).
set -eu
w=$1; what=$2
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
name=${SIM_NAME:-lean-quiet-ios}
app_id=local.leanquiet.app
mkdir -p "$w"

udid() {
  u=$(cat "$w/sim.udid" 2>/dev/null || true)
  if [ -z "$u" ] || ! xcrun simctl list devices | grep -q "$u"; then
    rt=$(xcrun simctl list runtimes iOS | sed -n 's/.* - \(com\.apple\.CoreSimulator\.SimRuntime\.iOS-[0-9-]*\)$/\1/p' | tail -1)
    [ -n "$rt" ] || { echo "no iOS simulator runtime" >&2; exit 1; }
    u=$(xcrun simctl create "$name" com.apple.CoreSimulator.SimDeviceType.iPhone-16e "$rt")
    echo "$u" > "$w/sim.udid"
  fi
  if ! xcrun simctl list devices | grep "$u" | grep -q Booted; then
    xcrun simctl boot "$u"
  fi
  xcrun simctl bootstatus "$u" -b >/dev/null
  echo "$u"
}

case $what in
  udid) udid ;;
  install)
    # a fresh install: no database from an earlier build
    u=$(udid); xcrun simctl uninstall "$u" "$app_id" 2>/dev/null || true; xcrun simctl install "$u" "$3" ;;
  launch)
    u=$(udid)
    SIMCTL_CHILD_LEANQUIET_CTL_PORT=${3:-7417} SIMCTL_CHILD_LEANQUIET_CTL_TOKEN=${4:-} \
      xcrun simctl launch --terminate-running-process \
      --stdout="$w/app.log" --stderr="$w/app.log" "$u" "$app_id" ;;
  shot) u=$(udid); xcrun simctl io "$u" screenshot "$3" >/dev/null 2>&1 ;;
  data) u=$(udid); xcrun simctl get_app_container "$u" "$app_id" data ;;
  delete)
    u=$(cat "$w/sim.udid" 2>/dev/null || true)
    if [ -n "$u" ]; then
      xcrun simctl shutdown "$u" 2>/dev/null || true
      xcrun simctl delete "$u"
      rm -f "$w/sim.udid"
    fi ;;
  *) sed -n 2,16p "$0"; exit 2 ;;
esac
