#!/usr/bin/env bash
# Only callers that already verified ownership of their emulator use this.
# sys.boot_completed does not imply MediaProvider's external volume is attached.
set -euo pipefail
serial=${1:?owned emulator serial};fixture=${2:?fixture image};art=${3:?artifacts}
case $serial in emulator-*) ;; *) echo 'photo fixture requires an owned emulator' >&2;exit 2;;esac
sdk=${ANDROID_SDK:-$HOME/android-sdk}
adb=("$sdk/platform-tools/adb" -s "$serial")
mkdir -p "$art"
probe=/sdcard/Pictures/.quiet-photo-ready-$$
deadline=$((SECONDS+30))
until timeout 2 "${adb[@]}" shell "mkdir -p /sdcard/Pictures && touch $probe && rm $probe" >>"$art/storage-ready.log" 2>&1; do
  if [ "$SECONDS" -ge "$deadline" ]; then
    "${adb[@]}" shell dumpsys mount >"$art/storage-mount.txt" 2>&1 || true
    "${adb[@]}" logcat -d >"$art/storage-logcat.txt" 2>&1 || true
    echo 'owned emulator media volume did not become writable' >&2;exit 2
  fi
  sleep .1
done
timeout 20 "${adb[@]}" push "$fixture" /sdcard/Pictures/quiet-photo-fixture.jpg
timeout 20 "${adb[@]}" shell am broadcast -a android.intent.action.MEDIA_SCANNER_SCAN_FILE \
  -d file:///sdcard/Pictures/quiet-photo-fixture.jpg
