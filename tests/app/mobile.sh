#!/usr/bin/env bash
# Provisioned-machine suites only. Keep build and run output even when
# either fails; the platform scripts collect their own final artifacts.
set -euo pipefail
cd "$(dirname "$0")/../.."
case ${1:?android or ios} in
  android)
    mkdir -p out/e2e-twin
    mise run android:twin-demo-apk 2>&1 | tee out/e2e-twin/build.log
    platforms/android/test/twin_demo_e2e.sh "${SERIAL:-emulator-5644}" out/e2e-twin \
      2>&1 | tee out/e2e-twin/suite.log ;;
  ios)
    mkdir -p out/ios-sim
    platforms/ios/ship.sh e2e 2>&1 | tee out/ios-sim/run.log ;;
  *) echo "expected android or ios" >&2; exit 2 ;;
esac
