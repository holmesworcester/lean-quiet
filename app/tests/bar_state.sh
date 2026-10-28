#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p out/safe/java
javac --release 17 -d out/safe/java \
  android/twin/java/com/holmes/leanquiet/BarState.java android/test/BarsTest.java
java -cp out/safe/java com.holmes.leanquiet.BarsTest
