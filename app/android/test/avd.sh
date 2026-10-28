#!/usr/bin/env bash
# (From lean-qr android/test, 61ff438.) Creates an AVD if it is
# missing: an x86_64 google_apis image whose back camera is the virtual
# scene. avdmanager creates nothing on this machine, so the AVD is written
# by hand (config.ini and its .ini pointer) under ~/.android/avd.
#
# usage: avd.sh [name] [system image dir, relative to the SDK]
set -euo pipefail
name=${1:-qr-harness-20261027}
img=${2:-system-images/android-36/google_apis/x86_64/}
sdk=${ANDROID_SDK:-$HOME/android-sdk}
home=${ANDROID_AVD_HOME:-$HOME/.android/avd}
dir=$home/$name.avd
[ -d "$sdk/$img" ] || { echo "no system image $sdk/$img" >&2; exit 2; }
if [ -f "$dir/config.ini" ]; then echo "$name exists"; exit 0; fi
mkdir -p "$dir"
api=$(echo "$img" | sed -n 's|.*android-\([0-9]*\)/.*|\1|p')
cat > "$home/$name.ini" <<INI
avd.ini.encoding=UTF-8
path=$dir
path.rel=avd/$name.avd
target=android-$api
INI
cat > "$dir/config.ini" <<INI
AvdId=$name
avd.ini.displayname=$name
avd.ini.encoding=UTF-8
PlayStore.enabled=no
abi.type=x86_64
disk.dataPartition.size=4G
hw.accelerometer=yes
hw.audioInput=no
hw.battery=yes
hw.camera.back=virtualscene
hw.camera.front=none
hw.cpu.arch=x86_64
hw.cpu.ncore=4
hw.device.manufacturer=Google
hw.device.name=pixel_6
hw.gpu.enabled=yes
hw.gpu.mode=swiftshader_indirect
hw.keyboard=yes
hw.lcd.density=420
hw.lcd.height=2400
hw.lcd.width=1080
hw.ramSize=3072M
hw.sensors.orientation=yes
hw.sensors.proximity=yes
image.sysdir.1=$img
sdcard.size=256M
tag.display=Google APIs
tag.id=google_apis
target=android-$api
vm.heapSize=256M
INI
echo "created $name ($img)"
