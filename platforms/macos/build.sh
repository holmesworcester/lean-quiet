#!/usr/bin/env bash
# Runs on macOS against the shared native source stage.
set -euo pipefail
st=$(cd "$1" && pwd)
mkdir -p "$2"; b=$(cd "$2" && pwd)
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Applications/Xcode-26.3.0.app/Contents/Developer}
rt=$b/leanrt
[ -f "$rt/macosx/libInit.a" ] || "$st/ios/leanrt.sh" "$st" "$rt" macosx
obj=$b/objects; mkdir -p "$obj"
header_hash=$(cat "$st"/glue/*.h "$st"/lean/include/lean/*.h | shasum | cut -c1-40)
export header_hash
for src in "$st"/ir/*.c "$st"/glue/{glue,crypto,sqlite3}.c; do
  flags="-O2 -w -I$st/lean/include -I$st/glue"
  [[ $src = */platforms.macos.Main.c ]] && flags="$flags -Dmain=lean_app_main"
  [[ $src = */sqlite3.c ]] && flags="$flags -include $st/glue/quiet_config.h"
  printf '%s|%s\n' "$src" "$flags"
done > "$b/sources.txt"
export obj
tr '\n' '\0' < "$b/sources.txt" | xargs -0 -P "${JOBS:-8}" -n 1 bash -c '
  src=${0%%|*}; flags=${0#*|}; o=$obj/$(basename "${src%.c}").o
  hash=$( (echo "$flags $header_hash"; cat "$src") | shasum | cut -c1-40)
  if [ ! -f "$o" ] || [ "$(cat "$o.sha" 2>/dev/null)" != "$hash" ]; then
    xcrun -sdk macosx clang -target arm64-apple-macos14.0 $flags -c "$src" -o "$o.tmp" && mv "$o.tmp" "$o" && echo "$hash" > "$o.sha" || exit 255
  fi'
app=$b/LeanQuiet.app
mkdir -p "$app/Contents/MacOS" "$app/Contents/Resources"
# Explicit members: stale objects from a changed closure never reach the link.
objects=()
while IFS='|' read -r src flags; do objects+=("$obj/$(basename "${src%.c}").o"); done < "$b/sources.txt"
xcrun -sdk macosx clang -target arm64-apple-macos14.0 -fobjc-arc -O2 -I"$st/lean/include" \
  "$st/macos/shell.m" "${objects[@]}" "$st/glue/rust/macosx/liblq_crypto.a" \
  "$rt/macosx/libInit.a" "$rt/macosx/libleanrt.a" "$rt/macosx/libuv.a" \
  -framework Cocoa -framework QuartzCore -framework Security -lc++ -o "$app/Contents/MacOS/LeanQuiet"
rsync -a --delete "$st/assets/" "$app/Contents/Resources/assets/"
cat > "$app/Contents/Info.plist" <<PLIST
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
<key>CFBundleExecutable</key><string>LeanQuiet</string>
<key>CFBundleIdentifier</key><string>local.leanquiet.desktop</string>
<key>CFBundleName</key><string>Lean Quiet</string>
<key>CFBundlePackageType</key><string>APPL</string>
<key>CFBundleShortVersionString</key><string>0.1.0</string>
<key>CFBundleVersion</key><string>${BUILD_NUMBER:-1}</string>
<key>LSMinimumSystemVersion</key><string>14.0</string>
<key>NSHighResolutionCapable</key><true/>
</dict></plist>
PLIST
codesign --force --sign - "$app"
echo "$app"
