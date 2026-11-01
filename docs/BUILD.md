# Reproducible builds

With one toolchain, a Lean build is byte-for-byte reproducible. The only
path-dependent outputs are the `.olean` files of modules that raise
warnings, because Lean stores each module's warnings in its `.olean`,
each with the absolute path of the source file.

Measured 2026-10-27 with Lean 4.34.0 on lean-quiet daf3ffa,
lean-engine-lists 354fb2a and lean-qr 61ff438, building
`lake build Quiet quiet_host two_nodes` (270 output files: `.olean`,
`.ilean`, generated `.c`, objects, `host.o` from the system `cc`, static
libraries and the two executables):

- **Same folder, clean rebuild:** all 270 files identical.
- **Two different folders:** 265 identical, both executables included.
  The five that differ are the `.olean` files of the five modules with
  warnings: `Community/Connect`, `Community/Link` and `Engine/Sqlite`
  (lean-engine-lists), `Qr/SegLaws` and `Qr/Segment` (lean-qr).
  lean-quiet's own modules raise no warnings, so their `.olean` files
  don't depend on the folder.
- **Control (lean-mdns 3f6f288):** renaming the one unused `h` in
  `Mdns/Decode.lean` to `_h` made `Decode.olean` identical across
  folders, while `Laws.olean`, with its warnings left in, still
  differed.

Lake's `.setup.json` and `.rsp` files hold absolute paths. They are
build bookkeeping, not output, and were left out of the comparison,
along with `.trace`, `.hash` and log files.

So:

- An executable is reproducible from any folder, given the same
  toolchain.
- For identical `.olean` files across machines, build from the same
  absolute path, or keep every module free of warnings.

Not measured: a second machine, the Android (NDK) and iOS (Xcode)
builds, and the toolchain's own build.

## System packages for the Linux desktop

`platforms/linux` (the `linux` executable, `linux:input`, `linux:e2e`)
links xcb from the system, and its tests drive a real X server. On
Ubuntu:

- To build: `libxcb1-dev`, `libxcb-shm0-dev`, `libxcb-sync-dev` (the
  window manager's `_NET_WM_SYNC_REQUEST` on resize) and `libx11-dev`
  (`shell.c` takes the cursor and key names from X11's headers).
- For `linux:e2e`: `xvfb`, `xdotool`, ImageMagick's `import` and Python's
  PIL. `tests/app/run.sh` skips it, building the shell only, under
  `SKIP_X=1` (by default whatever `SKIP_TCP` is).
- For `linux:links` (and `install.sh`): `xdg-utils` (`xdg-open`,
  `xdg-mime`), `desktop-file-utils` (`update-desktop-database`), `x11-utils`
  (`xprop`), `xvfb` and `xdotool`. `SKIP_X=1` skips it too.

## make install and make run (Linux)

The top-level `Makefile` is the hackathon's entry point: on a fresh
clone, `make install && make run` builds the Linux desktop and opens it.
It dispatches on `uname`: Linux runs `tools/make/linux.sh`; macOS runs
`tools/make/macos.sh`, which says it is not yet supported; other systems
say they are not supported.

`make install`, in order (run again, it redoes nothing that is done):

1. System packages: `gcc`, `libc6-dev`, `curl`, `ca-certificates`,
   `python3` and the four X packages above. It lists the missing ones,
   says it will install them, and runs `apt-get update` and
   `apt-get install` (with `sudo` unless root). Without apt it names what
   is missing and stops. The lakefile links xcb and libc from
   `/usr/lib/x86_64-linux-gnu`, so only Debian-style x86-64 systems build.
   `make check` lists what is missing and installs nothing.
2. Lean: elan into `ELAN_HOME` (default `~/.elan`), by its official
   script, then the toolchain `lean-toolchain` names. Rust: rustup's
   stable toolchain into `CARGO_HOME` and `RUSTUP_HOME` (defaults
   `~/.cargo`, `~/.rustup`), unless rustc 1.88 or newer (the newest
   `rust-version` among the crypto's locked crates) is already on `PATH`.
3. Assets (`tools/make/assets.sh`): one tarball of `assets/`, a GitHub
   release asset named by `tools/make/assets.pin`. Its sha256 is checked
   before it is opened, and each file against `tools/make/assets.sha256`
   after. `LQ_ASSETS_URL` downloads it from elsewhere (`https://` or
   `file://`). If it can't be had, `tools/fetch_assets.sh` builds the
   assets from their sources instead; that needs pip, unzip, librsvg,
   Cairo and the Noto fonts it pins (Ubuntu 24.04's `fonts-noto-core`).
4. `cargo fetch --locked` for the crypto's crates (the build itself runs
   offline), then `platforms/linux/build.sh`.

`make run` opens `.lake/build/bin/linux --demo` from the repository's
top, with `QUIET_DB=out/make/demo.db`. A judge has no second device, so
the demo seeds two communities on the first run, opens no sockets, and
shows the same screen every time; what they type is kept in that
database. `make online` runs the app with networking (the phone TCP
runner) and its own `out/make/quiet.db`. `ARGS` passes arguments to the
app (`make run ARGS="--chaos 300"`).

Updating the assets tarball: `tools/make/assets.py check` fails when a
change to the tree makes the published tarball stale (the Noto and CJK
hashes in `tools/*.sha256`, the glyph and UI font stamps, or the scripts
that make `font.bin`, `emoji.bin` and the photos). Then rebuild `assets/`
(`tools/fetch_assets.sh`), run `tools/make/assets.py pack`, which writes
the tarball to `out/make/` and rewrites the pin and the list, publish the
tarball under the pinned tag with `tools/make/publish_assets.sh`, and
commit the pin and the list. The script never marks the release latest
(the join page links `releases/latest/download/...`) and checks the
sha256 of the tarball it downloads back. Then
`CLEAN_ROOM_ASSETS=published mise run make:clean-room` tests what a judge
downloads.

Packing is deterministic: sorted names, time 0, owner 0, mode 0644, and
no name or time in the gzip header, so the same `assets/` gives the same
bytes with the same zlib.

| Task | Validation |
| --- | --- |
| `make:assets-test` | The assets step on made-up tarballs (no network): download, sha256 and per-file checks, repair, deterministic packing. Controls: a flipped bit, files that don't match the list, plain http, an unreachable URL, a stale pin and changed asset scripts must each fail |
| `make:clean-room` | `make install && make run` from a git clone of `HEAD` in fresh `ubuntu:24.04` and `debian:12` containers, as a user with sudo: `make check` fails and names the packages; a timed cold `make install`; a second one that redoes nothing; under Xvfb, a screenshot of the window must show it painted, while one of the empty screen must fail |

`ci/local.sh --full` runs both (parts `make:assets` and
`make:clean-room`). The clean room needs Docker and network access, and
about 10 GB under Docker's root per image while it runs; each container
gets 8 CPUs and 24 GB without swap (`CLEAN_ROOM_CPUS`,
`CLEAN_ROOM_MEMORY`). It packs the tarball from `assets/` here, fails
unless that has the pinned sha256, and serves it to the container by
`file://`; `CLEAN_ROOM_ASSETS=published` downloads the GitHub release
instead. Logs, `result.txt` (timings, peak memory) and screenshots stay
in `out/make/clean-room/<image>/`.

CLEAN_ROOM_RESULTS

## Checking it again

The measurement above predates the joined repository; its modules are
now `app/community/Connect`, `app/community/Link`, `engine/core/Sqlite`,
`engine/renderer/qr/SegLaws` and `engine/renderer/qr/Segment`, and the
build now links the engine's Rust crypto. Export one commit at two
roots, build both, then compare: by the measurement, only the `.olean`
files of modules with warnings should differ (not yet re-measured on
this layout).

```sh
export ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp
export PATH="$ELAN_HOME/bin:$PATH"
R="$TMPDIR/repro"
rm -rf "$R"
# Export both roots from one commit before building, so a commit landing
# mid-run can't split them.
c=$(git rev-parse HEAD)
for root in "$R/a" "$R/b/deeper"; do
  mkdir -p "$root"; git archive "$c" | tar -x -C "$root"
done
for root in "$R/a" "$R/b/deeper"; do
  (cd "$root/engine/native/crypto" && CARGO_TARGET_DIR="$PWD/target" cargo build --release --quiet)
  (cd "$root" && lake build Quiet quiet_host two_nodes)
  (cd "$root" && find .lake/build -type f ! -name '*.trace' ! -name '*.log*' \
     ! -name '*.hash' ! -name '*.setup.json' ! -name '*.rsp' |
   sort | xargs sha256sum) > "$root.sums"
done
diff "$R/a.sums" "$R/b/deeper.sums"
```

### Native system-photo selection

The composer uses Android's system photo picker (the document picker on API
30–32) and iOS PHPicker. Both read only the selected file, decode an oriented
sRGB image with a maximum side of 2048 pixels on a worker, and deliver a bounded
RGBA packet. Lean prepares the QOI attachment off the frame thread. Cancelling,
navigating, switching communities and duplicate/late callbacks cannot attach to
a different composer request. Presenting the OS picker may background the app;
that alone preserves the selection request. Desktop photo selection still opens
an availability notice. The development `photo` control command remains an
explicit bundled fixture; the drawn mobile button uses the real picker.

`mise run host:photo` builds and runs the shared native handoff under ASan/UBSan,
then drives actual composer/lifecycle/writer/attachment components against a
simulated OS result source. It is in the default local app CI gate. The request
predicates are running Lean code with accompanying laws; no claim is made that
Lean verifies UIKit, Android's decoder, or a wall-clock latency bound.

`mise run android:photo-e2e` builds the APK and a private AVD on `/mnt/storage`,
seeds a generated 4096×2048 JPEG with EXIF rotation, then drives the real picker:
cancel, immediately retry, choose, check 1024×2048 output, attach and send. It
never clears or tests against a physical phone. Prerequisites are the existing
Android SDK/NDK, API 36 google_apis x86_64 image, emulator/KVM, Java 17, Python
and Pillow. Logs, UI hierarchy and screenshots remain under `out/photo/android`.

`mise run ios:photo-e2e` builds/setup the private simulator via `MAC`, seeds its
Photos library and runs the same flow through XCUITest. The complete
`ios:sim-e2e` suite includes this case alongside scrolling/typing/navigation.
Prerequisites: the Mac lease described above, Xcode 26.3, an iOS simulator
runtime, xcodegen, SSH, matching Lean/libuv sources and the configured signing
setup for device builds. Failures retain `out/ios-sim/e2e.xcresult`, logs and
screenshots. `ios:device` produces a signed device build and installs nothing.

Provisioned mobile CI uses `ci/local.sh android-photo ios-ui` (the same named
Mise tasks), as the mobile release gate and as its manual dispatch. `ios-photo`
runs just the picker case; `android-ui` runs the native twin's input/keyboard
suite on the provisioned emulator named by `SERIAL` (default emulator-5644).
Run these before
a mobile release alongside the default deterministic local CI. GitHub Actions
is not used. The caller must hold the Mac lease and clean its private staging
folder/simulator after collecting build artifacts before releasing the lease.

During local app-test iteration, `APP_TEST_FROM=navigation ci/local.sh app`
resumes at a named stage after completing build/asset setup. Available stages
are `fonts`, `input`, `network`, `desktop`, `navigation`, `lifecycle`,
`appearance`, `safety`, and `components`. Omitted stages are explicitly logged;
a resumed run is not a full run. Without this variable, CI runs every stage.

### Android build modes

Both development and release APKs compile Lean-generated C and the Android
shell with `-O3`, SQLite with `-O2`, the Lean runtime with `-O3 -DNDEBUG`, and
Rust crypto with `--release`. `RELEASE=1` additionally removes the development
control listener, omits the manifest's debuggable flag, and selects D8's
`--release` mode. Local APKs still use the same development signing certificate
so installation can preserve an existing database; this is not store signing.

`mise run android:release-e2e` builds both modes and creates its own API 36 AVD
(`lean-quiet-release`, port 5594) under `/mnt/storage/holmes-avd`. It verifies
debug/run-as access and control-channel isolation, then runs the same native
swipe sequence over the same retained chaos database in each mode. It checks
that the transcript changes and the process survives, retaining screenshots,
CPU measurements, 120-frame native timing averages, and logcat under
`out/ctl-guard`. These emulator measurements are not Pixel latency guarantees.
This requires the Android photo suite's SDK/KVM/Java/Python prerequisites.
The provisioned release/manual CI entry is `ci/local.sh android-release`.

## macOS shared desktop

Apple Silicon macOS builds use the same Lean desktop as Linux, through an
AppKit shell. Build/setup and native OS-input tests are named Mise tasks
(`macos:build`, `macos:run`, `macos:e2e`). The manual/release local CI gates
`macos-ui` and `release-macos` invoke the same suite and propagate failures.
See [platforms/macos/README.md](../platforms/macos/README.md) for runner
prerequisites, artifact paths and data ownership.


## Shared message skeletons

`mise run host:skeleton` sets up fonts, builds the actual app fixture and checks
`engine/renderer/Hold` at 1×, 2×, 2.625× and 3×, both themes, narrow clipping and
phone/desktop widths. It exercises pending and unloaded `App.listFrame` rows
and `App.present` with both platform modes, comparing native fill-plane pixels
at signed offsets. PPM previews are retained in `out/skeleton`. The default
local CI app gate invokes this named task in its components stage.

Skeletons share the message avatar/text columns and use an 80 dp period,
published in placement word 26. All native compositors consume that period.
The legacy 48-pixel functions remain for compatibility and their existing Lean
proofs. The variable-period scalar exports have separate independent C-oracle,
boundary/thread and no-allocation audits in `mise run host:slide`; the legacy
proofs do not establish arbitrary-period geometry. `host:translate` retains the
legacy per-vsync pixel oracle. No animation or platform-specific drawing is
needed for the new skeletons.

## Windows desktop

`mise run windows:build` stages the shared Lean desktop and builds the Windows
executable in the local VM. `mise run windows:e2e` includes setup and exercises
real Windows input, persistence, encrypted TCP and listener restart.
See [Windows prerequisites, launch and release gates](../platforms/windows/README.md).
