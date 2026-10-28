# Testing the native builds

`ci/local.sh` runs the desktop gates. SQLite comes from
`third_party/sqlite/sqlite3.c` (3.50.4), built by Lake's `libsqlite`
extern library. Desktop, Android and iOS include `quiet_config.h`:
`SQLITE_THREADSAFE=2`, `SQLITE_DQS=0`, `SQLITE_DEFAULT_MEMSTATUS=0`,
`SQLITE_OMIT_LOAD_EXTENSION`. All three compile `engine/native/glue.c`.
Changing the options invalidates each build's SQLite object cache.

The engine gate checks the linked version and options through `Db`'s
actual externs, then runs the differential, crash and purge suites.
Purge searches the database, WAL and SHM files for secret bytes after
VACUUM and the WAL truncate, including while a reader holds the WAL.
Its existing controls omit the scrub or checkpoint and find retained
bytes. `tests/shipped/check.sh engine` also rebuilds with the system
SQLite, and with the wrong threading option; both must fail the checks.

The app gate includes `mise run host:twin-demo`: nine checks through
`platforms/headless/host.c`, covering taps, keyboard/text, send, scroll,
control replies and painted pixels. Its script, replies, stderr and
three PPM frames stay in `out/host-twin`. A scratch mutation disables
the C keyboard effect and must fail the same session. A second control
restores absolute dump paths, which host.c truncates at 63 characters;
the harness uses short names from its output directory and removes old
frames before running, so a missing dump cannot pass on stale pixels. Mutation logs
and frames stay in `out/shipped`. These checks make no new Lean laws.

On a socket-restricted sandbox, `SKIP_TCP=1 ci/local.sh` builds but
does not run `tcppair`, `jointcp`, `net_join`, `cross` and `attach`.
The report explicitly marks those omissions. Run the gate without that
variable on an unrestricted host to close them. No mobile test runs
as part of this local gate.

## The phone runtime options on desktop

`mise run test:engine-runtime` (also `ci/local.sh runtime`) builds the
phone runtime configuration for x86_64 Linux and runs the same engine
suites. It needs clang/clang++, ar/nm/readelf, Python 3, libsodium for the
crypto comparison, the pinned Lean toolchain,
the Rust crypto dependencies, and local source checkouts:

- `LEAN_SRC`: Lean 4.34.0, default
  `/mnt/storage/holmes-wt/lean-src/lean4`;
- `UV_SRC`: libuv 1.51.0, default
  `/mnt/storage/holmes-wt/lean-src/libuv`.

`platforms/headless/build_runtime.py` copies the toolchain's headers,
removes `LEAN_MIMALLOC`, leaves `LEAN_USE_GMP` undefined, and compiles
only `openssl.cpp` with `LEAN_EMSCRIPTEN`, as the phones do. All builds
use `platforms/leanrt/runtime.txt`; Linux and Android share libuv's
source list too. Init's 649 modules and the engine suites' entire
generated C closure (including Std) are recompiled against those
headers. There is no link to prebuilt Init, Std or Lean runtime code.
The original toolchain still elaborates Lean and checks the proofs.

Outputs and compiler command logs stay under `out/phone-runtime/`;
tests write under its `tests/` directory. `JOBS` bounds compilation
parallelism (default 8). Source and command hashes cache native objects.
An artifact check refuses mimalloc/GMP/OpenSSL symbols or links to
prebuilt shared Lean/SQLite libraries; substituting the toolchain's
runtime archive in a scratch copy must fail that check.
`SKIP_TCP=1` omits only the two engine socket runs, as above.

This tests the allocator, bignums and OpenSSL stubs on Linux. It does
not test Android's libc/NDK, arm64 pointer tagging, UIKit/Android event
delivery, or iOS's Darwin libuv sources, disabled `system()` and smaller
thread stacks. The emulator and Simulator jobs below exercise those
shells; physical-device testing remains separate.

## Provisioned mobile machines

These are manual or nightly jobs in `ci/workflow.yml`, which is an
inactive workflow template. They are deliberately separate from the
ordinary desktop gate. Activate that workflow and provision its runners
before expecting mobile coverage. Both suites include their build step,
fail on a failed build, and upload artifacts even when the run fails
(14-day retention). They must have exclusive use of their test targets.

| Task / runner label | Required machine | Session and artifacts |
|---|---|---|
| `android:twin-demo-e2e` / `linux, kvm, android` | Linux x86_64 with KVM, SDK/NDK, build-tools, Java 17+, Rust's x86_64 and arm64 Android targets, Lean/libuv sources above, Python with Pillow, mise. A dedicated **already booted** x86_64 emulator at `SERIAL` (default `emulator-5644`), 1080-pixel wide screen with the suite's expected 63-pixel navigation inset. No physical-device serial is accepted. `ANDROID_SDK`/`ANDROID_HOME` default to `~/android-sdk`; set both when overriding it. | Builds the runtime and twin APK for both ABIs, then builds/installs the test IME and drives taps, keyboard animation, Unicode composition, send, drag/fling, scrolling and Back. Restores the IME on exit. `out/e2e-twin/`: build/suite logs, logcat and screenshots, collected on failure too. |
| `ios:sim-e2e` / `linux, ios` | Linux build coordinator with Lean/libuv sources, Rust's `aarch64-apple-ios` and `aarch64-apple-ios-sim` targets, assets and SSH access to a dedicated Apple Silicon Mac (`MAC`, CI variable `LEANQUIET_CI_MAC`). The Mac needs Xcode 26.3 at the path in `ship.sh`, an iOS Simulator runtime, xcodegen at `~/quiet-e2e/xcodegen/bin/xcodegen`, and an unlocked login session. The task builds on the Mac; it is not a native macOS mise task. | Stages generated C, shared glue, SQLite and assets; builds, installs and launches in the suite's `lean-quiet-ios` Simulator, then runs both XCTest UI sessions (conversation and pinned Paste page). `out/ios-sim/`: complete run/build log, test/app logs, screenshots and the copied `e2e.xcresult`, also after failure. See [the shell's setup](../platforms/ios/README.md). |

The `lean-runtime` runner needs the Linux runtime prerequisites above;
its manual/nightly job runs the engine suites without socket omissions
and retains compiler logs and test databases. No job uses a phone.
The mobile jobs use fixed concurrency groups so runs cannot overlap.
