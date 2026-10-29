# lean-quiet on iOS

The app (Main.lean over the app's modules) on UIKit: `quiet_ios.m`
implements Platform.lean's seam, and `ctl_ios.c` is the control channel.
Lean has no iOS libraries, so ship.sh stages the C of Main's whole module
closure (the repository's modules and Std's), Init's C, Lean's runtime source, libuv's source, the
SQLite glue and the engine's crypto (its Rust library, built here for both
iOS targets). The Mac then builds all of it
with Xcode's clang (`build_ios.sh`, `leanrt.sh`). The scripts run from the
Linux box and do the Mac's part over SSH.

## Tasks

| task | what |
| --- | --- |
| `mise run ios:sim` | Builds for the Simulator, installs and launches the app in a simulator of its own (an iPhone 16e on the newest iOS runtime, named `lean-quiet-ios`, booted headless), seeds 500 chaos messages if the database has none, and saves a screenshot to `out/ios-sim/launch.png`. |
| `mise run ios:sim-e2e` | `ios:sim`, then the UI tests (`UITests/`) in that simulator, with real touches and the software keyboard. Each step is checked in Lean's state, and the twin's placement in the twin's own report (the control line `twin`), both read through the control channel. Screenshots are kept as artifacts and are never the check. The tap targets come from Lean (`test/Targets.lean`), so the test computes no layout of its own. **The conversation:** it flings towards older messages, comes back to the newest, long-presses a message to open the reaction sheet (the viewport shrinks) and taps the header to close it, then taps the composer's text rows to open the keyboard, types a message and sends it with the keyboard's Send key; the message is then stored and on screen. **A pinned page:** on Paste with the keyboard closed, page row 0 is at the viewport's top (`Seam.pinned`) and the page's bottom edge is the closed composer's top. A tap on the field opens the keyboard, after which the composer has risen and the page has not moved. A link is typed into the field, and a tap on Continue above the keyboard is reported as `pinned_tap` reads it; Lean takes it as Continue and moves on to Choose a name. Screenshots go to `out/ios-sim/shots/`, logs to `out/ios-sim/` (`e2e.log` with the `pinned:` measurements), and the result bundle is copied to `out/ios-sim/e2e.xcresult`. The exit trap collects artifacts on failure too. |
| `mise run ios:mdns` | The network probe (`probe/`) in that simulator. It reports three results separately, each from the app's own verdict and the Mac's view. **(1) lean-mdns raw multicast:** Lean's own UDP socket. The app announces `lean-ios-sim` of type `_leanquiet._udp`, and the Mac must list it (`dns-sd -B`) and resolve it (`dns-sd -L`). The Mac registers `dns-sd -R probe _leanquiet._udp local 7001`, and the app must log it as found. **(2) dns_sd:** the system's DNS-SD through `probe/dnssd.c`, driven by Lean. It registers `lean-ios-sim-sd` (the Mac must list it), browses, and resolves the Mac's `probe` to an address that Lean then connects to over TCP. **(3) TCP:** Lean connects out to the Mac and listens for the Mac's connection. The report goes to `out/ios-sim/probe-sim.txt` (`RESULT <name>: PASS/FAIL`); the task fails unless all three pass. |
| `mise run ios:device` | Builds a signed app for an iPhone. It installs nothing. |
| `mise run ios:ctl-guard` | Who can drive the control channel, in the simulator: no token or a wrong one gets nothing, the launch's token is answered, the Mac's Wi-Fi address is refused, and a `RELEASE=1` build neither listens nor holds a listener (`test/ctl_guard_mac.sh`). The development build stays installed. |
| `mise run ios:e2e` | End to end on the iPhone (`DEVICE`; ask before using it). It builds, installs and launches the app (`device_mac.sh`) with the control channel on every interface (`LEANQUIET_CTL_REMOTE=1`) behind a token made for the run, then drives it from the Mac over the Wi-Fi: chaos data if the database has none, Lean's state (data present, rows mounted), and frames still being drawn 5 s later. The console goes to `out/ios-device/`. The app is left running. |
| `mise run ios:mdns-device` | `ios:mdns` on the iPhone (instance `lean-ios-phone`), over the Mac's Wi-Fi. The first run needs a person to tap Allow on the phone's local network prompt. `IOS_MULTICAST=1` also asks for the multicast entitlement (see below). The report goes to `out/ios-sim/probe-device.txt`. |
| `platforms/ios/ship.sh run` | Device build, then install and launch on `$DEVICE`. Ask before using the phone. |
| `platforms/ios/ship.sh ctl CMD...` | Sends control commands (`state`, `chaos 500`, `wait`, `visible`, `send TEXT`, …; see `App.command`) to the app in the Simulator. |
| `platforms/ios/ship.sh shot FILE` | Saves a screenshot of the simulator to FILE on this box. |
| `platforms/ios/ship.sh clean` | Deletes the simulator and the Mac's work directory. |

## Prerequisites

- **Here:** the Lean toolchain (`ELAN_HOME`, default `/mnt/storage/elan`)
  and the repository, built by lake. You also need Lean's source at the toolchain's version
  (`LEAN_SRC`, default `/mnt/storage/holmes-wt/lean-src/lean4`, tag
  v4.34.0) and libuv v1.51.0 (`UV_SRC`, default
  `/mnt/storage/holmes-wt/lean-src/libuv`). The engine's Rust crypto needs
  cargo with the targets `aarch64-apple-ios` and `aarch64-apple-ios-sim`
  (`rustup target add`); it builds here, and the Mac only links it.
  `assets/` comes from `tools/fetch_assets.sh`. Init's C goes to `out/initc`
  (`tools/gen_init_c.sh`). Std's C is cached in `out/stdc`.
- **The Mac** (`MAC`, required: `user@host`): SSH without a
  password, and Xcode at `/Applications/Xcode-26.3.0.app` (used through
  `DEVELOPER_DIR`; never `xcode-select`) with an iOS simulator runtime.
  xcodegen must be at `~/quiet-e2e/xcodegen/bin/xcodegen` (`XCODEGEN`).
  For the device you also need the `quiet-build` keychain and the team's
  wildcard development profile (`IOS_PROFILE`), as lean-chat uses them.
  Everything goes in `~/lean-quiet-ios-work` (`MAC_DIR`): `stage/` (the
  tree from here), `build/` (Lean's runtime for each SDK, built once, and
  the app's objects, rebuilt only when their C changes, about 1 GB with
  DerivedData), `out/` and `sim.udid`.
- **The Mac is shared:** run `mac-turn wait <name>` first and
  `mac-turn release <name>` after (`~/.local/bin/mac-turn`).

## How the twin maps the seam

- **Screen:** pixels are device pixels (the screen's scale, 3 on an iPhone
  16e: 1170 x 2532). The density is 160 per point, so Lean's dp is UIKit's
  point. The insets are the safe area's.
- **Placement:** `Session.present` publishes `Surface.make`'s source and
  destination rectangles. The visible layer is outside the scroll view;
  UIKit copies the rectangles, converting pixels to points. Pages use
  `Seam.pinned`; conversations use `Seam.place`. `Placement.lean` audits
  these running functions, including serialization and input mapping.
  Each CADisplayLink calls the compiled `engine.renderer.Slide` helpers to move
  the published buffer at the current OS offset and fill exposed rows
  with Lean's shared `holdLine` plane. Pinned pages ignore the sample.
- **Header and composer:** their coordinates and the repeated composer
  rows below it come from Lean. They keep their published placement until
  Lean publishes another frame; keyboard motion follows Lean's frame rate.
- **Keyboard:** UIKit retains text editing, composition and the keyboard
  height probe. Raw hardware keys and IME return actions go to Lean.
- **Touches:** a passive observer forwards down/move/up/cancel, time,
  pointer ID, displayed frame serial and translation. `Input` chooses the
  first pointer, applies slop and long-press time, and maps the down position. Accepted
  list samples drive a hidden UIScrollView's native animation; its offset
  is clamped by Lean for each new frame. Between frames the compositor
  helpers translate and fill without clamping or waiting for App.step.
- **Pixels:** Lean's rows are R G B X and IOSurface's are B G R A, so a row
  is swizzled as it is copied. Rows that are the same object as last
  frame's are not copied: the staging buffer shifts and only new rows are
  copied in. Each layer has a ring of three IOSurfaces.
- **Control channel:** development builds only. `build_ios.sh` compiles
  `ctl_ios.c` with `LQ_CTL` unless `RELEASE=1`; a release build has no
  listener at all, and `ctlPoll` answers nothing. It listens on TCP
  127.0.0.1 (`LEANQUIET_CTL_PORT`, default 7417; 0 turns it off). In the
  Simulator that is the Mac's loopback. TCP carries no peer uid
  (Android's `SO_PEERCRED`), and other apps on a phone can reach
  127.0.0.1 too. So every connection must first send the token, `token
  <hex>`, 128 random bits compared in constant time. A connection that
  doesn't is closed, unread and unanswered.
  - **The token:** the launch's `LEANQUIET_CTL_TOKEN`; otherwise the app
    makes one and keeps it in `Documents/ctl.token` (0600). `ship.sh`
    keeps one per checkout in `out/ios-sim/ctl.token`. `device_mac.sh`
    makes one per run.
  - **Every interface:** only for a launch with `LEANQUIET_CTL_REMOTE=1`
    (a device test over the Mac's Wi-Fi), still behind the token. The
    listener then logs the phone's addresses.
  - **The line `twin`:** answered by the twin itself, for tests. It
    reports the screen's width and density, whether the frame is a page,
    the header's height, the overscan, the screen rows of the list
    frame's first row and of the scroll view's bottom (as UIKit laid them
    out), the composer's top, the last list tap reported, the last camera
    frame's header, and the keyboard's text.
  - **`twin local`:** puts a channel that listens on every interface back
    on 127.0.0.1 without a relaunch.
  - **`twin shot`:** writes the app's window to `Documents/screen.png`.
  - **The check:** `mise run ios:ctl-guard`.
- **Log:** stderr, Lean's and the twin's, also goes to `Documents/lean.log`,
  new at each launch. A phone's run can then be read back with `devicectl
  device copy from … --source Documents/lean.log`, for example the node's
  `node: listening on 47100, dialed as …`, without holding its console
  (ending a held console ends the app).
- **Working directory:** the app's Documents directory. `quiet.db` lives
  there, and `assets` is a symlink to the bundle's assets, made again at
  each launch.

- **Camera (Join with QR code):** `lq_scan` starts or stops an
  AVCaptureSession on the back wide-angle camera (1280 x 720, `420f`,
  frames not rotated). `lq_luma` hands Lean the newest frame's Y plane as
  `[w, h, stride, 90]`: the sensor is landscape, so a quarter turn
  clockwise makes a frame upright in portrait, as Camera2's
  SENSOR_ORIENTATION says of a back camera. Lean draws the preview
  (`Camera.preview`) and decodes (`Qr.decodeLuma`). Where there is no
  camera (the Simulator), nothing starts and no permission is asked; Lean
  keeps "Starting the camera…". `NSCameraUsageDescription` is in
  `project.yml`. Each step goes to stderr, as on Android.
- **Lean's threads:** Lean's runtime reserves 1 GB of stack for each
  thread on 64-bit. An iOS app's address space runs out after a few such
  threads, and `pthread_create` then fails with EAGAIN ("failed to create
  thread: Resource temporarily unavailable"). This happens on the phone,
  not in the Simulator. So the twin sets `LEAN_STACK_SIZE_KB=65536` before
  starting Lean, unless the launch environment sets it.

### Simplified compared with Android

- No predicted offset during a fling. The current OS sample drives the
  compiled Lean translation and fill helpers every refresh. See
  [SEAM.md](../docs/SEAM.md) for the coverage interface and proof statements.
- No hang watchdog.
- The control channel cannot be reached on a phone.
- `scrolling` is reported from the scroll view's tracking and decelerating
  flags, read every refresh.

## Networking on iOS

These findings come from `ios:mdns` (Simulator) and `ios:mdns-device`
(iPhone 16e, iOS 18.5) on 2026-10-27.

- **Simulator:** the app's sockets are the Mac's, and everything works.
  lean-mdns binds UDP 5353 next to mDNSResponder (libuv's REUSEADDR is
  SO_REUSEPORT on Darwin) and joins 224.0.0.251. The Mac's `dns-sd -B`
  and `dns-sd -L` see the app's announcement, and the app finds the Mac's
  `dns-sd -R`. Across machines on the LAN, avahi on another host resolves
  the app, and the app finds that host's avahi registration. Lean's TCP
  connect and listen both work. The probe announces every non-loopback
  address, and avahi picked the Mac's Tailscale address, so the app should
  announce only the Wi-Fi address.
- **iPhone, lean-mdns:** raw multicast is blocked. With local network
  access granted, `Net.open` still binds 5353 and joins the group, but
  every send and receive fails with EHOSTUNREACH (65). That is Apple's
  documented behaviour without the multicast entitlement (below). The
  Mac's dns-sd never sees `lean-ios-phone`, and the app never hears the
  Mac.
- **iPhone, TCP:** Lean's connect to the Mac and its listener (the Mac
  connecting to the phone's 192.168.4.36) both work over Wi-Fi.
- **iPhone, DNS-SD (the fallback below):** it works across machines. The
  phone's registration `lean-ios-phone-sd` is listed by the Mac's
  `dns-sd -B`, and is listed and resolved to 192.168.4.36:7401 by avahi on
  a third host on the Wi-Fi. A capture there shows the phone's full
  announcement: PTR, SRV, TXT, A. The phone resolves the Mac's `probe` to
  192.168.4.32:7001, and an avahi registration on the third host to its
  address and port.
- **Local network privacy (iPhone):** an app that has not been granted
  local network access gets EHOSTUNREACH (65) for every outgoing packet to
  the LAN. That includes multicast and also plain TCP to a LAN address.
  iOS asks once ("… would like to find and connect to devices on your
  local network") and a person must tap Allow. Incoming TCP to an app's
  listener works without the prompt: the e2e's control connection from
  the Mac reached the phone. The app's Info.plist therefore carries
  `NSLocalNetworkUsageDescription` and `NSBonjourServices`
  (`_leanquiet._udp`, `_leanquiet._tcp`), both in `project.yml`.
- **The multicast entitlement:** raw multicast sockets on iOS 14 and later
  need `com.apple.developer.networking.multicast`, and our signing cannot
  grant it. A device build with `IOS_MULTICAST=1` fails with: "Entitlement
  com.apple.developer.networking.multicast requires approval from Apple to
  include in a profile" and "Provisioning profile … doesn't include the
  Multicast Networking capability … needs to be assigned to your team and
  bundle identifier by Apple". No profile on the Mac carries it. Apple
  grants it to a team on request
  (https://developer.apple.com/contact/request/networking-multicast). It
  then goes on an explicit App ID and profile, not the wildcard one.
- **The fallback:** discovery through the system's DNS-SD. This is
  `dns_sd.h`, the API under NWBrowser and NWListener. It needs only
  `NSBonjourServices` and the local network permission, not the
  entitlement. `probe/dnssd.c` is the whole native side: register,
  browse, resolve and get-address, each result queued as an event. Lean
  takes the events (`Sd.register`, `Sd.browse`, `Sd.poll` in
  NetProbe.lean), picks the address on its own Wi-Fi /24, and does the TCP
  itself. In the Simulator it interoperates both ways with lean-mdns: each
  finds the other's services, and the Mac's dns-sd sees both. lean-quiet
  can take the same three externs into its seam.
- **Announcing the Wi-Fi address only:** the probe announces the IPv4
  addresses of en0 (Wi-Fi on iOS and macOS; wl* on Linux). Announcing
  every non-loopback address made avahi resolve the Mac's Tailscale
  address, which the LAN cannot reach.
- **iPhone results (ios:mdns-device, after Allow):**

      RESULT lean-mdns raw multicast: FAIL   (EHOSTUNREACH on every send and receive)
      RESULT dns_sd register/browse/resolve (+ Lean TCP to what it resolved): PASS
      RESULT TCP to the Mac (out) and from it (in): PASS

  In the Simulator all three pass.
