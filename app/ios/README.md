# lean-quiet on iOS

The app (Main.lean over Quiet/) on UIKit: `quiet_ios.m` implements
Platform.lean's seam, and `ctl_ios.c` is the control channel. Lean has no
iOS libraries, so ship.sh stages the C of Main's whole module closure (the
app's modules, lean-engine's, and Std's), Init's C, Lean's runtime source,
libuv's source and the SQLite/Ed25519 glue. The Mac then builds all of it
with Xcode's clang (`build_ios.sh`, `leanrt.sh`). The scripts run from the
Linux box and do the Mac's part over SSH.

## Tasks

| task | what |
| --- | --- |
| `mise run ios:sim` | Builds for the Simulator, installs and launches the app in a simulator of its own (an iPhone 16e on the newest iOS runtime, named `lean-quiet-ios`, booted headless), seeds 500 chaos messages if the database has none, and saves a screenshot to `out/ios-sim/launch.png`. |
| `mise run ios:sim-e2e` | `ios:sim`, then the UI test (`UITests/`) in that simulator. It uses real touches and the software keyboard: it opens on the seeded data pinned to the newest message, flings twice towards older messages, taps the header to jump back, long-presses a message to open the reaction sheet (the viewport shrinks) and taps the header to close it, taps the composer to open the keyboard (Lean gets its height), types a message, and sends it with the keyboard's Send key, after which the message is stored and on screen. Every step is checked in Lean's own state through the control channel. Screenshots go to `out/ios-sim/shots/`, logs to `out/ios-sim/`, and the result bundle to `~/lean-quiet-ios-work/out/e2e.xcresult` on the Mac. |
| `mise run ios:mdns` | The network probe (`probe/`) in that simulator. It uses Lean's own sockets (Std.Async over libuv) and lean-mdns. **mDNS:** the app announces `lean-ios-sim` of type `_leanquiet._udp`, and the Mac must list it (`dns-sd -B`) and resolve it (`dns-sd -L`). The Mac registers `dns-sd -R probe _leanquiet._udp local 7001`, and the app must log it as found. **TCP:** out to the Mac, and in from it. The report goes to `out/ios-sim/probe-sim.txt`; any `fail` line fails the task. |
| `mise run ios:device` | Builds a signed app for an iPhone. It installs nothing. |
| `mise run ios:e2e` | End to end on the iPhone (`DEVICE`; ask before using it). It builds, installs and launches the app (`device_mac.sh`) with the control channel on every interface (`LEANQUIET_CTL_ADDR=any`), then drives it from the Mac over the Wi-Fi: chaos data if the database has none, Lean's state (data present, rows mounted), and frames still being drawn 5 s later. The console goes to `out/ios-device/`. The app is left running. |
| `mise run ios:mdns-device` | `ios:mdns` on the iPhone (instance `lean-ios-phone`), over the Mac's Wi-Fi. The first run needs a person to tap Allow on the phone's local network prompt. `IOS_MULTICAST=1` also asks for the multicast entitlement (see below). The report goes to `out/ios-sim/probe-device.txt`. |
| `ios/ship.sh run` | Device build, then install and launch on `$DEVICE`. Ask before using the phone. |
| `ios/ship.sh ctl CMD...` | Sends control commands (`state`, `chaos 500`, `wait`, `visible`, `send TEXT`, …; see `App.command`) to the app in the Simulator. |
| `ios/ship.sh shot FILE` | Saves a screenshot of the simulator to FILE on this box. |
| `ios/ship.sh clean` | Deletes the simulator and the Mac's work directory. |

## Prerequisites

- **Here:** the Lean toolchain (`ELAN_HOME`, default `/mnt/storage/elan`)
  and `../lean-engine` built by lake. You also need Lean's source at the
  toolchain's version (`LEAN_SRC`, default
  `/mnt/storage/holmes-wt/lean-src/lean4`, tag v4.34.0) and libuv v1.51.0
  (`UV_SRC`, default `/mnt/storage/holmes-wt/lean-src/libuv`). `assets/`
  comes from `tools/fetch_assets.sh`. Init's C goes to `out/initc`
  (`tools/gen_init_c.sh`). Std's C is cached in `out/stdc`.
- **The Mac** (`MAC`, default `you@your-mac`): SSH without a
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
- **Scrolling:** a `UIScrollView` turned upside down (scale y by -1). Its
  content offset is then the bottom-anchored `b` itself, and content
  measured late at the older end never moves what is on screen. UIKit
  supplies the physics, bounce and indicator. A list frame is one layer
  in the scroll content at the distances it was drawn for, so Core
  Animation slides it with the finger and Lean redraws at the current
  offset. `scrollBy` sets the offset property, which keeps a fling going;
  `scrollTo` uses `setContentOffset:animated:NO`, which stops it.
- **Header and composer:** two views pinned to the screen's top and to
  the keyboard layout guide's top. The composer therefore moves inside the
  keyboard's own animation, and the list viewport between them carries
  the newest messages up with it. The composer's last row is repeated down
  to the screen's bottom.
- **Keyboard:** a `UITextField` drawn in clear holds the text (so
  autocorrection, marked text and dictation work as in any app). Its text,
  selection and marked range go to Lean in code points, and Return (shown
  as Send) is the send event. The keyboard's height is read every refresh
  from a probe view on the layout guide's presentation layer, mid-animation.
- **Touches:** list taps and long presses come from gesture recognizers
  on the scroll view, and `y` is the content distance. The header and
  composer track their own touches: an 8 pt slop, a long press after
  500 ms reported while still held, and the composer's drag as event 8.
- **Pixels:** Lean's rows are R G B X and IOSurface's are B G R A, so a row
  is swizzled as it is copied. Rows that are the same object as last
  frame's are not copied: the staging buffer shifts and only new rows are
  copied in. Each layer has a ring of three IOSurfaces.
- **Control channel:** TCP on 127.0.0.1 (`LEANQUIET_CTL_PORT`, default
  7417; 0 turns it off). In the Simulator that is the Mac's loopback. On a
  phone it is unreachable from outside.
- **Working directory:** the app's Documents directory. `quiet.db` lives
  there, and `assets` is a symlink to the bundle's assets, made again at
  each launch.

- **Lean's threads:** Lean's runtime reserves 1 GB of stack for each
  thread on 64-bit. An iOS app's address space runs out after a few such
  threads, and `pthread_create` then fails with EAGAIN ("failed to create
  thread: Resource temporarily unavailable"). This happens on the phone,
  not in the Simulator. So the twin sets `LEAN_STACK_SIZE_KB=65536` before
  starting Lean, unless the launch environment sets it.

### Simplified compared with Android

- No predicted offset during a fling. `scroll` answers the current offset,
  and a slide uncovers background until the next frame, as lean-chat does
  on iOS.
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
  entitlement. The probe app (`probe/probe_ios.m`) registers
  `<instance>-sd` and browses `_leanquiet._udp`, resolving each service to
  an IPv4 address and port, which is what Lean then connects to over TCP.
  In the Simulator it interoperates both ways with lean-mdns: each finds
  the other's services, and the Mac's dns-sd sees both. A lean-quiet seam
  for it would be one twin extern each for announce, browse and found,
  with Lean doing TCP and everything after.
