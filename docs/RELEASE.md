# Releases and invite links

## Invite links

An invite is shared as the join page link:

    https://holmesworcester.github.io/lean-quiet/join#<fields in base62>

as Signal's and WhatsApp's group links are. The fields (community,
invitation, the inviter's node key, dial hints, the bearer seed; see
`ops/community/Link.lean`) ride after `#`. A browser never sends that
part to the server. The page (`site/join.html`, served by GitHub Pages
from the `gh-pages` branch) loads nothing from anywhere: its policy is
`default-src 'none'` with its one script and style allowed by hash. It
stores nothing and sends nothing. It checks that what follows `#` is
base62, then its Open button links

    leanquiet://join/<the same fields>

which the OS hands to the app: Android by its `leanquiet://join` intent
filter, iOS and macOS by the registered `leanquiet` scheme, and Linux by
the `x-scheme-handler/leanquiet` desktop entry that
`platforms/linux/install.sh` registers. The app's parser takes either
form, or the bare fields, so a pasted or scanned link works too
(`parse_text`, `parse_uri`, `parse_valid`). The QR code holds the join
page link, so a phone's own camera app opens the page.

Without the app, the page offers this device's download first. Once it is
installed, the person comes back to the page and presses Open again.

- `mise run site:test`: the page in headless Chromium, with a real invite
  from the app's code, hostile fragments and a wrong-hash negative control.
- `mise run site:publish` publishes it. Once the macOS build and the
  TestFlight link exist, pass `--mac-url URL --testflight-url URL`
  (`site/publish.sh --mac-url … --testflight-url …`).

## Keys

| What | Where | Notes |
|---|---|---|
| Android release key | `~/.config/lean-quiet/release/android-release.jks` (alias `lean-quiet`; password in `android-release.pass`, mode 600) | Made 2026-10-31, RSA 4096, valid to 2056. Certificate SHA-256 `55:89:96:89:60:59:CD:60:CE:E8:CD:31:51:28:C4:2D:7A:F8:4E:11:EC:DC:0F:89:35:78:1E:FE:04:6A:C6:8D`. Android installs an update only if it is signed with the same key, so **back both files up** off this machine. |
| macOS Developer ID Application | the Mac, in a build keychain an SSH session can unlock (`lean-quiet-release.keychain-db`) | Not Quiet's team (CTYKSWN9T4): `tools/release/macos.sh` refuses it. |
| Notarization | `xcrun notarytool store-credentials lean-quiet-notary --keychain <that keychain>` with an App Store Connect API key of the same team | |

## Releasing

    VERSION=1.0.0 mise run release:android   # out/release/lean-quiet-android.apk, checked on an AVD
    VERSION=1.0.0 mise run release:linux     # out/release/lean-quiet-linux-x86_64.tar.gz
    MAC=holmes@100.101.83.38 SIGN_IDENTITY='Developer ID Application: … (TEAMID)' \
      tools/release/macos.sh 1.0.0           # out/release/LeanQuiet-macos.zip (reserve the Mac: mac-turn)
    VERSION=1.0.0 mise run release:publish   # GitHub release v1.0.0 + SHA256SUMS

The asset names stay fixed, because the join page links
`releases/latest/download/<name>`. Android's version code is
`X*10000 + Y*100 + Z`.

- Android: non-debuggable, with no control channel. It holds arm64-v8a
  (phones) and x86_64 (emulators, Chromebooks), and needs Android 11 (API 30)
  or newer. People install the APK from the page; it is not on Play.
- Linux: x86-64 on X11, or on Wayland through XWayland. It needs glibc 2.34
  or newer (Ubuntu 22.04, Debian 12 and later; the script checks this) and
  libxcb, libxcb-shm and libxcb-sync. `lean-quiet/install.sh` installs it
  into `~/.local` and registers the link handler.
- macOS: Apple silicon, macOS 14 or newer. It is notarized, so it opens
  without a Gatekeeper warning.
- iOS (TestFlight): the app record, bundle id and team come from the same
  non-Quiet Apple account (see the walkthrough in the PR or session notes).
  `platforms/ios/project.yml` still names the development team it was
  built with for devices.
