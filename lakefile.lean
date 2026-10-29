import Lake
open Lake DSL System

/-! Lean Quiet: one package (docs/LAYOUT.md). A module's name is its path
from here (`engine/core/Codec.lean` is `engine.core.Codec`), and each
library is a directory of the tree. A library inside another's directory
(mdns in engine/wire, qr in engine/renderer, the bootstrap in
ops/connection) is the outer one's too: `lake build Wire` builds mdns.
`lake build` builds every library but the tests'. -/
package quiet where
  -- Native C uses the host's headers. Lean's bundled older glibc linker
  -- stub lacks fcntl64 (SQLite's file locks); resolve against the host libc.
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libc.so.6",
    "-lpthread", "-ldl", "-lm", "-lrt"]

/-! ## The engine: what holds for every op type -/

-- op, codec, ids, judging, the store (SQLite and held), lists
@[default_target] lean_lib Engine where
  globs := #[.submodules `engine.core]

-- frames, the node and its TCP runner, and mDNS
@[default_target] lean_lib Wire where
  globs := #[.submodules `engine.wire]

-- Wire format, decoder, laws (building this library checks the proofs), and
-- the UDP announce/browse loop.
lean_lib Mdns where
  globs := #[.submodules `engine.wire.mdns]

-- the app's rows, text, images and paint, the platform seam, and QR
@[default_target] lean_lib Renderer where
  globs := #[.submodules `engine.renderer]

-- The codec, the frame decoder and their laws (building this library checks
-- the proofs). It imports only Init, so it cross-compiles to Android as is.
lean_lib Qr where
  globs := #[.submodules `engine.renderer.qr]

-- The composer's pictures: QOI, sizes, the thumbnail tray (also Init only).
lean_lib Pic where
  globs := #[.submodules `engine.renderer.pic]

/-! ## Ops: everything that names a kind -/

-- rounds, fingerprints, the connection's sync messages
@[default_target] lean_lib Sync where
  globs := #[.submodules `ops.sync]

-- the handshake and sessions, and the bootstrap's model
@[default_target] lean_lib Connection where
  globs := #[.submodules `ops.connection]

-- the bootstrap model and its laws
lean_lib Net where
  globs := #[.submodules `ops.connection.bootstrap]

-- the Community family, and each domain's view
@[default_target] lean_lib Community where
  globs := #[.submodules `ops.community]

-- the app's own state: pages, composer, switcher, removal
@[default_target] lean_lib AppState where
  globs := #[.submodules `ops.app]

/-! ## The app -/

-- the root component
@[default_target] lean_lib App where
  roots := #[`App, `AppTypes, `AppLife]

-- every module of the app, for its executables
@[default_target] lean_lib Quiet

/-! ## Platforms and tests -/

-- the headless twin's programs (platforms/headless)
lean_lib Headless where
  globs := #[.submodules `platforms.headless]

-- the test suites' modules (their executables are below)
lean_lib Tests where
  globs := #[.submodules `tests.engine, .submodules `tests.net, .submodules `tests.mdns,
    .submodules `tests.qr, .submodules `tests.app]

/-! ## Native code

The engine's glue (engine/native) and the headless twin
(platforms/headless/host.c). Every executable links all of them; an
archive's members that nothing calls are left out. -/

target glue.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "engine" / "native" / "glue.c"
  let header ← inputTextFile <| pkg.dir / "third_party" / "sqlite" / "sqlite3.h"
  let closeJob ← inputTextFile <| pkg.dir / "engine" / "native" / "listener.h"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
    "-I", (pkg.dir / "third_party" / "sqlite").toString]
  buildO oFile ((srcJob.zipWith (fun s _ => s) header).zipWith (fun s _ => s) closeJob) weakArgs #["-fPIC", "-O2"] "cc"

target crypto.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "crypto.o"
  let srcJob ← inputTextFile <| pkg.dir / "engine" / "native" / "crypto.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

/-- The engine's crypto, libquiet's pure-Rust crates behind a C ABI
(engine/native/crypto), built by `cargo build --release` in that
directory (the test scripts do it first). -/
extern_lib lqcrypto pkg :=
  inputBinFile <| pkg.dir / "engine" / "native" / "crypto" / "target" / "release" / "liblq_crypto.a"

extern_lib libglue pkg := do
  let o ← fetch <| pkg.target ``glue.o
  let c ← fetch <| pkg.target ``crypto.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "glue") #[o, c]

-- The same amalgamation and options as both phones, including purge's
-- VACUUM and WAL truncate. Track the options so changing them rebuilds it.
target sqlite.o pkg : FilePath := do
  let dir := pkg.dir / "third_party" / "sqlite"
  let src ← inputTextFile <| dir / "sqlite3.c"
  let config ← inputTextFile <| dir / "quiet_config.h"
  buildO (pkg.buildDir / "native" / "sqlite.o")
    (src.zipWith (fun s _ => s) config)
    #["-include", (dir / "quiet_config.h").toString]
    #["-O2", "-fPIC", "-std=gnu11"] "cc"

extern_lib libsqlite pkg := do
  let o ← fetch <| pkg.target ``sqlite.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "sqlite") #[o]

-- The headless twin (platforms/headless/host.c): Platform.lean's effects
-- driven by a script, for tests and CI. Every host executable links it.
target host.o pkg : FilePath := do
  let oFile := pkg.buildDir / "host" / "host.o"
  let source ← inputTextFile <| pkg.dir / "platforms" / "headless" / "host.c"
  let translate ← inputTextFile <| pkg.dir / "platforms" / "native" / "translate.h"
  let thread ← inputTextFile <| pkg.dir / "platforms" / "native" / "thread.h"
  let srcJob := (source.zipWith (fun s _ => s) translate).zipWith (fun s _ => s) thread
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  -- C11: in C23 mode the system's glibc headers bind sscanf to a symbol
  -- the glibc Lean links against lacks.
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=gnu11"] "cc"

extern_lib libhosttwin pkg := do
  let o ← fetch <| pkg.target ``host.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "hosttwin") #[o]

/-! ## The engine's suites (tests/engine/run.sh) -/

lean_exe sqlite_build where
  root := `tests.engine.SqliteBuild

lean_exe scenario where
  root := `tests.engine.Scenario

lean_exe differential where
  root := `tests.engine.Differential

lean_exe crash where
  root := `tests.engine.Crash

lean_exe querydiff where
  root := `tests.engine.QueryDiff

lean_exe linkcheck where
  root := `tests.engine.LinkCheck

lean_exe lifecycle where
  root := `tests.engine.Lifecycle

lean_exe wire where
  root := `tests.engine.Wire

lean_exe syncpair where
  root := `tests.engine.SyncPair

lean_exe syncworld where
  root := `tests.engine.SyncWorld

lean_exe tcppair where
  root := `tests.engine.TcpPair

lean_exe noise_check where
  root := `tests.engine.NoiseCheck

lean_exe connection_check where
  root := `tests.engine.ConnectionCheck

lean_exe purge where
  root := `tests.engine.Purge

-- Exact notices on SQLite: the journal netted and matched, against the
-- windows read again, with the key-level and unnetted controls.
lean_exe window_check where
  root := `tests.engine.WindowCheck

lean_exe jointcp where
  root := `tests.engine.JoinTcp

lean_exe merkle_check where
  root := `tests.engine.MerkleCheck

-- The cost laws on the code that runs, with their negative controls.
lean_exe costcheck where
  root := `tests.engine.CostCheck

lean_exe codecdiff where
  root := `tests.engine.CodecDiff

lean_exe bench where
  root := `tests.engine.Bench

lean_exe poolstarve where
  root := `tests.engine.PoolStarve

/-! ## The app on the headless twin (tests/app/run.sh) -/

lean_exe twin_demo where
  root := `platforms.headless.TwinDemo

-- The app's own harness: App.step on an Io of refs, no twin needed.
lean_exe host where
  root := `platforms.headless.Host

-- The app itself on the headless twin: Main over host.c's script.
lean_exe quiet_host where
  root := `Main

-- A send never waits on the node's full inbound channel.
lean_exe nodequeue where
  root := `platforms.headless.NodeQueue

-- The font's inkless glyphs are all invisible or spaces (names).
lean_exe inkless where
  root := `platforms.headless.Inkless

-- A picture whose chunks reach the board while its retry waits.
lean_exe pic_retry where
  root := `platforms.headless.PicRetry

-- Two apps joined by link, ops carried between them as sync would.
lean_exe two_nodes where
  root := `platforms.headless.TwoNodes

-- A real invite and its QR code (the camera e2e's poster).
lean_exe invite_link where
  root := `platforms.headless.InviteLink

-- Two apps joined over real TCP on loopback, each with its own node.
lean_exe net_join where
  root := `platforms.headless.NetJoin

-- Two phones, two communities, each in both, everything named alike.
lean_exe cross where
  root := `platforms.headless.Cross

-- A photo arriving chunk by chunk: the pill, the ring and the preview.
lean_exe arrival where
  root := `platforms.headless.Arrival

-- Photos over real TCP: two apps joined on loopback, one photo each way.
lean_exe attach where
  root := `platforms.headless.Attach

-- Dogfood UX regressions on the same app step and headless seam.
lean_exe ux where
  root := `platforms.headless.Ux

/-! ## QR, mDNS and the bootstrap (tests/qr, tests/mdns, tests/net) -/

lean_exe qr_check where
  root := `tests.qr.Check

lean_exe qr_tool where
  root := `tests.qr.Tool

lean_exe mdns_check where
  root := `tests.mdns.Check

lean_exe mdns_demo where
  root := `tests.mdns.Demo

lean_exe probe where
  root := `tests.mdns.Probe

lean_exe scene_check where
  root := `tests.net.SceneCheck

-- A store's ops, one line each (for comparing devices' stores).
lean_exe dump where
  root := `platforms.headless.Dump

lean_exe harden where
  root := `tests.engine.Harden

lean_exe harden_tcp where
  root := `tests.engine.HardenTcp

lean_exe bidi_check where
  root := `tests.app.Bidi

lean_exe bidi_host where
  root := `platforms.headless.Bidi

/-! ## The desktop (platforms/desktop) and its Linux shell (platforms/linux) -/

-- The desktop root: the app's own pixels in a fluid middle track, with
-- navigation on the left and a context pane on the right.
@[default_target] lean_lib DesktopRoot where
  globs := #[.submodules `platforms.desktop]

-- The Linux shell: xcb, MIT-SHM (PutImage without it), input, clipboard
-- and integer scale; it implements Platform.lean's externs.
target linux.o pkg : FilePath := do
  let oFile := pkg.buildDir / "linux" / "shell.o"
  let source ← inputTextFile <| pkg.dir / "platforms" / "linux" / "shell.c"
  let translate ← inputTextFile <| pkg.dir / "platforms" / "native" / "translate.h"
  let thread ← inputTextFile <| pkg.dir / "platforms" / "native" / "thread.h"
  let srcJob := (source.zipWith (fun s _ => s) translate).zipWith (fun s _ => s) thread
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=gnu11", "-Wall", "-Wextra", "-Werror"] "cc"

lean_exe linux where
  root := `platforms.linux.Main
  moreLinkObjs := #[linux.o]
  moreLinkArgs := #["/usr/lib/x86_64-linux-gnu/libxcb.so.1", "/usr/lib/x86_64-linux-gnu/libxcb-shm.so.0",
    "/usr/lib/x86_64-linux-gnu/libxcb-sync.so.1"]

-- The desktop root without a window: renders at boundary widths,
-- switching, settings and resize (tests/app/desktop.sh).
lean_exe desktop where
  root := `platforms.headless.Desktop

lean_exe app_lifecycle where
  root := `platforms.headless.Lifecycle

target listener_fixture.o pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "tests" / "engine" / "listener_fixture.c"
  buildO (pkg.buildDir / "native" / "listener_fixture.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC", "-O2"] "cc"

extern_lib listener_fixture pkg := do
  let o ← fetch <| pkg.target ``listener_fixture.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "listener_fixture") #[o]

lean_exe runner_restart where
  root := `tests.engine.Restart

lean_exe app_lifecycle_node where
  root := `platforms.headless.LifecycleNode

lean_exe noto where
  root := `platforms.headless.Noto

lean_exe cjk where
  root := `platforms.headless.Cjk

lean_exe cjk_scroll where
  root := `platforms.headless.CjkScroll

lean_exe font_load where
  root := `platforms.headless.FontLoad

lean_exe font_contract where
  root := `platforms.headless.FontContract

lean_exe seam where
  root := `platforms.headless.Seam

lean_exe seam_app where
  root := `platforms.headless.SeamApp

lean_exe translate where
  root := `platforms.headless.Translate

lean_exe appearance where
  root := `platforms.headless.Appearance

lean_exe appearance_seam where
  root := `platforms.headless.AppearanceSeam

lean_exe safe where
  root := `platforms.headless.Safe

lean_exe stateless where
  root := `tests.engine.Stateless

lean_exe fullsync where
  root := `tests.engine.FullSync

lean_exe simplify where
  root := `tests.engine.Simplify

-- T-fresh: a fresh post's latency while a backlog syncs, simulated time
lean_exe fresh where
  root := `tests.engine.Fresh

-- T-fresh over real TCP: a peer that never reads stops no one else
lean_exe fresh_tcp where
  root := `tests.engine.FreshTcp

-- Bounded header reads, full people list, and live removal invalidation.
lean_exe people_reader where
  root := `tests.app.PeopleReader

-- Actual RBSR exchange at its proved non-leaf logarithmic depth.
lean_exe claim_tree where
  root := `tests.engine.ClaimTree
