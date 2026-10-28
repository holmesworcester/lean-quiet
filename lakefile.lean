import Lake
open Lake DSL System

/-! Lean Quiet: one package (docs/LAYOUT.md). A module's name is its path
from here (`engine/core/Codec.lean` is `engine.core.Codec`), and each
library is a directory of the tree. A library inside another's directory
(mdns in engine/wire, qr in engine/renderer, the bootstrap in
ops/connection) is the outer one's too: `lake build Wire` builds mdns.
`lake build` builds every library but the tests'. -/
package quiet where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
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
@[default_target] lean_lib App

-- every module of the app, for its executables
@[default_target] lean_lib Quiet

/-! ## Platforms and tests -/

-- the headless twin's programs (platforms/headless)
lean_lib Headless where
  globs := #[.submodules `platforms.headless]

-- the test suites' modules (their executables are below)
lean_lib Tests where
  globs := #[.submodules `tests.engine, .submodules `tests.net, .submodules `tests.mdns,
    .submodules `tests.qr]

/-! ## Native code

The engine's glue (engine/native) and the headless twin
(platforms/headless/host.c). Every executable links all of them; an
archive's members that nothing calls are left out. -/

target glue.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "engine" / "native" / "glue.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

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

-- The headless twin (platforms/headless/host.c): Platform.lean's effects
-- driven by a script, for tests and CI. Every host executable links it.
target host.o pkg : FilePath := do
  let oFile := pkg.buildDir / "host" / "host.o"
  let srcJob ← inputTextFile <| pkg.dir / "platforms" / "headless" / "host.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  -- C11: in C23 mode the system's glibc headers bind sscanf to a symbol
  -- the glibc Lean links against lacks.
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=gnu11"] "cc"

extern_lib libhosttwin pkg := do
  let o ← fetch <| pkg.target ``host.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "hosttwin") #[o]

/-! ## The engine's suites (tests/engine/run.sh) -/

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
