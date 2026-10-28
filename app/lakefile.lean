import Lake
open Lake DSL System

package quiet where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    "-lpthread", "-ldl", "-lm", "-lrt"]

-- The engine: sync, the Rust crypto, the Connection family and
-- purge (lean-engine connection, a worktree pinned to 13da46d).
require engine from ".." / "engine"
require qr from ".." / "qr"

lean_lib Quiet

lean_lib QTests

-- The headless twin (host/host.c): Platform.lean's effects driven by a
-- script, for tests and CI. Every host executable links it.
target host.o pkg : FilePath := do
  let oFile := pkg.buildDir / "host" / "host.o"
  let srcJob ← inputTextFile <| pkg.dir / "host" / "host.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  -- C11: in C23 mode the system's glibc headers bind sscanf to a symbol
  -- the glibc Lean links against lacks.
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=gnu11"] "cc"

extern_lib libhosttwin pkg := do
  let o ← fetch <| pkg.target ``host.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "hosttwin") #[o]

lean_exe twin_demo where
  root := `QTests.TwinDemo

-- The app's own harness: App.step on an Io of refs, no twin needed.
lean_exe host where
  root := `QTests.Host

-- The app itself on the headless twin: Main over host/host.c's script.
lean_exe quiet_host where
  root := `Main

-- Two apps joined by link, ops carried between them as sync would.
lean_exe two_nodes where
  root := `QTests.TwoNodes

-- A real invite and its QR code (the camera e2e's poster).
lean_exe invite_link where
  root := `QTests.InviteLink

-- Two apps joined over real TCP on loopback, each with its own node.
lean_exe net_join where
  root := `QTests.NetJoin

-- Two phones, two communities, each in both, everything named alike.
lean_exe cross where
  root := `QTests.Cross

-- A photo arriving chunk by chunk: the pill, the ring and the preview.
lean_exe arrival where
  root := `QTests.Arrival

-- Photos over real TCP: two apps joined on loopback, one photo each way.
lean_exe attach where
  root := `QTests.Attach

-- Insets, resize, keyboard and the transient Toast layer, on App.step.
lean_exe safe where
  root := `QTests.Safe
