import Lake
open Lake DSL System

package quiet where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    "/usr/lib/x86_64-linux-gnu/libsodium.so.23"]

require engine from ".." / "lean-engine-lists"
require qr from ".." / "lean-qr"

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
