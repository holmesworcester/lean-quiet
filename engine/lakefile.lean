import Lake
open Lake DSL System

package engine where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0", "/usr/lib/x86_64-linux-gnu/libsodium.so.23"]

lean_lib Engine
lean_lib Community
lean_lib Connection
lean_lib Tests

target glue.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "glue.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib libglue pkg := do
  let o ← fetch <| pkg.target ``glue.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "glue") #[o]

-- The handshake's primitives: X25519, ChaCha20-Poly1305, OS random.
target noise.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "noise.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "noise.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib libnoise pkg := do
  let o ← fetch <| pkg.target ``noise.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "noise") #[o]

lean_exe scenario where
  root := `Tests.Scenario

lean_exe differential where
  root := `Tests.Differential

lean_exe crash where
  root := `Tests.Crash

lean_exe querydiff where
  root := `Tests.QueryDiff

lean_exe linkcheck where
  root := `Tests.LinkCheck

lean_exe lifecycle where
  root := `Tests.Lifecycle

lean_exe wire where
  root := `Tests.Wire

lean_exe syncpair where
  root := `Tests.SyncPair

lean_exe tcppair where
  root := `Tests.TcpPair

lean_exe noise_check where
  root := `Tests.NoiseCheck
