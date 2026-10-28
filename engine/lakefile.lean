import Lake
open Lake DSL System

package engine where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    "-lpthread", "-ldl", "-lm", "-lrt"]

lean_lib Engine
lean_lib Community
lean_lib Connection
lean_lib Tests

target glue.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "glue.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

target crypto.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "crypto.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "crypto.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

/-- The engine's crypto, libquiet's pure-Rust crates behind a C ABI
(native/crypto), built by `cargo build --release` in that directory
(tests/check.sh and tests/run.sh do it first). An extern lib, so every
package that requires the engine links it too. -/
extern_lib lqcrypto pkg :=
  inputBinFile <| pkg.dir / "native" / "crypto" / "target" / "release" / "liblq_crypto.a"

extern_lib libglue pkg := do
  let o ← fetch <| pkg.target ``glue.o
  let c ← fetch <| pkg.target ``crypto.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "glue") #[o, c]


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

lean_exe connection_check where
  root := `Tests.ConnectionCheck
