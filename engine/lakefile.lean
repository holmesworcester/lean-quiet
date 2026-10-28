import Lake
open Lake DSL System

package engine where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0", "/usr/lib/x86_64-linux-gnu/libsodium.so.23"]

lean_lib Engine
lean_lib Community
lean_lib Tests

target glue.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "glue.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "glue.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib libglue pkg := do
  let o ← fetch <| pkg.target ``glue.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "glue") #[o]

lean_exe scenario where
  root := `Tests.Scenario

lean_exe differential where
  root := `Tests.Differential

lean_exe crash where
  root := `Tests.Crash

lean_exe querydiff where
  root := `Tests.QueryDiff
