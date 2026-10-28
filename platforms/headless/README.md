# The headless twin

`host.c` implements Platform.lean's externs with no OS, for tests and CI.
The screen is a fixed 1080 x 2400 at 420 dpi, with insets 128 (top) and
63 (bottom). A script (`QUIET_SCRIPT=file`, else stdin) drives it one
line per frame; the header comment of `host.c` lists the lines (control
commands, `!tap`, `!text`, `!send`, `!scroll`, `!ime`, `!frames`,
`!sync`, `!dump file.ppm`). Control replies go to stdout, one per line.

Every executable of the package links it (the root lakefile.lean):

```lean
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
```

`tests/app/host_twin_demo.sh` (`mise run host:twin-demo`) is an example. The
other programs here (`Host.lean`, `TwoNodes.lean`, `NetJoin.lean`, …) are
the app's own harnesses; `tests/app/run.sh` (`mise run test:app`) runs them.
