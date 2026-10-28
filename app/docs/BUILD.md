# Reproducible builds

With one toolchain, a Lean build is byte-for-byte reproducible. The only
path-dependent outputs are the `.olean` files of modules that raise
warnings, because Lean stores each module's warnings in its `.olean`,
each with the absolute path of the source file.

Measured 2026-10-27 with Lean 4.34.0 on lean-quiet daf3ffa,
lean-engine-lists 354fb2a and lean-qr 61ff438, building
`lake build Quiet quiet_host two_nodes` (270 output files: `.olean`,
`.ilean`, generated `.c`, objects, `host.o` from the system `cc`, static
libraries and the two executables):

- **Same folder, clean rebuild:** all 270 files identical.
- **Two different folders:** 265 identical, both executables included.
  The five that differ are the `.olean` files of the five modules with
  warnings: `Community/Connect`, `Community/Link` and `Engine/Sqlite`
  (lean-engine-lists), `Qr/SegLaws` and `Qr/Segment` (lean-qr).
  lean-quiet's own modules raise no warnings, so their `.olean` files
  don't depend on the folder.
- **Control (lean-mdns 3f6f288):** renaming the one unused `h` in
  `Mdns/Decode.lean` to `_h` made `Decode.olean` identical across
  folders, while `Laws.olean`, with its warnings left in, still
  differed.

Lake's `.setup.json` and `.rsp` files hold absolute paths. They are
build bookkeeping, not output, and were left out of the comparison,
along with `.trace`, `.hash` and log files.

So:

- An executable is reproducible from any folder, given the same
  toolchain.
- For identical `.olean` files across machines, build from the same
  absolute path, or keep every module free of warnings.

Not measured: a second machine, the Android (NDK) and iOS (Xcode)
builds, and the toolchain's own build.

## Checking it again

Export the committed trees side by side at two roots, since the lakefile
finds `../lean-engine-lists` and `../lean-qr` by relative path. Build
both, then compare:

```sh
export ELAN_HOME=/mnt/storage/elan TMPDIR=/mnt/storage/holmes-tmp
export PATH="$ELAN_HOME/bin:$PATH"
W=/mnt/storage/holmes-wt
rm -rf "$TMPDIR/repro"
for root in "$TMPDIR/repro/a" "$TMPDIR/repro/b/deeper"; do
  for r in lean-quiet lean-engine-lists lean-qr; do
    mkdir -p "$root/$r"; git -C "$W/$r" archive HEAD | tar -x -C "$root/$r"
  done
  (cd "$root/lean-quiet" && lake build Quiet quiet_host two_nodes)
  (cd "$root" && find */.lake/build -type f ! -name '*.trace' ! -name '*.log*' \
     ! -name '*.hash' ! -name '*.setup.json' ! -name '*.rsp' |
   sort | xargs sha256sum) > "$root.sums"
done
diff "$TMPDIR/repro/a.sums" "$TMPDIR/repro/b/deeper.sums"
```
