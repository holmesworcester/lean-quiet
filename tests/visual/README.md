# Comparing Quiet with libquiet

`mise run visual:compare` builds the real Lean renderer, creates a signed
community in SQLite, waits for component queries, and captures every case in
`cases.tsv`. Local CI invokes this same task. It compares the entire RGB image
against the committed libquiet renders; it never changes a reference image or
masks text, controls, or content. Failure artifacts remain in
`out/visual/report/index.html`: reference, actual, 4× error heatmap, 50/50 overlay,
and `metrics.json`. A missing frame, changed dimensions, or exceeded budget
fails the task.

The reference is libquiet's actual `App.svelte`, rendered through its own
`Window` story and harness, at the commit in `reference.json`. Both apps use the
same viewport, identity, community name, messages and theme. This is
a browser render of the Tauri frontend, **not a native Tauri screenshot**.
Native title bars, keyboard and system insets are outside this comparison.
The native suites exercise those separately. The 48 cases include empty
conversations and two sender-controlled clumps with independent child messages,
at mobile, desktop and breakpoint widths in both themes.

`mae` is mean absolute RGB error divided by 255. `changed_fraction` counts
pixels whose largest channel error exceeds 16. `layout_mae` first pools into
8×8-pixel regions, making large geometry differences easier to see without
suppressing them in the full-resolution score. Lower is better in every metric.
Budgets are regression ceilings for the reviewed current result, not a claim
of pixel identity. Intentional differences remain visible: Quiet's contrast
checks darken some labels, unsupported settings open explanatory pages, and the
About row identifies this implementation as Lean. Font weight and rasterization
also differ. Tightening the ceilings requires reviewing the actual/diff images.

To explicitly refresh references (never part of comparison CI):

```sh
LIBQUIET=/path/to/libquiet mise run visual:reference
```

The task exports the pinned commit with `git archive`, installs its frozen pnpm
lockfile into `out/visual`, adds only the fixture story, and starts a private
Storybook server. It records source, fixture SHA-256 and browser version in
`reference/provenance.json`. It verifies the live CSS palette so a dark-mode
fixture cannot accidentally capture light mode. The existing libquiet checkout
is not modified. `CHROME=/path/to/chromium` uses an existing browser; otherwise
Playwright installs Chromium under `out/visual/browsers`.

Host prerequisites: Lean toolchain from `lean-toolchain`, Rust, Python with
Pillow and NumPy, librsvg and Cairo shared libraries (for the pinned SVG glyph
atlas), and the font assets fetched by `tools/noto_assets.sh`. Reference refresh
also needs git, tar, Node, pnpm, pip, browser system libraries and network access
for package setup. Keep this worktree and its `out` directory on `/mnt/storage`.
No GitHub workflow is required or created.
