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
The native suites exercise those separately. The 72 cases include empty
conversations and two sender-controlled clumps with independent child messages,
at mobile, desktop and breakpoint widths in both themes, populated sidebars
with long and multilingual names, and retention, disappearing-message,
storage, leave-community and About pages. Leaf fixtures include their real
parent navigation state so their back controls can be compared.

`mae` is mean absolute RGB error divided by 255. `changed_fraction` counts
pixels whose largest channel error exceeds 16. `layout_mae` first pools into
8×8-pixel regions, making large geometry differences easier to see without
suppressing them in the full-resolution score. At desktop widths the same
three metrics independently measure the 220px sidebar (`sidebar_*`), so empty
conversation space cannot dilute navigation errors. The report retains the
sidebar crops as well as whole frames. Lower is better in every metric.
Budgets are regression ceilings for the reviewed current result, not a claim
of pixel identity. Explicit sidebar colors now match the reference's opacity;
normal content text retains its contrast correction. Headings use a static
500-weight instance of the reference's bundled Noto font, retaining the other
scripts' Noto fallbacks. Rasterization still differs. Unsupported settings are
disabled or open explanatory pages, and About identifies this implementation
as Lean. Tightening ceilings requires reviewing the actual/diff images.

The desktop switcher has 22 additional cases in `switcher-cases.tsv`:
light/dark at 720 and 1280px, a real 17-community list at the top and end,
a hovered settings button, and 75/150/200% desktop zoom. Its references live
in `switcher-reference` with their own capture provenance. The popover's
source (`CommunitySwitcher.svelte`, `SquareAvatar.svelte`, `CommunityUnread.svelte`)
is unchanged between the pinned commit and libquiet `46f9d748d853cc417ef0bfd1093372c3ba8acf98`.
The fixture uses actual signed identities from the Lean SQLite fixture.
`popup_*` metrics independently gate its entire rectangle, including its
text, glyphs, border and corners; the whole-window score also includes the
shadow and underlying sidebar. DOM bounds and scroll position must agree
with the running native renderer within one CSS pixel
(after mapping both renderers into device pixels). No region is masked or resized.
The reviewed ceilings allow 3% metric headroom plus 0.00005, and the gate
rejects missing content, a moved popup, a heavy border and incorrect native
geometry in both themes, retaining those negative-control reports.
`host:desktop` also exercises dismissal, draft isolation, hit containment,
actual community switching with identical names, scrolling, popup actions,
and both directions across the mobile breakpoint. Those 22 cases assert desktop parity.
Linked devices opens an explanatory placeholder until linking is implemented.

To refresh only these additional references, using an existing Chromium:

```sh
CHROME=/path/to/chromium LIBQUIET=/path/to/libquiet mise run visual:reference -- --cases tests/visual/switcher-cases.tsv --output tests/visual/switcher-reference
```

The pinned reference still draws settings as a floating drawer with a shadow.
The running libquiet shell at `ab3d244cfb9937c05dc53736046127150c3e0bb9`
embeds settings without a shadow (`ContextPanel`, `.drawer.embedded`). Quiet
follows that newer edge treatment. The nine 1280px light settings cases have
reviewed full-frame ceilings accounting for this deliberate difference; their
references and sidebar ceilings are unchanged. `host:desktop` also compares
every exposed conversation pixel through the panel's left edge against the
underlying frame, so restoring the old shadow fails. Updating the reference
to the newer docked layout remains separate work; this gate does not claim
the older overlay geometry matches that layout.

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
Pillow, NumPy and fontTools, librsvg and Cairo shared libraries (for the pinned SVG glyph
atlas), and the font assets fetched by `tools/noto_assets.sh`. Reference refresh
also needs git, tar, Node, pnpm, pip, browser system libraries and network access
for package setup. Keep this worktree and its `out` directory on `/mnt/storage`.
The small static UI font is checked in with its source and OFL license under
`ui/fonts`; normal builds need no WOFF2 decoder. Explicitly regenerating it with
`tools/ui_fonts.py --regenerate` additionally needs Brotli. No GitHub workflow
is required or created.

## Hover comparisons

`mise run visual:hover` adds 42 paired resting/hovering frames in
`hover-reference`. `hover-targets.json` selects actual libquiet DOM controls;
their captured coordinates drive the native pointer transition. Each target is
compared independently, including the full message toolbar, shadow and tooltip.
`delta_mae` compares each renderer's hover-minus-rest RGB changes. `recall` and
`precision` measure overlap of changed pixels (>0.5/255, including dark mode's
subtle backgrounds). Missing visual hover and unexpected hover on disabled or
cursor-only controls fail unconditionally. Reviewed per-case ceilings retain
small antialiasing/layout differences, not a claim of exact pixel identity.
The gate also rejects 24 mutations of real native frames. Reports, crops and
negative-control artifacts are under `out/visual/hover-*`.

Refresh these independent references explicitly:

```sh
CHROME=/path/to/chromium LIBQUIET=/path/to/libquiet mise run visual:reference -- --cases tests/visual/hover-cases.tsv --output tests/visual/hover-reference
```

The runtime proof/test boundaries are documented in `docs/HOVER.md`.

## Mobile community switcher

The six `mobile-switcher-cases.tsv` captures compare the real mobile sheet at
320, 390 and 430 CSS pixels in both themes. References use the same pinned
actual `App.svelte`; `CommunitySwitcher.svelte` is unchanged between that pin
and libquiet main `ab3d244cfb9937c05dc53736046127150c3e0bb9`.
`visual:compare` runs these alongside the desktop cases in local CI. Entire
frames and the independently measured sheet rectangle are gated, with 3%
headroom plus 0.00005 over reviewed metrics. No image regions are masked.
Negative controls remove the current community, erase action glyphs or move
the sheet; all must fail in both themes at all three widths. Reference refresh
is explicit, using `visual:reference -- --cases tests/visual/mobile-switcher-cases.tsv
--output tests/visual/mobile-switcher-reference`.

`host:mobile-switcher`, also run by local CI's component stage, builds the actual
shared page and input dispatcher. Its 24 cases cover 160/320/420/480 dpi,
light/dark, three widths, full-identity avatar colors, duplicate community names,
pending joins, invite/settings/dismissal targets, and native scroll extent and
bottom-anchored input to actions below 24 communities. It needs the same fonts
and Lean toolchain as `host:skeleton`. Failure logs and reference comparison
artifacts remain under `out/mobile-switcher*` and `out/visual/mobile-switcher-*`.

This checks the mobile switcher, not every mobile screen. Browser/native text
rasterization and the sheet shadow still differ slightly; native safe areas
are exercised by the separate platform suites. The phone header remains fixed
while its community list scrolls.
