# Desktop hover: runtime rules, proofs, and pixels

Pointer movement is transient paint input. `Hover.Context` is `Option (Nat × Nat)`:
`none` means no hovering pointer, including touch. Linux supplies motion, entry,
exit and focus-loss events through X11. The app chooses native arrow, hand and
text cursors from the same visible action geometry used for dispatch. The text
cursor is reserved for editable fields; message text and toolbar padding use
the arrow until transcript selection is implemented. Android
and iOS retain the default `none`; this change does not synthesize hover from taps.

`Desktop.pointer` routes through front-to-back surfaces. A switcher's clear
dismiss surface covers the whole window; empty or disabled overlay space cannot
expose a covered component. Each component receives local coordinates clipped
to its viewport, with its scroll offset applied. Shared settings, page, composer,
message and reaction painters consume `Dim.hover`. Query state keeps `Dim.hover`
at `none`; pointer motion never enters a subscription key.

The desktop retains already-decoded inputs alongside each displayed row. A
single hovered-row cache is keyed by message version, image readiness, width,
density, theme and reaction target. Moving inside a message reuses that bitmap;
changing the hovered reaction repaints from the existing answers and image
references. The row's normal visibility lifecycle owns the snapshot. Hover
starts no reader query, decode or raster-pool job.

Messages expose the libquiet action bar. Moving diagonally toward an overlapping
bar retains its owner within the convex hull of the departure point and bar,
until the next frame after 400 ms. Entering the bar keeps the owner; leaving the window, scrolling,
resizing or retiring that row prevents a stale target. Tooltips use a separate
400 ms dwell, retained while moving within one action. Reaction opens the existing
message-owned sheet; Copy text uses the native clipboard. Author names and
avatars use the signed author identity to open their existing profile component. Threads and Edit
message currently open explanatory placeholders, as those features are not yet
implemented here.

## What is proved

`engine/renderer/HoverLaws.lean` proves the **functions used by the renderer**:

- disabled or absent pointers cannot activate a target;
- active coordinates are inside its half-open rectangle;
- the chosen front surface is drawn, and a containing overlay blocks surfaces
  below it, including disabled/empty overlay areas;
- local coordinates are within the child viewport;
- leaving, losing focus or switching to touch clears the pointer;
- travel grace expires after 400 ms, and the toolbar itself is reachable.

`platforms/desktop/HoverLaws.lean` connects those rules to the running driver:
pointer transitions preserve the entire app/query state and desktop layout;
hover cannot alter message, composer or reaction-sheet layout; the actual
switcher route blocks main-pane hover. `tests/app/DesktopAxioms.lean` audits these
alongside the existing desktop laws, accepting only Lean's standard axioms.
There are no added axioms or `sorry` placeholders. These are Lean proofs, not
Verus models or a separate specification of hypothetical code.

This is **not** a proof of Chromium/native rasterizer equivalence, OS event
delivery, end-to-end latency, or every possible pixel. Those boundaries are
checked with independent rendered and native tests. The proofs establish the
routing and stability rules; visual parity has measured tolerances.

## Reproducible gates

- `mise run host:desktop`: builds the actual driver and proofs, audits axioms,
  then exercises pixels, disabled controls, overlay isolation, cursor selection,
  row-cache reuse, unchanged work counters, toolbar ownership/actions and dwell.
- `mise run host:hover-proofs`: compiles isolated mutations of the actual hover
  core. The unchanged production proofs must reject disabled activation, an
  inclusive right edge, reversed stacking and failure to clear on exit.
- `mise run linux:e2e`: builds/setup plus real X11 motion, focus loss and exit,
  checking rendered hover and cursor state at 1×, 2× and the non-SHM blit path.
  This includes existing resize, scrolling, text and clipboard regressions and
  native ASan/UBSan checks. Rapid click/refocus/Return is repeated without waiting
  for a Lean frame: the C event pump yields UI transitions before interpreting
  subsequent queued keys, protecting focus and editor-buffer ownership. Requires Xvfb, xdotool, ImageMagick, XCB and local sockets.
- `mise run visual:hover`: builds/setup plus 42 independent DOM-targeted libquiet
  comparisons: light/dark, 125% zoom and narrow desktop windows. Every case has a
  resting frame. The gate measures the whole target and its hover delta, including
  message toolbar/shadow/tooltips, with no text masks or screenshot alignment.
  It rejects missing hover even in an otherwise empty frame, and tests its own
  sensitivity with missing, shifted and incorrectly colored actual frames.

Local CI's `app` gate invokes the behavioral/native/proof tasks; its `visual`
gate invokes both the existing visual suite and `visual:hover`. No GitHub
workflow is required. Failure logs, native screenshots, mutation logs, crops
and pixel reports remain under `out/`, notably `out/visual/hover-report/index.html`.

The independent reference is the real libquiet App through Storybook/Chromium,
from the pinned commit in `tests/visual/reference.json`. DOM selectors in
`hover-targets.json` supply coordinates to **both** renderers. The capture records
source/fixture/browser provenance, target geometry and pointer sequences. The
reference task is explicit; tests never rewrite expected images or budgets.
See `tests/visual/README.md` for existing deliberate settings-layout differences.
