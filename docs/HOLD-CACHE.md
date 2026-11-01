# Reusing the placeholder pixel period

The actual `App.present` used to regenerate the message placeholder period on
every frame. It now retains one tile keyed by background bytes, width, density
and theme, and expands references to its rows for the current viewport height.
Changed keys replace the tile. The cache stores an erased proof that its rows
equal the original generator's output, so an arbitrary incorrect tile cannot
inhabit its type.

Six Lean laws prove complete keys, exact output for every height and functional
reuse. Font cell size and hover are absent from the key because reducing the
actual generator proves they do not affect these pixels. Nonempty 1080px/420dpi
witnesses also cover a stale-density key and changed viewport height.

`mise run test:hold-cache` sets up assets and a source/build snapshot, checks 36
pixel/key comparisons, then drives the actual App presentation in all 32
existing skeleton density/theme/width cases on desktop and mobile modes. A
test-only unsafe `ptrEq` check retains both planes and compares an ink-bearing
row across two actual publications. An always-empty App-cache mutation fails
that reuse assertion. Five other compiled mutations omit key inputs or reuse
a mismatched tile; both exact pixel comparisons and kernel laws reject them.
The restored source passes. The app CI task invokes this same named task.
Artifacts remain in `out/hold-cache/negative`; Lean/Lake builds use 48 GiB scopes
with no swap.

The initial full app CJK attempt failed its unchanged 16.667 ms p95 limit. An
8-second scroll-only profile attributed about 26% of sampled App-worker cycles
to placeholder capsule drawing. In a later private comparison, both versions
passed: before caching, median 10.515 ms and p95 15.020 ms; after caching,
median 9.726 ms and p95 15.133 ms, with 547 frames each. Other workloads varied; these
observations do not establish a controlled p95 improvement or a universal
latency bound. The original failures remain documented in CJK-GATE.md.

The functional laws do not prove allocation counts or global byte/work bounds:
key equality still reads the background, expansion still depends on viewport
height, and width/density byte limits are separate. Native timing and the full
integrated app gate remain distinct evidence from the kernel pixel equality.

The integrated tree passes all 1,300 audited laws, the six new witness
applications and the complete named cache/Skeleton/control task. The
reachability audit counts five cache laws as fully wired and lists the pixel
equality under the retained `Hold.messagePlane` reference generator, which
the frame no longer calls. That equality's left side is the actual cached
helper; it proves equality to the old implementation, with no new axiom.
Integrated CJK timing and the full app gate remain separate pending checks.
