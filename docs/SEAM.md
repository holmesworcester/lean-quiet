# Running UI seam

Port of **c7534c8** (placement/input, translation/fill, scalar exports) onto
main **1ebab09**, in the approved layout. Scroll motion remains independent
of new Lean frames. `Session.present`
publishes the base offset, full buffer origin/height, content extent
`[high - height, high)`, the pinned flag, a repeated 48-line placeholder
tile, its extent, and the theme colours. The first 20 placement words keep
the original frame and input ABI; words 20–28 add this publication.

`engine.renderer.Slide` supplies the **compiled Lean functions the shells call**
for source/destination rectangles, source selection, tile indexing and tap
displacement. `SlideLaws` equates each export with its `engine.renderer.Translate`
integer specification for every ABI input. They are pure scalar functions: no IO, database access,
bitmap rendering, app state, offset clamp or wait for the frame thread.
Android calls them on its choreographer thread, iOS on CADisplayLink, and
the headless twin on each scripted vsync. Native code copies their numbers
and pixels. This includes cropping the moving buffer to the last published
viewport. There is no copied placement or fill formula in C/Objective-C.

With the current bottom-anchored convention the sign is **positive**:
`row at o = row at o₀ + (o - o₀)`. `Translate.equivariance` equates that with
`Geometry.Seam.place` at `o`. Pinned pages ignore OS offsets, as
`Translate.pinned` proves. Header and composer positions stay with their
Lean frame. Each new frame still clamps its base offset in Lean; interim
OS samples are deliberately **not** clamped by the compositor helpers.

The fill plane sits above the native window background and below the
painted list. Its phase also follows content, so it keeps moving after
the painted buffer is wholly outside the viewport. A new frame re-bases
painted placement at the latest clamped sample; the fill's content phase
is independent of that re-base. Android publishes frame serial and slide
together on presentation completion. Raw down events retain that slide;
Lean uses it when mapping the tap, even if scrolling continues before up.

## Composition with main's coverage law

The single `engine/renderer/Cover.lean` is main's renderer contract.
`App.listFrame` and its reader-window `frameSlice` stay intact. `App.holdLine`
now calls `Hold.holdLine`, whose unchanged body is shared with the published
48-line tile. No text, row-layout, message-read, navigation or leased-frame
function was restructured. `AppTypes.Io` carries the enlarged publication;
`App.present` calls it after main's `chatFrame`, `mountPage` and ownership checks.

The contract is compositional. A buffer row r contains
`Cover.seen pad bottom more rows (high - 1 - r)` resolved to pixels. At each
vsync `Translate.source_iff` selects exactly that r, and
`Translate.source_content` identifies its content position with the current
screen row. `Translate.covered` applies `Cover.covered` inside the buffer;
`Translate.line_painted` carries `Cover.line_painted`'s bitmap bound through
the selection. Outside the buffer, `Translate.outside` selects the hold
placeholder. `fill_covers`, `fill_index` and `fill_pixel` prove the plane
covers the entire viewport and the selected pixels are exactly
`holdLine` at the moving content phase, including negative OS samples.

`Cover.covered`'s content premises remain explicit: inside the buffer,
content is at or above `pad` and either within the loaded rows or has
more older rows. `Cover.Px.blank` remains intentional padding outside that
content. A stripe's background-colour spacer is a tile pixel, not an
uncovered compositor row. We do not strengthen Cover's theorem into a
claim that padding, or an empty list with `more = false`, is content.

**Freshness is separate.** Moving the published image and filling gaps no
longer waits for database reads, photo rendering, or another App.step.
Main's reader and window work provide freshness separately from this
composition. These laws prove per-vsync composition when the OS
runs the callback and supplies an offset, not an OS scheduling deadline,
new data arriving, or visually different pixels after a whole tile period.
Raw input is still classified by `Input.run` at frame boundaries; accepting
the start or change of a drag retains that latency. Once the OS offset
changes, presentation uses it on the next compositor callback without
waiting for new pixels.

## Native boundary and remaining verification

OS scroll physics, event acquisition and pixel/point conversion remain
native. Inputs are signed 32-bit physical-pixel samples; published extents
fit the existing 32-bit ABI. Tap displacement must also fit signed 32 bits,
as `delta_value` states. Pixel copies, graphics API application, fences,
Lean's compiler/runtime and actual display scheduling remain trusted.
The code uses no phone, emulator or Mac during local validation. iOS
compilation and device smoothness need the lead's native checks.

## Native thread safety follow-up

The first translation implementation had scalar signatures but boxed
arithmetic and lazy constants inside the generated C. Its runtime safety
claim was too strong. The exports now live in `engine/renderer/Slide.lean`; the
integer functions and every existing theorem remain unchanged.

A `UInt64` coordinate carries a bias of `3 * 2^32`, which is divisible by
48. This represents every intermediate signed position without boxing,
including both `Int32` endpoints and every `UInt32` extent. `Int32`/`Int64`
are only ABI bit interpretations; all arithmetic uses unsigned fixed-width
values. There are no object operations or once-cells in the export bodies.

`platforms/native/thread.h` additionally initializes each native thread once and
warms every export on the Lean frame thread before publication. Android
initializes at Choreographer thread entry and warms before creating it.
iOS initializes at `lq_translate`, covering both the first main-thread
publication and CADisplayLink, after a frame is available; it warms on the
Lean thread before dispatching that publication. The host initializes and
warms at screen/frame entry. Its scripted refreshes currently run on the
calling Lean thread; the TLS guard also covers future native callers.

`host:slide` builds the proofs and generated C. The raw-C checker permits
only ten explicitly audited `lean_uint*` inline C operators: it checks
their exact leaf bodies in the pinned toolchain's `lean.h`. Lean emits
those names even for fixed-width addition and comparison. Every other
`lean_`/`lp_` call, object, closed value or once-cell fails the check. It
also requires the optimized assembly of every export to contain **zero
calls and zero Lean symbols**, and links the actual exports into a native
boundary/thread test **without Lean's runtime**. No new extern arithmetic
or C placement copy was introduced.

The four new laws have no premises: they hold for the full ABI domain,
including values outside a published viewport. Therefore the old
Translate placement/coverage/tap laws transfer without narrower hypotheses.
Their exact statements are:

```lean
namespace Slide

theorem edge_eq (fill : Bool) (which : UInt8) (pin : Bool) (base : UInt32)
    (origin : Int32) (height top bottom : UInt32) (sample : Int32) :
    edge fill which pin base origin height top bottom sample =
      Translate.edge fill which pin base origin height top bottom sample

theorem delta_eq (pin : Bool) (base : UInt32) (sample : Int32) :
    delta pin base sample = Translate.delta pin base sample

theorem fillRow_eq (pin : Bool) (base top bottom : UInt32) (sample : Int32) (y : UInt32) :
    fillRow pin base top bottom sample y = Translate.fillRow pin base top bottom sample y

theorem pick_eq (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) :
    pick pin base origin height sample y = Translate.pick pin base origin height sample y

end Slide
```

## Port integration

The raw ABI is eight words: kind, pointer/code, signed x/action, signed y,
time low/high, displayed serial, signed slide. Tags 9–12 are touch phases;
13 is a clock tick, 14 Android keys, 15 USB keys, and 16–19 are background,
foreground, surface, resize. Lifecycle events cannot collide with touches.
`Session.receive` handles polls without a surface through the same decoder
as a frame; the existing lifecycle lease still governs acting on the events.
The growable queue retains lifecycle and touch samples alike. Unmount and
resize cancel accepted native motion and revoke the press and old displayed
contexts; `Input.revoked_release` prevents a late release acting on the
replacement mount. The frame serial remains monotonic.

Android retains `lq_log`, `lq_set_text`, `lq_poll`, `lq_links` and main's
`LQ_CTL` guards. iOS retains its token-protected debug channel and lifecycle
availability/resize checks; its fourth buffer is invalidated with the other
three when a publication is refused. `lq_listener_close` is unchanged.
The headless host retains resize, lifecycle, deep-link and unrestricted dump
paths. The Linux desktop keeps its existing mouse/editor event loop and
layout; its app track consumes the shared publication. Mouse classification
in that desktop-specific loop is outside the phone touch laws.

The platform has 19 externs (18 on main plus `motion`); `frame` and `scroll`
have updated signatures. Four scalar exports go the other direction. Their
source is `engine/renderer/Slide.lean`, generated C is
`.lake/build/ir/engine/renderer/Slide.c`. `tests/app/slide.py` preserves the
scalar audit, and `tests/app/run.sh` wires all three named tasks
`host:seam`, `host:translate`, `host:slide` into the app gate.

## Port validation

`SKIP_TCP=1 ci/local.sh check engine app readme reorg` passed all five
parts in one final run. `mise run check` audits **802 statements on standard
axioms**: main's 747 plus these 55. README wiring checked 436 links, and the
reorganization self-test rewrote 166 files with zero wrong results. The
exact statements follow below (the four scalar equalities are above).

The seam suites passed **33 classifier/ABI cases**, **3,280 geometry rows
per placement mode**, **2 native-twin sessions / 10,042 raw samples / 4,800
pixel rows**, **10 app integration checks**, and **14 native handoff checks**.
The slow-frame suite passed **250 vsync dumps / 522,250 viewport rows**:
336,635 painted-buffer rows, 185,615 fill rows and 105 translations between
Lean frames, with 50 ms publications and 8 ms offset changes. It also has
four input/coverage interface checks. The scalar suite passed **4,622,688
boundary/thread comparisons**, the four-body C/assembly audit, and six
native initialization/warm-up order checks.

All **57 seam-specific negative controls** were detected and reverted:
27 placement/input/publication controls, 18 translation/coverage controls,
and 12 scalar/thread controls. These include disabling native placeholder
fill, freezing native translation, boxed arithmetic, once-cells, and a
press surviving unmount or resize. Each script restored the source and
reran its positive suite. The app gate also passed the existing lifecycle
(91 checks, two four-check crash restores, native suspension/resize and
invite delivery), lifecycle-node (32 checks / 16 controls), desktop (105
checks / 27 renders / 67,733 exact reference pixels), host (40 checks),
two-node join/removal (53 checks),
arrival (24 checks), navigation, bidi, retry and shipped-code checks.

Android built `out/quiet.apk` for **x86_64 and arm64-v8a**, without installing
it. Linux built and passed **21 native input checks under ASan/UBSan**. The
iOS Lean placement boundary audits **16 laws on standard axioms**; this
is separate from compiling its Objective-C shell. TCP executables are
built, but their runs are explicitly
skipped here; the lead reruns them outside the socket sandbox. No device,
emulator or Mac was used. iOS Objective-C compilation, Pixel smoothness and
the Linux X11 end-to-end run remain unverified here.

## Exact ported law statements

These statements are audited in `tests/Axioms.lean`. Coverage's three
composition statements now take main's `pad` and use `.unloaded`.
All other existing statements are preserved. The scalar equations above
have no premises; the witnesses below exercise nonempty cases.

```lean
namespace Surface

theorem crop_row (origin : Int) (height lo hi r : Nat)
    (hr : r < height) (hl : (lo : Int) ≤ origin + r) (hh : origin + r < hi) :
    (crop origin height lo hi).src0 ≤ r ∧ r < (crop origin height lo hi).src1 ∧
    ((crop origin height lo hi).dst0 : Int) + (r - (crop origin height lo hi).src0 : Nat) =
      origin + r

theorem composer_top (g : Geom) (pin : Bool) (over bf bn height : Nat) :
    (make g pin over bf bn height).composer.dst0 = g.composerTop

theorem published_row (g : Geom) (pin : Bool) (over bf bn height r : Nat)
    (hr : r < height)
    (hl : (g.top : Int) ≤ (make g pin over bf bn height).row r)
    (hh : (make g pin over bf bn height).row r < g.composerTop)
    (hs : (make g pin over bf bn height).list.src0 < UInt32.size)
    (hd : (make g pin over bf bn height).list.dst0 < UInt32.size) :
    let f := make g pin over bf bn height
    (f.words[2]!.toNat : Int) + (r - f.words[0]!.toNat : Nat) = f.row r

theorem published_composer (g : Geom) (pin : Bool) (over bf bn height : Nat)
    (h : g.composerTop < UInt32.size) :
    (make g pin over bf bn height).words[10]!.toNat = g.composerTop

theorem row_place (g : Geom) (over bf bn height r : Nat) :
    (make g false over bf bn height).row r = Seam.place g over bf bn r

theorem row_pinned (g : Geom) (over bf bn height r : Nat) :
    (make g true over bf bn height).row r = Seam.pinned g over r

theorem placed_row (g : Geom) (hf : g.Fits) (over bf bn height r : Nat) :
    (make g false over bf bn height).row r = Seam.home g bn (Seam.frameRow g over bf r)

theorem visible_in_viewport (g : Geom) (hf : g.Fits) (over bf bn height r : Nat)
    (hr : r < height) (lo : (bn : Int) ≤ Seam.frameRow g over bf r)
    (hi : Seam.frameRow g over bf r < bn + g.viewNow) :
    let f := make g false over bf bn height
    f.list.src0 ≤ r ∧ r < f.list.src1 ∧
    (f.list.dst0 : Int) + (r - f.list.src0 : Nat) = Seam.home g bn (Seam.frameRow g over bf r)

theorem pinned_row (g : Geom) (over bf bn height r : Nat) :
    (make g true over bf bn height).row r = (g.top : Int) + Seam.pageRow over r

theorem pinned_visible (g : Geom) (over bf bn height k : Nat) (hk : k < g.viewNow) :
    (g.top : Int) ≤ (make g true over bf bn height).row (over + k) ∧
    (make g true over bf bn height).row (over + k) < g.composerTop

theorem newest_drawn (g : Geom) (hf : g.Fits) (over pad h height r : Nat)
    (fit : pad + h ≤ g.viewNow) (hr : Seam.frameRow g over 0 r = pad + h - 1) (hh : 0 < h) :
    (g.top : Int) ≤ (make g false over 0 0 height).row r ∧
    (make g false over 0 0 height).row r < g.composerTop

theorem offset_bounds (maxB : Nat) (sample : Int) :
    0 ≤ offset maxB sample ∧ offset maxB sample ≤ maxB

end Surface
```

```lean
namespace Input

theorem moved_not_tap (p : Press) (time : Nat) (h : p.context.slop < p.travel) :
    classify p time = none

theorem release_tap (p : Press) (time : Nat) (hm : p.travel ≤ p.context.slop)
    (hh : p.held = false) (ht : time - p.first.time < 500) :
    classify p time = some (.tap p.first.pos)

theorem sample_remembers (p : Press) (t : Touch) :
    p.travel ≤ (p.sample t).travel ∧ distance p.first.pos t.pos ≤ (p.sample t).travel

theorem release_moved (p : Press) (t : Touch)
    (h : p.context.slop < distance p.first.pos t.pos) :
    classify (p.sample t) t.time = none

theorem first_pointer (s : State) (p : Press) (t : Touch) (h : t.id ≠ p.first.id) :
    follow s p t = ⟨s, [], []⟩

theorem extra_down (c : Context) (s : State) (t : Touch)
    (hd : t.phase = 0) (hs : s.pointers.isEmpty = false) :
    (touch c s t).state.press = s.press ∧ (touch c s t).events = [] ∧
      (touch c s t).motion = []

theorem other_pointer (c : Context) (s : State) (p : Press) (t : Touch)
    (hp : s.press = some p) (hd : t.phase ≠ 0) (hi : t.id ≠ p.first.id) :
    (touch c s t).state.press = s.press ∧ (touch c s t).events = [] ∧
      (touch c s t).motion = []

theorem release_event (s : State) (p : Press) (t : Touch)
    (hi : t.id = p.first.id) (hu : t.phase = 2)
    (hm : (p.sample t).travel ≤ p.context.slop) (hh : p.held = false)
    (ht : t.time - p.first.time < 500) :
    deliver p.context.frame (.tap p.first.pos) ∈ (follow s p t).events

theorem revoked_release (c : Context) (s : State) (t : Touch) (up : 2 ≤ t.phase) :
    (touch c (revoke s) t).events = []

theorem deterministic (c : Context) (s s' : State) (es es' : List Raw)
    (hs : s = s') (he : es = es') : run c s es = run c s' es'

theorem step_offset (c : Context) (s : State) (e : Raw) :
    (step c s e).state.offset ≤ c.maxB

theorem sequence_offset (c : Context) (s : State) (es : List Raw) :
    0 ≤ (run c s es).state.offset ∧ (run c s es).state.offset ≤ c.maxB

theorem tap_content (g : Geom) (_hf : g.Fits) (over bf bn height y : Nat) :
    Seam.home g bn (content (Surface.make g false over bf bn height) y) = y

theorem tap_page (g : Geom) (hf : g.Fits) (over bf bn height y : Nat) :
    (g.view : Int) - 1 - content (Surface.make g true over bf bn height) y =
      (y : Int) - g.top

theorem tap_key (f : Surface.Frame) (grid : SheetGeom.Grid) (ok : grid.Ok)
    (scroll i : Nat) (p : Point) :
    (match deliver f (.tap p) with
      | .tap _ x y => grid.hit scroll x.toNat y.toNat
      | _ => none) = some i ↔
      i < grid.n ∧ grid.inBox scroll i p.x.toNat.toUInt32.toNat (coord f p).toUInt32.toNat

theorem classified_at_down (p : Press) (time : Nat) (q : Point)
    (h : classify p time = some (.tap q)) : q = p.first.pos

theorem classified_page (p : Press) (time : Nat) (q : Point)
    (_h : classify p time = some (.tap q))
    (pin : p.context.frame.pin = true) (fit : p.context.frame.g.Fits) (hy : 0 ≤ q.y) :
    (p.context.frame.g.view : Int) - 1 - content p.context.frame q.y = q.y - p.context.frame.g.top

theorem classified_key (p : Press) (time : Nat) (q : Point)
    (h : classify p time = some (.tap q)) (grid : SheetGeom.Grid) (ok : grid.Ok)
    (scroll i : Nat) :
    (match deliver p.context.frame (.tap q) with
      | .tap _ x y => grid.hit scroll x.toNat y.toNat
      | _ => none) = some i ↔
      i < grid.n ∧ grid.inBox scroll i p.first.pos.x.toNat.toUInt32.toNat (coord p.context.frame p.first.pos).toUInt32.toNat

theorem delivered_page (g : Geom) (fit : g.Fits) (over height x y : Nat)
    (lo : g.top ≤ y) (hi : y < g.composerTop) (hw : g.view < UInt32.size) :
    let f := Surface.make g true over 0 0 height
    match deliver f (.tap ⟨x, y⟩) with
    | .tap .list _ distance => g.view - 1 - distance.toNat = y - g.top
    | _ => False

theorem witnesses :
    let g : Geom := ⟨800, 20, 300, 80, 60⟩
    let c : Context := ⟨Surface.make g true 32 0 0 704, 160, 100⟩
    let p : Press := ⟨⟨0, 7, ⟨100, 120⟩, 1000⟩, c, 3, false⟩
    g.Fits ∧ classify p 1100 = some (.tap ⟨100, 120⟩) ∧
      classify (p.sample ⟨1, 7, ⟨120, 120⟩, 1100⟩) 1200 = none ∧
      (g.view : Int) - 1 - content c.frame 120 = 40

end Input
```

```lean
namespace Translate

theorem equivariance (g : Geom) (over bf base sample height r : Nat) :
    row (Surface.make g false over bf base height) sample r =
      Seam.place g over bf sample r

theorem pinned (g : Geom) (over bf base height r : Nat) (sample : Int) :
    row (Surface.make g true over bf base height) sample r = Seam.pinned g over r

theorem source_iff (pin : Bool) (base origin sample y : Int) (height r : Nat) :
    source pin base origin sample height y = some r ↔
      r < height ∧ y = position pin base origin sample + r

theorem copied_row (pin : Bool) (base origin sample : Int) (height top bottom r y : Nat)
    (hs : source pin base origin sample height y = some r)
    (lo : top ≤ y) (hi : y < bottom) :
    let q := rect pin base origin sample height top bottom
    q.src0 ≤ r ∧ r < q.src1 ∧ (q.dst0 : Int) + (r - q.src0 : Nat) = y

theorem fill_covers (pin : Bool) (base sample : Int) (top bottom : Nat) (fit : top ≤ bottom) :
    (fillRect pin base sample top bottom).dst0 = top ∧
    (fillRect pin base sample top bottom).dst1 = bottom

theorem fill_index (pin : Bool) (base sample : Int) (top bottom y : Nat)
    (lo : top ≤ y) (hi : y < bottom) :
    0 ≤ (y : Int) - fillOrigin pin base sample top bottom ∧
    ((y : Int) - fillOrigin pin base sample top bottom).toNat < bottom - top + 48

theorem tile_phase (base sample : Int) (top bottom y : Nat) (lo : top ≤ y) (hi : y < bottom) :
    47 - ((y : Int) - fillOrigin false base sample top bottom).toNat % 48 =
      (content sample bottom y % 48).toNat

theorem source_content (g : Geom) (fit : g.Fits) (over bf base height r y : Nat) (sample : Int)
    (hs : source false base (Surface.make g false over bf base height).origin sample height y = some r) :
    (bf : Int) + g.view + over - 1 - r = content sample g.composerTop y

theorem outside (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int)
    (h : source f.pin f.b f.origin sample height y = none) :
    seen f height high pad bottom more rows sample y = .unloaded

theorem covered (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int)
    (inside : ∀ r, source f.pin f.b f.origin sample height y = some r →
      pad ≤ (high - 1 - r).toNat ∧
      ((high - 1 - r).toNat < bottom + (rows.map (·.1)).sum ∨ more = true)) :
    seen f height high pad bottom more rows sample y ≠ .blank

theorem line_painted (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int) (j li : Nat)
    (h : seen f height high pad bottom more rows sample y = .line j li) :
    ∃ hj bh, rows[j]? = some (hj, some bh) ∧ li < bh

theorem edge_list (which : UInt8) (pin : Bool) (base : UInt32) (origin : Int32)
    (height top bottom : UInt32) (sample : Int32) :
    edge false which pin base origin height top bottom sample =
      let q := rect pin base.toNat origin.toInt sample.toInt height.toNat top.toNat bottom.toNat
      (if which == 0 then q.src0 else if which == 1 then q.src1
        else if which == 2 then q.dst0 else q.dst1).toUInt32

theorem edge_fill (pin : Bool) (base : UInt32) (origin : Int32)
    (height top bottom : UInt32) (sample : Int32) (fit : top.toNat ≤ bottom.toNat) :
    edge true 2 pin base origin height top bottom sample = top ∧
    edge true 3 pin base origin height top bottom sample = bottom

theorem pick_source (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) :
    (pick pin base origin height sample y).toInt =
      match source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat with
      | some r => (r : Int)
      | none => -1

theorem hold_row (s : Hold.St) (height r : Nat) (hr : r < height + 48) :
    (Hold.plane s height)[r]! = Hold.holdLine s (47 - r % 48)

theorem fill_pixel (s : Hold.St) (base top bottom : UInt32) (sample : Int32) (y : UInt32)
    (lo : top.toNat ≤ y.toNat) (hi : y.toNat < bottom.toNat)
    (size : bottom.toNat - top.toNat + 48 < UInt32.size) :
    (Hold.plane s (bottom.toNat - top.toNat))[
      (fillRow false base top bottom sample y).toNat]! =
      Hold.holdLine s (content sample.toInt bottom.toNat y.toNat % 48).toNat

theorem delta_value (pin : Bool) (base : UInt32) (sample : Int32)
    (lo : -2147483648 ≤ (if pin then 0 else sample.toInt - base.toNat : Int))
    (hi : (if pin then 0 else sample.toInt - base.toNat : Int) < 2147483648) :
    (delta pin base sample).toInt = if pin then 0 else sample.toInt - base.toNat

theorem tap_content (f : Surface.Frame) (pin : f.pin = false) (sample y : Int) :
    Input.content { f with slide := sample - f.b } y = content sample f.g.composerTop y

theorem witnesses :
    let g : Geom := ⟨200, 0, 0, 20, 20⟩
    let f := Surface.make g false 8 100 100 176
    seen f 176 268 0 0 false [(500, some 500)] 100 20 = .line 0 240 ∧
    seen f 176 268 0 0 false [(500, none)] 100 20 = .hold 0 ∧
    seen f 176 268 0 0 false [] 500 20 = .unloaded ∧
    (fillRect false 100 (-500) 20 180).dst0 = 20 ∧
    (fillRect false 100 (-500) 20 180).dst1 = 180

end Translate
```
