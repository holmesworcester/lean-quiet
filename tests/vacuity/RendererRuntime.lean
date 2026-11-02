import platforms.headless.Sim
import app.Proofs
import engine.renderer.Ttf.Laws
import tests.vacuity.RendererImages
import tests.vacuity.RendererLive
import tests.vacuity.RendererSupplement
import tests.engine.Checks

/-! Runtime premise certificates for native Float rasterization and real app
states holding SQLite/ref/task resources. No premise is assumed: each optional
certificate is produced only by an executable check. These are not closed
kernel proofs of foreign/native functions, and the data is synthetic. -/
set_option linter.defProp false
namespace Vacuity.RendererRuntime
open App Engine Data Tests

def backOpen (s : St) :=
  if hp : PageId.profile ≠ s.page then
    if hs : PageId.profile ∉ s.backStack then some (PLift.up (NavLaws.back_open .profile s hp hs))
    else none
  else none

def backRoot (s : St) := if h : s.backStack = [] then
  some (PLift.up (NavLaws.back_root s h)) else none

-- Laws with no premise: there is nothing to certify, so each check runs
-- the compiled code the law is about on the real App.start state and
-- tests the law's conclusion there (the proof itself is erased).
def switchBack (s : St) : Bool :=
  have := NavLaws.back_switch 5 (ByteArray.mk #[0x22]) s
  let n := (Nat.repeat backSt 5 (switchSt (ByteArray.mk #[0x22]) s)).nav
  n.page == .home && n.stack.isEmpty
def draftBack (s : St) : Bool :=
  have := NavLaws.draft_back s
  (backSt s).text == s.text && (backSt s).sel == s.sel && (backSt s).chips.size == s.chips.size
def stackDepth (s : St) := if h : (s.nav.page :: s.nav.stack).Nodup then
  some (PLift.up (NavLaws.depth .profile s h)) else none

def nativeInput (s : St) := if h : textTarget s ≠ .none then
  some (PLift.up (into_native s "A typed message אב" #[3, 3, 0, 0] h)) else none

def savedAnchor (s : St) : Bool :=
  have := LifecycleLaws.restore_page_anchor s
  (Lifecycle.restore (Codec.encode (checkpoint s))).map (fun cp =>
      (PageId.ofCode cp.2.1, cp.2.2.2.1, cp.2.2.2.2.1)) ==
    some (PageId.ofCode s.logNav.1, ((checkpointAnchor s).getD (.empty, 0)).1, ((checkpointAnchor s).getD (.empty, 0)).2) &&
  -- the page the log names is the page shown (App.withNav_cache)
  PageId.ofCode s.logNav.1 == s.page
def restoredAnchor (s target : St) :=
  match ha : checkpointAnchor s with
  | none => some (PLift.up (LifecycleLaws.apply_page_anchor s target (by
      intro x off hx; rw [ha] at hx; cases hx)))
  | some (x, off) =>
    if good : x.isEmpty = false then
      some (PLift.up (LifecycleLaws.apply_page_anchor s target (by
        intro y above hy; rw [ha] at hy; cases hy; exact good)))
    else none

def unmountedRead (s : St) : IO Bool := do
  have := LifecycleLaws.unmount_read s ⟨[ByteArray.mk #[0x61]], true⟩ .comms
  let (answer, _) ← (App.query ⟨[ByteArray.mk #[0x61]], true⟩ .comms).run (unmountState s)
  return answer.isNone
def unmountedWrite (s : St) : IO Bool := do
  have := LifecycleLaws.unmount_write s { ops := [Op.make 239 [] (ByteArray.mk #[1])] }
  let (sent, _) ← (App.writeAll { ops := [Op.make 239 [] (ByteArray.mk #[1])] }).run (unmountState s)
  return !sent
def oldCallback (s : St) : IO Bool := do
  have := LifecycleLaws.old_callback s (modify fun st => { st with text := "stale callback" })
  let (ran, after) ← (App.owned s.life.lease (modify fun st => { st with text := "stale callback" })).run
    { unmountState s with life := s.life.unmount.mount }
  return ran.isNone && after.text == s.text

-- Two different states, a minute apart, share a page key (the clock is not
-- on a page), so they draw the same page: not one key compared with itself.
theorem sameKey : ∀ s : St, drawPage s.font s.bgRow s.camView (pageIn { s with nowMs := s.nowMs + 60000 }) =
    drawPage s.font s.bgRow s.camView (pageIn s) :=
  fun s => App.drawPage_key s.font s.bgRow s.camView rfl
-- A state on another acceptance has another key, whatever else it shares:
-- so a switch always redraws.
theorem keyAcceptance : ∀ (s : St) (a : Id), a ≠ s.me.acc →
    pageIn { s with me := { s.me with acc := a } } ≠ pageIn s :=
  fun _ _ ha h => ha (App.pageIn_acc h)

-- Native float calculations cannot be reduced by Lean's kernel. Successful
-- runtime matches provide the exact raster-success premise to each theorem.
def rasterValid (f : Ttf.Face) (g : Nat) : Option (PLift (∃ b, Ttf.raster f g 20 24 = some b ∧ b.Valid)) := do
  match h : Ttf.raster f g 20 24 with
  | none => none
  | some b => some ⟨b, h, Ttf.raster_valid f g 20 24 b h⟩

def rasterPixel (f : Ttf.Face) (g : Nat) : Option (PLift (∃ b, Ttf.raster f g 20 24 = some b ∧
    ∃ hi : 0 * b.w + 0 < b.pixels.size, b.pixels[0 * b.w + 0].toNat ≤ 255)) := do
  match h : Ttf.raster f g 20 24 with
  | none => none
  | some b =>
    if hx : 0 < b.w then
      if hy : 0 < b.h then
        some ⟨b, h, Ttf.raster_pixel f g 20 24 b h 0 0 hx hy⟩
      else none
    else none

def added := Pic.add #[] 2 1 2 1 RendererImages.picture.px
def addStored := if grew : added.1.size = (#[] : Pic.Composer).size + 1 then
  some (PLift.up (Pic.add_stored (c := #[]) (c' := added.1) (msg := added.2) (ow := 2) (oh := 1) (w := 2) (h := 1) (px := RendererImages.picture.px) rfl grew))
  else none

attribute [local instance] LiveLaws.byteArray_lawful LiveLaws.listQ_lawful LiveLaws.q_lawful

def nextSnapshot (q : Q) : Ans :=
  if q == RendererLive.queryA then .bytes (some "changed hello".toUTF8) else RendererLive.snapshot q

def noticedAgreement :=
  let vs := #[ByteArray.mk #[0x61]]
  if hit : (RendererLive.cache.hit #[] vs).contains RendererLive.queryA = true then
    some (PLift.up (LiveLaws.agrees_notice RendererLive.store #[] vs (ans' := nextSnapshot) (by
      intro q hq
      by_cases same : q = RendererLive.queryA
      · subst q; rw [hit] at hq; cases hq
      · simp [nextSnapshot, same])))
  else none

-- Fitting viewport with a visible keyboard, including the app law's pair.
def viewport := LifecycleLaws.viewport_geometry (Geometry.Geom.mk 1280 24 300 80 100)
  (by unfold Geometry.Geom.Fits; decide) 8 100 124 600 200
def viewportExists := LifecycleLaws.viewport_possible

def pageCodec := App.page_round .profile

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "all supplemental signed-data checks pass" ((← RendererSupplement.main) == 0)
  let dir := "out/vacuity/renderer-runtime"
  IO.FS.createDirAll dir
  -- Named deterministic assets task supplies this font; no network is used.
  let bytes ← IO.FS.readBinFile "assets/NotoSans-Regular.ttf"
  let some face := Ttf.read bytes | throw (IO.userError "font fixture did not parse")
  let some glyph := Ttf.lookup face.cmap 65 | throw (IO.userError "font fixture lacks A")
  t.ok "real-font raster premise produces a valid bitmap certificate" (rasterValid face glyph).isSome
  t.ok "real-font nonempty raster has an in-bounds pixel certificate" (rasterPixel face glyph).isSome
  t.ok "invalid zero-size native raster is rejected" ((Ttf.raster face glyph 0 24).isNone)
  t.ok "changed-answer journal reaches the exact cached query" noticedAgreement.isSome
  let memo := Ttf.Memo.source bytes 24 24
  t.ok "real-font glyph memo answers the raster's bytes"
    ((memo.bitmap glyph).map (·.pixels) == (memo.uncached glyph).map (·.pixels) &&
      (memo.bitmap glyph).isSome)
  t.ok "compact keeps a real raster unchanged"
    (((Ttf.raster face glyph 24 24).map Ttf.Memo.compact).map (·.pixels) ==
      (Ttf.raster face glyph 24 24).map (·.pixels))
  t.ok "concrete two-pixel attachment grows and applies add_stored" addStored.isSome
  let sm ← Sim.new
  let s ← App.start sm.io #[390, 844, 0, 0, 160] (dir ++ "/quiet.db")
  let s := { s.withNav ⟨.chat, [.home]⟩ with text := "Draft message", field := "Name", mark := none }
  t.ok "opening profile satisfies the navigation premises" (backOpen s).isSome
  t.ok "root state satisfies the no-back-stack premise" (backRoot { s with backStack := [] }).isSome
  t.ok "a distinct finite page stack satisfies the navigation invariant" (stackDepth s).isSome
  t.ok "native text event has an actual editing target" (nativeInput s).isSome
  t.ok "checkpoint restoration satisfies the no-anchor branch" (restoredAnchor s s).isSome
  t.ok "nonempty concrete message anchor also satisfies restoration premises"
    (restoredAnchor { s with mark := some (ByteArray.mk #[0xAB, 0xCD], 180) } s).isSome
  t.ok "unmounted real app query executes without returning an answer" (← unmountedRead s)
  t.ok "unmounted real app write is declined" (← unmountedWrite s)
  t.ok "remounted real app rejects the old callback" (← oldCallback s)
  t.ok "back keeps the draft (Draft message), selection and photos" (s.text == "Draft message" && draftBack s)
  t.ok "five backs after switch stay on new home, with nothing under it" (switchBack s)
  t.ok "checkpoint roundtrip restores the actual app page and anchor" (savedAnchor s)
  s.raster.reconcile []
  return ← t.finish "renderer/app vacuity (runtime premises)"

end Vacuity.RendererRuntime

