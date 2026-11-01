import app.community.Proofs
import app.Commands
import engine.renderer.Row
import app.community.channel.message.attachment.View
import app.community.channel.message.attachment.chunk.View
import engine.renderer.Work
import engine.core.WindowIndex
import engine.renderer.Image
import engine.renderer.Arrival
import engine.core.Cost
import app.community.Family
import app.community.channel.message.Op
import app.community.Commands
import app.community.channel.message.attachment.chunk.Proofs
import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.attachment.chunk.Commands
import app.community.channel.message.attachment.Op
import app.community.Op

namespace ArrivalLaws
attribute [local irreducible] Text.oneLine
open _root_.Arrival
open _root_.Row
open _root_.Engine _root_.Community _root_.Data
attribute [local instance] modelReads
section
variable {C : Crypto} {s : DB Fact} (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
  (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct))
include hsize hspr

/-- **Complete is every chunk held.** A picture whose counts are its
attachment's progress (as `pic_progress` reads them) is complete exactly
when the store holds a Valid chunk of that attachment at every index. -/
theorem complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    {p : Pic} (hp : (p.got, p.total) = (progress c att len).eval s) :
    p.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) := by
  have hle := progress_le hsize hspr h hq ha
  have hfull := progress_full hsize hspr h hq ha
  have ht : (progress c att len).eval s = (((progress c att len).eval s).1, Merkle.nChunks len) := by
    unfold progress; simp
  rw [← hp] at hle hfull ht
  simp only [Prod.mk.injEq] at ht
  rw [Pic.complete, done_iff hle (by rw [ht.2]; exact Merkle.one_le_nChunks len)]
  exact hfull

/-- **A picture showing its file holds all of it.** Shown as the file
(`shown_file`), its counts being its attachment's progress, the
attachment's length is the file's and the store holds each of the
file's chunk ops, whose slices are the file. -/
theorem file_whole (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    {p : Pic} (hp : (p.got, p.total) = (progress c att len).eval s)
    {α : Type} (pre full : Option α) (hs : (p.shown pre full).2 = true) :
    len = ct.size ∧ ∀ i < Merkle.nChunks ct.size,
      V C s.ops (fileChunk c att ct i).id (.chunk c att (Merkle.fileRoot sha256 ct) ct.size i) := by
  have hc := ((shown_file p pre full).1 hs).1
  have hle := progress_le hsize hspr h hq ha
  refine progress_done hsize hspr h hq ha ?_
  rw [← hp] at hle ⊢
  simp only [Pic.complete, done, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only at hle ⊢
  omega

/-- **The picture the app reads is complete exactly when its file is
held**: `Kinds.File.pic` over the store, composed with `complete_iff_held`. -/
theorem pic_complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    (info : FileMeta) (fk fn : ByteArray) (deps : Array Q) :
    ((Kinds.File.pic (m := Model) c att (Merkle.fileRoot sha256 ct) len info fk fn deps).run s).1.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) :=
  complete_iff_held hsize hspr h hq ha (pic_progress c att _ len info fk fn deps s)

end
end ArrivalLaws

section

/- Op-type components use the generic Work pool. A picture's QOI decode
is one native/pure unit; scaling yields every eight output rows. The
measured largest unit is reported separately from the scheduler's laws. -/

namespace Raster
open Engine Paint

inductive Key where
  | row (generation : Nat) (message : Id) (version : Nat) (ready : List Bool) (theme : Theme.Value)
  | dim (generation : Nat) (message : Id) (version : Nat) (ready : List Bool) (theme : Theme.Value)
  | image (key : FileImage.Key) (theme : Theme.Value)
  deriving BEq

private theorem lawfulTheme : LawfulBEq Theme.Value where
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl
  rfl {a} := by cases a <;> rfl
attribute [local instance] Engine.lawfulBEqByteArray lawfulTheme
deriving instance ReflBEq, LawfulBEq for Key
/-- Scheduler key equality is equality of every render input named by Key. -/
theorem key_eq (a b : Key) : (a == b) = true ↔ a = b := beq_iff_eq

def messageOwner (community message : Id) : Demand.Owner :=
  ["community".toUTF8, community, "message".toUTF8, message]

def pictureOwner (community message attachment : Id) : Demand.Owner :=
  messageOwner community message ++ ["attachment".toUTF8, attachment]

/-- Bottom-origin content bounds, shared by component mounting and work
priority. A margin is explicit; it does not silently retain whole rows. -/
def near (bottom height offset viewport margin : Nat) : Bool :=
  bottom ≤ offset + viewport + margin && offset - margin ≤ bottom + height

/-- Exactly the sample box used by Image.scaled for target row y. -/
def scaledRow (src : Image.Src) (w h y : Nat) (bg : Color) : ByteArray :=
  let y0 := y * src.h / max h 1
  let y1 := max (y0 + 1) ((y + 1) * src.h / max h 1)
  (Image.scaleCrop src 0 y0 src.w (y1 - y0) w 1 bg).rows[0]!

def image (source : Unit → Option Image.Src) (w h : Nat) (theme : Theme.Value)
    (preview : Bool) : IO (Work.Action Bitmap) := do
  let state ← IO.mkRef ((none : Option Image.Src), (#[] : Array ByteArray))
  return fun _ => do
    let (src, rows) ← state.get
    let bg := Palette.color theme .bg
    match src with
    | none =>
      match source () with
      | none => return some (Bitmap.blank w h (solid (Palette.color theme .selected) w))
      | some src => state.set (some src, #[]); return none
    | some src =>
      let mut rows := rows
      for y in [rows.size:min (max h 1) (rows.size + 8)] do
        let row := scaledRow src (max w 1) (max h 1) y bg
        let row := if preview then (Arrival.soften bg { w := max w 1, rows := #[row] }).rows[0]! else row
        rows := rows.push row
      if rows.size == max h 1 then return some { w := max w 1, rows }
      state.set (some src, rows)
      return none

def fileSource (p : Row.Pic) (raw : List ByteArray) : Option Image.Src :=
  FileImage.source p raw

end Raster

end

section

/- A first committed own-body paint keeps its admitted snapshot while
compatible cosmetic updates accumulate. Work's lifetime gate stays intact. -/

namespace Raster.RowPaint
open Engine Paint Row

/-- Data whose change must revoke an in-flight body snapshot. Names and
reaction tallies, including their layout, may lag for one paint; identity, body, pending state,
attachments, selection and every other field must agree. -/
def bodyInputs (d : RowData) : RowData :=
  { d with name := "", namesake := false, tallies := [] }

structure Stamp where
  generation : Nat
  message : Id
  width : Nat
  dim : Dim
  background : ByteArray
  body : RowData
  ready : List Bool
  deriving BEq

def stamp (generation : Nat) (message : Id) (width : Nat) (dim : Dim)
    (background : ByteArray) (data : RowData) (ready : List Bool) : Stamp :=
  ⟨generation, message, width, dim, background, bodyInputs data, ready⟩

structure Flight where
  stamp : Stamp
  version : Nat
  requestId : Nat
  data : RowData
  lay : Layout
  images : Array (Option Bitmap)
  handle : Work.Handle Raster.Key Bitmap

/-- The caller declares the returned key for this frame. Retaining that
key keeps the original queue position and publication ticket; replacing it
still uses Work's ordinary revocation. Failed or revoked work is not reused. -/
def request (pool : Work.Pool Raster.Key Bitmap) (owner : Demand.Owner) (visible first : Bool)
    (previous : Option Flight) (stamp : Stamp) (version : Nat)
    (data : RowData) (lay : Layout) (images : Array (Option Bitmap))
    (action : Work.Action Bitmap) : IO (Flight × Option Bitmap) := do
  if let some old := previous then
    if old.stamp == stamp && (first || old.version == version) then
      let current ← pool.state.atomically do return (← get).plan.current old.handle.ticket
      if current then
        let value ← old.handle.value
        if value.isSome || !(← IO.hasFinished old.handle.result) then return (old, value)
  -- A replacement gets a distinct key even if its data version is unchanged
  -- (for example an attachment becomes ready, or a failed action is retried).
  let requestId := max version (previous.map (·.requestId + 1) |>.getD 0)
  let key := Raster.Key.row stamp.generation stamp.message requestId stamp.ready stamp.dim.theme
  let handle ← pool.request ⟨owner, key, visible⟩ action
  return (⟨stamp, version, requestId, data, lay, images, handle⟩, ← handle.value)

end Raster.RowPaint

end

section

/-
Historical picture cost model and negative controls, not the app's
runtime. The shipping attachment component uses FileImage and Work.Pool;
its ownership laws and integration tests cover that path. This model's
settling/cost laws must not be presented as proofs of the current app.

The app draws every picture on screen every frame (`image`). Decoding is
slow (a 64 KiB chunk's file, or a preview, scaled), so it runs on a task
and its bitmap is kept by key (hash, stage, size): a frame looks the key
up and starts a decode only when there is none. A file whose chunk ops
are not all readable yet is tried again two seconds on, or when its
chunks land (the app clears the retry table when the reader's board
takes them).

Everything this model's `image` does that costs goes through a door of
`Pics`: the store (`chunks`, the chunk ops' bytes) and a task (`spawn`).
Counted (`CostT`), each door is charged: a read per chunk
op, a spawn per task.

Laws, over a world as data (`World`, `PicM`):
- `decoded_started`: a key whose decode has started costs nothing,
  whatever its start would do.
- `image_steady`: a picture that is steady (its decodes started, or its
  file's retry not yet due) costs no spawn and no read.
- `image_settles`: one frame's `image` leaves the picture steady. So a
  frame whose data has not changed spawns no decode task and does no
  store read for any picture an earlier frame drew (`image_twice`),
  until a retry falls due.

The negative control is `imageV`, the old `decoded`: its start was a
value, and Lean evaluates an argument at the call, so the preview's
task was spawned on every call, before the lookup. Through the door that
is `start` run before the lookup. It costs a spawn in every steady world
(`imageV_over_budget`): 387–667% idle CPU on phones, as it shipped.
-/

namespace Pics
open Engine Paint Row

/-- A decode's key: the picture's hash and stage (0 the preview, 1 the
file), and the size it is drawn at. -/
abbrev Key := ByteArray × Nat × Nat

/-! ## The work: pure, run on a task -/

/-- A picture's QOI bytes decoded at a size (square, or scaled to fill),
or a placeholder. -/
def decodePic (bytes : ByteArray) (w h : Nat) (sq : Bool) (theme : Theme.Value := .dark) : Bitmap :=
  match Image.decode bytes with
  | some src => if sq then Image.square src w (Palette.color theme .bg) else Image.scaled src w h (Palette.color theme .bg)
  | none => Bitmap.blank w h (solid (Palette.color theme .selected) w)

/-- Chunk ops' bytes to their slices, in order. -/
def slicesFromOps (raw : List ByteArray) : Option (List ByteArray) :=
  raw.mapM fun b => do
    let o ← Engine.Op.decode b
    match (Codec.decode o.body : Option Community.Body) with
    | some (.chunk _ _ _ slice _) => some slice
    | _ => none

/-- An attachment's file from its chunk ops' bytes: opened with the
file's key, decoded and scaled to fill w × h, or a placeholder. -/
def decodeFile (p : Row.Pic) (raw : List ByteArray) (w h : Nat) (theme : Theme.Value := .dark) : Bitmap :=
  match ((slicesFromOps raw).bind fun slices => Community.openFile slices p.key p.nonce).bind
      Image.decode with
  | some src => Image.scaled src w h (Palette.color theme .bg)
  | none => Bitmap.blank w h (solid (Palette.color theme .selected) w)

/-! ## The doors -/

/-- What a frame's pictures go through. `chunks` and `spawn` cost; the
others are the app's own memory and the runtime's task states. -/
class Pics (m : Type → Type) where
  /-- The decode started for a key, if any. -/
  started : Key → m (Option (Task Bitmap))
  /-- Remember a key's decode. -/
  remember : Key → Task Bitmap → m Unit
  /-- Whether a task has finished. -/
  finished : Task Bitmap → m Bool
  /-- The frame from which a key's file may be tried again. -/
  retryAt : Key → m (Option Nat)
  /-- Try a key's file again in two seconds (120 frames). -/
  retryLater : Key → m Unit
  /-- The frame number. -/
  frame : m Nat
  /-- An attachment's chunk ops' bytes, in order, as stored (or in the
  outbox); none while one is not here. A store read per chunk op. -/
  chunks : Row.Pic → m (Option (List ByteArray))
  /-- Work on a task, off the app's thread. -/
  spawn : (Unit → Bitmap) → m (Task Bitmap)

/-! ## What the app runs -/

section
variable {m : Type → Type} [Monad m] [Pics m]

/-- A decode of `k` started (or finished): its bitmap once done. `start`
runs only when `k` has no decode yet. -/
def decoded (k : Key) (start : Unit → m (Option (Task Bitmap))) : m (Option Bitmap) := do
  match ← Pics.started k with
  | some t => if ← Pics.finished t then return some t.get else return none
  | none =>
    if let some t ← start () then Pics.remember k t
    return none

/-- The preview's decode, if it has one. -/
def startPre (p : Row.Pic) (w h : Nat) (theme : Theme.Value := .dark) : m (Option (Task Bitmap)) := do
  if p.preview.isEmpty then return none
  return some (← Pics.spawn fun _ => Arrival.soften (Palette.color theme .bg) (decodePic p.preview w h false theme))

/-- The file's decode, once its chunk ops are readable: else a retry,
two seconds on (or sooner, when the store changes). -/
def startFull (p : Row.Pic) (w h : Nat) (theme : Theme.Value := .dark) : m (Option (Task Bitmap)) := do
  let k := (p.hash.push 1, w, h)
  if let some t ← Pics.retryAt k then
    if (← Pics.frame) < t then return none
  let some raw ← Pics.chunks p
    | Pics.retryLater k; return none
  return some (← Pics.spawn fun _ => decodeFile p raw w h theme)

/-- An attachment drawn at its size, if ready, and whether it is the
file (not its preview), as `Row.Pic.shown` chooses: the preview
(softened, `Arrival.soften`) until every chunk is here and the file is
decoded, then the file. -/
def image (p : Row.Pic) (w h : Nat) (theme : Theme.Value := .dark) : m (Option Bitmap × Bool) := do
  let pre ← decoded (p.hash.push 0, w, h) fun _ => startPre p w h theme
  let full ← if !p.complete then pure none else decoded (p.hash.push 1, w, h) fun _ => startFull p w h theme
  return p.shown pre full

end

/-! ## Counted: a read per chunk op, a spawn per task -/

instance {m : Type → Type} [Monad m] [Pics m] : Pics (CostT m) where
  started k := CostT.lift (Pics.started k)
  remember k t := CostT.lift (Pics.remember k t)
  finished t := CostT.lift (Pics.finished t)
  retryAt k := CostT.lift (Pics.retryAt k)
  retryLater k := CostT.lift (Pics.retryLater k)
  frame := CostT.lift Pics.frame
  chunks p := CostT.charged { reads := p.chunks.length } (Pics.chunks p)
  spawn f := CostT.charged { spawns := 1 } (Pics.spawn f)

/-! ## A world as data -/

/-- What a frame's pictures see: the decode and retry tables, the frame
number, which tasks have finished (the runtime's choice), and what the
store holds. -/
structure World where
  imgs : Key → Option (Task Bitmap)
  retry : Key → Option Nat
  frames : Nat
  done : Task Bitmap → Bool
  store : Row.Pic → Option (List ByteArray)

/-- A state monad over the world, written out so runs reduce. -/
def PicM (α : Type) := World → α × World

instance : Monad PicM where
  pure a := fun w => (a, w)
  bind x f := fun w => f (x w).1 (x w).2

instance : Pics PicM where
  started k := fun w => (w.imgs k, w)
  remember k t := fun w => ((), { w with imgs := fun k' => if k' = k then some t else w.imgs k' })
  finished t := fun w => (w.done t, w)
  retryAt k := fun w => (w.retry k, w)
  retryLater k := fun w =>
    ((), { w with retry := fun k' => if k' = k then some (w.frames + 120) else w.retry k' })
  frame := fun w => (w.frames, w)
  chunks p := fun w => (w.store p, w)
  spawn f := fun w => (Task.spawn f, w)

/-- A counted run from w: its value and charge, and the world after. -/
def run {α : Type} (x : CostT PicM α) (w : World) : (α × Meter) × World := x.run w

/-- What a counted run charged. -/
def costIn {α : Type} (x : CostT PicM α) (w : World) : Meter := (run x w).1.2

/-- The world after a run. -/
def after {α : Type} (x : CostT PicM α) (w : World) : World := (run x w).2

section
variable {α β : Type}

@[simp] theorem run_pure (a : α) (w : World) : run (pure a : CostT PicM α) w = ((a, 0), w) := rfl

@[simp] theorem run_bind (x : CostT PicM α) (f : α → CostT PicM β) (w : World) :
    run (x >>= f) w =
      (((run (f (run x w).1.1) (run x w).2).1.1, (run x w).1.2 + (run (f (run x w).1.1) (run x w).2).1.2),
        (run (f (run x w).1.1) (run x w).2).2) := rfl

@[simp] theorem run_started (k : Key) (w : World) :
    run (Pics.started k : CostT PicM _) w = ((w.imgs k, 0), w) := rfl
@[simp] theorem run_remember (k : Key) (t : Task Bitmap) (w : World) :
    run (Pics.remember k t : CostT PicM _) w =
      (((), 0), { w with imgs := fun k' => if k' = k then some t else w.imgs k' }) := rfl
@[simp] theorem run_finished (t : Task Bitmap) (w : World) :
    run (Pics.finished t : CostT PicM _) w = ((w.done t, 0), w) := rfl
@[simp] theorem run_retryAt (k : Key) (w : World) :
    run (Pics.retryAt k : CostT PicM _) w = ((w.retry k, 0), w) := rfl
@[simp] theorem run_retryLater (k : Key) (w : World) :
    run (Pics.retryLater k : CostT PicM _) w =
      (((), 0), { w with retry := fun k' => if k' = k then some (w.frames + 120) else w.retry k' }) := rfl
@[simp] theorem run_frame (w : World) : run (Pics.frame : CostT PicM _) w = ((w.frames, 0), w) := rfl
@[simp] theorem run_chunks (p : Row.Pic) (w : World) :
    run (Pics.chunks p : CostT PicM _) w = ((w.store p, { reads := p.chunks.length }), w) := rfl
@[simp] theorem run_spawn (f : Unit → Bitmap) (w : World) :
    run (Pics.spawn f : CostT PicM _) w = ((Task.spawn f, { spawns := 1 }), w) := rfl

end

/-! ## Laws -/

section
variable {k : Key} {w : World}

theorem run_decoded_some {start : Unit → CostT PicM (Option (Task Bitmap))} {t : Task Bitmap}
    (h : w.imgs k = some t) :
    run (decoded k start) w = ((if w.done t then some t.get else none, 0), w) := by
  simp only [decoded, run_bind, run_started, h]
  by_cases hd : w.done t = true <;> simp [hd]

theorem run_decoded_none {start : Unit → CostT PicM (Option (Task Bitmap))} (h : w.imgs k = none) :
    run (decoded k start) w =
      ((none, (run (start ()) w).1.2),
        match (run (start ()) w).1.1 with
        | some t => { (run (start ()) w).2 with
            imgs := fun k' => if k' = k then some t else (run (start ()) w).2.imgs k' }
        | none => (run (start ()) w).2) := by
  simp only [decoded, run_bind, run_started, h]
  cases h' : (run (start ()) w).1.1 <;> simp

end

/-- **A key whose decode has started costs nothing**, whatever its
start would do: no spawn, no read, and the world unchanged. -/
theorem decoded_started (k : Key) (start : Unit → CostT PicM (Option (Task Bitmap))) (w : World)
    {t : Task Bitmap} (h : w.imgs k = some t) :
    costIn (decoded k start) w = 0 ∧ after (decoded k start) w = w := by
  simp [costIn, after, run_decoded_some h]

/-- The two stages' keys differ. -/
theorem key_ne (p : Row.Pic) (w h : Nat) : ((p.hash.push 0, w, h) : Key) ≠ (p.hash.push 1, w, h) := by
  intro e
  have := congrArg (fun k : Key => k.1.data.toList) e
  simp at this

section
variable {theme : Theme.Value}

theorem run_startPre (p : Row.Pic) (wd ht : Nat) (w : World) :
    (p.preview.isEmpty = true → run (startPre p wd ht theme) w = ((none, 0), w)) ∧
    (p.preview.isEmpty = false → ∃ t, run (startPre p wd ht theme) w = ((some t, { spawns := 1 }), w)) := by
  refine ⟨fun he => by simp [startPre, he],
    fun he => ⟨Task.spawn fun _ => Arrival.soften (Palette.color theme .bg) (decodePic p.preview wd ht false theme), ?_⟩⟩
  simp [startPre, he]

/-- The file's start: it waits while a retry is not due; else it reads
the chunk ops, and spawns the decode if they are all here, or sets a
retry. -/
theorem run_startFull (p : Row.Pic) (wd ht : Nat) (w : World) :
    let k := (p.hash.push 1, wd, ht)
    ((∃ t, w.retry k = some t ∧ w.frames < t) → run (startFull p wd ht theme) w = ((none, 0), w)) ∧
    ((∀ t, w.retry k = some t → t ≤ w.frames) →
      (∀ raw, w.store p = some raw →
        ∃ t, run (startFull p wd ht theme) w = ((some t, { reads := p.chunks.length, spawns := 1 }), w)) ∧
      (w.store p = none →
        run (startFull p wd ht theme) w = ((none, { reads := p.chunks.length }),
          { w with retry := fun k' => if k' = k then some (w.frames + 120) else w.retry k' }))) := by
  intro k
  refine ⟨fun ⟨t, hr, hlt⟩ => by simp [startFull, k, hr, hlt],
    fun hdue => ⟨fun raw hs => ⟨Task.spawn fun _ => decodeFile p raw wd ht theme, ?_⟩, fun hs => ?_⟩⟩
  · cases hr : w.retry k with
    | none => simp [startFull, k, hr, hs]; ext <;> simp
    | some t =>
      have := hdue t hr
      simp [startFull, k, hr, hs, Nat.not_lt.2 this]; ext <;> simp
  · cases hr : w.retry k with
    | none => simp [startFull, k, hr, hs]
    | some t =>
      have := hdue t hr
      simp [startFull, k, hr, hs, Nat.not_lt.2 this]

/-- `image` is the preview's `decoded`, then (every chunk here) the
file's. -/
theorem run_image (p : Row.Pic) (wd ht : Nat) (w : World) :
    let pre := decoded (p.hash.push 0, wd, ht) fun _ => startPre p wd ht theme
    let full := decoded (p.hash.push 1, wd, ht) fun _ => startFull p wd ht theme
    costIn (image p wd ht theme) w = costIn pre w + (if p.complete then costIn full (after pre w) else 0) ∧
      after (image p wd ht theme) w = (if p.complete then after full (after pre w) else after pre w) := by
  intro pre full
  simp only [costIn, after, image, run_bind]
  by_cases hc : p.complete = true <;> simp [hc, pre, full]

/-- A picture is steady in a world: its preview's decode has started
(or it has no preview), and if every chunk is here, its file's decode
has started or its retry is not yet due. -/
def Steady (p : Row.Pic) (wd ht : Nat) (w : World) : Prop :=
  (p.preview.isEmpty = false → (w.imgs (p.hash.push 0, wd, ht)).isSome) ∧
  (p.complete = true → (w.imgs (p.hash.push 1, wd, ht)).isSome ∨
    ∃ t, w.retry (p.hash.push 1, wd, ht) = some t ∧ w.frames < t)

/-- The preview's decoded, steady, costs nothing. -/
theorem pre_steady (p : Row.Pic) (wd ht : Nat) (w : World)
    (h : p.preview.isEmpty = false → (w.imgs (p.hash.push 0, wd, ht)).isSome) :
    costIn (decoded (p.hash.push 0, wd, ht) fun _ => startPre p wd ht theme) w = 0 ∧
      after (decoded (p.hash.push 0, wd, ht) fun _ => startPre p wd ht theme) w = w := by
  cases hk : w.imgs (p.hash.push 0, wd, ht) with
  | some t => exact decoded_started _ _ w hk
  | none =>
    have he : p.preview.isEmpty = true := by
      cases hp : p.preview.isEmpty
      · have := h hp; rw [hk] at this; cases this
      · rfl
    simp [costIn, after, run_decoded_none hk, ((run_startPre (theme := theme) p wd ht w).1 he)]

/-- The file's decoded, steady, costs nothing. -/
theorem full_steady (p : Row.Pic) (wd ht : Nat) (w : World)
    (h : (w.imgs (p.hash.push 1, wd, ht)).isSome ∨
      ∃ t, w.retry (p.hash.push 1, wd, ht) = some t ∧ w.frames < t) :
    costIn (decoded (p.hash.push 1, wd, ht) fun _ => startFull p wd ht theme) w = 0 ∧
      after (decoded (p.hash.push 1, wd, ht) fun _ => startFull p wd ht theme) w = w := by
  cases hk : w.imgs (p.hash.push 1, wd, ht) with
  | some t => exact decoded_started _ _ w hk
  | none =>
    rw [hk] at h
    have hw := h.resolve_left (by simp)
    simp [costIn, after, run_decoded_none hk, ((run_startFull (theme := theme) p wd ht w).1 hw)]

/-- **A steady picture costs nothing**: no spawn and no store read, and
the world is unchanged. -/
theorem image_steady (p : Row.Pic) (wd ht : Nat) (w : World) (h : Steady p wd ht w) :
    costIn (image p wd ht theme) w = 0 ∧ after (image p wd ht theme) w = w := by
  obtain ⟨c, a⟩ := run_image (theme := theme) p wd ht w
  obtain ⟨c1, a1⟩ := pre_steady (theme := theme) p wd ht w h.1
  rw [c, a, c1, a1]
  by_cases hc : p.complete = true
  · obtain ⟨c2, a2⟩ := full_steady (theme := theme) p wd ht w (h.2 hc)
    simp [hc, c2, a2]
  · simp [hc]

/-- After the preview's decoded, its key is started (if it has a
preview), and the other keys, the retries and the frame are as they
were. -/
theorem pre_after (p : Row.Pic) (wd ht : Nat) (w : World) :
    let w' := after (decoded (p.hash.push 0, wd, ht) fun _ => startPre p wd ht theme) w
    (p.preview.isEmpty = false → (w'.imgs (p.hash.push 0, wd, ht)).isSome) ∧
      (∀ k, k ≠ (p.hash.push 0, wd, ht) → w'.imgs k = w.imgs k) ∧
      w'.retry = w.retry ∧ w'.frames = w.frames := by
  intro w'
  cases hk : w.imgs (p.hash.push 0, wd, ht) with
  | some t =>
    have e : w' = w := (decoded_started _ (fun _ => startPre p wd ht theme) w hk).2
    rw [e, hk]; exact ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | none =>
    cases he : p.preview.isEmpty
    · obtain ⟨t, ht'⟩ := (run_startPre (theme := theme) p wd ht w).2 he
      simp only [w', after, run_decoded_none hk, ht']
      refine ⟨fun _ => by simp, fun k hk' => by simp [hk'], ?_⟩
      simp
    · simp [w', after, run_decoded_none hk, (run_startPre (theme := theme) p wd ht w).1 he]

/-- After the file's decoded, its key is started or its retry is not
yet due, and the other keys and the frame are as they were. -/
theorem full_after (p : Row.Pic) (wd ht : Nat) (w : World) :
    let k := (p.hash.push 1, wd, ht)
    let w' := after (decoded k fun _ => startFull p wd ht theme) w
    ((w'.imgs k).isSome ∨ ∃ t, w'.retry k = some t ∧ w'.frames < t) ∧
      (∀ k', k' ≠ k → w'.imgs k' = w.imgs k') ∧ w'.frames = w.frames := by
  intro k w'
  cases hk : w.imgs k with
  | some t =>
    have e : w' = w := (decoded_started _ (fun _ => startFull p wd ht theme) w hk).2
    rw [e, hk]; exact ⟨Or.inl rfl, fun _ _ => rfl, rfl⟩
  | none =>
    obtain ⟨hwait, hgo⟩ := run_startFull (theme := theme) p wd ht w
    by_cases hd : ∃ t, w.retry k = some t ∧ w.frames < t
    · simp only [w', after, run_decoded_none hk, hwait hd]
      exact ⟨Or.inr hd, fun _ _ => trivial, trivial⟩
    · have hdue : ∀ t, w.retry k = some t → t ≤ w.frames := fun t hr =>
        Nat.not_lt.1 fun hlt => hd ⟨t, hr, hlt⟩
      obtain ⟨hyes, hno⟩ := hgo hdue
      cases hs : w.store p with
      | some raw =>
        obtain ⟨t, ht'⟩ := hyes raw hs
        simp only [w', after, run_decoded_none hk, ht']
        refine ⟨Or.inl (by simp), fun k' hk' => by simp [hk'], ?_⟩
        simp
      | none =>
        simp [w', k, after, run_decoded_none hk, hno hs]

/-- **One frame's `image` leaves the picture steady.** -/
theorem image_settles (p : Row.Pic) (wd ht : Nat) (w : World) :
    Steady p wd ht (after (image p wd ht theme) w) := by
  rw [(run_image (theme := theme) p wd ht w).2]
  obtain ⟨p1, -, -, -⟩ := pre_after (theme := theme) p wd ht w
  by_cases hc : p.complete = true
  · simp only [hc, ite_true]
    obtain ⟨f1, f2, -⟩ := full_after (theme := theme) p wd ht (after (decoded (p.hash.push 0, wd, ht) fun _ => startPre p wd ht theme) w)
    refine ⟨fun hp => ?_, fun _ => f1⟩
    rw [f2 _ (key_ne p wd ht)]; exact p1 hp
  · simp only [hc]
    exact ⟨p1, fun h => absurd h hc⟩

/-- **A frame whose data has not changed spawns no decode task and does
no store read**: `image` run again on the world one run left costs
nothing. -/
theorem image_twice (p : Row.Pic) (wd ht : Nat) (w : World) :
    costIn (image p wd ht theme) (after (image p wd ht theme) w) = 0 :=
  (image_steady (theme := theme) p wd ht _ (image_settles (theme := theme) p wd ht w)).1

end

/-- **Steady stays steady** as frames pass, until a retry falls due. -/
theorem steady_later (p : Row.Pic) (wd ht : Nat) (w : World) (d : Nat) (h : Steady p wd ht w)
    (hd : ∀ t, w.retry (p.hash.push 1, wd, ht) = some t → w.frames + d < t) :
    Steady p wd ht { w with frames := w.frames + d } := by
  refine ⟨h.1, fun hc => ?_⟩
  rcases h.2 hc with h' | ⟨t, hr, _⟩
  · exact Or.inl h'
  · exact Or.inr ⟨t, hr, hd t hr⟩

/-! ## The negative control: the start as a value -/

section
variable {m : Type → Type} [Monad m] [Pics m]

/-- The old `decoded`: its start a value. Lean evaluates an argument at
the call, so the preview's task was spawned before the lookup, every
frame, and dropped when the key had one. -/
def decodedV (k : Key) (start : m (Option (Task Bitmap))) : m (Option Bitmap) := do
  let t? ← start
  match ← Pics.started k with
  | some t => if ← Pics.finished t then return some t.get else return none
  | none =>
    if let some t := t? then Pics.remember k t
    return none

/-- `image` with the old `decoded` for the preview, as it shipped. -/
def imageV (p : Row.Pic) (w h : Nat) : m (Option Bitmap × Bool) := do
  let pre ← decodedV (p.hash.push 0, w, h) (startPre p w h)
  let full ← if !p.complete then pure none else decoded (p.hash.push 1, w, h) fun _ => startFull p w h
  return p.shown pre full

end

/-- **The budget catches the old `decoded`**: a picture with a preview
costs a spawn in every world, steady or not. -/
theorem imageV_over_budget (p : Row.Pic) (wd ht : Nat) (w : World) (hp : p.preview.isEmpty = false) :
    1 ≤ (costIn (imageV p wd ht) w).spawns := by
  simp only [costIn, imageV, decodedV, startPre, hp, run_bind, Meter.spawns_add]
  simp only [Bool.false_eq_true, ite_false, run_bind, run_spawn, run_pure, Meter.spawns_add]
  omega

end Pics

end
