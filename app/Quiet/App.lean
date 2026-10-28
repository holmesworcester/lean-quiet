/-
The app: one conversation, bottom-anchored, with a header and a composer.

Each frame:
1. Takes the writer's notices: live answers go stale; outbox entries whose
   ops are now decided leave it (the store answers for them, same id).
2. Handles the twin's events and the control commands.
3. Reads the offset (the OS scrolls).
4. Reads again what is stale: the list's ids (one query, newest first,
   as many as the screen and the fetch distance need), and each mounted
   row's own answers (its message, author, pictures and reactions).
   Rows within the fetch distance of the frame are mounted: read and laid
   out, so their heights are known before they are drawn.
5. Keeps what is on screen still while heights change: the row at the
   viewport's bottom edge stays where it was (unless the view is pinned
   to the newest message, which then stays pinned).
6. Paints rows whose answers or decoded pictures changed, on worker
   tasks; the frame shows each row's last finished paint.
7. Assembles the list frame from the rows' own pixel rows (no copying:
   the frame holds the same row objects), and hands it over with the
   header and the composer.

Everything the platform does goes through `Io`, so tests drive the same
code without a window (QTests).
-/
import Quiet.Data
import Quiet.Chaos
import Quiet.Row
import Std.Data.HashMap

namespace App
open Engine Community Data Paint Font Row

/-- The platform, as the app uses it. -/
structure Io where
  scroll : UInt32 → UInt32 → IO UInt32
  scrollBy : Float → IO Unit
  scrollTo : Float → IO Unit
  frame : Array ByteArray → UInt32 → UInt32 → Array ByteArray → Array ByteArray → IO (Array UInt32)
  text : IO (String × Array UInt32)
  ime : Bool → IO Unit
  textClear : IO Unit
  ctlPoll : IO (Array String)
  ctlReply : String → IO Unit
  nowUs : IO UInt64

/-- How far beyond each end of the viewport the list frame is drawn. -/
def over : Nat := 1024
/-- A row's height before it is measured. -/
def est : Nat := 150
def bottomPad : Nat := 16

structure RowSt where
  data : RowData
  lay : Layout
  deps : Array Q
  /-- What the current paint was made from: data version and which
  pictures were ready. -/
  painted : Nat × List Bool
  task : Option (Task Bitmap)
  shown : Option Bitmap
  ver : Nat

abbrev ImgKey := ByteArray × Nat × Nat

structure St where
  io : Io
  W : Nat
  Hs : Nat
  insetTop : Nat
  insetBot : Nat
  font : Font
  bgRow : ByteArray
  rd : Db
  wr : Writer
  me : Chaos.Me
  live : Live := {}
  out : Array Pending := #[]
  limit : Nat := 64
  ids : Array Pos := #[]
  total : Nat := 0
  people : Nat := 0
  heights : Std.HashMap Id Nat := {}
  rows : Std.HashMap Id RowSt := {}
  imgs : Std.HashMap ImgKey (Task Bitmap) := {}
  selected : Option Id := none
  b : Nat := 0
  imeH : Nat := 0
  text : String := ""
  sel : Array UInt32 := #[0, 0, 0, 0]
  topBmp : Bitmap := default
  botBmp : Bitmap := default
  chromeKey : String := ""
  srcs : Option (Task (Array Image.Src)) := none
  ctl : Array String := #[]
  frames : Nat := 0
  times : Array Nat := #[]
  paints : Nat := 0
  seed : Nat := 1

instance : Inhabited Io := ⟨⟨fun _ _ => pure 0, fun _ => pure (), fun _ => pure (), fun _ _ _ _ _ => pure #[],
  pure ("", #[]), fun _ => pure (), pure (), pure #[], fun _ => pure (), pure 0⟩⟩

abbrev M := StateT St IO

def c (s : St) : Id := s.me.c

/-! ## Reading through live answers -/

def read (q : Q) : M Ans := do
  let s ← get
  if let some e := s.live.entries[q]? then
    if !e.stale then return e.ans
  let a ← q.run s.rd s.out
  modify fun s => { s with live := s.live.store q a }
  return a

def fresh (q : Q) : M Bool := do return (← get).live.fresh q

def listAll (s : St) (limit : Nat) : ListQ := { key := key 4 s.me.c s.me.c, desc := true, limit }

def getFact (x : Id) : M (Option Fact × Bool) := do
  match ← read (.get x) with
  | .fact f p => return (f, p)
  | _ => return (none, false)

def bytesStr (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

/-- A row's answers: the message, its author's current profile, its
pictures' blobs and its reactions; with the queries read. -/
def readRow (m : Id) : M (Option (RowData × Array Q)) := do
  let s ← get
  let c := s.me.c
  let mut deps : Array Q := #[.get m]
  let (f, pending) ← getFact m
  let some (.message _ u _ _ text tm atts) := f | return none
  -- author: the newest profile
  let pq : Q := .list { key := key 7 c u, desc := true, limit := 1 }
  deps := deps.push pq
  let mut name := "…"
  let mut avatar : Option ByteArray := none
  if let .list a _ ← read pq then
    if let some (_, pid) := a.rows.head? then
      deps := deps.push (.get pid)
      if let (some (.profile _ _ n _ av), _) ← getFact pid then
        name := bytesStr n
        if let some bid := av.head? then
          deps := deps.push (.get bid)
          if let (some (.blob _ hh _ _), _) ← getFact bid then avatar := some hh
  -- pictures
  let mut pics := #[]
  for a in atts do
    deps := deps.push (.get a)
    if let (some (.blob _ hh w h), _) ← getFact a then pics := pics.push (Pic.mk hh w h)
  -- reactions, tallied by emoji: distinct people, and whether I am one
  let rq : Q := .facts { key := key 8 c m, desc := false, limit := 500 }
  deps := deps.push rq
  let mut tallies : Array (String × List Id) := #[]
  if let .facts _ fs ← read rq then
    for f in fs do
      if let .react _ who _ e _ := f then
        let e := bytesStr e
        match tallies.findIdx? (·.1 == e) with
        | some i => tallies := tallies.modify i fun (e, us) => (e, if us.contains who then us else us ++ [who])
        | none => tallies := tallies.push (e, [who])
  let me := s.me.adm
  let ts := tallies.toList.map fun (e, us) => Tally.mk e us.length (us.contains me)
  return some (RowData.mk name avatar (bytesStr text) tm pics.toList ts pending (s.selected == some m), deps)

/-! ## Writing -/

/-- Notices made by this node itself: a change to the outbox. -/
def noticeLocal (keys : List ByteArray) : M Unit :=
  modify fun s => { s with live := s.live.notice keys.toArray }

/-- Compose, judge against decided facts, put in the outbox, queue. -/
def write (o : Op) : M Bool := do
  let s ← get
  let mut sts := []
  for r in o.reqs do
    sts := sts ++ [← (getSql (F := Fact) r).run s.rd]
  match judge fam o sts with
  | some (.valid f) =>
    let p : Pending := ⟨o, f, keys f⟩
    modify fun s => { s with out := s.out.push p }
    noticeLocal (opKey o.id :: p.keys)
    s.wr.submit ⟨[o], [], true⟩
    return true
  | _ =>
    IO.eprintln s!"write refused: its requirements are not all decided and valid"
    return false

def newestTime (s : St) : Nat :=
  match s.ids[0]? with
  | some (sk, _) => sk.foldl (fun n b => n * 256 + b.toNat) 0
  | none => Chaos.epoch

def sendText (text : String) : M Bool := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return false
  let o := post s.me.c s.me.adm s.me.dev "k".toUTF8 t.toUTF8 (newestTime s + 1)
  write o

def reactTo (m : Id) (e : String) : M Bool := do
  let s ← get
  write (react s.me.c s.me.adm m s.me.dev e.toUTF8 (newestTime s + 1))

/-! ## Geometry -/

def topH (s : St) : Nat := s.insetTop + 112

def composerLines (s : St) : Array Text.Line :=
  let tw := s.W - 24 - 96 - 24 - 48
  if s.text.isEmpty then #[#[]] else Text.layout s.font tw s.text

def botH (s : St) : Nat := 32 + 32 + (min 5 (composerLines s).size) * 40

def viewH (s : St) : Nat := s.Hs - topH s - botH s - s.insetBot

def heightOf (s : St) (x : Id) : Nat := s.heights.getD x est

/-- The loaded rows' bottoms (bottom-anchored), newest first, and the
content's height. -/
def bottoms (s : St) : Array Nat × Nat := Id.run do
  let mut out := Array.mkEmpty s.ids.size
  let mut y := bottomPad
  for (_, x) in s.ids do
    out := out.push y
    y := y + heightOf s x
  let unloaded := s.total - min s.total s.ids.size
  return (out, y + unloaded * est + 16)

/-! ## Mounting, measuring, painting -/

def decodeTask (bytes : ByteArray) (w h : Nat) (sq : Bool) : Task Bitmap :=
  Task.spawn fun _ =>
    match Image.decode bytes with
    | some src => if sq then Image.square src w Row.bg else Image.scaled src w h Row.bg
    | none => Bitmap.blank w h (solid Row.placeholder w)

/-- The decoded picture at its drawn size, if ready (a decode is started
when the bytes are there). -/
def image (hash : ByteArray) (w h : Nat) (sq : Bool) : M (Option Bitmap) := do
  let s ← get
  let k := (hash, w, h)
  match s.imgs[k]? with
  | some t => if ← IO.hasFinished t then return some t.get else return none
  | none =>
    match ← Data.Db.blob s.rd hash with
    | none => return none
    | some bytes =>
      modify fun s => { s with imgs := s.imgs.insert k (decodeTask bytes w h sq) }
      return none

/-- Mount (read, lay out) row x if any of its answers are stale. -/
def mount (x : Id) : M Unit := do
  let s ← get
  let need ← match s.rows[x]? with
    | none => pure true
    | some r => do
      let mut stale := r.data.selected != (s.selected == some x)
      for q in r.deps do
        if !(← fresh q) then stale := true
      pure stale
  if !need then return
  match ← readRow x with
  | none => pure ()
  | some (d, deps) =>
    let s ← get
    match s.rows[x]? with
    | some r =>
      if r.data == d then
        modify fun s => { s with rows := s.rows.insert x { r with deps } }
      else
        let lay := Row.layout s.font s.W d
        modify fun s => { s with rows := s.rows.insert x { r with data := d, lay, deps, ver := r.ver + 1 },
                                  heights := s.heights.insert x lay.h }
    | none =>
      let lay := Row.layout s.font s.W d
      modify fun s => { s with rows := s.rows.insert x ⟨d, lay, deps, (0, []), none, none, 1⟩,
                                heights := s.heights.insert x lay.h }

/-- Start a paint of row x if what it shows changed; collect a finished one. -/
def paintRow (x : Id) : M Unit := do
  let s ← get
  let some r := s.rows[x]? | return
  let av ← match r.data.avatar with
    | some hh => image hh Row.avatar Row.avatar true
    | none => pure none
  let mut imgs := #[]
  for i in [0:r.lay.pics.size] do
    let bx := r.lay.pics[i]!
    match r.data.pics[i]? with
    | some p => imgs := imgs.push (← image p.hash bx.w bx.h false)
    | none => imgs := imgs.push none
  let ready := av.isSome :: imgs.toList.map Option.isSome
  let s ← get
  let some r := s.rows[x]? | return
  -- a finished paint is shown
  let mut r := r
  if let some t := r.task then
    if ← IO.hasFinished t then r := { r with shown := some t.get, task := none }
  if r.painted != (r.ver, ready) && r.task.isNone then
    let (f, W, bgRow, d, l) := (s.font, s.W, s.bgRow, r.data, r.lay)
    let t := Task.spawn fun _ => Row.paint f W bgRow d l av imgs
    r := { r with task := some t, painted := (r.ver, ready) }
    modify fun s => { s with paints := s.paints + 1 }
  modify fun s => { s with rows := s.rows.insert x r }

/-! ## The frame -/

/-- The list frame: row r shows content at b + viewH + over - 1 - r. -/
def listFrame (s : St) (b : Nat) (bots : Array Nat) : Array ByteArray := Id.run do
  let vh := viewH s
  let hgt := vh + 2 * over
  let mut fr := Array.replicate hgt s.bgRow
  let top := b + vh + over     -- content above the frame's first row
  let low := if b ≥ over then b - over else 0
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    let x := s.ids[i]!.2
    let h := heightOf s x
    if bot ≥ top then break
    if bot + h ≤ low then continue
    match s.rows[x]? >>= (·.shown) with
    | none => pure ()
    | some bmp =>
      -- the row's pixel line li (top down) is content bot + h - 1 - li
      for li in [0:bmp.h] do
        let p := bot + h - 1 - li
        if p < top && p + over ≥ b then
          let r := top - 1 - p
          if r < hgt then fr := fr.set! r bmp.rows[li]!
  return fr

def header (s : St) : Bitmap := Id.run do
  let h := topH s
  let hb := 0x16181B
  let mut b := Bitmap.blank s.W h (solid hb s.W)
  b := b.line s.font (Text.oneLine s.font (s.W - 64) "# general") 32 (s.insetTop + 16) nameInk true
  let sub := s!"{s.total} messages · {s.people} people"
  b := b.line s.font (Text.oneLine s.font (s.W - 64) sub) 32 (s.insetTop + 60) dim
  b := b.fill 0 (h - 2) s.W h pill
  return b

def cursorAt (s : St) (i : Nat) : Nat × Nat :=
  let tw := s.W - 24 - 96 - 24 - 48
  let pre := String.ofList (s.text.toList.take i)
  let ls := if pre.isEmpty then #[#[]] else Text.layout s.font tw pre
  let last := ls.back?.getD #[]
  -- a prefix ending in a newline puts the cursor on the next line
  if pre.endsWith "\n" then (ls.size, 0) else (ls.size - 1, Paint.Line.width s.font last)

def composer (s : St) : Bitmap := Id.run do
  let h := botH s
  let mut b := Bitmap.blank s.W h s.bgRow
  b := b.fill 0 0 s.W 2 pill
  let fx1 := s.W - 24 - 96
  b := b.round 24 16 fx1 (h - 16) 28 0x3A3D41
  b := b.round 26 18 (fx1 - 2) (h - 18) 26 selBg
  let ls := composerLines s
  if s.text.isEmpty then
    b := b.line s.font (Text.oneLine s.font (fx1 - 72) "Message #general") 48 32 dim
  else
    for i in [0:min 5 ls.size] do
      b := b.line s.font ls[i]! 48 (32 + 40 * i) ink
    -- the composing span, underlined
    let cs := s.sel[2]!.toNat
    let ce := s.sel[3]!.toNat
    if ce > cs then
      let (l0, x0) := cursorAt s cs
      let (l1, x1) := cursorAt s ce
      if l0 == l1 then b := b.fill (48 + x0) (32 + 40 * l0 + 34) (48 + x1) (32 + 40 * l0 + 37) ink
  let (cl, cx) := cursorAt s s.sel[0]!.toNat
  b := b.fill (48 + cx) (32 + 40 * (min 4 cl)) (48 + cx + 3) (32 + 40 * (min 4 cl) + 32) accent
  -- send
  let sx := s.W - 24 - 88
  let sy := (h - 88) / 2
  b := b.round sx sy (sx + 88) (sy + 88) 44 (if s.text.trimAscii.isEmpty then pill else accent)
  b := b.glyph s.font 0x27A4 (sx + 28) (sy + 28) nameInk false
  return b

/-! ## Events and commands -/

/-- The row at content position p, and p's row within it (top down). -/
def rowAt (s : St) (p : Nat) : Option (Id × Nat) := Id.run do
  let (bots, _) := bottoms s
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    let x := s.ids[i]!.2
    let h := heightOf s x
    if bot ≤ p && p < bot + h then return some (x, bot + h - 1 - p)
  return none

def onTap (r : Region) (x y : Nat) (long : Bool) : M Unit := do
  let s ← get
  match r with
  | .composer =>
    if x ≥ s.W - 24 - 96 then
      if ← sendText s.text then
        modify fun s => { s with text := "", sel := #[0, 0, 0, 0] }
        s.io.textClear
    else s.io.ime true
  | .header => s.io.scrollTo 0
  | .list =>
    if s.imeH > 0 && !long then s.io.ime false; return
    match rowAt s y with
    | none => modify fun s => { s with selected := none }
    | some (m, ry) =>
      match s.rows[m]? with
      | none => pure ()
      | some row =>
        match Row.hit row.lay x ry with
        | .pill e =>
          if !(row.data.tallies.any fun t => t.emoji == e && t.mine) then
            let _ ← reactTo m e
        | .palette e =>
          let _ ← reactTo m e
          modify fun s => { s with selected := none }
        | .row => modify fun s => { s with selected := if s.selected == some m then none else some m }

def onEvent : Event → M Bool
  | .close => return false
  | .tap r x y => do onTap r x.toNat y.toNat false; return true
  | .long r x y => do onTap r x.toNat y.toNat true; return true
  | .text => do
    let (t, sel) ← (← get).io.text
    modify fun s => { s with text := t, sel := if sel.size == 4 then sel else #[0, 0, 0, 0] }
    return true
  | .send => do
    let s ← get
    if ← sendText s.text then
      modify fun s => { s with text := "", sel := #[0, 0, 0, 0] }
      s.io.textClear
    return true
  | .ime h => do modify fun s => { s with imeH := h.toNat }; return true
  | .scrolling _ => return true

def loadSrcs : IO (Array Image.Src) := do
  let mut out := #[]
  for i in [0:6] do
    if let .ok bytes ← (IO.FS.readBinFile s!"assets/{i}.qoi").toBaseIO then
      if let some src := Image.decode bytes then out := out.push src
  return out

def stats (s : St) : String :=
  let ts := s.times
  let n := max ts.size 1
  let avg := ts.foldl (· + ·) 0 / n
  let sorted := ts.qsort (· < ·)
  let p95 := sorted[sorted.size * 95 / 100]?.getD 0
  let mx := sorted.back?.getD 0
  s!"frames {s.frames} lean_us avg {avg} p95 {p95} max {mx} paints {s.paints} reads {s.live.reads} rows {s.rows.size} imgs {s.imgs.size}"

/-- One control command; false if it must wait (and the rest behind it). -/
def command (line : String) : M Bool := do
  let s ← get
  let ws := line.splitOn " "
  let rest := String.intercalate " " (ws.drop 1)
  match ws.headD "" with
  | "ping" => s.io.ctlReply "pong"
  | "state" =>
    s.io.ctlReply s!"b {s.b} total {s.total} loaded {s.ids.size} people {s.people} mounted {s.rows.size} ime {s.imeH} text {repr s.text} outbox {s.out.size} busy {← s.wr.busy.get} viewH {viewH s}"
  | "stats" => s.io.ctlReply (stats s)
  | "chaos" =>
    let n := (ws[1]? >>= String.toNat?).getD 500
    let srcs ← match s.srcs with
      | some t => pure t
      | none => IO.asTask loadSrcs >>= fun t => pure (t.map fun r => match r with | .ok a => a | .error _ => #[])
    modify fun s => { s with srcs := some srcs, seed := s.seed + 1 }
    let me := s.me
    let seed := s.seed
    let start := newestTime s + 1
    let wr := s.wr
    let t0 ← s.io.nowUs
    -- busy until every job is queued, so `wait` waits for the making too
    wr.busy.modify (· + 1)
    let _ ← IO.asTask (prio := .dedicated) do
      let jobs := Chaos.make me srcs.get seed n start
      for j in jobs do wr.submit j
      wr.busy.modify (· - 1)
      let t1 ← s.io.nowUs
      IO.eprintln s!"chaos: {jobs.size} jobs of {jobs.foldl (· + ·.ops.length) 0} ops made in {(t1 - t0) / 1000} ms"
    s.io.ctlReply s!"chaos {n} started"
  | "wait" =>
    if (← s.wr.busy.get) > 0 && !(← s.wr.paused.get) || !(← s.wr.jobs.get).isEmpty && !(← s.wr.paused.get) then
      return false
    s.io.ctlReply s!"idle total {s.total}"
  | "send" =>
    let ok ← sendText rest
    s.io.ctlReply (if ok then "sent" else "refused")
  | "react" =>
    let i := (ws[1]? >>= String.toNat?).getD 0
    match s.ids[i]? with
    | some (_, m) =>
      let ok ← reactTo m (ws[2]?.getD "👍")
      s.io.ctlReply (if ok then "reacted" else "refused")
    | none => s.io.ctlReply "no such message"
  | "pause" => s.wr.paused.set true; s.io.ctlReply "writer paused"
  | "resume" => s.wr.paused.set false; s.io.ctlReply "writer resumed"
  | "bottom" => s.io.scrollTo 0; s.io.ctlReply "ok"
  | "scroll" =>
    s.io.scrollTo ((ws[1]? >>= String.toNat?).getD 0).toFloat; s.io.ctlReply "ok"
  | "top" =>
    let (_, ch) := bottoms s
    s.io.scrollTo ch.toFloat; s.io.ctlReply "ok"
  | "visible" =>
    let (bots, _) := bottoms s
    let vh := viewH s
    let mut out := #[]
    for i in [0:s.ids.size] do
      let x := s.ids[i]!.2
      let h := heightOf s x
      if bots[i]! + h > s.b && bots[i]! < s.b + vh then
        if let some r := s.rows[x]? then
          out := out.push s!"{r.data.name}: {String.ofList (r.data.text.toList.take 40)}{if r.data.pending then " (pending)" else ""}"
    s.io.ctlReply (String.intercalate " | " out.toList)
  | _ => s.io.ctlReply s!"unknown: {line}"
  return true

/-! ## The loop -/

/-- One frame; the twin's events for the next one, or none when the
window closes. -/
def step (evs : List Event) : M (Option (List Event)) := do
  let t0 ← (← get).io.nowUs
  -- 1. notices
  let s ← get
  let ns ← s.wr.takeNotices
  if !ns.isEmpty then
    let decided := s.out.filter fun p => ns.contains (opKey p.op.id)
    modify fun s => { s with
      live := s.live.notice ns
      out := s.out.filter fun p => !ns.contains (opKey p.op.id) }
    if !decided.isEmpty then noticeLocal (decided.toList.flatMap fun p => opKey p.op.id :: p.keys)
  -- 2. events and commands
  for e in evs do
    if !(← onEvent e) then return none
  let cmds ← (← get).io.ctlPoll
  modify fun s => { s with ctl := s.ctl ++ cmds }
  let mut queue := (← get).ctl
  while !queue.isEmpty do
    if ← command queue[0]! then queue := queue.extract 1 queue.size else break
  modify fun s => { s with ctl := queue }
  -- 3. the list's ids and counts
  let s ← get
  if let .list a _ ← read (.list (listAll s s.limit)) then
    modify fun s => { s with ids := a.rows.toArray, total := a.total }
  let s ← get
  if let .list a _ ← read (.list { key := key 10 s.me.c s.me.c, limit := 0 }) then
    modify fun s => { s with people := a.total }
  -- 4. the offset, and the rows the frame and the fetch distance need
  let s ← get
  let (bots0, ch0) := bottoms s
  let b ← s.io.scroll ch0.toUInt32 (viewH s).toUInt32
  let b := b.toNat
  -- the anchor: the row at the viewport's bottom edge, and how far into it
  let anchor := (rowAt s b).map fun (x, _) => (x, b - (bots0[s.ids.findIdx? (·.2 == x) |>.getD 0]?.getD 0))
  let vh := viewH s
  let fetch := vh
  let lo := if b ≥ over + fetch then b - over - fetch else 0
  let hi := b + vh + over + fetch
  for i in [0:s.ids.size] do
    let bot := bots0[i]!
    if bot > hi then break
    if bot + heightOf s s.ids[i]!.2 ≥ lo then mount s.ids[i]!.2
  -- more ids, if the loaded ones end below what the fetch distance needs
  let s ← get
  let (bots, _) := bottoms s
  let loadedTop := match s.ids.back? with
    | some (_, x) => bots.back!.add (heightOf s x)
    | none => bottomPad
  if loadedTop < hi + 2 * est && s.ids.size < s.total && s.ids.size ≥ s.limit then
    -- enough more ids, at the estimate, to reach past the fetch distance
    let more := (hi + 2 * est - loadedTop) / est + 64
    modify fun s => { s with limit := s.limit + more }
  -- 5. keep the anchor still (unless pinned to the newest)
  let mut b := b
  if b > 4 then
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        let b' := bots[i]! + off
        if b' != b then
          s.io.scrollBy (b'.toFloat - b.toFloat)
          b := b'
  -- 6. paint what the frame shows
  let flo := if b ≥ over then b - over else 0
  let fhi := b + vh + over
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    if bot > fhi then break
    if bot + heightOf s s.ids[i]!.2 ≥ flo then paintRow s.ids[i]!.2
  -- forget rows far away (their heights stay)
  let s ← get
  if s.frames % 30 == 0 then
    let keepLo := if b ≥ 4 * vh then b - 4 * vh else 0
    let keepHi := b + 5 * vh
    let mut keep : Std.HashMap Id Unit := {}
    for i in [0:s.ids.size] do
      let bot := bots[i]!
      if bot ≤ keepHi && bot + heightOf s s.ids[i]!.2 ≥ keepLo then keep := keep.insert s.ids[i]!.2 ()
    let rows := s.rows.filter fun x _ => keep.contains x
    let deps := rows.fold (fun acc _ r => r.deps.foldl (fun a q => a.insert q ()) acc) ({} : Std.HashMap Q Unit)
    modify fun s => { s with rows, live := s.live.keep fun q => match q with
      | .list _ => true
      | q => deps.contains q }
  -- 7. chrome and the frame
  let s ← get
  let key := s!"{s.W}|{s.total}|{s.people}|{s.text}|{s.sel}"
  if key != s.chromeKey then
    modify fun s => { s with topBmp := header s, botBmp := composer s, chromeKey := key }
  let s ← get
  let fr := listFrame s b bots
  let t1 ← s.io.nowUs
  let times := (if s.times.size ≥ 600 then s.times.extract 300 s.times.size else s.times).push (t1 - t0).toNat
  modify fun s => { s with b := b, frames := s.frames + 1, times := times }
  let evs ← s.io.frame fr b.toUInt32 over.toUInt32 s.topBmp.rows s.botBmp.rows
  return some (Event.decode evs)

partial def loop (evs : List Event) : M Unit := do
  match ← step evs with
  | none => pure ()
  | some evs => loop evs

/-- The app's state at start: the window's size, the font, both
connections, this node's identity (the community founded on first run). -/
def start (io : Io) (screen : Array UInt32) (dbPath : String) : IO St := do
  let W := (screen[0]?.getD 1080).toNat
  let Hs := (screen[1]?.getD 2400).toNat
  let font ← Font.load
  let rd ← openDb dbPath
  let wr ← Writer.start dbPath
  let (me, first) ← Chaos.Me.load rd
  if (← (getSql (F := Fact) me.c).run rd).isNone then
    wr.submit ⟨first, [], true⟩
  return { io := io, W := W, Hs := Hs, insetTop := (screen[2]?.getD 0).toNat,
           insetBot := (screen[3]?.getD 0).toNat, font := font, bgRow := solid Row.bg W, rd := rd,
           wr := wr, me := me }

end App
