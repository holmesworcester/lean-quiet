import engine.core.Query
import engine.renderer.Platform
import engine.renderer.Row
import engine.renderer.Overlay
import engine.renderer.Label
import app.Commands
import Std.Data.HashMap.Lemmas
import engine.renderer.Image
import engine.core.Core
import app.community.Screen
import app.community.member.join.accept.View
import engine.renderer.Board
import engine.renderer.Demand
import Std.Sync.Mutex
import app.community.member.invite.request.Commands
import app.community.member.join.joining.Commands
import app.connection.Commands
import app.connection.Family
import app.connection.eph.Commands
import app.connection.established.Commands
import app.connection.given.Commands
import app.connection.opened.Commands
import app.connection.recv.Commands
import app.community.channel.message.attachment.Screen
import engine.renderer.Safe
import engine.renderer.Sheet
import engine.renderer.Geometry
import engine.renderer.Nav
import engine.renderer.Cover
import engine.renderer.Session
import engine.renderer.HoldCache
import engine.renderer.Toast
import engine.renderer.ThemeStore
import app.community.channel.message.draft.View
import app.community.member.invite.View
import engine.renderer.Camera
import app.community.member.remove.View
import Std.Data.HashMap
import engine.wire.Frame
import app.community.member.invite.request.approve.admit.Commands
import app.community.member.invite.request.Op
import app.community.channel.message.reaction.Op
import app.community.Family
import app.community.key.Op
import app.community.key.wrap.Op
import app.community.channel.message.Op
import app.community.member.invite.request.approve.admit.Op
import app.community.channel.message.reaction.View
import app.community.member.invite.Commands
import app.community.profile.Commands
import app.community.channel.message.reaction.Commands
import app.community.member.remove.Op
import app.community.member.join.joining.abandon.Commands
import app.community.member.admin.Op
import app.community.member.join.joining.abandon.Op
import app.community.Commands
import app.community.channel.message.Commands
import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.receipt.Op
import app.community.profile.Op
import app.community.profile.View
import app.community.device.secret.Op
import app.community.name.Op
import app.community.member.join.accept.Op
import app.community.channel.message.attachment.View
import app.community.member.invite.request.approve.Op
import app.community.channel.message.attachment.chunk.Commands
import app.community.channel.message.attachment.Op
import app.community.device.endpoint.Op
import app.community.member.invite.Op
import app.community.member.join.joining.Op
import app.community.member.invite.request.approve.Commands
import app.community.Op
import engine.renderer.Page
import app.community.member.join.Screen
import app.community.member.join.joining.Screen
import app.community.member.invite.Screen
import app.community.member.invite.request.Screen
import app.community.profile.Screen
import app.community.member.remove.Screen
import engine.renderer.Photo
import engine.renderer.SafeFrame
import engine.renderer.Presentation
import engine.wire.WriteAdmission

section

/-
The app's pages besides a conversation, in the layout and spirit of
libquiet's phone screens (its Stage, Rows and sheets): Get started,
Create a community, Join community, Join with invite link, Paste a link,
Join with QR code, Agree & join, Waiting to join, Join requests, Add
members, and the community switcher.

A page is a pure picture of the screen's content (drawn into the list
layer, which does not scroll on a page) plus its bar (drawn into the
header layer), and the boxes a tap can land on, each with what it does.
The painter and the taps read the same boxes.
-/

namespace Pages
open Paint Text Font Row



/-- What a tap on a page does. -/
inductive Act where
  | back
  | you | appearance | theme (setting : Theme.Setting)
  | communitySettings | channelSettings | stub (title : String)
  | joinCommunity
  | createCommunity
  | inviteLink
  | qrCode
  | pasteLink
  | field
  | continue_
  | agree
  | addMembers
  | share
  | copy
  | approve (i : Nat)
  | hide (i : Nat)
  | switchTo (i : Nat)
  | addCommunity
  | requests
  | openChannel (i : Nat)
  | stopWaiting
  /-- A person on home (people list row i): their profile. -/
  | person (i : Nat)
  | removeStart
  | removeYes
  | removeCancel
  | copyLabel | labelNext | labelPrev
  | none
  deriving BEq, Inhabited, Repr

instance : Inert Act := ⟨.none⟩

/-- A page of the app: its taps are the app's actions. -/
abbrev Page := PageOf Act

/-- The source label behind each compact navigation row. -/
def fullLabel (a : Act) (communities people : Array String) : Option String :=
  match a with
  | .switchTo i => communities[i]?
  | .person i => people[i]?
  | .openChannel _ => some "general"
  | .requests => some "Waiting to join"
  | .joinCommunity => some "Join a community"
  | .createCommunity => some "Create a community"
  | .inviteLink => some "Join with invite link"
  | .qrCode => some "Join with QR code"
  | _ => none

/-- Read a compact label in full, page by page, or copy it verbatim. -/
def label (f : Font) (dm : Dim) (W h : Nat) (text : String) (page : Nat) : Page :=
  let b := Label.paint f dm W h text page
  let (b, copy, _) := button f dm b "Copy full text" (h - dm.px 144) false .copyLabel
  let (b, next, _) := button f dm b "Next" (h - dm.px 96) false .labelNext
  let (b, prev, _) := button f dm b "Previous" (h - dm.px 48) false .labelPrev
  ⟨b, #[copy, next, prev]⟩
end Pages

end

section

/-
Lifecycle policy used by the app, not a second app model.

Durable: local checkpoint ops in `app_ops` in the same SQLite database as
community ops. They hold the acceptance, page/back stack, per-acceptance
composer drafts (including photo bytes), field, invite/name, removal flow,
and scroll anchor (message id and distance from the viewport bottom to
the message top). Each changed checkpoint is committed before the event turn returns. Joining,
admissions and removals themselves remain the engine's existing ops.

Ephemeral: mounted queries, generation leases, keyboard composition and
height, camera/decoder frames, paint tasks, sheets, toasts and velocity.
Unmount revokes leases, drops subscriptions and retires unfinished tasks. A new mount
gets a new generation, so even a return to the same page rejects old work.

An anchor keeps its distance from the viewport's bottom, not an absolute
screen coordinate (that coordinate may cease to exist after rotation).
At offset zero the newest message stays pinned. If an anchor is no longer
readable, the app falls back to the newest message.

`unmounted_quiet` and `old_quiet` prove the running effect gate issues no
read, paint or write for a revoked lease. `live_exact` proves the reader's
pruning (`Live.keep` by the reads its current wants hold) keeps exactly
those reads in the live cache. `resize_anchor` proves
the offset correction. `restore_checkpoint` proves the journal codec's
round trip; SQLite's atomic commit remains in the tested native seam.
-/

namespace Lifecycle
open Engine Data

attribute [local instance] LiveLaws.byteArray_lawful LiveLaws.listQ_lawful LiveLaws.q_lawful

structure Lease where
  generation : Nat
  deriving BEq, Repr, Inhabited

structure Mount where
  generation : Nat := 0
  mounted : Bool := true
  deriving Inhabited

def Mount.lease (m : Mount) : Lease := ⟨m.generation⟩
def Mount.allows (m : Mount) (l : Lease) : Bool :=
  m.mounted && decide (l.generation = m.generation)
def Mount.unmount (m : Mount) : Mount := ⟨m.generation + 1, false⟩
def Mount.mount (m : Mount) : Mount := { m with mounted := true }

/-- All page effects pass this gate, including queued event callbacks. -/
def owned {m : Type → Type} [Monad m] {α : Type} (s : Mount) (l : Lease) (action : m α) : m (Option α) :=
  if s.allows l then some <$> action else pure none

theorem unmounted_quiet {m : Type → Type} [Monad m] {α : Type}
    (s : Mount) (l : Lease) (action : m α) : owned s.unmount l action = pure none := by
  simp [owned, Mount.allows, Mount.unmount]

theorem old_quiet {m : Type → Type} [Monad m] {α : Type}
    (s : Mount) (action : m α) : owned s.unmount.mount s.lease action = pure none := by
  simp [owned, Mount.allows, Mount.unmount, Mount.mount, Mount.lease]

/-- **The live cache keeps exactly the reads the wants hold.** When the
wants move (an unmount drops its wants), the reader prunes its live cache
with `Live.keep`, by the reads its current wants hold. An entry it keeps
is held; and every held read that has an answer stays. -/
theorem live_exact (l : Live) (want : Q → Bool)
    (complete : ∀ q, want q = true → l.entries[q]?.isSome = true) (q : Q) :
    (l.keep want).entries[q]?.isSome = true ↔ want q = true := by
  simp only [Live.keep, Std.HashMap.getElem?_filter']
  cases h : l.entries[q]? with
  | none =>
    simp only [Option.filter_none, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hq
    have := complete q hq
    simp [h] at this
  | some e => simp

/-- Keep the message's top edge the same distance above the viewport
bottom. At the content boundary the platform clamps the offset to zero. -/
def offset (top above : Nat) : Nat := top - above

theorem resize_anchor (top above : Nat) (fits : above ≤ top) :
    (top : Int) - offset top above = above := by
  unfold offset; omega

/-- The conversation window's next anchor (`Reader.Want.window`'s): the
newest (none) only when pinned there with nothing newer; else the row at
the viewport, or the window's nearest end, when the window is about no
row yet or its edge with messages beyond comes within the fetch
distance; else the same. -/
def follow (cur : Option α) (newer : Nat) (pinned near : Bool) (atView nearEnd : Option α) : Option α :=
  if newer == 0 && pinned then none
  else if near || cur.isNone then
    match atView with
    | some p => some p
    | none => nearEnd
  else cur

/-- Away from the newest the window is always about a row, never "the
newest" (given a row to take): the window about a row holds it and the
rows older (`Reader.eval`'s `before`), so no burst of arrivals, however
large, pushes the row being read out of it. -/
theorem follow_away (cur : Option α) (newer : Nat) (near : Bool) (atView nearEnd : Option α)
    (h : nearEnd.isSome) : (follow cur newer false near atView nearEnd).isSome := by
  unfold follow
  cases cur <;> cases near <;> cases atView <;> simp_all

/-- The serialized checkpoint: version, page, acceptance, anchor id and
top-edge distance; the rest is an extensible list of canonical byte fields. -/
abbrev Checkpoint := Nat × Nat × Id × Id × Nat × List ByteArray

def restore (bytes : ByteArray) : Option Checkpoint := Codec.decode bytes

theorem restore_checkpoint (s : Checkpoint) : restore (Codec.encode s) = some s :=
  Codec.decode_encode s

/-- The gate admits real mounted work; the denial laws are not vacuous. -/
theorem mounted_runs (n : Nat) :
    owned (m := Id) ({ generation := n } : Mount) ⟨n⟩ (pure 7) = some 7 := by
  simp [owned, Mount.allows]
  rfl

/-- A local journal of app ops, isolated from the sync family's index.
The sequence is the local ordering; op bytes are content-addressed. -/
def init (db : Db) : IO Unit :=
  db.exec "CREATE TABLE IF NOT EXISTS app_ops (seq INTEGER PRIMARY KEY AUTOINCREMENT, id BLOB NOT NULL, bytes BLOB NOT NULL);"

/-- Commit an encoded checkpoint as the table's only row: the older rows
go in the same transaction. A checkpoint holds invite links with their
bearer seeds, drafts with their photos, and queued writes (a found or
join's device seed, node secret and content key), so an older row keeps
what the app has since forgotten; `secure_delete` zeroes the freed cells,
and the WAL's copies go at its next truncation (every scrubbing purge's,
so each session end's; a courier's purge does not truncate). Kept
forever, the rows also grew by one every committed frame. Only the
writer's thread runs it (`Data.Writer.start`): the frame hands
checkpoints over (`Writer.save`). tests/engine/Purge.lean
(`checkpointRows`) checks it, with the old INSERT as its control. -/
def save (db : Db) (cp : ByteArray) : IO Unit := do
  let o := Op.make 239 [] cp
  db.exec "BEGIN IMMEDIATE"
  try
    let _ ← db.query "DELETE FROM app_ops" #[]
    let _ ← db.query "INSERT INTO app_ops(id,bytes) VALUES (?,?)" #[o.id, o.bytes]
    db.exec "COMMIT"
  catch e =>
    db.exec "ROLLBACK"
    throw e

def load (db : Db) : IO (Option Checkpoint) := do
  let rows ← db.query "SELECT bytes FROM app_ops ORDER BY seq DESC LIMIT 1" #[]
  return do
    let row ← rows[0]?
    let bytes ← row[0]?
    let o ← Op.decode bytes
    if o.kind != 239 then none else restore o.body

end Lifecycle

end

section

/-
Offering the app's writes to the node without waiting (App.submit and
App.flushNode run `offerList` with the node channel's `trySend`): each
write in order until one is refused; the refused one and those after it
stay, to be offered again first.

The laws are about `offerList` itself, read in a model of the channel
(`Chan`): a channel answers each offer yes or no, in any sequence (full,
emptying, refusing for good), and takes what it says yes to.

- `offer_split`: what the channel took, then what stays, is exactly what
  was offered, in order: no write lost, none twice, none overtaken;
- `offer_runs`: so over any run of sends and re-offers, what the channel
  has taken, then what waits, is every write submitted, in submission
  order.
-/
namespace NodeOffer

variable {α : Type}

/-- Offer each in order until one is refused; the rest, from it on. -/
def offerList {m : Type → Type} [Monad m] (offer : α → m Bool) : List α → m (List α)
  | [] => pure []
  | a :: t => do if ← offer a then offerList offer t else pure (a :: t)

/-- A channel, as the app sees it: its answers to come, and what it took. -/
abbrev Chan (α : Type) := StateM (List Bool × List α)

/-- One offer: the channel's next answer (no, once it has none left);
taken if yes. -/
def offerM (a : α) : Chan α Bool := do
  let (ans, took) ← get
  match ans with
  | b :: r => set (r, if b then took ++ [a] else took); pure b
  | [] => pure false

/-- **What the channel took, then what stays, is what was offered, in
order**, whatever the channel answers. -/
theorem offer_split : ∀ (q : List α) (ans : List Bool) (took : List α),
    let r := (offerList offerM q).run (ans, took)
    r.2.2 ++ r.1 = took ++ q
  | [], ans, took => by simp [offerList, StateT.run, pure, StateT.pure]
  | a :: t, ans, took => by
    cases ans with
    | nil =>
      simp [offerList, offerM, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure]
    | cons b r =>
      cases b with
      | true =>
        have ih := offer_split t r (took ++ [a])
        simp only [StateT.run] at ih ⊢
        simp only [offerList, offerM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
          MonadStateOf.set, StateT.set, pure, StateT.pure, ite_true] at ih ⊢
        simpa using ih
      | false =>
        simp [offerList, offerM, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
          MonadStateOf.set, StateT.set, pure, StateT.pure]

/-- A run of the app's offers: each a write submitted (appended behind
those waiting) or a frame's re-offer, against the channel's answers. -/
def run : List (Option α) → List α → Chan α (List α)
  | [], waiting => pure waiting
  | some w :: t, waiting => do run t (← offerList offerM (waiting ++ [w]))
  | none :: t, waiting => do run t (← offerList offerM waiting)

/-- The writes a run submits, in order. -/
def submitted : List (Option α) → List α
  | [] => []
  | some w :: t => w :: submitted t
  | none :: t => submitted t

/-- **Over any run, what the channel has taken, then what waits, is every
write submitted, in submission order**: none lost, none twice, none
overtaken, however the channel answers. -/
theorem offer_runs : ∀ (steps : List (Option α)) (waiting : List α) (ans : List Bool) (took : List α),
    let r := (run steps waiting).run (ans, took)
    r.2.2 ++ r.1 = took ++ waiting ++ submitted steps
  | [], waiting, ans, took => by simp [run, submitted, StateT.run, pure, StateT.pure]
  | some w :: t, waiting, ans, took => by
    have hs := offer_split (waiting ++ [w]) ans took
    simp only [StateT.run] at hs ⊢
    generalize hq : offerList offerM (waiting ++ [w]) (ans, took) = q at hs
    obtain ⟨rest, ans', took'⟩ := q
    have ih := offer_runs t rest ans' took'
    simp only [StateT.run] at ih
    simp only [run, submitted, bind, StateT.bind, hq]
    rw [ih]; simp only at hs; rw [hs]; simp
  | none :: t, waiting, ans, took => by
    have hs := offer_split waiting ans took
    simp only [StateT.run] at hs ⊢
    generalize hq : offerList offerM waiting (ans, took) = q at hs
    obtain ⟨rest, ans', took'⟩ := q
    have ih := offer_runs t rest ans' took'
    simp only [StateT.run] at ih
    simp only [run, submitted, bind, StateT.bind, hq]
    rw [ih]; simp only at hs; rw [hs]

end NodeOffer

end


section

/-
A chaos generator, as libquiet's: a community's worth of people and
talk, made of real ops (signed, judged, stored like any sync).

- **People:** names in many scripts, each admitted the way the engine
  admits anyone: an invitation from this node's founder, the newcomer's
  request, the founder's approval, and the admission tallying it. Each
  has a profile.
- **Messages:** text in many languages and scripts (Latin with accents,
  Greek, Cyrillic, Georgian, Armenian, Hebrew, Arabic, Thai, Japanese,
  Chinese, Korean), emoji, symbols, long unbreakable words, several
  paragraphs; some attach one to three pictures (crops of the photos at
  many aspects).
- **Reactions:** on a third of the messages, one to four emoji, each by
  one to five people.

Times rise through the conversation with uneven gaps; jobs go to the
writer in batches of 100 ops, a little shuffled, as a sync delivers
them, so the engine also waits and catches up.
-/

namespace Chaos
open Engine Community Data

/-- A small seeded generator (splitmix64). -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if n == 0 then 0 else x.toNat % n, g)

def Rng.pick {α} [Inhabited α] (g : Rng) (xs : Array α) : α × Rng :=
  let (i, g) := g.below xs.size
  (xs[i]!, g)

def names : Array String := #[
  "Ada", "Søren", "Zoë", "Mateusz", "Γιώργος", "Анна", "Олексій", "美咲", "王芳", "지훈",
  "Nguyễn Văn An", "Ólafur", "ნინო", "Արամ", "יעל", "ليلى", "สมชาย", "Ayşe", "José", "Chidi",
  "Aroha", "Priya", "Björk", "Nadia", "Kwame", "Ingrid", "Tomás", "Hana", "Émile", "Leilani",
  "Dmitri", "Sakura", "Mihai", "Fatima", "Lars", "Amara", "Kenji", "Siobhán", "Raúl", "Thandiwe",
  "Ørjan", "Yuki", "Ľubica", "Zainab", "Pita", "Eilidh", "Bogdan", "Mei"]

def texts : Array String := #[
  "Morning all! Coffee is on.",
  "Ça marche très bien, à demain !",
  "Grüße aus München — schönes Wochenende!",
  "¿Quedamos mañana a las nueve?",
  "Chúc mừng năm mới! Hẹn gặp lại nhé.",
  "Zażółć gęślą jaźń — the classic test sentence.",
  "Καλημέρα σε όλους! Τι κάνετε σήμερα;",
  "Привет! Как дела? У нас всё отлично.",
  "Дякую за допомогу, це було дуже корисно.",
  "გამარჯობა, როგორ ხარ? დღეს კარგი ამინდია.",
  "Բարև ձեզ, ինչպե՞ս եք։",
  "שלום לכולם, מה שלומכם היום?",
  "مرحبا بالجميع، كيف حالكم اليوم؟",
  "สวัสดีครับ ยินดีที่ได้รู้จัก",
  "おはようございます！今日はいい天気ですね。",
  "我们明天见，好吗？会议改到下午三点。",
  "안녕하세요! 오늘 회의는 3시에 시작합니다.",
  "Görüşürüz, iyi akşamlar!",
  "Þetta reddast. Sjáumst á morgun.",
  "🎉🎉 ship it 🚀",
  "👍",
  "😂😂😂",
  "Meeting moved to 15:00 — 会議は15時に変更 🙏",
  "∑ xᵢ² ≤ ∞ for all ε > 0, obviously ∎",
  "Did anyone try `git rebase --onto main feature~3 feature` on the release branch?",
  "https://example.org/a/very/long/path/that/needs/to/wrap/somewhere/because/it/has/no/spaces?query=1&more=2",
  "Supercalifragilisticexpialidociouslyunbreakablewordthatgoesonandonforeverandever",
  "Lunch? 🍕 or 🍜 or 🥗",
  "The build is green again ✅ thanks everyone",
  "I'll be offline until Monday. ✈️",
  "Can someone review my PR when you get a chance? It touches the sync engine and the views.",
  "Here is the plan:\n1. measure\n2. fix the slow path\n3. measure again",
  "שלום! Hello! مرحبا! こんにちは! 你好! 안녕! Привет!",
  "Ελληνικά, кириллица, ქართული and Հայերեն in one line.",
  "♠♥♦♣ ☀☁☂☃ ★☆ ♪♫ ✓✗ ←↑→↓ ⌘⌥⇧",
  "Long thoughts: the thing about local-first software is that every device is a full replica, so the interesting questions are all about what happens when replicas disagree, and how quickly they converge once they can talk again.",
  "ok",
  "Agreed.",
  "Wait, what? 👀",
  "Photos from the trip!",
  "Ce n'est pas grave, on recommencera la semaine prochaine.",
  "Die Besprechung dauert länger als geplant.",
  "Ya llegué, estoy en la entrada principal.",
  "Не забудьте обновить приложение перед выходными.",
  "今日のデモ、とても良かったです！👏",
  "这个问题我们下周再讨论吧。",
  "고마워요! 내일 봐요 😊",
  "Happy birthday!! 🎂🎈🎁",
  "Family photo day 👨‍👩‍👧‍👦 and the dog 🐕‍🦺 came too",
  "Waving from Tokyo 🇯🇵 👋🏽 then Lagos 🇳🇬 👋🏿",
  "Press 1️⃣ for yes, 2️⃣ for no ✌🏼",
  "Weather: ☀️ then 🌧️ then ❄️ — text-style ☀ ☁ stays text"]

def emoji : Array String := #["👍", "❤️", "😂", "🎉", "🙏", "👀", "🔥", "✅", "👍🏽", "🇯🇵"]

/-! ## Pictures -/

def palette : Array UInt32 := #[0x4A90D9, 0xE8A33D, 0x43B581, 0xD9534F, 0x9B59B6, 0x1ABC9C,
  0xF06292, 0x7986CB, 0xA1887F, 0x4DB6AC]

/-- A 5 x 5 mirrored identicon in a colour, d x d, as packed RGBA. -/
def identicon (g : Rng) (d : Nat) : Array UInt32 × Rng := Id.run do
  let (bits, g) := g.next
  let (ci, g) := g.below palette.size
  let col := palette[ci]!
  let fg := (col <<< 8) ||| 255
  let bg : UInt32 := 0xF0F0F0FF
  let mut px := Array.mkEmpty (d * d)
  for y in [0:d] do
    for x in [0:d] do
      let cx := x * 5 / d
      let cy := y * 5 / d
      let mx := if cx > 2 then 4 - cx else cx
      let on := (bits >>> (cy * 3 + mx).toUInt64) &&& 1 == 1
      px := px.push (if on then fg else bg)
  return (px, g)

/-- Packed RGBA rows of a crop of s scaled to w x h. -/
def cropPx (s : Image.Src) (x0 y0 cw ch w h : Nat) : Array UInt32 := Id.run do
  let b := Image.scaleCrop s x0 y0 cw ch w h 0xFFFFFF
  let mut px := Array.mkEmpty (w * h)
  for row in b.rows do
    for i in [0:row.size / 4] do
      px := px.push ((row[4*i]!.toUInt32 <<< 24) ||| (row[4*i+1]!.toUInt32 <<< 16) |||
        (row[4*i+2]!.toUInt32 <<< 8) ||| 255)
  return px

/-- A crop of a random photo at a random aspect, at most 720 px a side. -/
def photo (srcs : Array Image.Src) (g : Rng) : (Nat × Nat × ByteArray) × Rng := Id.run do
  let (si, g) := g.below srcs.size
  let s := srcs[si]!
  let (aspect, g) := g.below 5
  let (w, h) := match aspect with
    | 0 => (720, 480) | 1 => (480, 640) | 2 => (600, 600) | 3 => (720, 300) | _ => (360, 540)
  -- a crop of the source with the target's aspect, at a random place
  let cw := min s.w (s.h * w / h)
  let ch := min s.h (s.w * h / w)
  let (fx, g) := g.below (s.w - cw + 1)
  let (fy, g) := g.below (s.h - ch + 1)
  let (half, g) := g.below 2
  let (w, h) := if half == 0 then (w / 2, h / 2) else (w, h)
  return ((w, h, Image.encode w h (cropPx s fx fy cw ch w h)), g)

/-- A picture's preview: the whole of it at most 32 px on its long side
(well inside an attachment's 8 KiB). -/
def preview (bytes : ByteArray) : ByteArray :=
  match Image.decode bytes with
  | some s =>
    let (w, h) := if s.w ≥ s.h then (32, max 1 (32 * s.h / s.w)) else (max 1 (32 * s.w / s.h), 32)
    Image.encode w h (cropPx s 0 0 s.w s.h w h)
  | none => .empty

/-- Chaos's pseudo-random bytes (test data only: never a key that guards
anything real). -/
def bytesOf (tag : String) (n : Nat) : ByteArray := (sha256 tag.toUTF8).extract 0 n

/-! ## The community -/

/-- This device in one community (Kinds.Accepted). -/
abbrev Me := Kinds.Accepted.Me

/-- A test seed from the clock: guessable, so only for test identities
(the app's secrets come from `App.newSeed`). -/
def freshSeed (salt : String) : IO ByteArray := do
  return sha256 s!"lean-quiet {salt} {← Data.nowUs}".toUTF8

/-- Minutes since 2026-10-01, for message times. -/
def epoch : Nat := 29330000

/-- The jobs that make a community of about n messages, their bodies
sealed under the community's content key k; a few carry photos, each an
attachment with its chunks (at most `maxFiles` files in all). -/
def make (me : Me) (k : ByteArray) (srcs : Array Image.Src) (seed n top now : Nat) : Array Job := Id.run do
  -- times rise with uneven gaps and end by `now` (wall-clock minutes);
  -- counters follow the channel's newest, `top`, so chaos goes at the end
  let start := now - min now (12 * n)
  let c := me.c
  let f := me.dev
  let mut g : Rng := ⟨seed.toUInt64 * 7919 + 17⟩
  let mut jobs : Array Job := #[]
  let mut batch : Array Op := #[]
  -- people: invited by the founder, who approves each request (one approval admits)
  let nUsers := max 6 (min names.size (n / 20))
  let mut people : Array (Id × Device) := #[(me.adm, f)]
  for i in [0:nUsers] do
    let d := Device.named s!"chaos-{seed}-{i}"
    let bearer := Device.named s!"chaos-bearer-{seed}-{i}"
    let inv := invite c me.adm f bearer.pk false
    let rq := request c inv.id d (cryptoSeal.pub (sha256 s!"chaos-node-{seed}-{i}".toUTF8)) bearer.sk
    let ap := approve c rq.id me.adm f
    let j := admit c rq.id ap.id
    let p := profile c j.id d names[i % names.size]!.toUTF8 start
    batch := batch ++ #[inv, rq, ap, j, p]
    people := people.push (j.id, d)
  jobs := jobs.push ⟨batch.toList, false⟩
  batch := #[]
  -- messages, their photos, and reactions
  let maxFiles := 12
  let mut files := 0
  let mut t := start
  let mut pending : Array Op := #[]
  for i in [0:n] do
    let (gap, g1) := g.below 100
    let (ai, g2) := g1.below people.size
    let (ti, g3) := g2.below texts.size
    let (more, g4) := g3.below 6
    let (ti2, g5) := g4.below texts.size
    let (att, g6) := g5.below 100
    g := g6
    t := min now (t + (if gap < 60 then 1 else if gap < 90 then 7 else 90))
    let (u, d) := people[ai]!
    let text := if more == 0 then texts[ti]! ++ " " ++ texts[ti2]! else
      if more == 1 then texts[ti]! ++ "\n\n" ++ texts[ti2]! else texts[ti]!
    let tag := s!"chaos {seed} {i}"
    let o := sealedPost c u d k (bytesOf (tag ++ " nonce") 24) text.toUTF8 (top + i + 1) t
    pending := pending.push o
    if att < 12 && !srcs.isEmpty && files < maxFiles then
      let ((w, h, bytes), g7) := photo srcs g
      g := g7
      files := files + 1
      let nf : NewFile := { info := { name := s!"photo-{i}.qoi".toUTF8, kind := "image/qoi".toUTF8, w, h,
                                      preview := preview bytes },
                            bytes, key := bytesOf (tag ++ " file key") 32, nonce := bytesOf (tag ++ " file nonce") 24,
                            metaNonce := bytesOf (tag ++ " meta nonce") 24 }
      let (a, cs) := attach c u o.id d k nf
      pending := pending ++ #[a] ++ cs.toArray
    -- reactions on this message, arriving with it
    let (r, g9) := g.below 3
    g := g9
    if r == 0 then
      let (ne, g10) := g.below 4
      g := g10
      for kk in [0:ne + 1] do
        let e := emoji[(i + kk * 3) % emoji.size]!
        let (nr, g11) := g.below 5
        g := g11
        for z in [0:nr + 1] do
          let (u2, d2) := people[(ai + z * 7 + kk) % people.size]!
          pending := pending.push (react c u2 o.id d2 e.toUTF8 (t + z))
    if pending.size ≥ 100 then
      -- a little shuffled within the batch: replies before what they cite
      let (rot, g12) := g.below pending.size
      g := g12
      let shuffled := pending.extract rot pending.size ++ pending.extract 0 rot
      jobs := jobs.push ⟨shuffled.toList, false⟩
      pending := #[]
  if !pending.isEmpty then jobs := jobs.push ⟨pending.toList, false⟩
  return jobs

end Chaos

end

section

/-
A request to join: the device asking, the approvals it has (one admits
it; an admission may cite only decided facts), and whether an admission
answers it.

Reads: `approval.byRequest [c, r]` and `admission.byDevice [c, d]` (a
count). The Join requests page lists `request.all [c]` and makes one of
these per row.
-/

namespace Kinds.Request
open Engine Community Data

structure Data where
  id : Id
  device : Key
  /-- Decided approvals' ids (what an admission may cite). -/
  approvals : List Id
  pending : Nat
  admitted : Bool
  deriving Inhabited, BEq

variable {m : Type → Type} [Monad m] [Reads m]

def read (c r : Id) (f : Fact) (deps : Array Q) : m (Option Data × Array Q) := do
  let .request _ _ d _ _ := f | return (none, deps)
  let (aps, pend, deps) ← readList (approval.byRequest.query [c, r]) deps
  let ids := aps.rows.map (·.1.2)
  let (adm, _, deps) ← readList (admission.byDevice.query [c, d] (limit := some 0)) deps
  return (some ⟨r, d, ids.filter (!pend.contains ·), (ids.filter pend.contains).length, adm.total > 0⟩, deps)

/-- The requests to c no admission answers yet. -/
def waiting (c : Id) : m (Array Data × Array Q) := do
  let (rq, _, deps) ← readList (request.all.query [c]) #[]
  let mut out := #[]
  let mut deps := deps
  for (pos, f) in rq.rows do
    let (r, d) ← read c pos.2 f deps
    deps := d
    if let some r := r then
      if !r.admitted then out := out.push r
  return (out, deps)

/-- Whether an approval of it is decided: one admits it. -/
def Data.ready (r : Data) : Bool := !r.approvals.isEmpty

/-- Whether its admission is on its way: an approval is pending or decided. -/
def Data.going (r : Data) : Bool := r.pending > 0 || r.ready

def hexShort (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let t := String.ofList (Nat.toDigits 16 x.toNat); if t.length < 2 then "0" ++ t else t)

/-- Its row on the Join requests page. -/
def Data.row (r : Data) : Pages.Asking :=
  { device := s!"Device {hexShort r.device}", when := if r.going then "approved" else "waiting",
    going := r.going }

end Kinds.Request

end

section

/-
The reader: what the frame wants read (the conversation's ids, its
rows), read on a connection of its own, one read transaction a pass, and
put on the board (Live.Board). The frame takes the board's values and
reads nothing of the store for them, so a slow read makes a value late,
never a frame slow (docs/PERF.md).

A pass takes the journal's rows and the frame's own notices (its
outbox's changes), netted and matched against the windows its reads
watch (Data.Live.notice: exactly the reads whose windows changed go
stale), forgets the wants the frame no longer has (and, when the wants
change, the windows of every read none of them holds: the reads it
watches are exactly its wants' own), and reads
again each want one of whose reads went stale, or that it does not hold,
at most `cap` of them, in the frame's order (the visible first). An
equal value leaves the board unchanged (`Board.put`). The pass's cache is
a `Live`, so LiveLaws holds of it on this connection: every value a pass
puts is of the pass's one moment.

On a device the passes run on a thread of their own (`run`); without
one (the headless twins) the frame runs a pass itself, at the points it
would take the board.
-/

namespace Reader
open Engine Community Data

/-- What the frame wants read. -/
inductive Want where
  /-- A window of c's conversation: the `above` readable messages at and
  older than the anchor and the `below` newer than it; with no anchor,
  the newest `above`. A refill reads O(above + below) rows, however long
  the conversation (Heights' `window_rows`). -/
  | window (c : Id) (anchor : Option Pos) (above below : Nat)
  /-- How many readable messages of c are newer than the anchor, and how
  many at or older than it (no anchor: all are older): counted, not read.
  They size the scroll extent beside the window (the page's own read,
  Screen's `chrome`), so a message filed outside the window notifies
  this want alone; the frame reads it after the rows. -/
  | count (c : Id) (anchor : Option Pos)
  /-- A root collection, or the children of one root. Both use the same
  bounded window API; membership comes from signed op references. -/
  | clumps (c : Id) (root : Option Id) (anchor : Option Pos) (above below : Nat)
  | clumpCount (c : Id) (root : Option Id) (anchor : Option Pos)
  /-- Message m's own fact and content key (Kinds.Message.readOwn). -/
  | row (c me m : Id)
  | author (c user : Id)
  | attachments (c message : Id)
  | attachment (c attachment : Id)
  | emojis (c message : Id)
  | reaction (c message me : Id) (emoji : String)
  /-- An attachment child owns its metadata/progress/chunk-list view. -/
  | picture (c attachment : Id)
  /-- An attachment's chunk ops' bytes, in order (as stored, or in the
  outbox): what its file is opened from, off the frame. -/
  | slices (chunks : List Id)
  /-- This device's communities (Kinds.Accepted.read). -/
  | comms
  /-- c's present member identities/devices and whether `user` is an
  admin. Mounted author components supply their profiles. -/
  | members (c user : Id)
  /-- c's join requests no admission answers yet. -/
  | asking (c : Id)
  /-- How many present members c has. -/
  | people (c : Id)
  /-- Session-owned reconciliation, not a visible widget subscription. -/
  | maintenance (c : Id)
  deriving DecidableEq, Hashable

/-- Two of this device's communities alike: every field but the device,
which its seed fixes (`dev_ok`). -/
instance : BEq Kinds.Accepted.Me := ⟨fun a b =>
  a.acc == b.acc && a.seed == b.seed && a.c == b.c && a.adm == b.adm && a.user == b.user &&
    a.name == b.name && a.joiningOp == b.joiningOp && a.dialing == b.dialing && a.removed == b.removed⟩

/-- What a want reads as. -/
inductive Val where
  /-- The window's positions, newest first, and how many of them are
  newer than its anchor. -/
  | window (ids : Array Pos) (newerRows : Nat)
  /-- The counts beside the anchor: newer than it, and at or older. -/
  | count (newer older : Nat)
  /-- The row, or none while its message cannot be shown. -/
  | row (d : Option Row.RowData)
  | author (name : String) (namesake : Bool)
  | ids (ids : List Id)
  | emojis (emojis : List String)
  | reaction (tally : Row.Tally)
  | picture (data : Option Row.Pic)
  /-- The chunk ops' bytes, or none while one is not here. -/
  | slices (raw : Option (List ByteArray))
  | comms (all : Array Kinds.Accepted.Me)
  | members (ms : Array (Id × List Key × String)) (admin : Bool)
  | asking (rs : Array Kinds.Request.Data)
  | people (n : Nat) (complete : Bool)
  | writes (ops : List ByteArray)
  deriving BEq

structure St where
  rd : Db
  live : Live := {}
  out : Array Pending := #[]
  seen : Nat := 0
  /-- Each held want's reads: it is read again when one goes stale. -/
  deps : Std.HashMap Want (Array Q) := {}
  /-- Wants to read again: marked when a pass's notices stale one of
  their reads, before any is read again (two wants reading one list
  both see its change), and kept until read. -/
  dirty : Std.HashSet Want := {}
  passes : Nat := 0
  /-- The communities last read: Kinds.Accepted.read keeps their devices. -/
  known : Array Kinds.Accepted.Me := #[]
  /-- The wants of the last pass: when they change, the reads no want
  holds stop being watched. -/
  last : Array Want := #[]
  /-- The reverse index: each read, the wants that recorded it
  (RestLaws' `rev`, complete). -/
  rev : Std.HashMap Q (Array Want) := {}
  /-- The frame's wants as of `gen`. -/
  gen : Nat := 0
  wantSet : Std.HashSet Want := {}
  /-- The reads the want being read has made. -/
  log : Array Q := #[]
  /-- The writers' commit count as of the last journal read, and when
  that was (ms). -/
  seenC : Nat := 0
  readAt : Nat := 0
  /-- The passes that opened the store. -/
  opens : Nat := 0
  retired : Nat := 0
  /-- Revocation checked before each query and board publication. -/
  enabled : IO Bool := pure true
  /-- Deterministic instrumentation after a real query/cache operation.
  Production leaves it empty; tests can hold an in-flight read here. -/
  afterQuery : Q → IO Unit := fun _ => pure ()

abbrev RM := StateT St IO

/-- A user action: its id (the frame's, for its continuation) and its
intent, run in a pass on the reader's connection, before the marks. -/
abbrev Act := Id × RM Community.Write

/-- What the frame and the reader share. -/
structure Shared where
  board : IO.Ref (_root_.Live.Board Want Val)
  /-- One atomic publication: generation and wants, most urgent first.
  A reader must never pair a new generation with the previous wants. -/
  request : IO.Ref (Nat × Array Want)
  /-- The outbox: the pass's. The frame's own writes join it; the pass
  adds its acts' ops and drops those the store has decided. -/
  out : IO.Ref (Array Pending)
  /-- The rows the frame's own writes filed (to its outbox) since the
  last pass. -/
  notes : IO.Ref (Array Filing)
  /-- The journal's rows the reader has taken (the writer prunes below
  the frame's and this). -/
  seen : IO.Ref Nat
  /-- The writers' commits (the app's writer counts its own, the node's
  notify counts the node's): a pass that sees it unmoved, with no note,
  the same wants and nothing dirty, reads nothing (RestLaws.start_rest). -/
  commits : IO.Ref Nat
  /-- The frame's acts, for the next pass (`Shared.act`). -/
  acts : IO.Ref (Array Act)
  /-- What each act wrote: its write, or none when refused (an op
  Invalid, or the intent failed). The frame takes them, submits each
  write and runs its continuation. -/
  done : IO.Ref (Array (Id × Option Community.Write))
  plan : IO.Ref (Demand.Plan Want)
  /-- Scheduling belongs to this reader lifetime, outside transaction rollback.
  A failed selected query retries behind retained work on the next pass.
  stopReader creates a fresh Shared before any replacement worker starts. -/
  queue : IO.Ref (List Want)
  /-- Protects only demand changes and publication, never database IO. -/
  gate : Std.BaseMutex

def Shared.new (commits : IO.Ref Nat) : IO Shared :=
  return ⟨← IO.mkRef {}, ← IO.mkRef (0, #[]), ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0,
    commits, ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef {}, ← IO.mkRef [], ← Std.BaseMutex.new⟩

def Shared.locked (sh : Shared) (action : IO α) : IO α := do
  sh.gate.lock
  try action finally sh.gate.unlock

/-- Queue an act: the next pass opens the store for it (`Live.mustReadActs`). -/
def Shared.act (sh : Shared) (id : Id) (intent : RM Community.Write) : IO Unit :=
  sh.acts.modify (·.push (id, intent))

/-- The frame's wants, set; the generation moves only when they change,
so a reader at rest stays at rest (RestLaws.nextGen_same). -/
def Shared.setNeeds (sh : Shared) (needs : Array (Demand.Need Want)) : IO Unit := sh.locked do
  let old ← sh.plan.get
  if old.needs == needs.toList then return
  let plan := old.reconcile needs.toList
  -- Ref.modify uses take/set, so concurrent readers cannot put an older
  -- snapshot back over this update (a bare Ref.set does not take first).
  sh.plan.modify (fun _ => plan)
  let ws := (needs.toList.map (·.key)).eraseDups.toArray
  sh.request.modify fun (gen, old) => (_root_.Live.nextGen old ws gen, ws)
  let held := plan.heldIndex
  sh.board.modify (·.keep held.contains)

/-- Compatibility for page-level callers. Components pass their own paths
through setNeeds; counts and secondary page lists are prefetch priority. -/
def Want.need (w : Want) : Demand.Need Want :=
  { key := w, owner := match w with
      | .row c _ m => ["community".toUTF8, c, "message".toUTF8, m]
      | _ => ["page".toUTF8],
    visible := match w with | .count .. | .clumpCount .. | .people .. | .members .. => false | _ => true }

def Shared.setWants (sh : Shared) (ws : Array Want) : IO Unit := sh.setNeeds (ws.map Want.need)

def Shared.current (sh : Shared) (ticket : Demand.Ticket Want) : IO Bool :=
  return (← sh.plan.get).current ticket

/-- Validation and publication share the demand lock: an unmount cannot
slip between a successful ticket check and the board update. -/
def Shared.publish (sh : Shared) (ticket : Demand.Ticket Want) (value : Val) : IO Unit := sh.locked do
  if let some v := Demand.complete (← sh.plan.get) ticket value then
    sh.board.modify (·.put ticket.key v)

def Shared.wants (sh : Shared) : IO (Array Want) := return (← sh.request.get).2
def Shared.generation (sh : Shared) : IO Nat := return (← sh.request.get).1


/-- A read through the pass's cache, on this connection. -/
def read (q : Q) : RM Ans := do
  let s ← get
  if !(← s.enabled) then return default
  modify fun s => { s with log := s.log.push q }
  let (a, live) ← (Live.readWith (fun q => q.run s.rd s.out) q).run s.live
  modify fun s => { s with live }
  s.afterQuery q
  return a

instance : Reads RM := ⟨read⟩

/-- One pagination interpreter for every community list, including nested
collections. It watches row windows separately from counts. -/
abbrev ListView := Option Nat → Bool → Option Pos → Option Pos → View Fact (Answer Fact)

def readWindow (view : ListView) (anchor : Option Pos) (above below : Nat) : RM (Val × Array Q) := do
  match anchor with
  | none =>
    let (a, deps) ← readView (view (some above) true none none) #[]
    return (.window (a.rows.map (·.1)).toArray 0, deps)
  | some p =>
    let (o, deps) ← readView (view (some above) true none (some (p.1, p.2.push 0))) #[]
    let (n, deps) ← readView (view (some below) false (some p) none) deps
    return (.window ((n.rows.reverse ++ o.rows).map (·.1)).toArray n.rows.length, deps)

def readCounts (view : ListView) (anchor : Option Pos) : RM (Val × Array Q) := do
  let (n, deps) ← readView (view (some 0) true anchor none) #[]
  return (match anchor with
    | none => (.count 0 n.inRange, deps)
    | some _ => (.count n.inRange (n.total - n.inRange), deps))

/-- A want's value, and the reads it made. -/
def eval : Want → RM (Val × Array Q)
  | .window c anchor above below =>
    readWindow (fun limit desc after before => Community.readable c limit desc after before) anchor above below
  | .count c anchor =>
    readCounts (fun limit desc after before => Community.readable c limit desc after before) anchor
  | .clumps c root anchor above below =>
    readWindow (fun limit desc after before => Community.readableClumps c root limit desc after before) anchor above below
  | .clumpCount c root anchor =>
    readCounts (fun limit desc after before => Community.readableClumps c root limit desc after before) anchor
  | .comms => do
    let (all, deps) ← Kinds.Accepted.read (← get).known
    modify fun s => { s with known := all }
    return (.comms all, deps)
  | .members c user => do
    let (ms, deps) ← readView (Kinds.Profile.present c) #[]
    -- an admin: the founder's user (the community's id), or one granted admin
    let (ad, _, deps) ← readList (Community.admin.byUser.query [c, user] (limit := some 0)) deps
    return (.members (ms.toArray.map fun (u, ds) => (u, ds, "…")) (!user.isEmpty && (user == c || ad.total > 0)), deps)
  | .asking c => do
    let (rs, deps) ← Kinds.Request.waiting c
    return (.asking rs, deps)
  | .people c => do
    let ((n, all), deps) ← readView (Kinds.Profile.presentCount c 999 1024) #[]
    return (.people n (all && n < 999), deps)
  | .maintenance c => do
    let (all, deps) ← Kinds.Accepted.read (← get).known
    let some me := all.find? (fun m => m.c == c && !m.waiting) | return (.writes [], deps)
    let now := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60
    let (profile, deps) ← readView (Community.introduce c me.dev now) deps
    let (keys, deps) ← readView (Community.unwrap c) deps
    return (.writes ((profile.ops ++ keys.ops).map Op.bytes), deps)
  | .row _ _ m => do
    match ← Kinds.Message.readOwn m with
    | some (d, deps) => return (.row (some d), deps)
    -- not shown yet: no reads held, so it is read again each pass
    | none => return (.row none, #[])
  | .author c u => do
    let ((name, twin), deps) ← Kinds.Profile.author c u
    return (.author name twin, deps)
  | .attachments c msg => do
    let (ids, deps) ← Kinds.File.ids c msg
    return (.ids ids, deps)
  | .attachment c att => do
    let (p, deps) ← Kinds.File.readOne c att false
    return (.picture p, deps)
  | .emojis c msg => do
    let (emojis, deps) ← Kinds.React.emojis c msg
    return (.emojis emojis, deps)
  | .reaction c msg me emoji => do
    let (tally, deps) ← Kinds.React.one c msg me emoji
    return (.reaction tally, deps)
  | .picture c attachment => do
    let (p, deps) ← Kinds.File.readOne c attachment
    return (.picture p, deps)
  | .slices xs => do
    -- each chunk op's read is held: one arriving reads the want again
    let mut raw := #[]
    let mut deps := #[]
    for x in xs do
      match (← get).out.find? (·.op.id == x) with
      | some pd => raw := raw.push pd.op.bytes
      | none =>
        deps := deps.push (Q.op x)
        match ← read (Q.op x) with
        | .bytes (some b) => raw := raw.push b
        | _ => return (.slices none, deps)
    return (.slices (some raw.toList), deps)

/-- w's value, with every read it made recorded whatever it found: a
row not shown yet holds the reads it made, so a notice on one of them,
not every pass, reads it again. -/
def evalLogged (w : Want) : RM Val := do
  modify fun s => { s with log := #[] }
  return (← eval w).1

/-- The index after w's reads move from `old` to `new`. -/
def reindex (rev : Std.HashMap Q (Array Want)) (w : Want) (old new : Array Q) :
    Std.HashMap Q (Array Want) :=
  let rev := old.foldl (fun r q => r.modify q (·.filter (· != w))) rev
  new.foldl (fun r q => r.insert q ((r.getD q #[]).push w)) rev

/-- An act's write, judged as App.writeAll judges the frame's: each op
in order against what is decided, the ops before it in the same write,
then the outbox's (pending, so valid), then the store's. Its valid ops,
to show pending; none when one is Invalid (the write is refused). -/
def judgeWrite (rd : Db) (out : Array Pending) (w : Community.Write) : IO (Option (Array Pending)) := do
  let mut mine : Std.HashMap Id (Verdict SF) := {}
  let mut pend := #[]
  for o in w.ops do
    let mut sts := []
    for r in o.reqs do
      sts := sts ++ [← match mine[r]? with
        | some v => pure (some v)
        | none => match out.find? (·.op.id == r) with
          | some p => pure (some (.valid (.inl p.fact)))
          | none => Data.status rd r]
    match judge fam o sts with
    | some (.valid (.inl f)) =>
      mine := mine.insert o.id (.valid (.inl f))
      pend := pend.push (⟨o, f, opKey o.id :: keys f⟩ : Pending)
    | some (.valid v) => mine := mine.insert o.id (.valid v)
    | none => pure ()
    | some .invalid => return none
  return some pend

/-- One pass, in one read transaction; whether it put anything or took
any change. `afterSnapshot` is a deterministic scheduling seam: a test
may publish another request after this pass has captured its whole pair.
`afterJournal` schedules a producer/teardown after the SQL snapshot opens. -/
def pass (sh : Shared) (cap : Nat := 64) (afterSnapshot : IO Unit := pure ())
    (budgetMs : Nat := 0) (afterJournal : IO Unit := pure ()) : RM Bool := do
  if !(← (← get).enabled) then return false
  let (gen, wants) ← sh.request.get
  let plan ← sh.plan.get
  afterSnapshot
  -- Observe the admission cutoff without taking ownership before SQL can
  -- fail. Only this reader consumes an active Shared; producers append, and
  -- teardown detaches it permanently before starting a replacement reader.
  let notes ← sh.notes.get
  let noteCount := notes.size
  let acts ← sh.acts.get
  -- at rest (the writers' counter unmoved, no note, the same wants,
  -- nothing dirty) a pass reads nothing, not even the journal
  -- (RestLaws.start_rest); once a second it reads it anyway, for commits
  -- the counter does not see (the node's purges, until its notify counts
  -- them), and the sessions with it; acts queued open it whatever else
  -- (ActsLaws.acts_force)
  let c ← sh.commits.get
  let now ← IO.monoMsNow
  let s0 ← get
  unless _root_.Live.mustReadActs (!acts.isEmpty) c s0.seenC (!notes.isEmpty) (gen != s0.gen) s0.dirty
      (now ≥ s0.readAt + 1000) do
    return false
  modify fun s => { s with seenC := c, readAt := now, opens := s.opens + 1 }
  let rd := (← get).rd
  rd.exec "BEGIN"
  try
    let s ← get
    -- the journal, read first: the commits this pass's reads see
    let (fs, vs, top) ← rd.filingsSince s.seen
    afterJournal
    if !(← (← get).enabled) then
      rd.exec "COMMIT"
      return false
    -- Claim only the captured prefix: arrivals after the cutoff belong to
    -- the next database snapshot. Per-act revocation checks remain below.
    sh.acts.modify fun a => a.extract acts.size a.size
    -- the outbox is the pass's: the ops the store has decided leave it
    -- (their rows move from pending to stored, a notice too)
    let judged : Std.HashSet Id := vs.foldl (fun a (x, _) => a.insert x) {}
    let (out, gone) ← sh.out.modifyGet fun o =>
      let kept := o.filter fun p => !judged.contains p.op.id
      ((kept, o.filter fun p => judged.contains p.op.id), kept)
    modify fun s => { s with out }
    -- the acts, before the marks (ActsLaws.passActs): each intent runs in
    -- this transaction and its write is judged against the store and the
    -- outbox; its valid ops join the outbox, pending, and their rows are
    -- this pass's notices, so the wants they touch are read now
    let mut actNotes : Array Filing := #[]
    for (id, intent) in acts do
      if !(← (← get).enabled) then break
      let r ← try
          let w ← intent
          if !(← (← get).enabled) then pure none
          else pure (some (w, ← judgeWrite rd (← get).out w))
        catch e => do
          IO.eprintln s!"reader: an act failed: {e}"
          pure none
      match r with
      | some (w, some pend) =>
        if !(← (← get).enabled) then break
        modify fun s => { s with out := s.out ++ pend }
        sh.out.modify (· ++ pend)
        actNotes := actNotes ++ Pending.filings pend.toList
        sh.done.modify (·.push (id, some w))
      | _ => sh.done.modify (·.push (id, none))
    let notes := notes ++ Pending.filings gone.toList ++ actNotes
    -- at rest (no filing, no note, the same wants, nothing dirty) a pass
    -- does nothing (RestLaws.rest_idle)
    if fs.isEmpty && vs.isEmpty && notes.isEmpty && gen == s.gen && s.dirty.isEmpty then
      rd.exec "COMMIT"
      sh.notes.modify fun a => a.extract noteCount a.size
      return false
    -- the wants moved: the new ones are marked, the gone ones forgotten,
    -- and the reads none of them holds stop being watched (RestLaws.wantIdx;
    -- Screen.screen_subs: what is watched is what the wants read)
    let moved := gen != s.gen
    if moved then
      let want : Std.HashSet Want := wants.foldl (·.insert ·) {}
      -- Unmount/remount can happen entirely between two reader passes.
      -- The key then looks unchanged, but its board answer was revoked.
      let board ← sh.board.get
      let fresh := wants.toList.filter fun w => !s.wantSet.contains w || (board.get? w).isNone
      let dirty := fresh.foldl (·.insert ·) (s.dirty.filter want.contains)
      let deps := s.deps.filter fun w _ => want.contains w
      let held := deps.fold (fun acc _ qs => qs.foldl (fun a q => a.insert q) acc) ({} : Std.HashSet Q)
      let rev := deps.fold (fun acc w qs => reindex acc w #[] qs) {}
      -- the live cache keeps exactly the held reads (Lifecycle.live_exact)
      modify fun s => { s with gen, wantSet := want, dirty, deps, rev, last := wants,
                               live := s.live.keep held.contains }
    -- the reads this pass's filings and notes reach (Live.hit, exact per
    -- window), before the notice disarms them; the store's rows and the
    -- outbox's are netted apart: a row the store files as it leaves the
    -- outbox is two changes (stored, no longer pending), not one undone
    let s ← get
    let hit := (s.live.hit fs (vs.map (·.1))).toList ++ (s.live.hit notes #[]).toList
    let hitActs := (s.live.hit actNotes #[]).toList
    modify fun s => { s with seen := top, live := (s.live.notice fs (vs.map (·.1))).notice notes,
                             passes := s.passes + 1 }
    -- mark the dirty and the wanted wants those reads name, through the
    -- index; read every want the acts' rows touched, then the first `cap`
    -- other marked in the frame's order: the model's decisions
    -- (Live.markHit, Live.pickActs), so ActsLaws' acts_shown and
    -- inv_passActs, and with no act RestLaws', are about this pass
    let s ← get
    let rev := fun q => (s.rev.getD q #[]).toList
    let marked := (_root_.Live.markHit rev s.dirty hit).filter s.wantSet.contains
    let touched := (_root_.Live.markHit rev {} hitActs).filter s.wantSet.contains
    let ready := _root_.Live.pickActs wants.toList touched marked wants.size
    sh.queue.modify (Demand.reconcile ready)
    modify fun s => { s with dirty := marked }
    let start ← IO.monoMsNow
    let mut published := 0
    for i in [0:cap] do
      if i > 0 && budgetMs > 0 && (← IO.monoMsNow) - start ≥ budgetMs then break
      let choice ← sh.queue.modifyGet
        (Demand.take (fun w => touched.contains w || plan.visible w) true)
      let some w := choice | break
      let some ticket := plan.ticket w | continue
      unless ← sh.current ticket do
        modify fun s => { s with retired := s.retired + 1 }
        continue
      let old := (← get).deps.getD w #[]
      let enabled := (← get).enabled
      modify fun s => { s with enabled := do return (← enabled) && (← sh.current ticket) }
      let v ← try evalLogged w finally modify fun s => { s with enabled }
      unless (← enabled) && (← sh.current ticket) do
        modify fun s => { s with retired := s.retired + 1 }
        continue
      modify fun s =>
        { s with deps := s.deps.insert w s.log, dirty := s.dirty.erase w, rev := reindex s.rev w old s.log }
      -- Publish each finished value promptly; a later, slow want cannot
      -- hold an already-read visible row behind the rest of the batch.
      sh.publish ticket v
      published := published + 1
    rd.exec "COMMIT"
    -- Notes remain retryable through query/COMMIT failure. Later appended
    -- notes still belong to the next pass, even when this pass produced acts.
    sh.notes.modify fun a => a.extract noteCount a.size
    -- This is the last effect before returning the successful reader state.
    -- A failed query/COMMIT must leave its notices available to the retry.
    sh.seen.modify (fun _ => top)
    return published > 0 || moved || !fs.isEmpty || !vs.isEmpty || !acts.isEmpty
  catch e =>
    rd.exec "ROLLBACK"
    throw e

/-- The reader's thread: a pass, and a short rest when it found nothing. -/
partial def run (sh : Shared) (s : St) : IO Unit := do
  let s ← try
      let (busy, s) ← (pass sh).run s
      if !busy then IO.sleep 2
      pure s
    catch e => do
      IO.eprintln s!"reader: {e}"
      IO.sleep 50
      pure s
  run sh s

end Reader

end

section

/- A revocable reader owned by a mounted page. Queries and publication
check its stop flag. The app detaches the board and polls completion;
Worker.stop is a joining API for callers outside the frame. -/

namespace Reader

structure Worker where
  stopped : IO.Ref Bool
  done : Task (Except IO.Error St)

def work (sh : Shared) (stopped : IO.Ref Bool) (initial : St) : IO St := do
  let mut s := initial
  while !(← stopped.get) do
    try
      let (busy, next) ← (pass sh (budgetMs := 4)).run s
      s := next
      if !busy then IO.sleep 2
    catch e =>
      IO.eprintln s!"reader: {e}"
      IO.sleep 50
  return s

def Worker.start (sh : Shared) (s : St) : IO Worker := do
  let stopped ← IO.mkRef false
  let done ← IO.asTask (prio := .dedicated) (work sh stopped { s with enabled := return !(← stopped.get) })
  return ⟨stopped, done⟩

/-- Publish cancellation through Ref.take/restore, so an overlapping native
Ref.get cannot restore an old false value over a completed stop request. -/
def Worker.requestStop (w : Worker) : IO Unit :=
  w.stopped.modify (fun _ => true)

def Worker.stop (w : Worker) : IO (Option St) := do
  w.requestStop
  match ← IO.wait w.done with
  | .ok s => return some s
  | .error e => throw e

end Reader

end

section

/- Components receive identities and constraints, and observe their own
queries. Lists/sets discover identities; an op component interprets its
own data. The app supplies one interpreter backed by the shared Reader. -/

namespace Component
open Engine

structure Scope where
  owner : Demand.Owner
  visible : Bool := true

def Scope.child (s : Scope) (kind : String) (id : Id) : Scope :=
  { s with owner := s.owner ++ [kind.toUTF8, id] }

def Scope.need (s : Scope) (key : Reader.Want) : Demand.Need Reader.Want :=
  ⟨s.owner, key, s.visible⟩

class Queries (m : Type → Type) where
  query : Scope → Reader.Want → m (Option Reader.Val)

export Queries (query)

variable {m : Type → Type} [Monad m] [Queries m]

def author (scope : Scope) (c user : Id) (old : String × Bool) : m (String × Bool) := do
  match ← query scope (.author c user) with
  | some (.author name twin) => return (name, twin)
  | _ => return old

def attachments (scope : Scope) (c msg : Id) (old : List Id) : m (List Id) := do
  match ← query scope (.attachments c msg) with
  | some (.ids ids) => return ids
  | _ => return old

/-- Once opened, an attachment's dimensions/key/preview are immutable.
Retain that measured result without retaining a metadata subscription. -/
def attachment (scope : Scope) (c id : Id) (old : Option Row.Pic) : m (Option Row.Pic) := do
  if old.isSome then return old
  match ← query scope (.attachment c id) with
  | some (.picture p) => return p
  | _ => return none

def picture (scope : Scope) (c id : Id) (old : Row.Pic) : m Row.Pic := do
  match ← query scope (.picture c id) with
  | some (.picture (some p)) => return p
  | _ => return old

def emojis (scope : Scope) (c msg : Id) (old : List String) : m (List String) := do
  match ← query scope (.emojis c msg) with
  | some (.emojis es) => return es
  | _ => return old

def reaction (scope : Scope) (c msg me : Id) (emoji : String) (old : Row.Tally) : m Row.Tally := do
  match ← query scope (.reaction c msg me emoji) with
  | some (.reaction t) => return t
  | _ => return old

/-- Initial measurement composes child answers, without waiting for image
pixels. Pending metadata is distinct from an answered, unavailable file.
Once mounted, each child refreshes only inside its own visibility bounds. -/
def measure (scope : Scope) (c msg : Id) : m (Option (List Row.Pic × List Row.Tally)) := do
  let some (.ids ids) ← query (scope.child "attachments" msg) (.attachments c msg)
    | return none
  let mut pics := []
  for id in ids do
    let some (.picture p) ← query (scope.child "attachment" id) (.attachment c id)
      | return none
    if let some p := p then pics := pics ++ [p]
  let some (.emojis es) ← query (scope.child "reactions" msg) (.emojis c msg)
    | return none
  return some (pics, es.map fun e => ⟨e, 0, false⟩)

end Component

end

section

/- A collection owns its window and counts, independently of the op rows
within it. Geometry keeps an unloaded range as one spacer; drawing still
mounts individual messages, attachments, authors and reaction pills. -/

namespace ClumpList
open Engine

structure Window where
  anchor : Option Pos := none
  ids : Array Pos := #[]
  newer : Nat := 0
  older : Nat := 0
  ready : Bool := false
  deriving Inhabited

def observe {m : Type → Type} [Monad m] [Component.Queries m]
    (scope : Component.Scope) (c root : Id) (old : Window) (half : Nat) : m Window := do
  let rows ← Component.query (scope.child "messages" root) (.clumps c (some root) old.anchor half half)
  let counts ← Component.query { scope.child "count" root with visible := false }
    (.clumpCount c (some root) old.anchor)
  match rows, counts with
  | some (.window ids nr), some (.count cn co) =>
    return { old with ids := ids, newer := cn - (min cn nr), older := co - (min co (ids.size - nr)), ready := true }
  | _, _ => return old

/-- Synthetic spacer ids cannot be real SHA-256 op ids: their prefix
already exceeds 32 bytes. They never enter the query or write API. -/
def gap (root : Id) (part : Nat) : Id :=
  "quiet/clump/spacer/not-an-op-identifier/".toUTF8 ++ Codec.encode (root, part)

/-- A flat virtualizer cell: position, measured/estimated height, spacer. -/
abbrev Cell := Pos × Nat × Bool

def cells (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) : Array Cell :=
  (if w.newer > 0 then #[((.empty, gap root.2 0), w.newer * estimate, true)] else #[]) ++
  w.ids.map (fun p => (p, height p.2, false)) ++
  (if w.older > 0 then #[((.empty, gap root.2 1), w.older * estimate, true)] else #[]) ++
  #[(root, height root.2, false)]

/-- The collapsed and expanded forms share exactly one geometry function. -/
def extent (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) : Nat :=
  (cells root w height estimate).foldl (fun n cell => n + cell.2.1) 0

/-- A million unloaded children still cost at most two spacer cells.
Only the bounded page contributes individual message cells. -/
theorem cells_bounded (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) :
    (cells root w height estimate).size ≤ w.ids.size + 3 := by
  simp only [cells, Array.size_append, Array.size_map]
  split <;> split <;> simp_all <;> omega

/-- Collapsing an offscreen collection cannot move its neighbours. -/
theorem extent_cells (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) :
    extent root w height estimate = (cells root w height estimate).foldl (fun n cell => n + cell.2.1) 0 := rfl

end ClumpList

end

section

/- Settings share libquiet's drawer geometry on phones and desktop.
Every row has one layout used for both pixels and dispatch. -/

namespace Appearance
open Paint Pages Row

def gray50 (dm : Dim) : Color := if dm.theme == .dark then 0xa0a0a0 else 0x767676

def choices : Array (Theme.Setting × String) :=
  #[(.system, "System"), (.light, "Light"), (.dark, "Dark")]

def chosen (current choice : Theme.Setting) : Bool := current == choice

structure Item where
  text : String
  action : Act
  icon : String := ""
  detail : String := ""
  sub : String := ""
  selected : Bool := false
  danger : Bool := false
  disabled : Bool := false

/-- Full-width settings row: 14/20 text, 16px inset and a one-pixel rule. -/
def item (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat) (a : Item) : Bitmap × (Pages.Box × Act) × Nat := Id.run do
  let px := dm.px
  let font := f.atSize (px 14)
  let small := f.atSize (px 12)
  let left := px (if a.icon.isEmpty then 16 else 48)
  let right := px (if a.selected then 40 else 52)
  let sub := if a.sub.isEmpty then #[] else Text.layoutFine small (b.w - left - right) a.sub
  let h := max (px 48) (px 25 + px 20 + sub.size * px 16)
  let mut b := b
  if dm.hot 0 y b.w h (!a.disabled) then b := b.fill 0 y b.w (y + h) (Palette.color dm.theme .selected)
  let ink := if a.disabled then (if dm.theme == .dark then 0x888888 else 0x999999)
    else Palette.color dm.theme (if a.danger then .error else .fg)
  let ty := y + (if a.sub.isEmpty then (h - px 20) / 2 else px 12)
  b := b.line font (Text.oneLineFine font (b.w - left - right) a.text) left (ty + px 4) ink (exactInk := a.disabled)
  for i in [0:sub.size] do
    b := b.line small sub[i]! left (ty + px 20 + i * px 16 + px 1) (gray50 dm)
  if !a.icon.isEmpty then b := b.icon f a.icon (px 16) (y + (h - px 20) / 2) (px 20) (gray50 dm)
  if !a.detail.isEmpty then
    let l := Text.oneLine font (b.w / 2) a.detail
    b := b.line font l (b.w - px 44 - Paint.Line.width font l) (ty + px 4) (gray50 dm)
  b := b.icon f (if a.selected then "icon-check" else "icon-chevron") (b.w - px 32) (y + (h - px 16) / 2) (px 16)
    (if a.selected then Palette.color dm.theme .fg else gray50 dm)
  b := b.fill 0 (y + h - px 1) b.w (y + h) (Palette.color dm.theme .selected)
  return (b, (⟨0, y, b.w, h⟩, a.action), h)

def sectionTitle (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat) (title : String) : Bitmap × Nat :=
  let font := f.atSize (dm.px 12)
  let b := b.line font (Text.oneLine font b.w title) (dm.px 16) (y + dm.px 27) (gray50 dm)
  (b.fill 0 (y + dm.px 46) b.w (y + dm.px 47) (Palette.color dm.theme .selected), dm.px 47)

def group (f : Font.Font) (dm : Dim) (pg : Page) (y : Nat) (title : String) (items : Array Item) : Page × Nat := Id.run do
  let (b, h) := sectionTitle f dm pg.bmp y title
  let mut pg := { pg with bmp := b }
  let mut y := y + h
  for a in items do
    let (b, tap, h) := item f dm pg.bmp y a
    pg := { bmp := b, taps := if a.disabled then pg.taps else pg.taps.push tap }
    y := y + h
  return (pg, y)

def header (f : Font.Font) (dm : Dim) (w insetTop : Nat) (title : String) (back := false) : Bitmap :=
  let b := Bitmap.blank w (insetTop + dm.px 60) (solid (Palette.color dm.theme .panel) w)
  let b := b.icon f (if back then "icon-back" else "icon-close") (dm.px 20) (insetTop + dm.px 20) (dm.px 20) (Palette.color dm.theme .fg)
  let font := (f.atSize (dm.px 16)).medium
  let line := Text.oneLineFine font (min ((w - dm.px 16) / 2) (w - dm.px 192)) title
  let b := b.line font line ((w - Paint.Line.width font line) / 2) (insetTop + dm.px 23) (Palette.color dm.theme .fg)
  b.fill 0 (b.h - dm.px 1) w b.h (Palette.color dm.theme .selected)

def page (f : Font.Font) (dm : Dim) (w h : Nat) (current : Theme.Setting) : Page := Id.run do
  let mut pg : Page := ⟨Bitmap.blank w h (solid (Palette.color dm.theme .panel) w), #[]⟩
  let small := f.atSize (dm.px 11)
  pg := { pg with bmp := pg.bmp.line small (Text.oneLine small w "THEME") (dm.px 16) (dm.px 18) (gray50 dm) }
  let mut y := dm.px 40
  for (choice, name) in choices do
    let (b, tap, rh) := item f dm pg.bmp y { text := name, action := .theme choice, selected := chosen current choice }
    -- A non-selected theme has no navigation chevron.
    let b := if chosen current choice then b else b.fill (w - dm.px 36) (y + dm.px 8) (w - dm.px 12) (y + rh - dm.px 8) (Palette.color dm.theme (if dm.hot 0 y w rh then .selected else .panel))
    pg := { bmp := b, taps := pg.taps.push tap }
    y := y + rh
  return pg

/-- The profile hero shared by You and Community settings. -/
def hero (f : Font.Font) (dm : Dim) (w h : Nat) (name id tally : String) (community : Bool) : Page := Id.run do
  let px := dm.px
  let color := Palette.color dm.theme
  let mut b := Bitmap.blank w h (solid (color .panel) w)
  let ax := (w - px 96) / 2
  let ay := px 24
  b := b.round ax ay (ax + px 96) (ay + px 96) (px 8) (Palette.avatar id)
  let large := f.atSize (px 56)
  let initial := Text.oneLine large (px 96) (String.ofList [(name.toList.headD '?').toUpper])
  b := b.line large initial (ax + (px 96 - Paint.Line.width large initial) / 2) (ay + px 24) 0xffffff
  let ex := ax + px 96 - px 18
  b := b.round ex (ay - px 10) (ex + px 28) (ay + px 18) (px 14) (color .panel)
  b := b.icon f "image-plus" (ex + px 5) (ay - px 5) (px 18) (color .fg)
  b := centred (f.atSize (px 16)) b name (px 135) (color .fg)
  b := centred (f.atSize (px 12)) b tally (px 159) (gray50 dm)
  let bw := (w - px 40) / 2
  let buttonY := px 192
  b := b.round (px 16) buttonY (px 16 + bw) (buttonY + px 44) (px 16) (if dm.hot (px 16) buttonY bw (px 44) then Palette.buttonHover dm.theme else color .button)
  let right := px 24 + bw
  b := b.round right buttonY (w - px 16) (buttonY + px 44) (px 16) (if dm.hot right buttonY bw (px 44) then color .accentInk else color .line)
  b := b.round (right + px 1) (buttonY + px 1) (w - px 17) (buttonY + px 43) (px 15) (color .panel)
  let font := f.atSize (px 14)
  for (x, text, icon, ink) in [(px 16, if community then "Add members" else "Link a device", if community then "icon-person-add" else "icon-devices", color .onAccent),
      (right, "Edit profile", "icon-edit", color .fg)] do
    let l := Text.oneLine font bw text
    let tx := x + (bw - Paint.Line.width font l - px 26) / 2
    b := b.icon f icon tx (buttonY + px 13) (px 18) ink
    b := b.line font l (tx + px 26) (buttonY + px 14) ink
  b := b.fill 0 (px 256) w (px 257) (color .selected)
  return ⟨b, #[(⟨ax, ay, px 96, px 96⟩, .stub "Edit profile"),
    (⟨px 16, buttonY, bw, px 44⟩, if community then .addMembers else .stub "Link a device"),
    (⟨right, buttonY, bw, px 44⟩, .stub "Edit profile")]⟩

/-- Text at the reference's line height, retaining fractional font advances. -/
def prose (f : Font.Font) (dm : Dim) (b : Bitmap) (x y w : Nat)
    (text : String) (size line : Nat := 14) (centered := false) (muted := false) : Bitmap × Nat := Id.run do
  let font := f.atSize (dm.px size)
  let font := if size == 18 then font.medium else font
  let ls := Text.layoutFine font w text
  let mut b := b
  for i in [0:ls.size] do
    let tx := x + (if centered then (w - Paint.Line.width font ls[i]!) / 2 else 0)
    b := b.line font ls[i]! tx (y + i * dm.px line + dm.px (if size == 12 then 1 else 4))
      (if muted then gray50 dm else Palette.color dm.theme .fg)
  return (b, y + ls.size * dm.px line)

def outlineButton (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat)
    (text icon : String) (danger := false) : Bitmap := Id.run do
  let px := dm.px
  let ink := Palette.color dm.theme (if danger then .error else .fg)
  let hot := dm.hot (px 16) y (b.w - px 32) (px 44)
  let mut b := b.round (px 16) y (b.w - px 16) (y + px 44) (px 16)
    (if danger then ink else if hot then Palette.gray30 dm.theme else Palette.color dm.theme .line)
  b := b.round (px 17) (y + px 1) (b.w - px 17) (y + px 43) (px 15) (if hot then Palette.gray03 dm.theme else Palette.color dm.theme .panel)
  let font := f.atSize (px 14)
  let l := Text.oneLineFine font (b.w - px 64) text
  let mark := if icon.isEmpty then 0 else px 26
  let x := (b.w - Paint.Line.width font l - mark) / 2
  if !icon.isEmpty then b := b.icon f icon x (y + px 13) (px 18) ink
  return b.line font l (x + mark) (y + px 14) ink

def leafTitle (title : String) : String :=
  if title == "Message retention" then "Message retention limit"
  else if title == "Storage on this device" then "Storage limits"
  else title


def you (f : Font.Font) (dm : Dim) (w h : Nat) (name id : String) (communities devices : Nat) (setting : Theme.Setting) : Page := Id.run do
  let tally := s!"{communities} {if communities == 1 then "community" else "communities"} · {devices} {if devices == 1 then "device" else "devices"}"
  let pg := hero f dm w (max h (dm.px 1400)) name id tally false
  let (pg, y) := group f dm pg (dm.px 257) "Devices" #[{ text := "Linked devices", action := .stub "Linked devices", icon := "icon-devices", detail := toString devices }]
  let (pg, y) := group f dm pg y "On this device" #[
    { text := "Appearance", action := .appearance, icon := "icon-appearance", detail := match setting with | .system => "System" | .light => "Light" | .dark => "Dark" },
    { text := "Generate link previews", action := .stub "Link previews", icon := "icon-link", sub := "Fetches a link you share so its card shows the page; the site sees your address." }]
  let (pg, y) := group f dm pg y "Connection" #[{ text := "Connecting", action := .stub "Connection", icon := "icon-signal", sub := "disconnected (searching)" }]
  let (pg, y) := group f dm pg y "About" #[{ text := "About Quiet", action := .stub "About Quiet", icon := "icon-info", detail := "Lean" }]
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (y + dm.px 64)) } }

def community (f : Font.Font) (dm : Dim) (w h : Nat) (name id : String) (members : Nat) : Page := Id.run do
  let pg := hero f dm w (max h (dm.px 1400)) name id s!"{members} {if members == 1 then "member" else "members"} · 1 channel" true
  let (pg, y) := group f dm pg (dm.px 257) "People" #[{ text := "Members", action := .stub "Members", icon := "icon-people", detail := toString members }]
  let (pg, y) := group f dm pg y "Conversations" #[
    { text := "Notifications", action := .stub "Notifications", icon := "icon-bell", detail := "All messages" },
    { text := "Create channel", action := .stub "Create channel", icon := "hash" },
    { text := "Message retention", action := .stub "Message retention", detail := "Off", sub := "How long messages are kept" }]
  let (pg, y) := group f dm pg y "Connection" #[
    { text := "Network status", action := .stub "Network status", icon := "icon-signal", detail := "Not connected" },
    { text := "Storage on this device", action := .stub "Storage on this device", icon := "icon-storage" }]
  let buttonY := y + dm.px 32
  let pg := { pg with
    bmp := outlineButton f dm pg.bmp buttonY "Leave community" "icon-leave" true
    taps := pg.taps.push (⟨dm.px 16, buttonY, w - dm.px 32, dm.px 44⟩, .stub "Leave community") }
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (buttonY + dm.px 108)) } }

def channel (f : Font.Font) (dm : Dim) (w h members : Nat) : Page := Id.run do
  let mut pg : Page := ⟨Bitmap.blank w (max h (dm.px 800)) (solid (Palette.color dm.theme .panel) w), #[]⟩
  let mut y := 0
  let items : Array Item := #[
    { text := "Community settings", action := Act.communitySettings },
    { text := "Members in this channel", action := .stub "Members", detail := toString members },
    { text := "Permissions", action := .stub "Permissions", sub := "Roles and members" },
    { text := "Disappearing messages", action := .stub "Disappearing messages", detail := "Off" },
    { text := "Notifications", action := .stub "Notifications", sub := "All messages" },
    { text := "Delete channel", action := .stub "Delete channel", danger := true },
    { text := "Chaos", action := .stub "Chaos", sub := "Generate test people, messages, and pictures" }]
  for a in items do
    let (b, tap, rh) := item f dm pg.bmp y a
    pg := { bmp := b, taps := pg.taps.push tap }
    y := y + rh
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (y + dm.px 64)) } }

/-- Proposed settings keep libquiet's real choices and selected defaults.
They have no dispatch targets until the corresponding ops exist. -/
def staticPage (f : Font.Font) (dm : Dim) (w h : Nat) (title name id : String) : Page := Id.run do
  let px := dm.px
  let color := Palette.color dm.theme
  let mut b := Bitmap.blank w (max h (px 1400)) (solid (color .panel) w)
  let mut y := px 16
  let mut taps := #[]
  if title == "Message retention" || title == "Disappearing messages" then
    let retention := title == "Message retention"
    let text := if retention then "When enabled, all messages older than the chosen retention limit will be deleted."
      else "When enabled, all messages by anyone in this channel will auto-delete after the chosen countdown. (Countdowns start on send, so short countdowns may lead to undelivered messages.)"
    let (pic, endY) := prose f dm b (px 16) y (w - px 32) text 14 20
    b := pic
    y := endY + px 16
    let options := if retention then #["Off", "1 week", "1 month", "3 months", "6 months", "12 months", "18 months", "24 months", "Custom"]
      else #["Off", "1 min", "5 min", "1 day", "1 week", "1 month", "3 months", "6 months", "12 months", "18 months", "24 months", "Custom"]
    for i in [0:options.size] do
      let (pic, _, rh) := item f dm b y { text := options[i]!, action := .back, selected := i == 0, disabled := true }
      b := if i == 0 then pic else pic.fill (w - px 36) (y + px 8) (w - px 12) (y + rh - px 8) (color .panel)
      y := y + rh
    let foot := if retention then "All messages older than the limit will be deleted. Anyone can set shorter times for particular channels or DMs, but only select roles can choose longer times."
      else "All new messages initiated by anyone in the channel will follow this setting."
    let (pic, endY) := prose f dm b (px 16) (y + px 16) (w - px 32) foot 12 16 false true
    b := pic
    y := endY + px 16
  else if title == "Storage on this device" then
    let (pic, endY) := prose f dm b (px 16) y (w - px 32)
      "Customize your device storage limits for images and files posted by you and others." 14 20
    b := pic
    y := endY + px 16
    for (label, sub) in [("Your files and images", "No limit"), ("Others' files and images", "2 GB")] do
      let (pic, _, rh) := item f dm b y { text := label, action := .back, sub, disabled := true }
      b := pic.fill (w - px 36) (y + px 8) (w - px 12) (y + rh - px 8) (color .panel)
      b := b.icon f "icon-down" (w - px 32) (y + (rh - px 16) / 2) (px 16) (gray50 dm)
      y := y + rh
  else if title == "About Quiet" then
    for text in ["Version: 0.1 (Lean Quiet)", "Copyright © A Quiet LLC"] do
      let (pic, endY) := prose f dm b (px 16) y (w - px 32) text 14 20
      b := pic
      y := endY + px 4
  else if title == "Leave community" then
    let ax := (w - px 96) / 2
    let ay := px 40
    b := b.round ax ay (ax + px 96) (ay + px 96) (px 8) (Palette.avatar id)
    let font := f.atSize (px 56)
    let initial := Text.oneLineFine font (px 96) (String.ofList [(name.toList.headD '?').toUpper])
    b := b.line font initial (ax + (px 96 - Paint.Line.width font initial) / 2) (ay + px 24) 0xffffff
    let bx := ax + px 74
    let badgeY := ay + px 74
    b := b.round (bx - px 3) (badgeY - px 3) (bx + px 35) (badgeY + px 35) (px 19) (color .panel)
    b := b.round bx badgeY (bx + px 32) (badgeY + px 32) (px 16) (color .error)
    b := b.icon f "icon-leave" (bx + px 7) (badgeY + px 7) (px 18) 0xffffff
    let (pic, endY) := prose f dm b (px 16) (px 160) (w - px 32) s!"Leave {name}?" 18 26 true
    let bw := min (px 300) (w - px 32)
    let (pic, endY) := prose f dm pic ((w - bw) / 2) (endY + px 12) bw
      "You'll lose access to its channels and messages on this device. To come back, someone will need to invite you again." 14 20 true true
    y := endY + px 24
    let costs := #[("1 channel and their history leave this device", "icon-chats"),
      ("Members will still see messages you sent", "icon-people")]
    let costHeight := px 3 + costs.foldl (fun total (label, _) => total + px 24 +
      (Text.layoutFine (f.atSize (px 14)) (w - px 98) label).size * px 20) 0
    b := pic.round (px 16) y (w - px 16) (y + costHeight) (px 16) (color .line)
    b := b.round (px 17) (y + px 1) (w - px 17) (y + costHeight - px 1) (px 15) (color .panel)
    let startY := y
    y := y + px 1
    for i in [0:costs.size] do
      let (label, icon) := costs[i]!
      let rh := px 24 + (Text.layoutFine (f.atSize (px 14)) (w - px 98) label).size * px 20
      let (pic, _) := prose f dm b (px 65) (y + px 12) (w - px 98) label 14 20
      b := pic.icon f icon (px 33) (y + (rh - px 20) / 2) (px 20) (gray50 dm)
      y := y + rh
      if i + 1 < costs.size then
        b := b.fill (px 17) y (w - px 17) (y + px 1) (color .selected)
        y := y + px 1
    y := startY + costHeight + px 32
    b := b.round (px 16) y (w - px 16) (y + px 44) (px 16) (mixC (color .panel) (color .error) 154)
    let font := (f.atSize (px 14)).medium
    let line := Text.oneLineFine font (w - px 64) "Leave community"
    b := b.line font line ((w - Paint.Line.width font line) / 2) (y + px 14)
      (mixC (color .panel) 0xffffff 154) (exactInk := true)
    y := y + px 52
    b := outlineButton f dm b y "Stay" ""
    taps := taps.push (⟨px 16, y, w - px 32, px 44⟩, .back)
    y := y + px 68
  else
    let (pic, endY) := prose f dm b (px 16) (px 24) (w - px 32)
      s!"{title} is not available in this build yet." 14 20 false true
    b := pic
    y := endY
  return ⟨{ b with rows := b.rows.extract 0 (max h (y + px 64)) }, taps⟩

def stub (f : Font.Font) (dm : Dim) (w h : Nat) (title : String) (name id : String := "") : Page :=
  staticPage f dm w h title name id

theorem selected_check (s : Theme.Setting) : chosen s s = true := by cases s <;> rfl

end Appearance

end



section

/- App types shared by the root and lifecycle hooks. Existing fields retain their meaning. -/

namespace App
open Engine Community Data Paint Font Row

/-- The platform, as the app uses it. -/
structure Io where
  screen : IO (Array UInt32)
  scroll : UInt32 → UInt32 → IO Float
  scrollBy : Float → IO Unit
  scrollTo : Float → IO Unit
  frame : Session.Show
  text : IO (String × Array UInt32)
  ime : Bool → IO Unit
  copy : String → IO Unit
  ctlPoll : IO (Array String)
  ctlReply : String → IO Unit
  nowUs : IO UInt64
  /-- Wall-clock minutes since the Unix epoch, and the local timezone's
  offset from UTC in minutes. -/
  wall : IO (Nat × Int) := do
    return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, 0)
  scan : Bool → IO Unit
  luma : IO (Array UInt32 × ByteArray)
  /-- A line for the platform's log (logcat, the device console, stderr). -/
  log : String → IO Unit := IO.eprintln
  /-- The native text field's text becomes t (left alone if it is t). -/
  setText : String → IO Unit := fun _ => pure ()
  poll : IO (Array UInt32) := pure #[]
  links : IO (Array String) := pure #[]
  motion : Array UInt32 → IO Unit := fun _ => pure ()
  appearance : Bool → UInt32 → IO Unit := fun _ _ => pure ()
  bars : UInt32 → UInt32 → Bool → Bool → IO Unit := fun _ _ _ _ => pure ()
  pickPhoto : UInt32 → IO Bool := fun _ => pure false
  photoResult : IO (Array UInt32 × ByteArray) := pure (#[], .empty)
  editorIo : Editor.Io := {}

/-- How far beyond each end of the viewport the list frame is drawn. -/
def over : Nat := 2048
/-- Keep the original image horizon while text gains more overscan. -/
def imageOver : Nat := 1024
/-- A row's height before it is measured. -/
def est : Nat := 150
/-- A window's rows on each side of its anchor. -/
def half : Nat := 100
def bottomPad : Nat := 12

/-- The already-decoded inputs of the displayed row. Desktop hover repaints
only this component, without a reader query, decode or raster work request. -/
structure RowPixels where
  data : RowData
  lay : Layout
  images : Array (Option Bitmap)
  version : Nat
  ready : List Bool

structure RowSt where
  data : RowData
  lay : Layout
  /-- What the current paint was made from: data version and which
  pictures were ready. -/
  painted : Nat × List Bool
  task : Option (Work.Handle Raster.Key Bitmap)
  shown : Option Bitmap
  ver : Nat
  /-- The board version its data came from (Reader). -/
  bver : Nat := 0
  /-- The shown paint darkened, for behind the reaction tray, and the
  version it was made from. -/
  dimmed : Option (Work.Handle Raster.Key Bitmap) := none
  dimVer : Nat := 0
  dimShown : Option Bitmap := none
  pixels : Option RowPixels := none
  /-- Captured inputs of the admitted paint, distinct from latest row data. -/
  paintFlight : Option Raster.RowPaint.Flight := none
  /-- An optimistic bitmap does not discharge the first committed paint. -/
  shownCommitted : Bool := false
  /-- Computed once when this exact raster ticket publishes. -/
  presentation : Option (Demand.Ticket Raster.Key × Option (Nat × Nat)) := none

/-- At most one accepted frame is awaiting native completion. -/
structure PresentationCandidate where
  message : Id
  frame : UInt64
  generation : Nat
  ticket : Demand.Ticket Raster.Key

abbrev ImgKey := FileImage.Key

/-- Which page is up: a conversation, or one of libquiet's other screens. -/
inductive PageId where
  | home | chat | getStarted | create | createName | joinChoice | openInvite | paste | scan | name | agree | waiting
  | requests | invite | switcher | profile | removeConfirm | duplicate | you | appearance | label
  | communitySettings | channelSettings | stub
  deriving DecidableEq, Repr, Inhabited

/-- Every page (Nav.depth: back reaches a root in fewer steps than this). -/
def PageId.all : List PageId :=
  [.home, .chat, .getStarted, .create, .createName, .joinChoice, .openInvite, .paste, .scan, .name, .agree,
   .waiting, .requests, .invite, .switcher, .profile, .removeConfirm, .duplicate, .you, .appearance, .label,
   .communitySettings, .channelSettings, .stub]

def PageId.drawer : PageId → Bool
  | .you | .appearance | .communitySettings | .channelSettings | .stub => true
  | _ => false

/-- Pages whose bodies use the native scroll view. -/
def PageId.scrolls (p : PageId) : Bool := p.drawer || p == .switcher

/-- The reaction sheet's state: quick or the catalogue, its category,
tone, search, and the grid's scroll (with a drag or fling in progress). -/
structure SheetSt where
  catalog : Bool := false
  cat : Nat := 0
  tone : Nat := 0
  query : String := ""
  searching : Bool := false
  scroll : Nat := 0
  drag : Option (Nat × Nat) := none
  lastY : Nat := 0
  lastT : Nat := 0
  vel : Float := 0
  deriving Inhabited

/-- Everything a page and its bar are drawn from, besides the font, the
background row and the camera's frame: the page cache's key. Communities
appear by their keys (acceptance op id, community id, name, …), so two
entries that share a name are still two keys. -/
structure PageIn where
  page : PageId
  setting : Theme.Setting := .system
  ownName : String := "…"
  ownId : String := ""
  communityId : String := ""
  devices : Nat := 1
  people : Nat := 0
  W : Nat
  h : Nat
  insetTop : Nat
  dim : Dim
  field : String
  /-- The full label shown (Full label), and its page. -/
  labelText : String := ""
  labelPage : Nat := 0
  refusal : Option String
  me : Kinds.Accepted.Key
  comms : Array Kinds.Accepted.Key
  /-- The join requests shown (not hidden), and how many there are in all. -/
  asking : Array Pages.Asking
  askingAll : Nat
  link : Option String
  members : Array (String × Bool)
  memberIds : Array String := #[]
  backEmpty : Bool
  drawerBack : Bool := false
  /-- Which camera frame is shown (a new frame, a new key). -/
  camFrame : Nat
  /-- The open profile: name, whether it is me, whether removed, and
  whether Remove is offered (Remove.offered); and the removal's stage
  (1, 2: asked once, twice; 3: sending; 4: refused) and refusal. -/
  profile : String × Bool × Bool × Bool := ("", false, false, false)
  removeStage : Nat := 0
  removeWhy : String := ""
  deriving BEq, Inhabited

structure St where
  io : Io
  theme : Theme.State := {}
  wide : Bool := false
  mobile : Bool := true
  editorFocused : Bool := false
  ownName : String := "…"
  ownDevices : Nat := 1
  window : Safe.Input := ⟨1080, 2400, {}, {}, {}⟩
  nowMs : Nat := 0
  noticeClock : Option (String × Nat) := none
  W : Nat
  Hs : Nat
  insetTop : Nat
  insetBot : Nat
  font : Font
  bgRow : ByteArray
  holdCache : Hold.MessageCache := none
  rd : Db
  wr : Writer
  dbPath : String := ""
  /-- The network, if this app runs one: the port its node listens on,
  and whether it is reached on loopback (two apps on one machine, in
  tests) instead of its LAN addresses. -/
  netCfg : Option (Nat × Bool) := none
  /-- The node's runner (Engine.Sync.Runner): it owns the writes once it
  runs. And the ids it stored since the frame last took them. -/
  net : Option Engine.Sync.Runner := none
  /-- The node starting, off the frame (its connection opened and its
  first reads made on a thread of its own). -/
  netBoot : Option (Task (Except IO.Error Engine.Sync.Runner)) := none
  /-- Writes the node's inbound channel could not take yet, in order. -/
  toNode : Array (List Op) := #[]
  /-- The journal's newest row this app has taken notice of. -/
  seen : Nat := 0
  me : Chaos.Me
  /-- One-shot command reads; persistent observations belong to Reader. -/
  intentReads : Nat := 0
  serviceSeen : Std.HashMap Id (List ByteArray) := {}
  out : Array Pending := #[]
  /-- Explicit local sends retain a bounded presentation obligation. -/
  ownSends : Presentation.Queue := {}
  presenting : Option PresentationCandidate := none
  /-- What the native text field holds, as last set or reported. -/
  native : String := ""
  editor : Editor.State := {}
  editorEpoch : Nat := 0
  editorContent : Nat := 0
  /-- The reader's board, and the frame's wants of it (Reader): the
  conversation's ids and rows are read there, not on the frame. -/
  sh : Reader.Shared
  /-- The reader's state while the frame runs its passes itself (no
  reader thread: the headless twins); none once a thread runs them. -/
  rst : Option Reader.St := none
  /-- The window of the conversation loaded (Reader.Want.window): its
  anchor (none: the newest), its rows newest first, and how many
  readable messages are newer and older than it, counted, not read: they
  take `est` each, as placeholders, until a window holds them. -/
  anchor : Option Pos := none
  ids : Array Pos := #[]
  /-- The outer collection and its independently owned child windows. -/
  roots : Array Pos := #[]
  clumps : Std.HashMap Id ClumpList.Window := {}
  clumpHeights : Std.HashMap Id Nat := {}
  /-- Flat cells are an ephemeral geometry projection, never a data cache. -/
  cellRoot : Std.HashMap Id Id := {}
  spacers : Std.HashSet Id := {}
  newer : Nat := 0
  older : Nat := 0
  total : Nat := 0
  people : Nat := 0
  peopleAll : Bool := true
  heights : Std.HashMap Id Nat := {}
  rows : Std.HashMap Id RowSt := {}
  imgs : Std.HashMap ImgKey (Work.Handle Raster.Key Bitmap) := {}
  raster : Work.Pool Raster.Key Bitmap
  rasterNeeds : Array (Demand.Need Raster.Key) := #[]
  queryNeeds : Array (Demand.Need Reader.Want) := #[]
  querySeen : Std.HashSet (Demand.Owner × Reader.Want × Bool) := {}
  /-- Diagnostic: mounted pictures waiting for their chunk bytes. Demand,
  never a timer, owns these queries. -/
  imgWaiting : Std.HashSet ImgKey := {}
  selected : Option Id := none
  b : Nat := 0
  imeH : Nat := 0
  input : Input.State := {}
  text : String := ""
  sel : Array UInt32 := #[0, 0, 0, 0]
  /-- Last published layers are retained by reference; compose only when opening a sheet. -/
  lastDisplay : Option (Array UInt32 × Array ByteArray × Array ByteArray × Array ByteArray) := none
  switcherBackdrop : Array ByteArray := #[]
  topBmp : Bitmap := default
  botBmp : Bitmap := default
  chromeKey : String := ""
  srcs : Option (Task (Array Image.Src)) := none
  /-- Chaos's writes, being made (ctl `chaos`). -/
  chaos : Option (Task (Array Job)) := none
  ctl : Array String := #[]
  frames : Nat := 0
  times : Array Nat := #[]
  paints : Nat := 0
  seed : Nat := 1
  dim : Dim := default
  /-- The reaction sheet, open on the message in `selected`. -/
  sheet : Option SheetSt := none
  catalog : Array Sheet.Item := #[]
  gridKey : String := ""
  gridRows : Std.HashMap Nat Bitmap := {}
  /-- Every community this device is in; `me` is the current one. -/
  comms : Array Chaos.Me := #[]
  /-- The current community: memory, not state. -/
  cur : Id := .empty  -- the current entry's acceptance (Kinds.Accepted.Me.acc)
  /-- The link pasted or scanned, while Agree & join is asked. -/
  invite : Option Community.Invite := none
  /-- This session's invite link per entry (acceptance; Add members). -/
  links : List (Id × String) := []
  /-- Photos attached in the composer: QOI bytes, size, and the chip. -/
  chips : Array (ByteArray × Nat × Nat × Composer.Chip) := #[]
  photoNext : Nat := 0
  photoSerial : UInt32 := 0
  photoRequest : Option Photo.Request := none
  photoWork : Option (Task (Option (ByteArray × Nat × Nat × Composer.Chip))) := none
  /-- The name chosen for joining (Choose a name). -/
  joinName : String := ""
  /-- The community being created, while its founder names themself. -/
  newCommunity : String := ""
  /-- The people of the current community (Direct messages on home):
names, and whether it is me. -/
  members : Array (String × Bool) := #[]
  /-- Each member's user (as `members`). -/
  memberIds : Array Id := #[]
  /-- Whether this device's user is an admin of the current community. -/
  amAdmin : Bool := false
  /-- The member whose profile is open: user, name, whether it is me. -/
  profileOf : Option (Id × String × Bool) := none
  /-- Entries already removed when told (or when the app started): their
removal is not announced again. -/
  goneSeen : List Id := []
  /-- Standing notices (libquiet's: no timeout; a tap puts the first
  away), e.g. "You've been removed from …". -/
  notices : List String := []
  /-- The removal flow (Remove.step). -/
  removal : Remove.Step := .idle
  /-- A toast and the frame it goes at (libquiet's: centred, about 3 s). -/
  toast : Option (String × Nat) := none
  page : PageId := .chat
  backStack : List PageId := []
  /-- A page's one-line field (the keyboard's text while a page shows one). -/
  field : String := ""
  /-- The full label a long press opened (Full label), and its page. -/
  labelText : String := ""
  labelPage : Nat := 0
  refusal : Option String := none
  hidden : List Id := []
  /-- The key of the page drawn (`drawPage`): it is redrawn when the key changes. -/
  pageKey : Option PageIn := none
  pageNow : Option Pages.Page := none
  /-- Initialize a settings viewport at its top once on entry, not on repaint. -/
  pageScrollStarted : Bool := false
  /-- Requests to join the current community no admission answers yet:
  the request's id, its fact, and its approvals' ids. -/
  asking : Array Kinds.Request.Data := #[]
  /-- Whether the camera is on (as last asked of the twin), and its newest
  frame as drawn on Join with QR code. -/
  camOn : Bool := false
  camView : Option Bitmap := none
  camFrame : Nat := 0
  /-- A camera frame being decoded, off the app's thread. -/
  decoding : Option (Task (Option String)) := none
  /-- Camera frames decoded so far (ctl `scans`). -/
  scans : Nat := 0

  life : Lifecycle.Mount := {}
  active : Bool := true
  surface : Bool := true
  /-- A message and its top-edge distance above the viewport bottom.
  `anchor` above remains the reader's window position. -/
  mark : Option (Id × Nat) := none
  restoreAnchor : Bool := false
  restorePos : Option Pos := none
  drafts : List (Id × String × List ByteArray) := []
  saved : Option Lifecycle.Checkpoint := none
  pendingLinks : List String := []
  queuedWrites : List ByteArray := []
  mountedPage : Option (PageId × Id) := none
  reader : Option Reader.Worker := none
  threaded : Bool := false
  /-- Teardown may outlive its deadline; these handles stay owned until
  finished. Foreground never starts another node before netStop finishes. -/
  netStop : Option (Task (Except IO.Error Unit)) := none
  /-- A failed runner's journal is decoded and submitted off the frame.
  Later local writes park until this submission has completed. -/
  netReplay : Option (Task (Except IO.Error Unit)) := none
  /-- Failed-runner teardown stays owned separately: it does not suppress
  active UI frames or local writing. Recovery never starts another runner. -/
  failedNetStop : Option (Task (Except IO.Error Unit)) := none
  readerStop : Option Reader.Worker := none
  retiredBoard : Option Reader.Shared := none
  paintStop : Array (Task Unit) := #[]

instance : Inhabited Io := ⟨⟨pure #[1080, 2400, 0, 0, 420], fun _ _ => pure 0, fun _ => pure (), fun _ => pure (), fun _ _ _ _ _ _ _ _ => pure #[],
  pure ("", #[]), fun _ => pure (), fun _ => pure (), pure #[], fun _ => pure (), pure 0, pure (0, 0), fun _ => pure (), pure (#[], .empty), IO.eprintln, fun _ => pure (), pure #[], pure #[], fun _ => pure (), fun _ _ => pure (), fun _ _ _ _ => pure (), fun _ => pure false, pure (#[], .empty), {}⟩⟩

abbrev M := StateT St IO

/-- The only observation door for UI components. It declares ownership
and consumes a published answer; it never performs database IO. -/
def query (scope : Component.Scope) (want : Reader.Want) : M (Option Reader.Val) := do
  let s ← get
  if !s.life.mounted then return none
  let need := scope.need want
  let id := (scope.owner, want, scope.visible)
  if !s.querySeen.contains id then
    modify fun s => { s with queryNeeds := s.queryNeeds.push need, querySeen := s.querySeen.insert id }
  return ((← s.sh.board.get).get? want).map (·.1)

instance : Component.Queries M := ⟨query⟩

/-- Attachment demand, for diagnostics and lifecycle regression tests. -/
def St.pictureNeeds (s : St) : Array (Demand.Need Reader.Want) :=
  s.queryNeeds.filter fun n => match n.key with
    | .picture .. | .slices .. | .attachment .. => true
    | _ => false

/-- Headless accounting includes the reader state driven by the twin. -/
def St.queryReads (s : St) : Nat := s.intentReads + (s.rst.map (·.live.reads)).getD 0

def c (s : St) : Id := s.me.c

/-- The page and the back stack, as Nav has them. -/
def St.nav (s : St) : Nav.Nav PageId := ⟨s.page, s.backStack⟩

/-- The page and the back stack, set to a Nav step's. -/
def St.withNav (s : St) (n : Nav.Nav PageId) : St := { s with editorEpoch := s.editorEpoch + 1, page := n.page, backStack := n.stack, ownSends := if n.page == .chat then s.ownSends else {}, presenting := if n.page == .chat then s.presenting else none }


end App

end

section

/- Bounded lifecycle polling. Only suspend may call waitFor; normal frames
poll completed handles once. A timed-out handle remains owned for a later
poll, so foreground cannot race a still-stopping node. No new axioms. -/

namespace App

/-- One absolute deadline shared by all teardown stages. The readiness
check must itself be nonblocking. Reserve the last poll interval. -/
def waitFor (deadline : Nat) (ready : M Bool) : M Bool := do
  repeat
    if (← IO.monoMsNow) + 5 ≥ deadline then return false
    if ← ready then return true
    IO.sleep 1

/-- Runs on its own dedicated thread, never on the frame. It retains a
late boot's Runner until stop has closed its listener and sessions. -/
def stopNodes (boot : Option (Task (Except IO.Error Engine.Sync.Runner)))
    (net : Option Engine.Sync.Runner) : IO Unit := do
  if let some r := net then r.stop
  if let some t := boot then
    if let .ok r ← IO.wait t then r.stop

/-- Wiring controls: never called by the app. -/
def waitsOnNode (r : Engine.Sync.Runner) (ops : List Engine.Op) : IO Unit := r.write ops
def waitsOnTask (t : Task Unit) : IO Unit := discard <| IO.wait t
def waitsOnDeadline : M Bool := waitFor 1000 (pure false)

end App

end

section

/-
App lifecycle hooks: checkpoint local UI ops, revoke the mounted page,
restore drafts, rebuild geometry. Root reads run on the app thread;
unmount revokes the reader and retires its board and pure workers.
Only suspend polls for quiescence, with one absolute deadline. `page_round` checks the durable page tag.
-/

namespace App
open Engine Community Data Paint Font Row

def PageId.code : PageId → Nat
  | .home => 0 | .chat => 1 | .getStarted => 2 | .create => 3 | .createName => 4
  | .joinChoice => 5 | .openInvite => 6 | .paste => 7 | .scan => 8 | .name => 9
  | .agree => 10 | .waiting => 11 | .requests => 12 | .invite => 13 | .switcher => 14
  | .profile => 15 | .removeConfirm => 16 | .duplicate => 17 | .you => 18 | .appearance => 19 | .label => 20
  | .communitySettings => 21 | .channelSettings => 22 | .stub => 23

def PageId.ofCode : Nat → PageId
  | 0 => .home | 1 => .chat | 2 => .getStarted | 3 => .create | 4 => .createName
  | 5 => .joinChoice | 6 => .openInvite | 7 => .paste | 8 => .scan | 9 => .name
  | 10 => .agree | 11 => .waiting | 12 => .requests | 13 => .invite | 14 => .switcher
  | 15 => .profile | 16 => .removeConfirm | 17 => .duplicate | 18 => .you | 19 => .appearance | 20 => .label
  | 21 => .communitySettings | 22 => .channelSettings | 23 => .stub | _ => .getStarted

theorem page_round (p : PageId) : PageId.ofCode p.code = p := by cases p <;> rfl

def fieldPage (p : PageId) : Bool :=
  p == .create || p == .createName || p == .paste || p == .name

/-- Which string the native field edits: a page's one-line field, the
emoji sheet's search, the composer's draft, or none (no visible field,
or the sheet open without its search: the draft is left as it is). -/
inductive TextTarget where
  | field | query | draft | none
  deriving BEq, DecidableEq, Repr

def textTarget (s : St) : TextTarget :=
  if fieldPage s.page then .field
  else if s.page != .chat then .none
  else match s.sheet with
    | some sh => if sh.searching then .query else .none
    | none => .draft

/-- What the native field is to hold now, if anything. -/
def nativeText (s : St) : Option String :=
  match textTarget s with
  | .field => some s.field
  | .query => s.sheet.map (·.query)
  | .draft => some s.text
  | .none => none

/-- A `.text` event's text and selection into the string the field edits. -/
def textInto (s : St) (t : String) (sel : Array UInt32) : St :=
  match textTarget s with
  | .field => { s with field := t, refusal := none, pageKey := none }
  | .query => match s.sheet with
    | some sh => { s with sheet := some { sh with query := t, scroll := 0 } }
    | none => s
  | .draft => { s with text := t, sel := if sel.size == 4 then sel else #[0, 0, 0, 0] }
  | .none => s

/-- **A text event edits the string the field edits, and nothing that
chooses it**: the target is the same after. -/
theorem into_target (s : St) (t : String) (sel : Array UInt32) : textTarget (textInto s t sel) = textTarget s := by
  unfold textInto
  cases hf : fieldPage s.page
  · by_cases hc : s.page = .chat
    · cases hs : s.sheet with
      | none => simp [textTarget, fieldPage, hf, hc, hs]
      | some sh => by_cases hq : sh.searching <;> simp [textTarget, fieldPage, hf, hc, hs, hq]
    · simp [textTarget, hf, hc]
  · simp [textTarget, hf]

/-- **After a text event the field holds what the app holds** (unless it
edits nothing), so `syncText` sets nothing back: no echo, no lost text. -/
theorem into_native (s : St) (t : String) (sel : Array UInt32) (h : textTarget s ≠ .none) :
    nativeText (textInto s t sel) = some t := by
  unfold nativeText
  rw [into_target]
  unfold textInto
  cases hf : fieldPage s.page
  · by_cases hc : s.page = .chat
    · cases hs : s.sheet with
      | none => simp [textTarget, fieldPage, hf, hc, hs]
      | some sh => by_cases hq : sh.searching <;> simp_all [textTarget, fieldPage]
    · simp_all [textTarget, fieldPage]
  · simp [textTarget, hf]

/-- A field's durable meaning, independent of mount and pixel geometry. -/
def editorTarget (s : St) : String :=
  s!"{s.page.code}|{repr s.cur.data.toList}|{repr s.me.acc.data.toList}|{repr (textTarget s)}|{repr (s.selected.map (·.data.toList))}"

/-- Semantic incarnation: resizing/IME animation is deliberately absent. -/
def editorContext (s : St) : String := s!"{s.editorEpoch}|{editorTarget s}"
def editorKey (s : St) : String := editorContext s

/-- Photos/chips have a separate captured revision; adding one never installs
an older text value over typing in the same Field. -/
def editorContentKey (s : St) : String :=
  s!"{s.editorContent}|{s.photoRequest.map (·.token)}|{s.photoRequest.map (·.selected)}"

def readEditor : M (Option Editor.Latest) := do
  let s ← get
  if s.editor.enabled == some false then return none
  let response ← s.io.editorIo.exchange 0 s.editor.owner.toUInt64 s.editor.revision ""
  if response.2[0]? == some 2 then
    modify fun s => { s with editor := { s.editor with enabled := some true } }
    return none
  let value := Editor.latest response
  modify fun s => { s with editor := { s.editor with enabled := some value.isSome } }
  return value

/-- Adopt only the Field installed for this exact semantic incarnation. -/
def adoptEditor (value : Editor.Latest) : M Unit := do
  let s ← get
  if value.owner != s.editor.owner.toUInt64 || s.editor.target != editorTarget s then return
  if value.revision != s.editor.revision || value.consumed then
    modify fun s => { textInto s (if value.consumed then "" else value.text) value.selection with
      native := if value.consumed then "" else value.text, editor := { s.editor with revision := value.revision, clear := if value.clearing == 0 then none else s.editor.clear } }
  else if value.clearing == 0 then
    modify fun s => { s with editor := { s.editor with clear := none } }

/-- Install/revoke is asynchronous. A new Activity's empty Field is reinstalled
without relying on the previous Activity's text memo. -/
def refreshEditor : M Unit := do
  let some value ← readEditor | return
  let s ← get
  if !s.active || !s.surface || !s.life.mounted then
    discard <| s.io.editorIo.exchange 3 0 0 ""
    modify fun s => { s with editor := { s.editor with key := "", clear := none } }
    return
  adoptEditor value
  let s ← get
  -- The exact consumed action owns its clear until Java compares revisions.
  -- A photo/content update cannot supersede that receipt with an installation.
  if s.editor.clear.isSome && value.clearing != 0 then return
  let changed := s.editor.key != editorKey s || value.exhausted
  if changed then
    let some next := s.editor.next | do
      discard <| s.io.editorIo.exchange 3 0 0 ""
      return
    modify fun s => { s with editor := { s.editor with owner := next.toNat, key := editorKey s, context := editorContext s, target := editorTarget s, handoff := s.editor.owner != 0 && s.editor.target == editorTarget s, revision := 0, clear := none } }
  let owner := (← get).editor.owner.toUInt64
  let s ← get
  if s.editor.contentKey != editorContentKey s then
    if s.editor.content + 1 ≥ 18446744073709551616 then
      discard <| s.io.editorIo.exchange 3 0 0 ""
      return
    modify fun s => { s with editor := { s.editor with contentKey := editorContentKey s, content := s.editor.content + 1 } }
  let s ← get
  if changed || !value.ready || value.owner != owner then
    discard <| s.io.editorIo.exchange (if s.editor.handoff then 5 else 1) owner s.editor.content.toUInt64 ((nativeText s).getD s.native)
  else
    discard <| s.io.editorIo.exchange 6 owner s.editor.content.toUInt64 ""

/-- Pending commands coalesce; the latest installed revision is their receipt.
No synchronous UI-thread call or receipt wait occurs on the frame thread. -/
def syncEditor : M Bool := do
  refreshEditor
  let s ← get
  if s.editor.enabled != some true then return false
  if s.editor.clear.isSome || s.editor.revision == 0 then return true
  if let some text := nativeText s then
    if text != s.native then
      discard <| s.io.editorIo.exchange 2 s.editor.owner.toUInt64 s.editor.revision text
  return true

/-- Bottom coordinates shared with the conversation's anchor. -/
def rowBottom (s : St) (x : Id) : Option Nat := Id.run do
  let mut y := bottomPad + s.newer * est
  for (_, m) in s.ids do
    if m == x then return some y
    y := y + s.heights.getD m est
  return none

def captureAnchor (s : St) : Option (Id × Nat) := Id.run do
  if s.page != .chat then return s.mark
  if s.b ≤ 4 then return none
  if let some (x, above) := s.mark then
    if let some bot := rowBottom s x then
      let top := bot + s.heights.getD x est
      if s.b ≤ top && top - s.b == above then return s.mark
  let mut y := bottomPad + s.newer * est
  for (_, x) in s.ids do
    let h := s.heights.getD x est
    if y ≤ s.b && s.b < y + h then return some (x, y + h - s.b)
    y := y + h
  return s.mark

def stashDraft (s : St) : St :=
  if s.me.acc.isEmpty then s else
  { s with drafts := (s.me.acc, s.text, s.chips.toList.map (·.1)) :: s.drafts.filter (·.1 != s.me.acc) }

def removalBytes (r : Remove.Step) : ByteArray :=
  Codec.encode (match r with
    | .idle => (0, .empty, ByteArray.empty) | .first u => (1, u, .empty)
    | .second u => (2, u, .empty) | .sending u => (3, u, .empty)
    | .failed u why => (4, u, why.toUTF8) : Nat × Id × ByteArray)

def removalFrom (b : ByteArray) : Remove.Step :=
  match (Codec.decode b : Option (Nat × Id × ByteArray)) with
  | some (1, u, _) => .first u | some (2, u, _) => .second u | some (3, u, _) => .sending u
  | some (4, u, why) => .failed u (String.fromUTF8! why) | _ => .idle

/-- A fling can stop inside an unloaded range. Persist that collection's
real root so cold restoration cannot submit a spacer to the query API. -/
def checkpointAnchor (s : St) : Option (Id × Nat) :=
  s.mark.bind fun (x, off) =>
    if s.spacers.contains x then s.cellRoot[x]?.map (·, 0) else some (x, off)

def checkpoint (s : St) : Lifecycle.Checkpoint :=
  let s := { stashDraft s with mark := checkpointAnchor s }
  let a := s.mark.getD (.empty, 0)
  (1, s.page.code, s.cur, a.1, a.2,
    [Codec.encode (s.backStack.map PageId.code), s.field.toUTF8,
     ((s.invite.map (·.text)).getD "").toUTF8, s.joinName.toUTF8, s.newCommunity.toUTF8,
     removalBytes s.removal,
     Codec.encode (s.profileOf.toList.map fun (u, n, me) => (u, n.toUTF8, me)),
     Codec.encode (s.drafts.map fun (a, t, bs) => (a, t.toUTF8, bs)), Codec.encode s.anchor,
     Codec.encode (s.links.map fun (a, l) => (a, l.toUTF8)), Codec.encode s.queuedWrites,
     Codec.encode (s.mark.bind fun (x, _) => (s.ids.find? (·.2 == x)).orElse fun _ => s.roots.find? (·.2 == x)),
     (Theme.encode s.theme.setting).toUTF8, Codec.encode (s.labelText.toUTF8, s.labelPage),
     Codec.encode (s.mark.bind fun (x, _) => s.cellRoot[x]?.bind fun r => s.roots.find? (·.2 == r))])

/-- Called only by the writer thread. Both writes are idempotent when its
checkpoint retry meets a transient SQLite lock. -/
def commitCheckpoint (db : Db) (bytes : ByteArray) : IO Unit := do
  if let some (_, _, _, _, _, bs) := (Codec.decode bytes : Option Lifecycle.Checkpoint) then
    if let some value := bs[12]? then Theme.save db (Theme.decode (String.fromUTF8! value))
  Lifecycle.save db bytes

/-- A changed checkpoint, handed to the writer's thread, which commits
it. The frame never commits: it holds its read transaction all turn, and
a node's `wal_checkpoint(TRUNCATE)` holds the write lock until every
reader finishes, so a commit here waited on the frame itself until
SQLite's busy timeout threw out of `step`. -/
def saveCheckpoint : M Unit := do
  let s ← get
  if s.dbPath.isEmpty then return
  let cp := checkpoint s
  if s.saved == some cp then return
  s.wr.save (Codec.encode cp)
  modify fun s => { s with saved := some cp }

/-- `saveCheckpoint` as it was: committed on the frame's thread while
its read transaction is open. The `block` rule's negative control (`waits` in
tests/wiring.txt); never run. -/
def saveWaits : M Unit := do
  let s ← get
  Lifecycle.save s.rd (Codec.encode (checkpoint s))

def restoreChips (s : St) (bs : List ByteArray) : Array (ByteArray × Nat × Nat × Composer.Chip) :=
  (bs.filterMap fun b => do
    let src ← Image.decode b
    return (b, src.w, src.h, ⟨Image.square src (s.dim.px 64) (Palette.color s.dim.theme .bg), s!"{Arrival.humanBytes b.size}"⟩)).toArray

def useDraft (s : St) : St :=
  let (_, t, bs) := (s.drafts.find? (·.1 == s.me.acc)).getD (.empty, "", [])
  { s with editorContent := s.editorContent + 1, text := t, chips := restoreChips s bs, sel := #[t.length.toUInt32, t.length.toUInt32, 0, 0] }

/-- Called after switchToAcc selected the saved acceptance. A removed or
missing acceptance is never restored by this function. -/
def applyCheckpoint (s : St) (cp : Lifecycle.Checkpoint) : St := Id.run do
  let (_, p, _, x, off, bs) := cp
  let b := fun i => bs[i]?.getD .empty
  let str := fun i => String.fromUTF8! (b i)
  let drafts := ((Codec.decode (b 7) : Option (List (Id × ByteArray × List ByteArray))).getD []).map
    fun (a, t, pics) => (a, String.fromUTF8! t, pics)
  let profile := ((Codec.decode (b 6) : Option (List (Id × ByteArray × Bool))).getD []).head?.map
    fun (u, n, me) => (u, String.fromUTF8! n, me)
  let stack := ((Codec.decode (b 0) : Option (List Nat)).getD []).map PageId.ofCode
  let (label, labelPage) := (Codec.decode (b 13) : Option (ByteArray × Nat)).getD (.empty, 0)
  let nav := match stack.reverse with
    | [] => Nav.reset (PageId.ofCode p)
    | x :: xs => xs.foldl (fun n p => Nav.go p n) (Nav.reset x)
  let s := { s.withNav (Nav.go (PageId.ofCode p) nav) with
    field := str 1, invite := Community.Invite.parse (str 2), joinName := str 3, newCommunity := str 4,
    removal := removalFrom (b 5), profileOf := profile, drafts,
    labelText := String.fromUTF8! label, labelPage,
    mark := if x.isEmpty then none else some (x, off), restoreAnchor := !x.isEmpty,
    restorePos := (Codec.decode (b 11) : Option (Option Pos)).getD none,
    anchor := (Codec.decode (b (if bs.length > 14 then 14 else 11)) : Option (Option Pos)).getD
      ((Codec.decode (b 8) : Option (Option Pos)).getD none),
    links := ((Codec.decode (b 9) : Option (List (Id × ByteArray))).getD []).map fun (a, l) => (a, String.fromUTF8! l),
    saved := some cp, mountedPage := none }
  return useDraft s

/-- Pure workers may finish, but their results cannot publish after
revocation. Retain them for suspend's bounded quiescence check. -/
def retireRow (r : RowSt) : M Unit := do
  for t in r.task.toList ++ r.dimmed.toList do
    modify fun s => { s with paintStop := s.paintStop.push (t.result.map fun _ => ()) }

def retirePaints (s : St) : M Unit := do
  s.raster.reconcile []
  for (_, r) in s.rows.toList do retireRow r
  for (_, t) in s.imgs.toList do
    modify fun s => { s with paintStop := s.paintStop.push (t.result.map fun _ => ()) }
  if let some t := s.decoding then
    modify fun s => { s with paintStop := s.paintStop.push (t.map fun _ => ()) }

/-- Acts already judged by the reader belong to the store. Retiring a
page never discards their writes or runs their UI continuations. -/
def parkDone (sh : Reader.Shared) : M Unit := do
  let done ← sh.done.modifyGet fun ds => (ds, #[])
  let writes := done.filterMap fun (_, w) => w.map (·.ops)
  if writes.isEmpty then return
  modify fun s => { s with
    toNode := s.toNode ++ writes, queuedWrites := s.queuedWrites ++ writes.toList.flatten.map Op.bytes }
  saveCheckpoint

/-- Replay accepted local bytes through the ordinary writer. The journal
can still contain operations already committed before the runner failed;
the store identifies those by the same operation ID. -/
def replayNodeWrites (writer : Writer) (bytes : List ByteArray) : IO Unit := do
  let ops := bytes.filterMap Op.decode
  unless ops.isEmpty do writer.submit ⟨ops, true⟩

/-- The loop's completion releases its SQLite ownership. Native socket
teardown remains separately owned by `netStop`; a delayed OS callback must
not delay the journal's handoff to the ordinary writer. A late boot is
included because suspend may begin before the Runner handle is returned. -/
def replayStoppedNodeWrites (boot : Option (Task (Except IO.Error Engine.Sync.Runner)))
    (net : Option Engine.Sync.Runner) (writer : Writer) (bytes : List ByteArray) : IO Unit := do
  if let some r := net then discard <| IO.wait r.done
  if let some task := boot then
    if let .ok r ← IO.wait task then discard <| IO.wait r.done
  replayNodeWrites writer bytes

/-- Observe a finished installed runner before offering any further work.
The journal covers channel-admitted writes as well as parked ones. A failure
racing a later offer is recovered at the next observation. No check-and-offer
atomicity or exactly-once IO across an outer StateT rollback is claimed. -/
def recoverNode : M Unit := do
  let s ← get
  let some r := s.net | return
  unless ← IO.hasFinished r.done do return
  let replay ← IO.asTask (prio := .dedicated) (replayNodeWrites s.wr s.queuedWrites)
  let stopping ← IO.asTask (prio := .dedicated) (stopNodes none (some r))
  modify fun s => { s with
    net := none, netBoot := none, netCfg := none, toNode := #[],
    netReplay := some replay, failedNetStop := some stopping,
    notices := s.notices ++ ["Sync stopped. Changes will retry locally. Restart Quiet to reconnect."] }

/-- A single nonblocking poll. A result is taken only after completion. -/
def pollRetired : M Unit := do
  let s ← get
  if let some t := s.netReplay then
    if ← IO.hasFinished t then
      modify fun s => { s with netReplay := none }
      if let .error _ := t.get then
        modify fun s => { s with notices := s.notices ++
          ["Local recovery failed. Restart Quiet to retry queued changes."] }
  if let some t := s.failedNetStop then
    if ← IO.hasFinished t then
      modify fun s => { s with failedNetStop := none }
      if let .error _ := t.get then
        modify fun s => { s with notices := s.notices ++
          ["Sync could not finish stopping. Restart Quiet before reconnecting."] }
  if let some t := s.netStop then
    if ← IO.hasFinished t then
      match t.get with
      | .ok _ => modify fun s => { s with netStop := none }
      | .error e => throw e
  if let some w := s.readerStop then
    if ← IO.hasFinished w.done then
      match w.done.get with
      | .ok r =>
        if let some sh := s.retiredBoard then parkDone sh
        modify fun s => { s with readerStop := none, retiredBoard := none, rst := some { rd := r.rd } }
      | .error e => throw e
  let mut pending := #[]
  for t in s.paintStop do
    unless ← IO.hasFinished t do pending := pending.push t
  modify fun s => { s with paintStop := pending }

def unmountState (s : St) : St :=
  { stashDraft s with
    editorEpoch := s.editorEpoch + 1, editor := { s.editor with key := "", clear := none },
    mark := captureAnchor s, life := s.life.unmount, input := Input.revoke s.input,
    rows := {}, imgs := {}, imgWaiting := {},
    sheet := none, selected := none, camOn := false, camView := none, decoding := none,
    pageNow := none, pageKey := none, chromeKey := "", imeH := 0, mountedPage := none,
    rasterNeeds := #[], queryNeeds := #[], querySeen := {} }

/-- Revoke before detaching the board. An issued SQLite read may finish
on the old refs, but no subsequent query or publication is authorized. -/
def stopReader : M Unit := do
  let s ← get
  if let some w := s.reader then w.requestStop
  parkDone s.sh
  let out ← s.sh.out.get
  s.sh.acts.set #[]
  s.sh.setWants #[]
  s.sh.board.set {}
  s.sh.out.set #[]
  s.sh.notes.set #[]
  s.sh.seen.set 0
  let sh ← Reader.Shared.new s.wr.count
  sh.out.set out
  modify fun s => { s with
    sh, reader := none,
    readerStop := s.reader.orElse fun _ => s.readerStop,
    retiredBoard := if s.reader.isSome then some s.sh else s.retiredBoard,
    rst := s.rst.map fun r => { rd := r.rd } }
  pollRetired

def resumeReader : M Unit := do
  pollRetired
  let s ← get
  if !s.threaded || !s.active || !s.surface || s.netStop.isSome || s.reader.isSome then return
  if let some r := s.rst then
    let w ← Reader.Worker.start s.sh r
    modify fun s => { s with reader := some w, rst := none }

/-- The unmount barrier used by navigation and suspension. -/
def leavePage : M Unit := do
  let s ← get
  if s.editor.enabled == some true then discard <| s.io.editorIo.exchange 3 0 0 ""
  s.io.ime false
  if let some p := s.input.press then s.io.motion { p.first with phase := 3 }.words
  if s.camOn then s.io.scan false
  stopReader
  retirePaints s
  modify unmountState

/-- Mount after refreshing the viewport. -/
def mountPage : M Unit := do
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome then return
  if s.mountedPage == some (s.page, s.cur) then resumeReader; return
  if s.mountedPage.isSome then leavePage
  modify fun s => { s with life := s.life.mount, mountedPage := some (s.page, s.cur) }
  let s ← get
  resumeReader
  let t := if fieldPage s.page then s.field else s.text
  s.io.setText t
  modify fun s => { s with native := t }

/-- The callback's lease is captured when queued. -/
def owned (l : Lifecycle.Lease) (action : M α) : M (Option α) := do
  Lifecycle.owned (← get).life l action

/-- Re-layout every mounted row and invalidate its old pixels. -/
def resizeContent (sc : Array UInt32) : M Unit := do
  let s ← get
  let w := (sc[0]?.getD s.W.toUInt32).toNat
  let h := (sc[1]?.getD s.Hs.toUInt32).toNat
  let it := (sc[2]?.getD s.insetTop.toUInt32).toNat
  let ib := (sc[3]?.getD s.insetBot.toUInt32).toNat
  let dpi := (sc[4]?.getD s.dim.dpi.toUInt32).toNat
  if w == s.W && h == s.Hs && it == s.insetTop && ib == s.insetBot && dpi == s.dim.dpi then return
  if let some p := s.input.press then s.io.motion { p.first with phase := 3 }.words
  retirePaints s
  let font ← if dpi == s.dim.dpi then pure s.font else Font.load (density := dpi)
  let font := font.atSize (((if s.wide then 14 else 15) * dpi + 80) / 160)
  let dm : Dim := ⟨dpi, font.cell, s.dim.theme, none⟩
  let mut rows := s.rows
  let mut heights := if w == s.W && dpi == s.dim.dpi then s.heights else {}
  for (x, r) in s.rows.toList do
    let data := { r.data with wide := s.wide }
    let lay := Row.layout font dm w data
    rows := rows.insert x { r with
      data, lay, ver := r.ver + 1, task := none, shown := none,
      dimmed := none, dimShown := none }
    heights := heights.insert x lay.h
  modify fun s => { s with
    W := w, Hs := h, insetTop := it, insetBot := ib, font, dim := dm, input := Input.revoke s.input,
    bgRow := solid (Palette.color s.dim.theme (if s.wide then .panel else .bg)) w, rows, heights, imgs := {}, imgWaiting := {},
    clumpHeights := if w == s.W && dpi == s.dim.dpi then s.clumpHeights else {},
    life := { s.life with generation := s.life.generation + 1 },
    mark := captureAnchor s, restoreAnchor := true, pageKey := none, pageNow := none,
    chromeKey := "", gridKey := "", gridRows := {} }

/-- Apply the latest safe-area snapshot after resizeContent has retired and
re-laid out mounted rows. This is the handler used by the live frame. -/
def screenChanged (sc : Array UInt32) (now : Nat) (s : St) : St :=
  let window := SafeFrame.report sc s.imeH
  let safe := Safe.content { window with ime := {} }
  let changed := window != s.window
  { s with
    window := window, W := safe.w, Hs := window.h, insetTop := safe.y,
    insetBot := window.h - safe.bottom, imeH := window.ime.bottom, nowMs := now,
    pageKey := if changed then none else s.pageKey,
    chromeKey := if changed then "" else s.chromeKey,
    gridRows := if changed then {} else s.gridRows }

def resize (sc : Array UInt32) : M Unit := do
  let s ← get
  let window := SafeFrame.report sc s.imeH
  let safe := Safe.content { window with ime := {} }
  resizeContent #[safe.w.toUInt32, window.h.toUInt32, safe.y.toUInt32,
    (window.h - safe.bottom).toUInt32, sc[4]?.getD s.dim.dpi.toUInt32]
  -- Insets can move content sideways without changing its width. Revoke
  -- the displayed input contexts for every changed safe-area/IME snapshot.
  if window != s.window && (← get).life.generation == s.life.generation then
    if let some p := s.input.press then s.io.motion { p.first with phase := 3 }.words
    modify fun s => { s with
      input := Input.revoke s.input,
      life := { s.life with generation := s.life.generation + 1 } }
  modify (screenChanged sc ((← s.io.nowUs).toNat / 1000))

/-- The native field may have changed in the same poll as background.
Save its final text before hiding it; search text is not a composer draft. -/
def captureInput : M Unit := do
  let s ← get
  if !s.active || !s.surface || !s.life.mounted then return
  if let some value ← readEditor then
    adoptEditor value
    return
  -- A failed owned read must preserve the last known draft. The legacy text
  -- getter has no owner and cannot safely substitute for this snapshot.
  if (← get).editor.enabled == some true then return
  if fieldPage s.page then
    let (field, _) ← s.io.text
    modify fun s => { s with field }
  else if s.page == .chat && !(s.sheet.map (·.searching)).getD false then
    let (text, _) ← s.io.text
    modify fun s => { s with text }

/-- A finished producer's writes are store-owned, even after unmount. -/
def parkChaos : M Unit := do
  let s ← get
  if let some t := s.chaos then
    if ← IO.hasFinished t then
      let jobs := t.get
      let ops := jobs.toList.flatMap (·.ops)
      modify fun s => { s with
        chaos := none, toNode := s.toNode ++ jobs.map (·.ops), queuedWrites := s.queuedWrites ++ ops.map Op.bytes }
      s.wr.busy.modify (· - 1)
      saveCheckpoint

/-- Reap only finished work; used by background polls and foreground too. -/
def reap : M Unit := do
  pollRetired
  if !(← get).life.mounted then parkChaos

/-- One deadline, not one timeout per worker. On expiry, pending handles
and every parked write remain owned. Resume only polls; it never joins. -/
def suspend (budget : Nat := 250) : M Unit := do
  let deadline := (← IO.monoMsNow) + budget
  recoverNode
  captureInput
  let s ← get
  if s.net.isSome || s.netBoot.isSome then
    let stopping ← IO.asTask (prio := .dedicated) (stopNodes s.netBoot s.net)
    let replay ← IO.asTask (prio := .dedicated)
      (replayStoppedNodeWrites s.netBoot s.net s.wr s.queuedWrites)
    -- The journal includes both channel-admitted and parked operations.
    -- Later submissions park afresh until this handoff has completed.
    modify fun s => { s with netStop := some stopping, netReplay := some replay, toNode := #[] }
  modify fun s => { s with net := none, netBoot := none, restoreAnchor := s.mark.isSome }
  s.wr.setPaused false
  leavePage
  saveCheckpoint
  discard <| waitFor deadline do
    reap
    let s ← get
    return s.netStop.isNone && s.netReplay.isNone && s.failedNetStop.isNone &&
      s.readerStop.isNone && s.paintStop.isEmpty &&
      s.chaos.isNone && (← s.wr.busy.get) == 0 && (← s.wr.saveDone)

end App

end


section

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

namespace App
open Engine Community Data Paint Font Row

/-- Rebuild every colour-bearing cache from the new effective theme.
Old asynchronous tasks lose their references and cannot publish later. -/
def themed (s : St) (theme : Theme.State) : St :=
  let dm := s.dim
  let dm := { dm with theme := Theme.effective theme }
  { s with
    theme := theme
    dim := dm
    bgRow := solid (Palette.color (Theme.effective theme) (if s.wide then .panel else .bg)) s.W,
    rows := {}, imgs := {}, imgWaiting := {}, gridRows := {}, gridKey := "",
    chips := s.chips.map fun (bytes, w, h, chip) =>
      let thumb := match Image.decode bytes with
        | some src => Image.square src (s.dim.px 64) (Palette.color (Theme.effective theme) .bg)
        | none => Bitmap.blank (s.dim.px 64) (s.dim.px 64) (solid (Palette.color (Theme.effective theme) .bg) (s.dim.px 64))
      (bytes, w, h, { chip with thumb }),
    topBmp := default, botBmp := default, chromeKey := "", pageNow := none, pageKey := none }

def setTheme (setting : Theme.Setting) : M Unit := do
  let s ← get
  set (themed s { s.theme with setting })
  saveCheckpoint
  let s ← get
  s.io.appearance (Theme.effective s.theme == .dark) (Palette.color s.dim.theme .bg)

def systemTheme (system : Theme.Value) : M Unit := do
  let s ← get
  let theme := { s.theme with system }
  if Theme.effective theme != Theme.effective s.theme then
    set (themed s theme)
  else modify fun s => { s with theme }
  let s ← get
  s.io.appearance (Theme.effective s.theme == .dark) (Palette.color s.dim.theme .bg)

/-! ## One-shot transactions

Visual components cannot perform store reads: M has no Reads instance.
Commands needing an authoritative snapshot run the same Reader/Reads
interpreter once. These are transaction reads, never UI subscriptions. -/

def transaction (action : Reader.RM α) : M α := do
  let s ← get
  let (a, r) ← action.run { rd := s.rd, out := s.out, known := s.comms }
  modify fun s => { s with intentReads := s.intentReads + r.live.reads }
  return a

def intentView (view : View Fact α) : M α :=
  transaction do return (← readView view #[]).1

/-! ## The native text field

One native field edits one of the app's strings at a time. The `.text`
event writes the field's text into it (`textInto`), and each frame sets
the field to it (`syncText`), so the field and the app's string never
drift: a page change never empties the composer's draft by way of the
field (TextLaws in this file: `into_target`, `into_native`). -/

/-- Set the native field to the string it edits, when they differ. -/
def syncText : M Unit := do
  if ← syncEditor then return
  let s ← get
  if let some t := nativeText s then
    if t != s.native then
      s.io.setText t
      modify fun s => { s with native := t }

/-- Message m's row: its view (Kinds.Message.readOwn: the claimed time, in
UTC minutes), shown at the local time (the platform's timezone). -/
def readRow (m : Id) : M (Option (RowData × Array Q)) := do
  let s ← get
  if !s.life.mounted then return none
  return (s.rows[m]?).map fun r => (r.data, #[])

/-! ## Writing -/

/-- Notices made by this node itself: a change to the outbox, at its ops'
positions under their keys. -/
def noticeLocal (ps : List Pending) : M Unit := do
  let fs := Pending.filings ps
  (← get).sh.notes.modify (· ++ fs)

/-- Offer writes to the node's inbound channel, in order, without waiting:
each that fits is in; the rest, from the first that did not fit, stay
(the dedicated local-write channel is bounded, so it can be full
while sync is busy). It is `NodeOffer.offerList` over the channel's
`trySend`: NodeOffer.offer_split and offer_runs say no write is lost,
sent twice or overtaken, whatever the channel answers. -/
def offerAll (ch : Std.CloseableChannel.Sync (List Op)) (q : Array (List Op)) : IO (Array (List Op)) := do
  return (← NodeOffer.offerList (fun w => (ch.trySend w : IO Bool)) q.toList).toArray

/-- Re-offer parked writes in submission order, only after teardown. -/
def flushNode : M Unit := do
  recoverNode
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome || s.netReplay.isSome || s.toNode.isEmpty then return
  let some r := s.net | do
    if s.netCfg.isNone && s.netBoot.isNone then
      for ops in s.toNode do s.wr.submit ⟨ops, true⟩
      modify fun s => { s with toNode := #[] }
    return
  let rest ← offerAll r.writes s.toNode
  modify fun s => { s with toNode := rest }

/-- Store-owned writes survive unmount and are journaled before offering. -/
def submit (j : Job) : M Unit := do
  if j.ops.isEmpty then return
  let s ← get
  modify fun s => { s with queuedWrites := s.queuedWrites ++ j.ops.map Op.bytes }
  saveCheckpoint
  if !s.active || !s.surface || s.net.isSome || s.netBoot.isSome || s.netStop.isSome || s.netReplay.isSome then
    modify fun s => { s with toNode := s.toNode.push j.ops }
    flushNode
  else s.wr.submit j

/-- The negative control of the frame's no-wait rule (`block` and
`waits` in tests/wiring.txt): `submit` to the node as it was, through
`Runner.write`, which waits while the local channel is full. Never
run; the wiring check must catch it. -/
def submitWaits (j : Job) : M Unit := do
  if let some r := (← get).net then r.write j.ops

/-- Position an admitted message exactly as the Reader's ordered views do.
Saturated counters use this device's receipt, including a receipt in this
same write; they never invent a position from the display timestamp. -/
def presentationPosition (ps : Array Pending) (message : Id) (fact : Fact) : M (Option Pos) := do
  let .message _ _ _ _ _ n _ _ := fact | return none
  if n < countCap then return some (sortOf fact, message)
  let receipt := ps.find? fun p => match p.fact with
    | .received _ _ m _ _ => m == message
    | _ => false
  if let some p := receipt then return some (sortOf p.fact, message)
  let stored ← intentView (Community.received.byMsg.read [message] (limit := some 1))
  return stored.rows.head?.map fun (pos, _) => (pos.1, message)

def presentationEntry (ps : Array Pending) (p : Pending) : M (Option Presentation.Entry) := do
  let s ← get
  let .message c _ _ _ _ _ _ parent := p.fact | return none
  let some position ← presentationPosition ps p.op.id p.fact | return none
  let root ← match parent with
    | none => pure (some position)
    | some id => do
      let fact ← match ps.find? (·.op.id == id) with
        | some p => pure (some p.fact)
        | none => intentView (Community.Clump.fact id)
      match fact with
      | some f => presentationPosition ps id f
      | none => pure none
  return root.map fun root => ⟨s.cur, c, root, position⟩

def presentationRefusal : M Bool := do
  let now ← IO.monoMsNow
  let message := "Your earlier messages are still being shown. Try sending again shortly."
  modify fun s => { s with toast := Toast.raise now message }
  return false

/-- A user action's write (an intent's ops): each op is
judged in order against what is decided and the ops before it in the
same write. Valid ops show at once, pending. An op whose requirements are
not all here yet (a join's request cites the community's ops, which come
by sync) shows nothing and waits in the store, as the engine waits for
any op. An Invalid op refuses the whole write. Otherwise the ops go in as one job
of this node's own (`submit`). -/
def writeAll (w : Community.Write) (present := false) : M Bool := do
  let s ← get
  if !s.life.allows s.life.lease then return false
  let present := present && s.page == .chat
  if let some reason := WriteAdmission.refusal {} s.queuedWrites w.ops then
    let now ← IO.monoMsNow
    modify fun s => { s with toast := Toast.raise now reason }
    return false
  if present && s.ownSends.entries.length ≥ Presentation.capacity then return ← presentationRefusal
  let some pend ← Reader.judgeWrite s.rd s.out w | do
    s.io.log "write refused: an op is Invalid"
    return false
  let mut ownSends := s.ownSends
  if present then
    for p in pend do
      if let .message c user _ _ _ _ _ _ := p.fact then
        if c == s.me.c && user == s.me.user then
          let some entry ← presentationEntry pend p | return ← presentationRefusal
          let some next := ownSends.offer entry | return ← presentationRefusal
          ownSends := next
    if ownSends.entries.length == s.ownSends.entries.length then return ← presentationRefusal
  modify fun s => { s with out := s.out ++ pend, ownSends }
  s.sh.out.modify (· ++ pend)
  noticeLocal pend.toList
  submit ⟨w.ops, true⟩
  return true

def write (o : Op) : M Bool := writeAll ⟨[o]⟩


/-- Chaos's writes, once made: each job one write, as a user's action is. -/
def chaosStep : M Unit := do
  let some t := (← get).chaos | return
  if !(← IO.hasFinished t) then return
  modify fun s => { s with chaos := none }
  for j in t.get do
    let _ ← writeAll ⟨j.ops⟩
  (← get).wr.busy.modify (· - 1)
  (← get).io.log s!"chaos: {t.get.size} writes of {t.get.foldl (· + ·.ops.length) 0} ops"

/-- n bytes of the OS's randomness (`randomBytes`: getrandom, through
engine/native/crypto): the one door every secret, key and nonce the app
makes goes through. Nothing derives one from the clock. -/
def newBytes (n : UInt32) : IO ByteArray := Engine.Crypto.randomBytes n

/-- A new secret seed: a device's, or an invitation's bearer secret. -/
def newSeed : IO ByteArray := newBytes 32

/-- Wall-clock minutes since the Unix epoch: the time a write claims. -/
def nowMin : M Nat := do return (← (← get).io.wall).1

/-- A user action for the reader: its intent runs in the next pass, in
its transaction and before the marks, and what it touches shows in the
frame that pass serves (ActsLaws.acts_shown). Its id, for `takeDone`. -/
def act (intent : Reader.RM Community.Write) : M Id := do
  if !(← get).life.mounted then return .empty
  let id ← newBytes 16
  (← get).sh.act id intent
  return id

/-- The acts the reader has run: each write submitted, as the frame's
own are (`submit`), in order; what each wrote, for its continuation. -/
def takeDone : M (Array (Id × Option Community.Write)) := do
  let ds ← (← get).sh.done.modifyGet fun a => (a, #[])
  for (_, w?) in ds do
    if let some w := w? then submit ⟨w.ops, true⟩
  return ds

def sendText (text : String) : M Bool := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return false
  -- sealed under the community's current key, as the composer's send is
  let k? ← intentView (Community.currentKey s.me.c)
  let some k := k? | return false
  let w ← intentView (Community.send s.me.c s.me.adm s.me.dev k (← newBytes 24) t.toUTF8
    (← nowMin))
  writeAll w

/-- `sendText` as an act: the reader reads the key and runs the send
intent in its next pass; none when there is nothing to send. -/
def sendTextAct (text : String) : M (Option Id) := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return none
  let (c, adm, dev) := (s.me.c, s.me.adm, s.me.dev)
  let nonce ← newBytes 24
  let now ← nowMin
  some <$> act do
    let (k?, _) ← readView (Community.currentKey c) #[]
    let some k := k? | throw (IO.userError "this community's key hasn't arrived yet")
    let (w, _) ← readView (Community.send c adm dev k nonce t.toUTF8 now) #[]
    return w

def reactTo (m : Id) (e : String) : M Bool := do
  let s ← get
  write (react s.me.c s.me.adm m s.me.dev e.toUTF8 (← nowMin))

/-! ## Geometry -/

def topH (s : St) : Nat :=
  if s.page == .chat then s.insetTop + s.dim.px (if s.wide then 64 else 60)
  else if s.page == .home then s.insetTop + s.dim.px 64
  else if s.page.scrolls then s.insetTop + s.dim.px 60
  else s.insetTop + s.dim.px 56

/-- The composer's layout (Composer: the painter and the taps both read it). -/
def composerFont (s : St) : Font := s.font.atSize (s.dim.px (if s.wide then 14 else 15))

def photoLoading (s : St) : Bool := s.photoRequest.any (·.selected)

def composerLayout (s : St) : Composer.Layout :=
  Composer.layout (composerFont s) s.dim s.W s.text (Composer.visibleCount s.chips.size (photoLoading s)) s.wide s.mobile

def sheetItems (s : St) (sh : SheetSt) : Array Nat := Sheet.shown s.catalog sh.cat sh.query

def catOf (s : St) (sh : SheetSt) : Sheet.Cat :=
  Sheet.cat s.dim s.font s.W s.Hs s.insetTop (sheetItems s sh).size

def botH (s : St) : Nat :=
  if s.page != .chat then 1 else
  match s.sheet with
  | some sh => if sh.catalog then (catOf s sh).h else (Sheet.quick s.dim s.W).h
  | none => (composerLayout s).h

/-- The screen's geometry as of this frame (Geometry: the theorems that
list content is never under the header, composer or keyboard are about
these numbers). -/
def geom (s : St) : Geometry.Geom := ⟨s.Hs, s.insetBot, s.imeH, topH s, botH s⟩

def viewH (s : St) : Nat := (geom s).view

def heightOf (s : St) (x : Id) : Nat := s.heights.getD x est

/-- The window's rows' bottoms (bottom-anchored), newest first, and the
content's height: the messages newer and older than the window at `est`
each, below and above it. -/
def bottoms (s : St) : Array Nat × Nat := Id.run do
  let mut out := Array.mkEmpty s.ids.size
  let mut y := bottomPad + s.newer * est
  for (_, x) in s.ids do
    out := out.push y
    y := y + heightOf s x
  return (out, y + s.older * est + 16)

/-! ## Mounting, measuring, painting -/

/-- An attachment's slices, read from its chunk ops in order (a chunk this
device sends may still be in the outbox); none while one is not here. -/
def slicesOf (p : Row.Pic) : M (Option (List ByteArray)) := do
  -- the chunk ops' bytes, read by the reader (Reader.Want.slices): wanted
  -- from the next frame, none until the board has them all; nothing is
  -- decoded here (a 64 KiB chunk is slow to decode; the frame must not wait)
  let w := Reader.Want.slices p.chunks
  match (← (← get).sh.board.get).get? w with
  | some (.slices raw, _) => return raw
  | _ => return none

/-- All expensive visual work passes through the shared component pool.
The declaration is retained for this frame even when its result is cached. -/
def rasterRequest (owner : Demand.Owner) (key : Raster.Key) (visible : Bool)
    (action : Work.Action Bitmap) : M (Work.Handle Raster.Key Bitmap) := do
  let need : Demand.Need Raster.Key := ⟨owner, key, visible⟩
  modify fun s => { s with rasterNeeds := s.rasterNeeds.push need }
  (← get).raster.request need action

/-- An attachment child owns its chunk request and both image stages.
Its parent supplies identity, metadata and bounds; it does not start its
work. No timer keeps an offscreen picture subscribed. -/
def image (p : Row.Pic) (w h : Nat) (owner : Demand.Owner := [])
    (visible : Bool := true) : M (Option Bitmap × Bool) := do
  let s ← get
  let stage (n : UInt8) (source : Unit → Option Image.Src) : M (Option Bitmap) := do
    let k : ImgKey := (p.hash.push n, w, h)
    let action ← Raster.image source w h s.dim.theme (n == 0)
    let handle ← rasterRequest owner (.image k s.dim.theme) visible action
    modify fun s => { s with imgs := s.imgs.insert k handle }
    handle.value
  let pre ← if p.preview.isEmpty then pure none else stage 0 (fun _ => Image.decode p.preview)
  let mut full := none
  if p.complete then
    let want := Reader.Want.slices p.chunks
    match ← query ⟨owner, visible⟩ want with
    | some (.slices (some raw)) => full ← stage 1 (fun _ => Raster.fileSource p raw)
    | _ =>
      -- Kept for diagnostics of a missing dependency, never as a timer
      -- authorizing work. The child's declaration alone owns the query.
      modify fun s => { s with imgWaiting := s.imgWaiting.insert (p.hash.push 1, w, h) }
  return p.shown pre full

/-- In the headless twins, the frame runs the reader's pass itself; on a
device the reader's thread runs them. The outbox is the reader's
(`Reader.Shared.out`): the frame's writes join it as they are made. -/
def readerPass : M Unit := do
  let s ← get
  if !s.life.mounted then return
  -- Devices publish the complete component tree once, in present. A
  -- partial tree would reorder requests twice per frame and repeatedly
  -- rebuild the reader's dependency index while it is serving them.
  if s.rst.isNone then return
  -- Keep last frame's owners while this frame discovers descendants.
  -- Presentation reconciles the completed declaration set exactly once.
  let previous := (← s.sh.plan.get).needs.toArray
  s.sh.setNeeds (s.queryNeeds ++ previous.filter fun n => !s.queryNeeds.any
    (fun current => current.owner == n.owner && current.key == n.key))
  if let some r := s.rst then
    let (_, r) ← (Reader.pass s.sh).run r
    modify fun s => { s with rst := some r }

/-- Take the board's moved set in one swap. A mounted attachment checks
its answer every frame; this only clears its waiting diagnostic. -/
def takeBoard : M (_root_.Live.Board Reader.Want Reader.Val) := do
  let (moved, b) ← (← get).sh.board.modifyGet fun b => let (mv, b') := b.take; ((mv, b'), b')
  if moved.toList.any fun | .slices _ => true | _ => false then
    modify fun s => { s with imgWaiting := {} }
  return b

/-- Select pixels that actually communicate the sent content. Blank/inkless
text lines do not acknowledge a body below the viewport. A photo-only send
waits for an actual preview/file bitmap, not its empty text band or placeholder. -/
def findPresentationBand (s : St) (r : RowSt) : Option (Nat × Nat) := Id.run do
  let some bitmap := r.shown | return none
  let ground := if r.data.selected then Paint.solid (Palette.color s.dim.theme .selected) s.W
    else if s.dim.hover.isSome then Paint.solid (Palette.gray03 s.dim.theme) s.W else s.bgRow
  let left := 4 * s.dim.textX
  let right := 4 * (s.W - s.dim.pad)
  let backdrop := ground.extract left right
  for i in [0:r.lay.text.size] do
    let y := r.lay.textY + Row.bodyHeight s.dim r.data i
    let h := min (max 1 s.dim.lineH) (bitmap.rows.size - y)
    if (bitmap.rows.extract y (y + h)).any (fun row => row.extract left right != backdrop) then
      return some (y, h)
  if let some box := r.lay.pics[0]? then
    if r.painted.2[1]?.getD false then
      return some (box.y, min box.h (max 1 s.dim.lineH))
  return none

/-- Constant-size lookup; a changed ticket invalidates the cached band. -/
def presentationBand (_s : St) (r : RowSt) : Option (Nat × Nat) := do
  let (ticket, band) ← r.presentation
  if r.paintFlight.map (·.handle.ticket) == some ticket then band else none

/-- Initially pin the measured row; once its pixels exist, pin its first
visible content band. This also handles a tall inkless prefix. -/
def presentationOffset (s : St) (x : Id) : Nat :=
  match s.rows[x]? with
  | some r => match presentationBand s r with
    | some (y, _) => min r.lay.h (y + (geom s).viewNow)
    | none => min (heightOf s x) (geom s).viewNow
  | none => min (heightOf s x) (geom s).viewNow

/-- Keep the admitted first committed body and its measured layout together.
Child queries still run; their latest answers are adopted after publication.
Only ancillary name/reaction changes may wait. Access/content/global display
changes immediately leave this path. -/
def deferRowPaint (s : St) (x : Id) (r : RowSt) (next : RowData) : Bool :=
  r.data.own && !r.data.pending && (!r.shownCommitted || s.ownSends.contains x) &&
  r.paintFlight.any (fun old => old.stamp ==
    Raster.RowPaint.stamp s.life.generation x s.W s.dim s.bgRow next old.stamp.ready)

/-- Row x from the board (Reader's row want), laid out again when its
version moved; nothing while the board has none (the frame shows the
row's placeholder, Cover). Its time is shown in the local timezone. -/
def mount (bd : _root_.Live.Board Reader.Want Reader.Val) (x : Id) : M Unit := do
  let s ← get
  if s.page != .chat || !s.life.mounted then return
  let answer := bd.get? (.row s.me.c s.me.adm x)
  if let some (.row none, _) := answer then
    if let some old := s.rows[x]? then retireRow old
    modify fun s => { s with
      rows := s.rows.erase x,
      ownSends := s.ownSends.keep (·.message.2 != x),
      presenting := s.presenting.filter (·.message != x) }
    return
  let some (.row (some d), ver) := answer | return
  if (s.rows[x]?.map (·.bver)) == some ver then return
  let tz := (← s.io.wall).2
  let d := { d with time := (d.time + tz).toNat, wide := s.wide, own := d.author == s.me.user }
  let measured ← match s.rows[x]? with
    | some r => pure (some (r.data.pics, r.data.tallies))
    | none => Component.measure ⟨Raster.messageOwner s.me.c x, true⟩ s.me.c x
  let some (pics, tallies) := measured | return
  let d := { d with pics, tallies }
  -- Preserve a child's already displayed value when an unrelated parent
  -- query changes. The child still refreshes from its own board entry.
  let d := match s.rows[x]? with
    | none => d
    | some r => { d with
        pics := r.data.pics, tallies := r.data.tallies,
        name := if d.author == r.data.author then r.data.name else d.name,
        namesake := d.author == r.data.author && r.data.namesake }
  match s.rows[x]? with
  | some r =>
    if r.data == d then
      modify fun s => { s with rows := s.rows.insert x { r with bver := ver } }
    else if !deferRowPaint s x r d then
      let lay := Row.layout s.font s.dim s.W d
      modify fun s => { s with rows := s.rows.insert x { r with data := d, lay, bver := ver, ver := r.ver + 1 },
                                heights := s.heights.insert x lay.h }
  | none =>
    let lay := Row.layout s.font s.dim s.W d
    modify fun s => { s with
      rows := s.rows.insert x { data := d, lay, painted := (0, []), task := none, shown := none,
                                ver := 1, bver := ver },
      heights := s.heights.insert x lay.h }

/-- Assemble child outputs. Each child observes by identity through the
same API; only the message op's own data arrives through its row query.
Geometry is recomputed before anchoring when a child supplies a new size. -/
def mountChildren (x : Id) (bottom offset viewport : Nat) : M Unit := do
  let s ← get
  let some r := s.rows[x]? | return
  let scope : Component.Scope := ⟨Raster.messageOwner s.me.c x,
    Raster.near bottom r.lay.h offset viewport 0⟩
  let group := (s.cellRoot[x]?.bind fun root => s.clumps[root]?).getD {}
  let continued := group.newer > 0 || group.ids.any (fun p => p.2 != x) &&
    (group.ids[0]?.map (·.2) != some x)
  let mut d := { r.data with continued := continued, wide := s.wide }
  let ids ← Component.attachments (scope.child "attachments" x) s.me.c x (d.pics.map (·.attachment))
  let mut pics := []
  for id in ids do
    if let some p ← Component.attachment (scope.child "attachment" id) s.me.c id
        (d.pics.find? (·.attachment == id)) then pics := pics ++ [p]
  d := { d with pics }
  let lay := if d == r.data then r.lay else Row.layout s.font s.dim s.W d
  let authorBottom := bottom + lay.h - (Row.headY s.dim d + s.dim.px 26)
  if d.clump.isNone && Raster.near authorBottom (s.dim.px 26) offset viewport over then
    let authorScope := { scope.child "author" d.author with
      visible := Raster.near authorBottom (s.dim.px 26) offset viewport 0 }
    let (name, twin) ← Component.author authorScope s.me.c d.author (d.name, d.namesake)
    d := { d with name, namesake := twin }
  let reactionHeight := match lay.pills[0]? with
    | some (box, _) => lay.h - box.y
    | none => s.dim.pillH + s.dim.gap + s.dim.px 8
  if Raster.near bottom reactionHeight offset viewport over then
    let block := { scope.child "reactions" x with
      visible := Raster.near bottom reactionHeight offset viewport 0 }
    let es ← Component.emojis block s.me.c x (d.tallies.map (·.emoji))
    let tallies := es.map fun e => (d.tallies.find? (·.emoji == e)).getD ⟨e, 0, false⟩
    let pillLayout := if tallies == d.tallies then lay else Row.layout s.font s.dim s.W { d with tallies }
    let mut next := []
    for i in [0:tallies.length] do
      let old := tallies[i]!
      let box := (pillLayout.pills[i]!).1
      let childBottom := bottom + pillLayout.h - box.y - box.h
      let t ← if Raster.near childBottom box.h offset viewport over then
        Component.reaction { block.child "reaction" old.emoji.toUTF8 with
          visible := Raster.near childBottom box.h offset viewport 0 } s.me.c x s.me.user old.emoji old
        else pure old
      next := next ++ [t]
    d := { d with tallies := next }
  if d != r.data && !deferRowPaint s x r d then
    let lay := Row.layout s.font s.dim s.W d
    modify fun s => { s with
      rows := s.rows.insert x { r with data := d, lay, ver := r.ver + 1 },
      heights := s.heights.insert x lay.h }

/-- Start a paint of row x if what it shows changed; collect a finished one. -/
def paintRow (x : Id) (bottom offset viewport : Nat := 0) : M Unit := do
  let s ← get
  if s.page != .chat || !s.life.mounted then return
  let some r := s.rows[x]? | return
  let viewport := if viewport == 0 then viewH s else viewport
  let owner := Raster.messageOwner s.me.c x
  let visible := Raster.near bottom r.lay.h offset viewport 0
  let av : Option Bitmap := none
  let mut imgs := #[]
  let mut ready := [false]
  let mut data := r.data
  for i in [0:r.lay.pics.size] do
    let bx := r.lay.pics[i]!
    let childBottom := bottom + r.lay.h - (bx.y + bx.h)
    match r.data.pics[i]? with
    | some p =>
      if Raster.near childBottom bx.h offset viewport imageOver then
        let owner := Raster.pictureOwner s.me.c x p.attachment
        let visible := Raster.near childBottom bx.h offset viewport 0
        let p ← Component.picture ⟨owner, visible⟩ s.me.c p.attachment p
        data := { data with pics := data.pics.set i p }
        let (b, isFile) ← image p bx.w bx.h owner visible
        imgs := imgs.push b
        ready := ready ++ [b.isSome, isFile]
      else
        imgs := imgs.push none
        ready := ready ++ [false, false]
    | none => imgs := imgs.push none
  let s ← get
  let mut r := r
  if data != r.data then r := { r with data, ver := r.ver + 1 }
  let selected := s.selected == some x
  if r.data.selected != selected then
    r := { r with data := { r.data with selected }, ver := r.ver + 1 }
  let (f, dm, W, bgRow, d, l) := (s.font, s.dim, s.W, s.bgRow, r.data, r.lay)
  let stamp := Raster.RowPaint.stamp s.life.generation x W dm bgRow d ready
  let first := d.own && !d.pending && (!r.shownCommitted || s.ownSends.contains x)
  let (flight, value) ← Raster.RowPaint.request s.raster owner visible first r.paintFlight
    stamp r.ver d l imgs (fun _ => pure (some (Row.paint f dm W bgRow d l av imgs)))
  -- Presentation must keep the admitted snapshot's key, not a newer
  -- cosmetic version which would revoke the first paint before publication.
  modify fun s => { s with rasterNeeds := s.rasterNeeds.push ⟨owner, flight.handle.ticket.key, visible⟩ }
  if (r.paintFlight.map (·.handle.ticket)) != some flight.handle.ticket then
    modify fun s => { s with paints := s.paints + 1 }
  r := { r with
    task := if value.isSome then none else some flight.handle,
    paintFlight := some flight,
    painted := if value.isSome then (flight.version, flight.stamp.ready) else r.painted,
    shown := value.orElse fun _ => r.shown,
    shownCommitted := r.shownCommitted || (value.isSome && !flight.data.pending),
    pixels := if !s.mobile && value.isSome then
      some ⟨flight.data, flight.lay, flight.images, flight.version, flight.stamp.ready⟩ else r.pixels }
  if value.isSome && r.presentation.map (·.1) != some flight.handle.ticket then
    r := { r with presentation := some (flight.handle.ticket,
      findPresentationBand s { r with data := flight.data, lay := flight.lay }) }
  if s.selected.isSome && !selected then
    if let some bmp := r.shown then
      let key := Raster.Key.dim s.life.generation x r.ver ready s.dim.theme
      let dimmed ← rasterRequest owner key visible (fun _ => pure (some (Row.Bitmap.dim bmp)))
      r := { r with dimmed := some dimmed, dimVer := r.ver, dimShown := ← dimmed.value }
  else r := { r with dimmed := none, dimShown := none }
  modify fun s => { s with rows := s.rows.insert x r }

/-! ## The frame -/

/-- Shared message-shaped skeleton for rows not painted or loaded yet. -/
def holdLine (s : St) (li : Nat) : ByteArray :=
  Hold.messageLine ⟨s.bgRow, s.dim, s.W⟩ li

/-- The rows overlapping the list frame, from the first one up: the
first's index, and each one's height and the height of the paint it
shows (Cover.seen's rows), with the paints. -/
def frameSlice (s : St) (b : Nat) (bots : Array Nat) : Nat × Array (Nat × Option Nat) × Array (Option Bitmap) :=
  Id.run do
  let top := b + viewH s + over     -- content above the frame's first row
  let low := if b ≥ over then b - over else 0
  let mut i0 := s.ids.size
  let mut slice : Array (Nat × Option Nat) := #[]
  let mut bmps : Array (Option Bitmap) := #[]
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    let x := s.ids[i]!.2
    let h := heightOf s x
    if bot ≥ top then break
    if bot + h ≤ low then continue
    if i0 == s.ids.size then i0 := i
    let pick := s.rows[x]? >>= fun r =>
      if s.selected.isSome && s.selected != some x then r.dimShown <|> r.shown else r.shown
    slice := slice.push (h, pick.map (·.h))
    bmps := bmps.push pick
  return (i0, slice, bmps)

/-- The list frame: row r shows content at b + viewH + over - 1 - r, as
Cover.seen says: a painted row's line, else a placeholder (Cover.covered:
nothing inside the content is left blank, however slow a read or a
decode is). -/
def listFrame (s : St) (b : Nat) (bots : Array Nat) : Array ByteArray := Id.run do
  let vh := viewH s
  let hgt := vh + 2 * over
  let top := b + vh + over     -- content above the frame's first row
  let (i0, slice, bmps) := frameSlice s b bots
  let bottom := if i0 < s.ids.size then bots[i0]! else
    match s.ids.back? with
    | some (_, x) => bots.back! + heightOf s x
    | none => bottomPad + s.newer * est
  -- messages outside the window: nothing past the loaded rows is blank
  let more := s.older > 0
  let pad := if s.newer > 0 then bottomPad else bottom
  let rows := slice.toList
  let mut fr := Array.mkEmpty hgt
  for r in [0:hgt] do
    let p := top - 1 - r
    fr := fr.push (match Cover.seen pad bottom more rows p with
      | .line j li => ((bmps[j]?).join.map (·.rows[li]!)).getD s.bgRow
      | .hold j => holdLine s (heightOf s (s.ids[i0 + j]?.map (·.2) |>.getD .empty) - 1 - (p - (bots[i0 + j]?.getD 0)))
      | .unloaded => Hold.unloadedLine ⟨s.bgRow, s.dim, s.W⟩ p
      | .blank => s.bgRow)
  return fr

def header (s : St) : Bitmap := Id.run do
  let px := s.dim.px
  let h := topH s
  let color := Palette.color s.dim.theme
  let mut b := Bitmap.blank s.W h (solid (color .panel) s.W)
  let font := s.font.atSize (px 16)
  if s.wide then
    b := b.icon s.font "title-hash" (px 20) (s.insetTop + px 26) (px 12) (color .fg)
    b := b.line font (Text.oneLine font (s.W - px 96) "general") (px 36) (s.insetTop + px 22) (color .fg)
  else
    b := b.icon s.font "arrow-back" (px 16) (s.insetTop + px 18) (px 24) (color .fg)
    b := Pages.centred font b "#general" (s.insetTop + px 12) (color .fg)
    b := Pages.centred (s.font.atSize (px 12)) b s!"({s.me.name})" (s.insetTop + px 32) (color .fg)
  let x := s.W - px (if s.wide then 52 else 46)
  let y := s.insetTop + px (if s.wide then 16 else 14)
  let hot := s.dim.hot x y (px 32) (px 32)
  if hot then b := b.round x y (x + px 32) (y + px 32) (px 6) (color .selected)
  b := b.icon s.font "more" (x + px 4) (y + px 4) (px 24) (if hot then color .fg else if s.dim.theme == .dark then 0x909090 else 0x999999)
  return b.fill 0 (h - px 1) s.W h (color .selected)

/-- Header targets share the visible navigation: Back, channel settings. -/
def headerHit (s : St) (x _y : Nat) : PageId :=
  if !s.wide && x < s.dim.px 56 then .home else .channelSettings

def cursorAt (s : St) (i : Nat) : Nat × Nat :=
  let pre := String.ofList (s.text.toList.take i)
  let ls := if pre.isEmpty then #[#[]] else Text.layoutFine (composerFont s) (composerLayout s).textW pre
  let last := ls.back?.getD #[]
  -- a prefix ending in a newline puts the cursor on the next line
  if pre.endsWith "\n" then (ls.size, 0) else (ls.size - 1, Paint.Line.width (composerFont s) last)

def composerChips (s : St) : Array Composer.Chip :=
  Composer.withPending s.dim (s.chips.map (·.2.2.2)) (photoLoading s) (s.frames / 4)

/-- The actual painter receives a pending tile immediately, independent of
whether the OS provider or the encoding worker has completed. -/
theorem composer_pending_feedback (s : St) (h : photoLoading s = true) :
    (composerChips s).size = s.chips.size + 1 := by
  simp [composerChips, Composer.withPending, h]

/-- Opening the picker alone does not invent an attachment. -/
theorem composer_no_selection (s : St) (h : photoLoading s = false) :
    (composerChips s).size = s.chips.size := by
  simp [composerChips, Composer.withPending, h]

def composer (s : St) : Bitmap :=
  Composer.paint (composerFont s) s.dim s.W s.bgRow (composerLayout s) s.text "Message #general"
    (composerChips s) (if s.editorFocused || s.imeH > 0 then some (cursorAt s s.sel[0]!.toNat) else none) s.photoRequest.isSome

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

/-! ## Pages and communities -/

def hexShort (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let t := String.ofList (Nat.toDigits 16 x.toNat); if t.length < 2 then "0" ++ t else t)

/-- A toast, for about 3 s (libquiet's: an outcome stated, then gone). -/
def say (t : String) : M Unit := do
  let now := (← (← get).io.nowUs).toNat / 1000
  modify fun s => { s with toast := Toast.raise now t }

/-- Where this device is dialed: its LAN addresses at the node's port
(Link.hints, Wi-Fi first), or loopback in a one-machine test. -/
def listenHints : M (List ByteArray) := do
  let s ← get
  let (port, loop) := s.netCfg.getD (Link.port, false)
  if loop then return [s!"127.0.0.1:{port}".toUTF8]
  let addrs ← try Link.local? catch _ => pure []
  return Link.hints addrs port

/-! ## Navigation

The page and the back stack change only by Nav's steps (its laws in
engine/renderer/Nav.lean, the app's in app/app/NavLaws.lean). -/

/-- Open p (Nav.go); the page's refusal is cleared. Opening the switcher
composes its backdrop from the last frame shown; opening any other page
keeps it, so back to the switcher draws the backdrop it opened over
(NavLaws.back_open). -/
def openSt (p : PageId) (s : St) : St :=
  let backdrop := if p == .switcher then
    match s.lastDisplay with
    | some (words, rows, top, bot) => Surface.compose words s.Hs s.bgRow rows top bot
    | none => #[]
    else s.switcherBackdrop
  { s.withNav (Nav.go p s.nav) with
    refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := backdrop }

/-- Back (Nav.back); the page's one-line field and refusal are cleared
(the native field's text with them), never the composer's draft. -/
def backSt (s : St) : St := { s.withNav (Nav.back s.nav) with field := "", refusal := none, pageKey := none, pageScrollStarted := false }

/-- Navigation revokes an outstanding photo selection. OS backgrounding
alone does not: presenting the native picker itself suspends the app. -/
def cancelPhoto : M Unit := do
  let s ← get
  if s.photoRequest.isSome then discard <| s.io.pickPhoto 0
  modify fun s => { s with photoRequest := none, photoWork := none }

/-- Open a page (the current one goes on the back stack). -/
def openPage (p : PageId) : M Unit := do
  let s ← get
  if s.page == p then return
  cancelPhoto
  -- Add members issues this community's link once per session: an
  -- invitation op of mine, and the link that carries its bearer secret
  if p == .invite && !s.me.waiting && !(s.links.any (·.1 == s.me.acc)) then
    let bearer ← newSeed
    -- dial hints: this device's private LAN addresses (Link.hints)
    -- the link names this node's key (Community.inviteTo reads it)
    let issued ← intentView (Community.inviteTo s.me.c s.me.adm s.me.dev bearer (← listenHints))
    if let some (w, i) := issued then
      if ← writeAll w then
        modify fun s => { s with links := (s.me.acc, i.text) :: s.links }
  leavePage
  s.io.scrollTo 0
  modify (openSt p)
  modify fun s => { s with editorFocused := false }
  modify fun s => { s with restoreAnchor := p == .chat && s.mark.isSome }
  mountPage

/-- Back: the page before; at a root, it stays (Nav.back_root). -/
def back : M Unit := do
  cancelPhoto
  leavePage
  let s ← get
  s.io.ime false
  s.io.scrollTo 0
  modify backSt

  modify fun s => { s with restoreAnchor := s.page == .chat && s.mark.isSome }
  mountPage

/-- What the app holds for an entry no longer listed, forgotten: its
invite link, a pasted link to its community, an open profile, and, if it
was current, the composer's text and photos. -/
def forgetEntry (s : St) (a c : Id) : St :=
  let cur := s.me.acc == a
  { s with links := s.links.filter (·.1 != a),
           invite := if (s.invite.map (·.community == c)).getD false then none else s.invite,
           profileOf := if cur then none else s.profileOf,
           text := if cur then "" else s.text, chips := if cur then #[] else s.chips }

/-- The communities, as read by the Community kind: those listed (a
removed entry hidden), the current one kept or, gone, the first (Get
started when none is left). -/
def applyComms (all : Array Chaos.Me) : M Unit := do
  let cs := Kinds.Accepted.listed all
  -- removed since last told: a standing notice each, and forgotten
  for g in Kinds.Accepted.newlyGone (← get).goneSeen all do
    modify fun s => { forgetEntry s g.acc g.c with
      goneSeen := g.acc :: s.goneSeen,
      notices := s.notices ++ [s!"You’ve been removed from {if g.name.isEmpty then "a community" else g.name}."] }
  modify fun s =>
    match Kinds.Accepted.landing cs s.cur with
    | some me => { s with comms := cs, me, cur := me.acc }
    | none =>
      -- nothing listed: Get started (unless a join is being made)
      { s.withNav (if s.comms.isEmpty then s.nav else Nav.reset .getStarted) with
          comms := cs, me := default, cur := .empty }

/-- The state a switch to acceptance `a` leaves: its home as a root (back
stays there: Nav.back_reset), and its conversation's window empty. -/
def switchSt (a : Id) (s : St) : St :=
  let s := { s.withNav (Nav.reset .home) with cur := a, me := (Kinds.Accepted.select s.comms a).getD s.me }
  let s := { s with ids := #[], roots := #[], clumps := {}, clumpHeights := {}, cellRoot := {}, spacers := {}, restorePos := none, total := 0, people := 0, peopleAll := true, anchor := none, newer := 0, older := 0 }
  let s := { s with heights := {}, rows := {}, selected := none, sheet := none, ownSends := {}, presenting := none }
  { s with asking := #[], hidden := [], chromeKey := "", pageKey := none, ownName := "…", ownDevices := 1 }

/-- The communities as the reader's board has them (Reader.Want.comms):
each frame. -/
def refreshComms : M Unit := do
  if let some (.comms all) ← query ⟨["session".toUTF8, "communities".toUTF8], true⟩ .comms then applyComms all

/-- The communities read now, on the frame: after an action that founds,
joins or stops waiting, which the next page shows at once. -/
def refreshCommsNow : M Unit := do
  let known := (← get).comms
  let (all, _) ← transaction (Kinds.Accepted.read known)
  applyComms all

/-- Make the entry of acceptance `a` the current one (memory only): the
list starts again from its newest. An entry is its acceptance, never its
community id or name (Switch.select_tapped). -/
def switchToAcc (a : Id) : M Unit := do
  cancelPhoto
  leavePage
  (← get).io.scrollTo 0
  modify (switchSt a)
  modify fun s => { useDraft s with mark := none, restoreAnchor := false }
  mountPage

def switchTo (i : Nat) : M Unit := do
  if let some m := (← get).comms[i]? then switchToAcc m.acc

/-- A link pasted or scanned: Choose a name, then Agree & join; but a link
to a community this device already holds (a member, or its join pending)
goes to that community instead, and joins nothing (libquiet's rule: a
node holds a community at most once). -/
def takeInvite (i : Community.Invite) : M Unit := do
  let s ← get
  if let some m := s.comms.find? (·.c == i.community) then
    s.io.ime false
    modify fun s => { s with invite := none, field := "", refusal := none }
    switchToAcc m.acc
    say (if m.waiting then "You're already waiting to join this community." else "You're already in this community.")
    return
  modify fun s => { s with invite := some i, field := "", refusal := none }
  openPage .name
  s.io.ime true

/-- The acceptance a write makes (found's, join's): its accept op. -/
def acceptOf (w : Community.Write) : Option Id :=
  (w.ops.find? fun o => match (Codec.decode o.body : Option Community.Body) with
    | some (.accept ..) => true
    | _ => false).map (·.id)

/-- Found a community named n: its root and my profile, and it becomes
current. -/
def found (n myName : String) : M Unit := do
  let seed ← newSeed
  -- the last fresh bytes are this node's key, if it has none yet
  let w ← intentView (Community.found seed n.toUTF8 myName.toUTF8 (← nowMin)
    (← newBytes 32) (← newBytes 32) (← newBytes 32))
  if ← writeAll w then
    if let some a := acceptOf w then
      refreshCommsNow
      switchToAcc a

/-- The node: started at launch, once (it speaks for every device whose
secret this store holds: Connection.hooks reads them all, and picks the
device for each community from its acceptance). The retained boot task waits
for earlier local writer work; later App writes park behind that task. -/
def netStep : M Unit := do
  recoverNode
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome || s.netReplay.isSome then return
  let some (port, _) := s.netCfg | return
  if s.net.isSome then return
  -- started: taken once it is up (the frame never waits on it)
  if let some t := s.netBoot then
    if !(← IO.hasFinished t) then return
    modify fun s => { s with netBoot := none }
    match t.get with
    | .ok r =>
      s.io.log s!"node: listening on {r.port}"
      modify fun s => { s with net := some r }
      flushNode
    | .error e =>
      s.io.log s!"node: cannot start: {e}"
      modify fun s => { s with netCfg := none }
      let pending := (← get).toNode
      modify fun s => { s with toNode := #[] }
      if !pending.isEmpty then for ops in pending do s.wr.submit ⟨ops, true⟩
    return
  let listen := ((← listenHints).head?).getD s!"127.0.0.1:{port}".toUTF8
  let x : Engine.Sync.Sync SF (SqlM SF) :=
    { fam, cfg := { every := 30000, askTime := 20000 },
      hooks := Connection.hooks fam Connection.sodium listen }
  let path := s.dbPath
  let sh := s.sh
  let writer := s.wr
  let t ← IO.asTask (prio := .dedicated) do
    -- Installing netBoot makes later App submissions park. Only the
    -- previously admitted writer work remains ahead of this store open.
    while (← writer.busy.get) > 0 do IO.sleep 2
    let db ← Db.openAt path
    -- the node's commits move the reader's counter (Reader.Shared.commits)
    Engine.Sync.Runner.start x db 0 port.toUInt16 (notify := fun _ => sh.commits.modify (· + 1))
  s.io.log s!"node: starting, dialed as {(String.fromUTF8? listen).getD "?"}"
  modify fun s => { s with netBoot := some t }

/-- The rows every commit since the last call filed or unfiled (the
writer's and the node's alike), and the verdicts it recorded or cleared,
from the store's journal: read inside the frame's read transaction, they
are exactly the commits this frame's reads see. -/
def takeChanges : M (Array Filing × Array (Id × Bool)) := do
  let s ← get
  let (fs, vs, top) ← s.rd.filingsSince s.seen
  modify fun s => { s with seen := top }
  -- taken by the frame and the reader: the writer may delete them
  s.wr.noticed (min top (← s.sh.seen.get))
  return (fs, vs)

/-- Join with QR code: the camera on while the page shows; each new
frame drawn in the page's square (Camera.preview: it reads only inside the
frame, src_in) and, one at a time, decoded off the app's thread; a code
that is an invite is taken as a pasted link is. -/
def scanStep : M Unit := do
  let s ← get
  let on := s.page == .scan
  if on != s.camOn then
    s.io.scan on
    modify fun s => { s with camOn := on, camView := none, decoding := none }
  if !on then return
  let (hdr, px) ← s.io.luma
  if hdr.size == 4 && px.size > 0 then
    let fr : Camera.Frame := ⟨hdr[0]!.toNat, hdr[1]!.toNat, hdr[2]!.toNat, hdr[3]!.toNat, px⟩
    let side := (Pages.scanBox s.dim s.W (viewH s)).w
    modify fun s => { s with camView := some (Camera.preview fr side), camFrame := s.camFrame + 1 }
    if s.decoding.isNone then
      let t := Task.spawn fun _ =>
        (Qr.decodeLuma hdr[0]! hdr[1]! hdr[2]! px).bind fun (b, _) => String.fromUTF8? b
      modify fun s => { s with decoding := some t, scans := s.scans + 1 }
  match (← get).decoding with
  | some t =>
    if ← IO.hasFinished t then
      modify fun s => { s with decoding := none }
      if let some text := t.get then
        match Community.Invite.parse text with
        | some i => takeInvite i
        | none => say "That code isn't a Quiet invite."
  | none => pure ()

/-- Home owns a count subscription, not the hidden conversation's rows. -/
def refreshHomeCount : M Unit := do
  let s ← get
  if s.page != .home || s.me.c.isEmpty then return
  if let some (.count _ total) ← query ⟨["home".toUTF8, s.me.c, "messages".toUTF8], true⟩ (.count s.me.c none) then
    modify fun s => { s with total }

/-- The people of the current community, for home's Direct messages:
its members (the Profile kind's), me first. -/
def refreshMembers : M Unit := do
  let s ← get
  if s.me.c.isEmpty || (s.page != .home && s.page != .profile && s.page != .removeConfirm) then return
  -- read by the reader (Reader.Want.members): nothing until it is
  let some (.members ms admin) ← query ⟨["page".toUTF8, s.cur, "members".toUTF8], true⟩
    (.members s.me.c s.me.user) | return
  let ordered := ms.filter (·.1 == s.me.user) ++ ms.filter (·.1 != s.me.user)
  let mut sorted := #[]
  let peopleY := Pages.homePeopleTop s.dim s.asking.size 1
  for i in [0:ordered.size] do
    let (u, _, _) := ordered[i]!
    let old := ((s.memberIds.findIdx? (· == u)).bind fun i => s.members[i]?).map (·.1) |>.getD "…"
    let rowVisible := s.page == .home && peopleY + (i + 1) * s.dim.px 40 ≤ viewH s
    let profileVisible := (s.page == .profile || s.page == .removeConfirm) && s.profileOf.any (·.1 == u)
    let name ← if rowVisible || profileVisible || (s.page == .home && u == s.me.user) then
      pure (← Component.author ⟨["page".toUTF8, s.cur, "profile".toUTF8, u], true⟩ s.me.c u (old, false)).1
      else pure old
    sorted := sorted.push ((name, u == s.me.user), u)
    if profileVisible then modify fun s => { s with profileOf := s.profileOf.map fun (id, _, me) => (id, name, me) }
  modify fun s => { s with members := sorted.map (·.1), people := ms.size, peopleAll := true,
                           memberIds := sorted.map (·.2), amAdmin := admin }
  -- a removal being sent is done once its target is no longer present
  if let .sending u := (← get).removal then
    if !(← get).memberIds.contains u then
      let name := ((← get).profileOf.map (·.2.1)).getD "They"
      modify fun s => { s.withNav (Nav.reset .home) with
          removal := (Remove.step s.removal .done).1, profileOf := none }
      say s!"Removed {name} from the community."

/-- The requests to join the current community, read by the Request kind. -/
def refreshAsking : M Unit := do
  let s ← get
  if s.me.c.isEmpty then return
  if let some (.asking out) ← query ⟨["page".toUTF8, s.cur, "requests".toUTF8], true⟩ (.asking s.me.c) then
    modify fun s => { s with asking := out }

/-- My approval of request r (my device in this community signs it). -/
def approveReq (r : Id) : M Unit := do
  -- a fresh ephemeral secret for the wrap of the community's key to the
  -- requester's device
  let esk ← newBytes 32
  let s ← get
  -- the intent reads the request: my approval admits it, so the
  -- admission goes in the same write
  let w ← intentView (Community.approveReq s.me.c r s.me.adm s.me.dev esk)
  let _ ← writeAll w

/-- The profile and counts belong to the settings surfaces that show them. -/
def observeSettings (owner : Demand.Owner) (profile counts : Bool) : M Unit := do
  let s ← get
  if s.me.c.isEmpty then return
  if profile then
    let (name, _) ← Component.author ⟨owner ++ ["author".toUTF8], true⟩ s.me.c s.me.user (s.ownName, false)
    modify fun s => { s with ownName := name }
    if let some (.members ms _) ← query ⟨owner ++ ["devices".toUTF8], true⟩ (.members s.me.c s.me.user) then
      let devices := (ms.find? (·.1 == s.me.user)).map (·.2.1.length) |>.getD 1
      modify fun s => { s with ownDevices := devices }
  if counts then
    if let some (.people n all) ← query ⟨owner ++ ["people".toUTF8], true⟩ (.people s.me.c) then
      modify fun s => { s with people := n, peopleAll := all }

/-- The current page's picture and taps (kept until what it shows changes). -/
def pageTitle : PageId → String × Bool
  | .you => ("You", false)
  | .appearance => ("Appearance", false)
  | .communitySettings => ("Community settings", true)
  | .channelSettings => ("#general", true)
  | .stub => ("", false)
  | .getStarted => ("", false) | .create => ("", false) | .joinChoice => ("", false)
  | .openInvite => ("", false) | .paste => ("", false) | .scan => ("Join with QR code", true)
  | .name => ("", false) | .createName => ("", false)
  | .agree => ("Agree & join", false) | .waiting => ("", false) | .requests => ("Waiting to join", true)
  | .invite => ("Add members", true) | .switcher => ("Communities", true) | .chat => ("", false)
  | .profile => ("", true) | .removeConfirm => ("", true) | .duplicate => ("Warning!", true)
  | .home => ("", false) | .label => ("Full label", true)

/-- A page and its bar, from its key alone (and the font, background and
camera frame): nothing else of the app's state can reach the pixels, so a
cached page whose key matches is the page (`drawPage_key`). -/
def drawPage (f : Font) (bg : ByteArray) (cam : Option Bitmap) (k : PageIn) : Pages.Page × Bitmap :=
  let dm := k.dim
  let W := k.W
  let h := k.h
  let me := k.me
  let pg : Pages.Page := match k.page with
    | .getStarted => Pages.getStarted Pages.Act.joinCommunity Pages.Act.createCommunity f dm W h
    | .create => Pages.create Pages.Act.continue_ Pages.Act.field f dm W h k.field true
    | .joinChoice => Pages.joinChoice Pages.Act.inviteLink Pages.Act.qrCode f dm W h none
    | .openInvite => Pages.openInvite Pages.Act.pasteLink f dm W h
    | .paste => Pages.paste Pages.Act.continue_ Pages.Act.field f dm W h k.field true k.refusal
    | .name => Pages.chooseName Pages.Act.continue_ Pages.Act.field f dm W h k.field
    | .createName => Pages.chooseName Pages.Act.continue_ Pages.Act.field f dm W h k.field
    | .scan => Pages.scan Pages.Act.pasteLink f dm W h cam "Starting the camera…"
    | .agree => Pages.agree Pages.Act.agree f dm W h "this community"
    | .waiting => Pages.waiting Pages.Act.stopWaiting f dm W h (Kinds.Request.hexShort me.c)
        -- the request is stored and waits for the community's ops; until the
        -- network says more, the first beat is where it is
        #[(if me.dialing.isEmpty then "Looking for someone to hand your join to" else s!"Sending your request to {me.dialing}",
            "Quiet sends it again until a member's device answers.", .now),
          ("Waiting for a member to let you in", "Quiet asks again whenever it finds one. They see you waiting the next time they open the app.", .next),
          ("Keys and history arrive", "Then the community opens, with what was shared before you got here.", .next)] #[]
    | .requests => Pages.requests Pages.Act.addMembers Pages.Act.hide Pages.Act.approve f dm W h k.asking
    | .invite => Pages.invite Pages.Act.share Pages.Act.copy f dm W h (k.link.bind fun l => Link.qr l (Pages.qrSide dm W h)) (k.link.getD "…")
    | .switcher => Pages.switcher Pages.Act.switchTo Pages.Act.addMembers Pages.Act.communitySettings Pages.Act.joinCommunity Pages.Act.createCommunity Pages.Act.stub Pages.Act.back f dm W h (k.comms.map fun m =>
        ({ name := m.name, id8 := Pages.identity m.c, unread := 0, current := m.acc == me.acc, waiting := m.waiting } : Pages.Entry))
        k.askingAll (!me.waiting && !me.c.isEmpty)
    | .home => Pages.home Pages.Act.stub Pages.Act.requests Pages.Act.openChannel Pages.Act.person f dm W h (if me.waiting then 0 else k.askingAll) #["general"] k.members k.memberIds
    | .label => Pages.label f dm W h k.labelText k.labelPage
    | .profile => let (n, isMe, removed, can) := k.profile; Pages.profile Pages.Act.you Pages.Act.removeStart f dm W h n isMe removed can
    | .removeConfirm => Pages.removeConfirm Pages.Act.removeYes Pages.Act.removeCancel f dm W h k.profile.1 k.removeStage k.removeWhy
    | .duplicate => Pages.duplicate f dm W h
    | .you => Appearance.you f dm W h k.ownName k.ownId k.comms.size k.devices k.setting
    | .appearance => Appearance.page f dm W h k.setting
    | .communitySettings => Appearance.community f dm W h me.name k.communityId k.people
    | .channelSettings => Appearance.channel f dm W h k.people
    | .stub => Appearance.stub f dm W h k.labelText me.name k.communityId
    | .chat => ⟨Bitmap.blank W h bg, #[]⟩
  let (t, cross) := pageTitle k.page
  -- a first launch's Get started has nowhere to go back to
  let top := if k.page == .home then
      Pages.homeBand f dm W k.insetTop me.name k.communityId k.ownName k.ownId
    else if (k.page == .getStarted && k.backEmpty && k.comms.isEmpty) || k.page == .waiting
    then Bitmap.blank W (k.insetTop + dm.px 56) bg
    else if k.page == .switcher then Pages.switcherBar f dm W k.insetTop
    else if k.page.drawer then Appearance.header f dm W k.insetTop (if k.page == .stub then Appearance.leafTitle k.labelText else t) k.drawerBack
    else Pages.bar f dm W k.insetTop t cross
  (pg, top)

/-- **A page is its key.** Two app states whose keys match draw the same
page and bar (with the same font, background and camera frame): what the
cache relies on to keep a page drawn earlier. -/
theorem drawPage_key (f : Font) (bg : ByteArray) (cam : Option Bitmap) {k k' : PageIn} (h : k = k') :
    drawPage f bg cam k = drawPage f bg cam k' := by rw [h]

/-- The current state's page key. -/
def pageIn (s : St) : PageIn :=
  { page := s.page, setting := s.theme.setting, W := s.W, h := viewH s, insetTop := s.insetTop, dim := s.dim, field := s.field,
    ownName := s.ownName, ownId := Pages.identity s.me.user, communityId := Pages.identity s.me.c, devices := s.ownDevices, people := s.people,
    refusal := s.refusal, me := s.me.key, comms := s.comms.map (·.key),
    asking := (s.asking.filter fun r => !s.hidden.contains r.id).map (·.row), askingAll := s.asking.size,
    link := (s.links.find? (·.1 == s.me.acc)).map (·.2), members := s.members, memberIds := s.memberIds.map Pages.identity,
    backEmpty := s.backStack.isEmpty, drawerBack := s.backStack.head?.any PageId.drawer,
    camFrame := s.camFrame, labelText := s.labelText, labelPage := s.labelPage,
    profile := match s.profileOf with
      | some (u, n, isMe) =>
        let present := s.memberIds.contains u
        (n, isMe, !present, Remove.offered s.amAdmin present s.me.user u)
      | none => ("", false, false, false),
    removeStage := match s.removal with
      | .first _ => 1 | .second _ => 2 | .sending _ => 3 | .failed _ _ => 4 | .idle => 0,
    removeWhy := match s.removal with | .failed _ why => why | _ => "" }

/-- **The current entry is in the key.** Two states with the same page
key (`pageIn`, what the frame draws a page from) are on the same entry
(acceptance), whatever else they share: a switch always redraws. -/
theorem pageIn_acc {s s' : St} (h : pageIn s = pageIn s') : s.me.acc = s'.me.acc := by
  have := congrArg (fun k : PageIn => k.me.acc) h
  simpa [pageIn, Kinds.Accepted.Me.key] using this

/-- Write the removal of user u (the engine's intent). -/
def removeWrite (u : Id) : M Bool := do
  let s ← get
  -- nothing when this device is no admin, u is its own user, already
  -- removed, or not admitted (removeMember_valid: what it writes is a
  -- Valid removal of u by an admin)
  let w ← intentView (Community.removeMember s.me.c u s.me.dev)
  if w.ops.isEmpty then return false
  writeAll w

/-- One step of the removal flow; a write happens only where Remove.step
says (the second yes, or a retry). -/
def removeEv (e : Remove.Ev) : M Unit := do
  let (s', w) := Remove.step (← get).removal e
  modify fun s => { s with removal := s' }
  if let some u := w then
    if !(← removeWrite u) then
      modify fun s => { s with removal := (Remove.step s.removal (.refused "The removal couldn't be written. Try again.")).1 }
  if (← get).removal == .idle then
    -- cancelled: back where it was opened
    if (← get).page == .removeConfirm then back

/-- A refused native candidate is not permission to consult latest text. -/
def refuseSubmission (refusal : Option UInt32) (submission : Option Editor.Snapshot) : M Bool := do
  let some code := refusal | return false
  if code == 0 && submission.isSome then return false
  say (if code == 1 then "Your previous action is still finishing. Try again."
    else if code == 3 then "This message is too large to send. Shorten it and try again."
    else "This editor changed. Please try the action again.")
  return true

/-- A page's tap: what it does. -/
def onPageAct (a : Pages.Act) (submission : Option Editor.Snapshot := none) (refusal : Option UInt32 := none) : M Unit := do
  let s ← get
  match a with
  | .back => back
  | .you => openPage .you
  | .appearance => openPage .appearance
  | .communitySettings => openPage .communitySettings
  | .channelSettings => openPage .channelSettings
  | .stub title =>
    modify fun s => { s with labelText := title }
    openPage .stub
  | .theme setting => setTheme setting
  | .copyLabel => s.io.copy (Label.copied s.labelText); say "Label copied."
  | .labelNext =>
    let n := (Label.lines s.font s.dim s.W s.labelText).size
    let last := (n - 1) / Label.capacity s.dim (viewH s)
    modify fun s => { s with labelPage := min last (s.labelPage + 1) }
  | .labelPrev => modify fun s => { s with labelPage := s.labelPage - 1 }
  | .joinCommunity => openPage .joinChoice
  | .createCommunity =>
    modify fun s => { s with field := "" }
    openPage .create
    s.io.ime true
  | .inviteLink => openPage .openInvite
  | .qrCode => openPage .scan
  | .pasteLink =>
    modify fun s => { s with field := "" }
    openPage .paste
    s.io.ime true
  | .field => s.io.ime true
  | .continue_ =>
    if ← refuseSubmission refusal submission then return
    let field := (submission.map (·.text)).getD s.field
    match s.page with
    | .create =>
      let n := field.trimAscii.toString
      if !n.isEmpty then
        modify fun s => { s with field := "", newCommunity := n }
        if let some action := submission then discard <| s.io.editorIo.action action.ticket 4
        openPage .createName
        s.io.ime true
    | .createName =>
      let me := field.trimAscii.toString
      if !me.isEmpty then
        s.io.ime false
        modify fun s => { s with field := "" }
        if let some action := submission then discard <| s.io.editorIo.action action.ticket 4
        found s.newCommunity me
    | .paste =>
      match Community.Invite.parse field with
      | some i =>
        if let some action := submission then discard <| s.io.editorIo.action action.ticket 4
        takeInvite i
      | none =>
        modify fun s => { s with refusal := some "That isn't a Quiet invite link. Check that you copied all of it.", pageKey := none }
    | .name =>
      let n := field.trimAscii.toString
      if !n.isEmpty then
        s.io.ime false
        modify fun s => { s with joinName := n }
        if let some action := submission then discard <| s.io.editorIo.action action.ticket 4
        openPage .agree
    | _ => pure ()
    if let some action := submission then discard <| s.io.editorIo.action action.ticket 2
  | .agree =>
    -- join: a device of its own for this community, the request the link
    -- asks for, and this device's accept and joining facts, as one write
    if let some i := s.invite then
      let seed ← newSeed
      -- the engine's join: nothing for a held community, the same request
      -- again for a stopped one, else a fresh join
      let w ← intentView (Community.join i seed s.joinName.toUTF8 (← newBytes 32))
      if ← writeAll w then
        modify fun s => { s.withNav (Nav.reset s.page) with invite := none, field := "" }
        refreshCommsNow
        match acceptOf w, (← get).comms.find? (·.c == i.community) with
        | some a, _ => switchToAcc a
        | none, some m => switchToAcc m.acc
        | none, none => pure ()
  | .addMembers => openPage .invite
  | .share | .copy =>
    if let some (_, l) := s.links.find? (·.1 == s.me.acc) then
      s.io.copy l
      say "Invitation copied."
  | .stopWaiting =>
    -- a local op superseding my joining fact: the request stays with the
    -- members, and an approval would still let this device in
    if !s.me.joiningOp.isEmpty then
      if ← writeAll (Community.stopWaiting s.me.joiningOp) then
        refreshCommsNow
        if (← get).comms.isEmpty then
          modify fun s => { s.withNav (Nav.reset .getStarted) with pageKey := none }
        else switchTo 0
  | .approve i =>
    let shown := s.asking.filter fun r => !s.hidden.contains r.id
    if let some r := shown[i]? then
      approveReq r.id
      say s!"Approved <{Kinds.Request.hexShort r.device}>"
  | .hide i =>
    let shown := s.asking.filter fun r => !s.hidden.contains r.id
    if let some r := shown[i]? then modify fun s => { s with hidden := r.id :: s.hidden, pageKey := none }
  | .switchTo i => switchTo i
  | .addCommunity => openPage .getStarted
  | .requests => openPage .requests
  | .person i =>
    if let some u := s.memberIds[i]? then
      let (n, isMe) := s.members[i]!
      modify fun s => { s with profileOf := some (u, n, isMe) }
      openPage .profile
  | .removeStart =>
    if let some (u, _, _) := s.profileOf then
      if Remove.offered s.amAdmin (s.memberIds.contains u) s.me.user u then
        removeEv (.start u)
        openPage .removeConfirm
  | .removeYes => removeEv .yes
  | .removeCancel => removeEv .cancel
  | .openChannel _ =>
    s.io.scrollTo 0
    modify fun s => { openSt .chat s with chromeKey := "" }
  | .none => pure ()

def closeSheet : M Unit := do
  let s ← get
  if (s.sheet.map (·.searching)).getD false then
    s.io.ime false
  modify fun s => { s with sheet := none, selected := none }

/-- The same shaping and glyph painter as a message body, at its current
width/theme. This runs once per composer action and stops at the first
visible line; completely inkless drafts have no presentation to promise. -/
def composerHasInk (s : St) (text : String) : Bool := Id.run do
  let font := s.font.atSize (s.dim.px (if s.wide then 14 else 15))
  let width := s.W - s.dim.textX - s.dim.pad
  let canvas := Bitmap.blank width (max 1 s.dim.lineH) (s.bgRow.extract 0 (4 * width))
  for paragraph in text.splitOn "\n" do
    for line in Text.layoutFine font width paragraph do
      let pixels := canvas.line font (Row.flush line) 0 (s.dim.px (if s.wide then 3 else 5))
        (Palette.color s.dim.theme .fg)
      if pixels.rows != canvas.rows then return true
  return false

/-- Send what the composer holds: its text and photos, as the engine's
send intent (the post sealed under the community's current key, then
each photo's attachment and chunks), one write. -/
def sendNow (submission : Option Editor.Snapshot := none) (refusal : Option UInt32 := none) : M Unit := do
  try
    if ← refuseSubmission refusal submission then return
    let s ← get
    if s.photoRequest.isSome then say "Finishing the selected photo…"; return
    let t := ((submission.map (·.text)).getD s.text).trimAscii.toString
    if t.isEmpty && s.chips.isEmpty then return
    -- String stores its UTF-8 byte length. Reject an impossible payload
    -- before allocating/shaping it merely to check whether it has ink.
    if t.utf8ByteSize > Sync.maxFrame then
      say "This message is too large to send. Shorten it and try again."
      return
    if s.chips.isEmpty && !composerHasInk s t then
      say "Add visible text or a photo."
      return
    let k? ← intentView (Community.currentKey s.me.c)
    let some k := k? | say "This community's key hasn't arrived yet."; return
    let mut files := []
    for (bytes, w, h, _) in s.chips.toList do
      files := files ++ [({ info := { name := "photo.qoi".toUTF8, kind := "image/qoi".toUTF8, w, h,
                                      preview := Chaos.preview bytes },
                            bytes, key := ← newBytes 32, nonce := ← newBytes 24,
                            metaNonce := ← newBytes 24 } : Community.NewFile)]
    let nonce ← newBytes 24
    let w ← intentView (Community.send s.me.c s.me.adm s.me.dev k nonce t.toUTF8 (← nowMin) files)
    if ← writeAll w (present := true) then
      if let some action := submission then
        discard <| s.io.editorIo.action action.ticket 3
        if let some latest ← readEditor then adoptEditor latest
        modify fun s => { s with chips := #[], chromeKey := "", editorContent := s.editorContent + (if s.chips.isEmpty then 0 else 1), editor := { s.editor with clear := some (action.ticket, action.revision) } }
      else
        modify fun s => { s with text := "", sel := #[0, 0, 0, 0], chips := #[], chromeKey := "", editorContent := s.editorContent + (if s.chips.isEmpty then 0 else 1) }
  finally
    if let some action := submission then discard <| (← get).io.editorIo.action action.ticket 2

/-- A photo prepared for sending: at most 2048 px a side, as QOI, with its
chip (a 64 dp square crop) and how much smaller than its raw pixels it is. -/
def preparePhoto (dm : Dim) (src : Image.Src) : ByteArray × Nat × Nat × Composer.Chip :=
  let (w, h) := if src.w ≤ 2048 && src.h ≤ 2048 then (src.w, src.h) else Image.fit src 2048 2048
  let px := Chaos.cropPx src 0 0 src.w src.h w h
  let bytes := Image.encode w h px
  let raw := w * h * 4
  let pct := 100 - bytes.size * 100 / max raw 1
  let thumb := Image.square src (dm.px 64) (Palette.color dm.theme .bg)
  (bytes, w, h, ⟨thumb, s!"{Arrival.humanBytes bytes.size} · {pct}% smaller"⟩)

/-- Deterministic development-control fixture; never the composer button. -/
def attachSamplePhoto : M Unit := do
  let s ← get
  if s.chips.size ≥ Composer.maxChips then say "At most 4 photos in one message."; return
  let i := s.photoNext % 6
  match ← (IO.FS.readBinFile s!"assets/{i}.qoi").toBaseIO with
  | .ok b =>
    match Image.decode b with
    | some src => modify fun s => { s with editorContent := s.editorContent + 1, chips := s.chips.push (preparePhoto s.dim src), photoNext := s.photoNext + 1, chromeKey := "" }
    | none => say "That photo could not be read."
  | .error _ => say "No photos here."

/-- The composer requests one OS selection. Its bytes are prepared on a
worker; frame/input work never waits for a full-size decode or QOI encode. -/
def attachPhoto : M Unit := do
  let s ← get
  if s.page != .chat then return
  if s.chips.size ≥ Composer.maxChips then say "At most 4 photos in one message."; return
  if s.photoRequest.isSome then say "Finishing the selected photo…"; return
  let token := if s.photoSerial + 1 == 0 then 1 else s.photoSerial + 1
  modify fun s => { s with photoSerial := token }
  s.io.ime false
  if ← s.io.pickPhoto token then
    modify fun s => { s with photoRequest := some ⟨token, s.cur, false⟩, photoWork := none, chromeKey := "" }
  else say "Photo selection is not available on this platform yet."

def photoStep : M Unit := do
  let s ← get
  let some request := s.photoRequest | return
  unless request.accepts request.token s.cur (s.page == .chat) do cancelPhoto; return
  if let some task := s.photoWork then
    unless ← IO.hasFinished task do return
    let result := task.get
    modify fun s => { s with photoWork := none, photoRequest := none }
    match result with
    | some chip =>
      if s.chips.size < Composer.maxChips then
        modify fun s => { s with editorContent := s.editorContent + 1, chips := s.chips.push chip, chromeKey := "" }
    | none => say "That photo could not be read."
    return
  let (header, bytes) ← s.io.photoResult
  if header.isEmpty then return
  unless request.accepts (header[0]?.getD 0) s.cur (s.page == .chat) do return
  let status := header[1]?.getD 3
  if status == 4 then
    modify fun s => { s with photoRequest := some { request with selected := true } }
  else if status == 2 then
    modify fun s => { s with photoRequest := none }
  else if status != 1 then
    modify fun s => { s with photoRequest := none }
    say "That photo could not be read."
  else
    let dm := s.dim
    let task ← BaseIO.asTask (prio := .dedicated) do
      return (Photo.pixels header bytes).map (preparePhoto dm)
    modify fun s => { s with photoWork := some task, photoRequest := some { request with selected := true } }

def mineOn (s : St) (m : Id) : List String :=
  ((s.rows[m]?.map (·.data.tallies)).getD []).filter (·.mine) |>.map (·.emoji)

/-- A tap on the sheet: the key under the finger (SheetGeom.hit_iff: the
one drawn there). -/
def onSheetTap (sh : SheetSt) (x y : Nat) : M Unit := do
  let s ← get
  let some m := s.selected | closeSheet
  if !sh.catalog then
    match Sheet.hitQuick s.dim s.W x y with
    | .react e =>
      if !(mineOn s m).contains e then let _ ← reactTo m e
      closeSheet
    | .browse =>
      let sh' := { sh with catalog := true, scroll := 0 }
      modify fun s => { s with sheet := some sh' }
    | .copy =>
      if let some r := s.rows[m]? then s.io.copy r.data.text
      closeSheet
    | .none => pure ()
  else
    let items := sheetItems s sh
    let c := catOf s sh
    match Sheet.hitCat c sh.scroll x y with
    | .back =>
      if sh.searching then s.io.ime false
      let sh' := { sh with catalog := false, searching := false, query := "" }
      modify fun s => { s with sheet := some sh' }
    | .search =>
      s.io.ime true
      modify fun s => { s with sheet := some { sh with searching := true } }
    | .tone t => modify fun s => { s with sheet := some { sh with tone := t } }
    | .category k =>
      if sh.searching then s.io.ime false
      let sh' := { sh with cat := k, scroll := 0, query := "", searching := false }
      modify fun s => { s with sheet := some sh' }
    | .pick i =>
      if let some it := items[i]? >>= (s.catalog[·]?) then
        let e := it.toned sh.tone
        if !(mineOn s m).contains e then let _ ← reactTo m e
      closeSheet
    | .none => pure ()

/-- A drag on the catalogue's grid scrolls it, and a release flings it. -/
def onSheetDrag (phase x y : Nat) : M Unit := do
  let s ← get
  let some sh := s.sheet | return
  if !sh.catalog then return
  let now := (← s.io.nowUs).toNat / 1000
  let c := catOf s sh
  match phase with
  | 0 =>
    let sh' := { sh with drag := some (y, sh.scroll), lastY := y, lastT := now, vel := 0 }
    modify fun s => { s with sheet := some sh' }
  | _ =>
    match sh.drag with
    | none => pure ()
    | some (y0, s0) =>
      let target := (Int.ofNat s0 + Int.ofNat y0 - Int.ofNat y).toNat
      let dt := max 1 (now - sh.lastT)
      let v := (Float.ofNat sh.lastY - Float.ofNat y) / Float.ofNat dt
      let vel := if phase == 2 then sh.vel else sh.vel * 0.5 + v * 0.5
      let sh' := { sh with scroll := c.grid.clamp target, lastY := y, lastT := now, vel := vel,
                           drag := if phase == 2 then none else sh.drag }
      modify fun s => { s with sheet := some sh' }
  let _ := x

/-- Long-press a compact label to read every line and copy its source. -/
def showLabel (text : String) : M Unit := do
  closeSheet
  modify fun s => { s with labelText := text, labelPage := 0 }
  openPage .label

/-- A long press on a compact label opens it in full: the community's
header (home or the conversation), a page's row naming a community or a
person, or a profile. True when it did. -/
def longLabel (r : Region) (x y : Nat) : M Bool := do
  let s ← get
  let name ← match r with
    | .header => pure (if s.page == .home || s.page == .chat then some s.me.name else none)
    | .list =>
      let vh := viewH s
      if s.page == .chat || y ≥ vh then pure none
      else if s.page == .profile then pure (s.profileOf.map (·.2.1))
      else
        let pg := (s.pageNow).getD (drawPage s.font s.bgRow s.camView (pageIn s)).1
        pure (Pages.fullLabel (pg.hit x (vh - 1 - y)) (s.comms.map (·.name)) (s.members.map (·.1)))
    | .composer => pure none
  let some name := name | return false
  showLabel name
  return true

def onTap (r : Region) (x y : Nat) (long : Bool) (submission : Option Editor.Snapshot := none) (refusal : Option UInt32 := none) : M Unit := do
  let s ← get
  -- A transient toast never intercepts the underlying action.
  modify fun s => { s with toast := none, noticeClock := none }
  -- a tap puts a standing notice away
  if !s.notices.isEmpty then
    modify fun s => { s with notices := s.notices.drop 1 }
    return
  if long then if ← longLabel r x y then return
  -- a page: its bar's back, or its content's taps (rows from its top)
  if s.page != .chat then
    match r with
    | .header =>
      if s.page == .home then openPage (if x ≥ s.W - s.dim.px 60 then .you else .switcher)
      else if s.page == .switcher then
        if x < s.dim.px 50 || x ≥ Pages.switcherWidth s.dim s.W then back
      else if (Pages.barBack s.dim s.insetTop).has x y then back
    | .list =>
      let vh := viewH s
      let pg := (s.pageNow).getD (drawPage s.font s.bgRow s.camView (pageIn s)).1
      let height := if s.page.scrolls then pg.bmp.h else vh
      if y < height then
        let hit := pg.hit x (height - 1 - y)
        if !(long && hit == .continue_) then onPageAct hit submission refusal
    | .composer => pure ()
    return
  if let some sh := s.sheet then
    if r == .composer then onSheetTap sh x y; return
    if r == .header then closeSheet; return
  if !Occlusion.active s.sheet.isSome .page then
    closeSheet
    return
  match r with
  | .composer =>
    match Composer.hit (composerLayout s) x y with
    | .text => modify (fun s => { s with editorFocused := true, chromeKey := "" }); s.io.ime true
    | .send => if !long then sendNow submission refusal
    | .addPhotos => attachPhoto
    | .takePhoto => say "Taking a photo arrives with the native camera."
    | .emoji | .mention | .voice => say "Not yet."
    | .removeChip i =>
      if i == s.chips.size && s.photoRequest.isSome then cancelPhoto
      else modify fun s => { s with editorContent := s.editorContent + 1, chips := s.chips.eraseIdxIfInBounds i, chromeKey := "" }
    | .none => pure ()
  | .header =>
    match headerHit s x y with
    | .home => back
    | p => openPage p
  | .list =>
    if s.imeH > 0 && !long then s.io.ime false; return
    -- an open sheet: a tap on the list closes it
    if s.sheet.isSome && !long then
      closeSheet; return
    match rowAt s y with
    | none => pure ()
    | some (m, ry) =>
      match s.rows[m]? with
      | none => pure ()
      | some row =>
        if long then
          -- the long press: the sheet for this message
          if s.imeH > 0 then s.io.ime false
          modify fun s => { s with selected := some m, sheet := some {} }
        else match Row.hit row.lay x ry with
          | .pill e =>
            if !(row.data.tallies.any fun t => t.emoji == e && t.mine) then
              let _ ← reactTo m e
          | .twin => openPage .duplicate
          | _ => pure ()

/-- Shell coordinates are checked against the current safe rectangle,
then translated to the content coordinates used by the existing handlers. -/
def onScreenTap (r : Region) (x y : Nat) (long : Bool) (submission : Option Editor.Snapshot := none) (refusal : Option UInt32 := none) : M Unit := do
  let s ← get
  let g := geom s
  let sy := match r with
    | .header => y
    | .composer => g.composerTop + y
    | .list => if s.page == .chat || s.page.scrolls then (Int.ofNat g.composerTop - 1 - (Int.ofNat y - s.b)).toNat
      else g.composerTop + g.shift - 1 - y
  let i := { s.window with ime := ⟨0, 0, 0, s.imeH⟩ }
  if (Safe.target i ⟨x, sy, 1, 1⟩).isNone then return
  onTap r (x - (Safe.content i).x) y long submission refusal

def plainEvent (event : Event) (submission : Option Editor.Snapshot := none) (refusal : Option UInt32 := none) : M Bool := do
  let refusal := if refusal.isNone && submission.isNone && (← get).editor.enabled == some true then some 2 else refusal
  match event with
  | .action ticket _ _ _ => do discard <| (← get).io.editorIo.action ticket 5; return true
  | .close => do suspend; return false
  | .background => do
    suspend
    modify fun s => { s with active := false }
    return true
  | .foreground => do modify fun s => { s with active := true }; return true
  | .surface present => do
    if !present then suspend
    modify fun s => { s with surface := present }
    return true
  | .resize => do resize (← (← get).io.screen); return true
  | .deepLink url => do
    modify fun s => { s with pendingLinks := s.pendingLinks ++ [url] }
    return true
  | .tap r x y => do onScreenTap r x.toNat y.toNat false submission refusal; return true
  | .long r x y => do onScreenTap r x.toNat y.toNat true submission refusal; return true
  | .text => do
    refreshEditor
    if (← get).editor.enabled == some true then return true
    let (t, sel) ← (← get).io.text
    modify fun s => { textInto s t sel with native := t, editorFocused := s.page == .chat }
    return true
  | .send => do
    if !Occlusion.active (← get).sheet.isSome .page then return true
    if (← get).page == .create || (← get).page == .createName || (← get).page == .paste || (← get).page == .name then
      onPageAct .continue_ submission refusal
      return true
    if (← get).page != .chat then
      if let some action := submission then discard <| (← get).io.editorIo.action action.ticket 2
      say "Open a conversation to send a message."
      return true
    sendNow submission refusal
    return true
  | .ime h => do modify fun s => { s with imeH := h.toNat, chromeKey := "", pageKey := none }; return true
  | .scrolling on => do
    if on then modify fun s => { s with ownSends := {}, presenting := none }
    return true
  | .drag ph x y => do
    if ph == 3 then
      modify fun s => { s with sheet := s.sheet.map fun sh => { sh with drag := none, vel := 0 } }
    else onSheetDrag ph.toNat (x.toNat - (Safe.content (← get).window).x) y.toNat
    return true

/-- One total terminal envelope owns all classified events and its cleanup. -/
def onEvent (event : Event) : M Bool :=
  match event with
  | .action ticket owner refusal events => do
    let io := (← get).io
    try
      refreshEditor
      let s ← get
      let action := Editor.snapshot (← io.editorIo.action ticket 0)
      let valid := owner != 0 && owner == s.editor.owner.toUInt64 &&
        -- A current displayed field can request focus while its native owner
        -- installs. Refusal still reaches Send/Continue, so it cannot submit.
        ((refusal == 1 || refusal == 2 || refusal == 3) || (refusal == 0 && s.editor.contentKey == editorContentKey s &&
          action.any (fun a => a.ticket == ticket && a.owner == owner && a.content == s.editor.content.toUInt64))) &&
        s.active && s.surface && s.life.mounted && s.editor.key == editorKey s
      if !valid then
        discard <| io.editorIo.action ticket 2
        -- Input has already retired pointer/native motion. Retire the App's
        -- sheet drag too; never execute a refused semantic tap or Send.
        for e in events do
          match e with
          | .drag _ x y => discard <| plainEvent (.drag 3 x y)
          | _ => pure ()
        if !events.isEmpty then say (if refusal == 1 then "Your previous action is still finishing. Try again."
          else if refusal == 3 then "This message is too large to send. Shorten it and try again."
          else "This editor changed. Please try the action again.")
        return true
      for e in events do
        if !(← plainEvent e action (some refusal)) then return false
      return true
    finally
      discard <| io.editorIo.action ticket 1
  | e => plainEvent e

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
  s!"frames {s.frames} lean_us avg {avg} p95 {p95} max {mx} paints {s.paints} intent_reads {s.intentReads} rows {s.rows.size} imgs {s.imgs.size}"

/-- One control command; false if it must wait (and the rest behind it). -/
def command (line : String) : M Bool := do
  let s ← get
  let ws := line.splitOn " "
  let rest := String.intercalate " " (ws.drop 1)
  match ws.headD "" with
  | "ping" => s.io.ctlReply "pong"
  | "state" =>
    s.io.ctlReply s!"b {s.b} total {s.total} loaded {s.ids.size} people {s.people} mounted {s.rows.size} ime {s.imeH} text {repr s.text} outbox {s.out.size} busy {← s.wr.busy.get} viewH {viewH s}"
  | "typography" =>
    -- Native accessibility tests read the running font and actual OS report.
    let sc ← s.io.screen
    s.io.ctlReply s!"dpi {s.dim.dpi} cell {s.font.cell} line {s.dim.lineH} W {s.W} H {s.Hs} osDpi {(sc[4]?.getD 0).toNat} generation {s.life.generation}"
  | "stats" => s.io.ctlReply (stats s)
  | "work" => s.io.ctlReply s!"{repr (← s.raster.stats)} owned_queries {(← s.sh.wants).size} picture_queries {s.pictureNeeds.size}"
  | "input" => s.io.ctlReply s!"page {repr s.page} serial {s.input.serial} retained {s.input.frames.map (·.1)} press {s.input.press.isSome} lastTap {s.input.lastTap} generation {s.life.generation}"
  | "reader" =>
    let ws ← s.sh.wants
    let board ← s.sh.board.get
    let window := match board.get? (.clumps s.me.c none s.anchor half half) with
      | some (.window ids _, _) => s!"ids={ids.size}"
      | _ => "missing"
    s.io.ctlReply s!"threaded {s.threaded} active {s.active} surface {s.surface} reader {s.reader.isSome} stopping {s.readerStop.isSome} rst {s.rst.isSome} wants {ws.size} generation {← s.sh.generation} window {window} anchor {s.anchor.isSome} restore {s.restoreAnchor} netStop {s.netStop.isSome}"

  | "invite" => s.io.ctlReply ((s.invite.map (·.text)).getD "")
  | "scans" => s.io.ctlReply s!"{s.scans} frames decoded, camera {if s.camOn then "on" else "off"}, preview {s.camView.isSome}"
  | "hints" =>
    -- the dial hints an invite issued now would carry (writes nothing)
    let r ← (try (do let as ← Std.Net.interfaceAddresses; pure (Except.ok as)) catch e => pure (Except.error (toString e)))
    match r with
    | .error e => s.io.ctlReply s!"error {e}"
    | .ok as =>
      let hs ← listenHints
      s.io.ctlReply s!"{as.size} interfaces; hints {hs.map fun h => (String.fromUTF8? h).getD "?"}"
  | "chaos" =>
    let n := (ws[1]? >>= String.toNat?).getD 500
    let srcs ← match s.srcs with
      | some t => pure t
      | none => IO.asTask loadSrcs >>= fun t => pure (t.map fun r => match r with | .ok a => a | .error _ => #[])
    modify fun s => { s with srcs := some srcs, seed := s.seed + 1 }
    let me := s.me
    let k? ← intentView (Community.currentKey me.c)
    let k := k?.getD .empty
    let seed := s.seed
    let top ← intentView (Community.topCount me.c)
    let now ← nowMin
    -- made off the app's thread; written by `chaosStep` as user actions
    -- are (writeAll: judged, shown pending, through the node)
    let t ← IO.asTask (prio := .dedicated) (pure (Chaos.make me k srcs.get seed n top now))
    s.wr.busy.modify (· + 1)  -- so `wait` waits for the making too
    modify fun s => { s with chaos := some (t.map fun r => match r with | .ok j => j | .error _ => #[]) }
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
  | "tray" =>
    let i := (ws[1]? >>= String.toNat?).getD 0
    match s.ids[i]? with
    | some (_, m) => modify fun s => { s with selected := some m, sheet := some {} }; s.io.ctlReply "sheet open"
    | none => s.io.ctlReply "no such message"
  | "untray" => closeSheet; s.io.ctlReply "sheet closed"
  | "browse" =>
    match s.sheet with
    | some sh => modify fun s => { s with sheet := some { sh with catalog := true } }; s.io.ctlReply "catalogue"
    | none => s.io.ctlReply "no sheet"
  | "sheet" =>
    -- sheet tap X Y | sheet drag PHASE X Y: as the twin would send them
    match ws[1]?, (ws[2]? >>= String.toNat?), (ws[3]? >>= String.toNat?), (ws[4]? >>= String.toNat?) with
    | some "tap", some x, some y, _ => onTap .composer x y false; s.io.ctlReply "tapped"
    | some "drag", some ph, some x, some y => onSheetDrag ph x y; s.io.ctlReply "dragged"
    | _, _, _, _ => s.io.ctlReply "sheet tap X Y | sheet drag PHASE X Y"
  | "found" =>
    -- found COMMUNITY[|MYNAME]
    let (n, me) := match rest.splitOn "|" with
      | [n, me] => (n, me)
      | _ => (rest, "Me")
    found n me
    s.io.ctlReply s!"founded {n}"
  | "switch" =>
    match ws[1]? >>= String.toNat? with
    | some i => switchTo i
    | none =>
      -- by name, for scripts: refused when two entries share it
      match (← get).comms.filter (·.name == rest) with
      | #[m] => switchToAcc m.acc
      | ms => s.io.ctlReply s!"switch: {ms.size} communities named {rest}; use an index"
    s.io.ctlReply s!"current {(← get).me.name}"
  | "theme" =>
    match rest with
    | "system" | "light" | "dark" => setTheme (Theme.decode rest)
    | _ => pure ()
    let t := (← get).theme
    s.io.ctlReply s!"theme {Theme.encode t.setting} effective {repr (Theme.effective t)}"
  | "open" =>
    let p : Option PageId := match ws[1]? with
      | some "you" => some .you | some "appearance" => some .appearance
      | some "getStarted" => some .getStarted | some "create" => some .create | some "join" => some .joinChoice
      | some "openInvite" => some .openInvite | some "paste" => some .paste | some "scan" => some .scan
      | some "agree" => some .agree | some "waiting" => some .waiting | some "requests" => some .requests
      | some "invite" => some .invite | some "switcher" => some .switcher | some "chat" => some .chat
      | _ => none
    match p with
    | some .chat => back; s.io.ctlReply "chat"
    | some p => openPage p; s.io.ctlReply s!"page {repr p}"
    | none => s.io.ctlReply "open getStarted|create|join|openInvite|paste|scan|agree|waiting|requests|invite|switcher|chat"
  | "back" => back; s.io.ctlReply s!"page {repr (← get).page}"
  | "channel" => onPageAct (.openChannel 0); s.io.ctlReply s!"page {repr (← get).page}"
  | "page" =>
    -- page X ROW: a tap at row ROW of the page's content, as a finger would land
    let x := (ws[1]? >>= String.toNat?).getD 0
    let row := (ws[2]? >>= String.toNat?).getD 0
    let vh := viewH (← get)
    onTap .list x (vh - 1 - row) false
    s.io.ctlReply s!"page {repr (← get).page}"
  | "comms" =>
    let st ← get
    s.io.ctlReply (String.intercalate " | " (st.comms.toList.map fun m => s!"{m.name}{if m.c == st.me.c then "*" else ""}"))
  | "asking" => s.io.ctlReply s!"asking {(← get).asking.size}"
  | "pause" => s.wr.setPaused true; s.io.ctlReply "writer paused"
  | "resume" => s.wr.setPaused false; s.io.ctlReply "writer resumed"
  | "bottom" => s.io.scrollTo 0; s.io.ctlReply "ok"
  | "scroll" =>
    s.io.scrollTo ((ws[1]? >>= String.toNat?).getD 0).toFloat; s.io.ctlReply "ok"
  | "top" =>
    let (_, ch) := bottoms s
    s.io.scrollTo ch.toFloat; s.io.ctlReply "ok"
  -- For driving a demo on phones over ctl, as a person would: the link
  -- Add members shows, a page's field typed (on a page whose keyboard is
  -- open, the keyboard's own text replaces it: type there instead), a
  -- button the page shows, Add photos, and the composer sent with its
  -- text and photos.
  | "link" =>
    s.io.ctlReply (((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD "")
  | "field" =>
    modify fun s => { s with field := rest, refusal := none, pageKey := none }
    s.io.ctlReply s!"field {rest.length}"
  | "act" =>
    let a : Option Pages.Act := match ws[1]?, (ws[2]? >>= String.toNat?) with
      | some "continue", _ => some .continue_
      | some "agree", _ => some .agree
      | some "approve", some i => some (.approve i)
      | _, _ => none
    -- only a button the page shows, as a tap could press only that
    let shown := match a, s.pageNow with
      | some a, some pg => pg.taps.any (·.2 == a)
      | _, _ => false
    match a with
    | some a =>
      if shown then onPageAct a; s.io.ctlReply s!"page {repr (← get).page}"
      else s.io.ctlReply s!"no such button on page {repr s.page}"
    | none => s.io.ctlReply "act continue|agree|approve I"
  | "photo" =>
    attachSamplePhoto
    s.io.ctlReply s!"photos {(← get).chips.size}"
  | "pick-photo" =>
    attachPhoto
    s.io.ctlReply "photo picker requested"
  | "photo-status" =>
    s.io.ctlReply s!"photos {s.chips.size} pending {s.photoRequest.isSome} sizes {s.chips.toList.map fun p => (p.2.1, p.2.2.1)} slots {(composerLayout s).chips.size}"
  | "post" =>
    modify fun s => { s with text := rest }
    sendNow
    s.io.ctlReply s!"posted, composer {(← get).chips.size} photos"
  | "pics" =>
    -- the mounted rows with pictures: text, and each picture's chunks here
    let out := s.rows.toList.filterMap fun (_, r) =>
      if r.data.pics.isEmpty then none else
      some s!"{r.data.name}: {String.ofList (r.data.text.toList.take 30)} [{", ".intercalate (r.data.pics.map fun p => s!"{p.got}/{p.total}{if p.complete then " complete" else ""}")}]{if r.shown.isSome && r.task.isNone && (r.painted.2.drop 1).all id then " painted" else ""}"
    s.io.ctlReply (if out.isEmpty then "no pictures mounted" else " | ".intercalate out)
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

/-- The sheet's pixels: quick, or the catalogue composed from its header,
its grid's rows scrolled (painted once per row and kept) and its bar
(SheetGeom.compose: compose_row is about this). -/
def sheetBitmap (sh : SheetSt) (mine : List String) : M Bitmap := do
  let s ← get
  let backdrop := Paint.mixC (Palette.color s.dim.theme .bg) (Palette.color s.dim.theme .scrim) 154
  if !sh.catalog then return Sheet.paintQuick s.font s.dim s.W backdrop mine
  let items := sheetItems s sh
  let c := catOf s sh
  let gk := s!"{sh.cat}|{sh.tone}|{sh.query}|{mine}|{s.W}"
  if gk != s.gridKey then modify fun s => { s with gridKey := gk, gridRows := {} }
  let g := c.grid
  let r0 := sh.scroll / g.key
  let r1 := (sh.scroll + g.vh) / g.key
  for r in [r0:r1 + 1] do
    if !(← get).gridRows.contains r then
      let row := Sheet.gridRow s.font s.dim s.W c s.catalog items sh.tone mine r
      modify fun s => { s with gridRows := s.gridRows.insert r row }
  let rows := (← get).gridRows
  let blank := solid (Palette.color s.dim.theme .panel) s.W
  let line (k : Nat) : ByteArray :=
    let (r, li) := g.lineOf k
    match rows[r]? with
    | some b => b.rows[li]?.getD blank
    | none => blank
  let top := Sheet.catTop s.font s.dim s.W c backdrop sh.query sh.searching sh.tone sh.cat
  let bot := Sheet.catBot s.font s.dim s.W c sh.cat sh.searching
  return { w := s.W, rows := SheetGeom.compose top.rows line g.vh sh.scroll bot.rows }

/-- Protect a page's input too: it is inside the list frame, unlike the
channel's composer. Protecting an unfocused field is harmless. -/
def focusBox (s : St) : Safe.Rect :=
  if s.page == .chat then ⟨0, (geom s).composerTop, s.W, botH s⟩
  else match s.pageNow.bind (fun p => p.taps.find? (·.2 == .field)) with
    | some (b, _) => ⟨b.x, topH s + b.y, b.w, b.h⟩
    | none => ⟨0, 0, 0, 0⟩

/-- The one transient Toast layer, in the current visible viewport. The
frame row accounts for the existing seam's keyboard lift on a channel. -/
def withToast (s : St) (fr : Array ByteArray) (_vh : Nat) : Array ByteArray := Id.run do
  let some t := Toast.showing s.nowMs s.noticeClock <|> Toast.showing s.nowMs s.toast
    | return fr
  let tb := Pages.toast s.font s.dim s.W t
  let g := geom s
  let view : Safe.Rect := ⟨0, g.top, s.W, g.viewNow⟩
  let focused := focusBox s
  let input : Safe.Input := ⟨s.W, s.Hs, ⟨0, s.insetTop, 0, s.insetBot⟩, {}, ⟨0, 0, 0, s.imeH⟩⟩
  let some placed := Toast.layout input view focused tb.w tb.h (SafeFrame.targetPx s.dim.dpi) | return fr
  let r0 := over + (placed.rect.y - g.top) + (if s.page == .chat then g.shift else 0)
  let mut fr := fr
  for k in [0:tb.h] do
    if r0 + k < fr.size then
      fr := fr.set! (r0 + k) (Overlay.toastRow s.dim.theme fr[r0 + k]! tb.rows[k]! placed.rect.x k tb.w tb.h (s.dim.px 16) (max 2 (s.dim.px 2)))
  return fr

/-- Settings and conversations share the native scrolling seam. -/
def scrollHeight (s : St) : Nat :=
  if s.page == .chat then (bottoms s).2
  else if s.page.scrolls then max (viewH s) (s.pageNow.map (·.bmp.h) |>.getD 0)
  else viewH s

/-- The same placement and raw-input boundary on every phone and twin. -/
def present (fr : Array ByteArray) (b : Nat) (pin : Bool) : M (List Event) := do
  refreshEditor
  let work ← get
  work.sh.setNeeds work.queryNeeds
  work.raster.reconcile work.rasterNeeds.toList
  work.raster.pause false
  modify fun s => { s with imgs := s.imgs.filter (fun _ h =>
    work.rasterNeeds.any (fun n => n.key == h.ticket.key)) }
  let s ← get
  let screen := if s.sheet.isSome then SafeFrame.Screen.sheet else if s.page == .chat then .channel
    else if s.page == .home then .home else .page
  let colours := SafeFrame.colours s.dim.theme
  let top := (SafeFrame.band s.window screen colours .top).colour
  let bottom := (SafeFrame.band s.window screen colours .bottom).colour
  s.io.bars top bottom (SafeFrame.lightIcons top) (SafeFrame.lightIcons bottom)
  -- Retain references to the last unobscured frame, not a copied screenshot.
  let pw := Pages.switcherWidth s.dim s.W
  let shadeAlpha := if s.page != .switcher then #[] else (Array.range (s.W - pw)).map fun distance =>
    let shadow := 0.42 * (-(distance.toFloat * distance.toFloat) / (2.0 * (s.dim.px 12).toFloat ^ 2)).exp
    (107.0 + 148.0 * shadow).toUInt64.toNat
  let saved ← IO.mkRef s.lastDisplay
  let display : Session.Show := fun list b over top bot pin words hold => do
    if s.page != .switcher then saved.set (some (words, list, top, bot))
    let shade (rows : Array ByteArray) (start : Int) := if s.page != .switcher then rows else
      rows.mapIdx fun i row => Id.run do
        let y := start + i
        let bg := s.switcherBackdrop[y.toNat]?.getD s.bgRow
        let mut row := row
        for x in [pw - s.dim.px 16:s.W] do
          if x ≥ pw || Paint.getPx row x == Palette.color s.dim.theme .scrim then
            -- CSS mask alpha .42 plus the sheet's soft edge shadow.
            let alpha := if x ≥ pw then shadeAlpha[x - pw]! else 107
            row := Paint.setPx row x (Paint.blendText 0 (Paint.getPx bg x) alpha)
        return row
    let list := shade list (Int.ofNat (geom s).top - Int.ofNat over.toNat)
    let top := shade top 0
    s.io.frame (SafeFrame.extend s.window list) b over (SafeFrame.extend s.window top)
      (SafeFrame.extend s.window bot) pin words (SafeFrame.extend s.window hold)
  let (hold, holdCache) := Hold.cachedMessagePlane s.holdCache ⟨s.bgRow, s.dim, s.W⟩ (geom s).viewNow
  modify fun s => { s with holdCache }
  let result ← Session.present display s.io.motion (geom s) s.dim.dpi
    (scrollHeight s - (geom s).viewNow) s.input fr b over s.topBmp.rows s.botBmp.rows pin
    hold (Hold.period s.dim)
    s.editor.owner.toUInt64 (fun ticket => discard <| s.io.editorIo.action ticket 1)
  let lastDisplay ← saved.get
  modify fun s => { s with input := result.state, lastDisplay }
  -- Session retains the new serial only when the native publication was
  -- accepted; Android can return a failed publication without throwing.
  let published := result.accepted
  if s.page == .chat && s.sheet.isNone then
    if let some e := s.ownSends.head then
      if let some row := s.rows[e.message.2]? then
        let current := row.paintFlight.map (·.handle.ticket)
        let committed := row.shownCommitted && !row.data.pending && row.shown.isSome &&
          row.task.isNone && row.painted.1 == row.ver
        let prior := s.presenting.filter fun p => p.message == e.message.2 &&
          p.generation == s.life.generation && current == some p.ticket && committed
        let mut candidate : Option PresentationCandidate := none
        if published then
          if let some bottom := rowBottom s e.message.2 then
            if let some (bodyY, bodyH) := presentationBand s row then
              let bodyTop := bottom + row.lay.h - bodyY
              let visible := bodyH > 0 && b + bodyH ≤ bodyTop && bodyTop ≤ b + (geom s).viewNow
              let drawn := row.shown.any fun bitmap =>
                let body := bitmap.rows.extract bodyY (bodyY + bodyH)
                let frameRow := over + (b + viewH s - bodyTop)
                !body.isEmpty && fr.extract frameRow (frameRow + body.size) == body
              if visible && committed && drawn then
                candidate := current.map fun ticket =>
                  ⟨e.message.2, result.publication, s.life.generation, ticket⟩
        let receipt (c : Option PresentationCandidate) :=
          Presentation.acknowledge (c.map fun p => (p.frame, p.message))
            ((result.completed.filter fun receipt => receipt.2 == 0).map Prod.fst)
        let (done, presenting) := Presentation.transition
          (fun p => receipt (some p) == some e.message.2) prior candidate published
        modify fun s => { s with
          ownSends := if done then s.ownSends.pop else s.ownSends, presenting }
  return result.events

/-- Lifecycle polling uses the same raw decoder, even with no surface. -/
def pollInput : M (List Event) := do
  let s ← get
  let context : Input.Context := ⟨Surface.make (geom s) (s.page != .chat && !s.page.scrolls) over s.b s.b 0,
    s.dim.dpi, scrollHeight s - (geom s).viewNow, s.editor.owner.toUInt64⟩
  let result ← Session.receive s.io.motion context s.input (← s.io.poll)
    (fun ticket => discard <| s.io.editorIo.action ticket 1)
  modify fun s => { s with input := result.state }
  return result.events

/-- Materialize only nearby clumps into message cells. Every other clump
is one spacer at its last measured extent. A large clump's child window
has two counted spacers; it never becomes a whole-clump paint task. -/
def projectClumps (offset viewport : Nat) (heldRoot : Option Id := none) : M Unit := do
  let s ← get
  let mut ids := #[]
  let mut owners := ({} : Std.HashMap Id Id)
  let mut spacers := ({} : Std.HashSet Id)
  let mut heights := s.heights
  let mut clumps := s.clumps
  let mut spans := s.clumpHeights
  let mut bottom := bottomPad + s.newer * est
  for root in s.roots do
    let old := clumps.getD root.2 {}
    let span := if old.ready then ClumpList.extent root old (heightOf s) est
      else spans.getD root.2 est
    -- A new root/count answer can move the current anchor beyond the old
    -- viewport. Keep its bounded child collection until chatFrame has
    -- corrected the offset; only then can geometry decide visibility.
    let near := Raster.near bottom span offset viewport (over + viewport) || heldRoot == some root.2
    let scope : Component.Scope := ⟨["community".toUTF8, s.me.c, "clump".toUTF8, root.2],
      s.ownSends.head.any (·.root.2 == root.2) || Raster.near bottom span offset viewport 0⟩
    let pinned := s.ownSends.head.filter (fun e => e.root.2 == root.2)
    let old := if let some e := pinned then
      { old with anchor := if e.message.2 == root.2 then none else some e.message } else old
    let old := if s.restoreAnchor && s.anchor.map (·.2) == some root.2 && old.anchor.isNone then
      { old with anchor := s.restorePos.filter (fun p => p.2 != root.2) } else old
    let group ← if near then ClumpList.observe scope s.me.c root.2 old half else pure old
    clumps := clumps.insert root.2 group
    let span := if group.ready then ClumpList.extent root group (heightOf s) est else span
    spans := spans.insert root.2 span
    let cells := if near && group.ready then ClumpList.cells root group (heightOf s) est
      else #[((ByteArray.empty, ClumpList.gap root.2 2), span, true)]
    for (pos, height, spacer) in cells do
      ids := ids.push pos
      owners := owners.insert pos.2 root.2
      if spacer then
        spacers := spacers.insert pos.2
        heights := heights.insert pos.2 height
    bottom := bottom + span
  -- Child ids are retained only for the bounded outer window. Immutable
  -- height hints may outlive a subscription, just like message heights.
  let held := s.roots.foldl (fun (h : Std.HashSet Id) p => h.insert p.2) {}
  modify fun s => { s with
    ids := ids
    cellRoot := owners
    spacers := spacers
    heights := heights
    clumps := clumps.filter (fun id _ => held.contains id)
    clumpHeights := spans }

/-- Each visible child collection follows its own cursor. Moving through
one large clump does not reload siblings or revive offscreen subscriptions. -/
def followClumps (offset viewport : Nat) : M Unit := do
  let s ← get
  let lo := offset - (over + viewport)
  let hi := offset + viewport + over + viewport
  let mut groups := s.clumps
  for root in s.roots do
    if s.ownSends.head.any (·.root.2 == root.2) then continue
    let some group := groups[root.2]? | continue
    let some first := group.ids[0]? | continue
    let some last := group.ids.back? | continue
    let some low := rowBottom s first.2 | continue
    let some lastBottom := rowBottom s last.2 | continue
    let high := lastBottom + heightOf s last.2
    let near := (group.newer > 0 && lo < low) || (group.older > 0 && hi > high)
    let cursorRow := (rowAt s offset).bind fun (x, _) => group.ids.find? (·.2 == x)
    let edge := if offset < low then some first else some last
    let next := Lifecycle.follow group.anchor group.newer (offset ≤ low && group.newer == 0) near cursorRow edge
    if next != group.anchor then groups := groups.insert root.2 { group with anchor := next }
  modify fun s => { s with clumps := groups }

/-- Read and paint only the mounted conversation. -/
def chatFrame : M (Nat × Array Nat × UInt64 × UInt64 × UInt64) := do
  modify fun s => { s with
    ownSends := s.ownSends.keep (fun e => e.acceptance == s.cur && e.community == s.me.c) }
  modify fun s => { s with presenting := s.presenting.filter fun p =>
    p.generation == s.life.generation && s.ownSends.head.any (·.message.2 == p.message) }
  if let some e := (← get).ownSends.head then
    modify fun s => { s with anchor := some e.root }
  -- 3. the list's ids and counts
  let s ← get
  -- the conversation: the messages this device can read (Community.readable,
  -- a union of message.byKey over the keys it holds); one it cannot read
  -- is not in it, and appears when its key's wrap opens (the key's list is
  -- one the view reads)
  -- (read by the reader: Reader.Want.window; the last window stays until
  -- the board has the wanted one, which is applied below, once the row at
  -- the viewport is known)
  -- (the counts beside it are a want of their own, read after the rows:
  -- the placeholders are the counts less the window's rows on each side)
  let idsW := Reader.Want.clumps s.me.c none s.anchor half half
  let countW := Reader.Want.clumpCount s.me.c none s.anchor
  -- (the wants as last set, unless the anchor moved: a steady frame
  -- keeps each held want's ticket, so it starts no new read,
  -- Demand.retained_ticket)
  discard <| query ⟨["community".toUTF8, s.me.c, "messages".toUTF8], true⟩ idsW
  discard <| query ⟨["community".toUTF8, s.me.c, "count".toUTF8], false⟩ countW
  discard <| query ⟨["community".toUTF8, s.me.c, "people".toUTF8], false⟩ (.people s.me.c)
  discard <| query ⟨["community".toUTF8, s.me.c, "total".toUTF8], false⟩ (.count s.me.c none)
  if s.restoreAnchor then
    if let some (x, _) := s.mark then
      discard <| query ⟨["community".toUTF8, s.me.c, "restore".toUTF8, x], true⟩ (.row s.me.c s.me.adm x)
  readerPass
  let bd ← takeBoard
  if let some (.count _ n, _) := bd.get? (.count s.me.c none) then
    modify fun s => { s with total := n }
  let fresh := match bd.get? idsW with
    | some (.window ids nr, _) =>
      -- until this anchor's counts are read, the last placeholders stay
      let (newer, older, total) := match bd.get? countW with
        | some (.count cn co, _) => (cn - min cn nr, co - min co (ids.size - nr), cn + co)
        | _ => (s.newer, s.older, s.total)
      if ids != s.roots || newer != s.newer || older != s.older || s.restoreAnchor then some (ids, newer, older, total)
      else none
    | _ => none
  let s ← get
  -- people: the present members (admitted, not removed), each once
  if let some (.people n all, _) := (← s.sh.board.get).get? (.people s.me.c) then
    modify fun s => { s with people := n, peopleAll := all }
  let tIds ← (← get).io.nowUs
  -- 4. the offset, and the rows the frame and the fetch distance need
  let s ← get
  let (_, ch0) := bottoms s
  let sample ← s.io.scroll ch0.toUInt32 (geom s).viewNow.toUInt32
  let input := Input.sampleOffset (ch0 - (geom s).viewNow) s.input sample.toInt64.toInt
  modify fun s => { s with input }
  let b := input.offset
  -- the anchor: the row at the viewport's bottom edge, and how far into it
  let mut anchor := if let some e := s.ownSends.head then
    some (e.message.2, presentationOffset s e.message.2)
    else if s.restoreAnchor then s.mark else captureAnchor { s with b }
  let heldRoot := s.ownSends.head.map (·.root.2) <|>
    (anchor.bind fun (x, _) => s.cellRoot[x]? <|> s.anchor.map (·.2))
  -- a new window: in place now; the viewport, in its offsets, is where
  -- the anchor row went (`bv`; the native offset `b` follows in 5)
  let mut b := b
  let mut bv := b
  if let some (roots, newer, older, _) := fresh then
    modify fun s => { s with roots, newer, older }
  projectClumps bv (viewH (← get)) heldRoot
  readerPass
  projectClumps bv (viewH (← get)) heldRoot
  -- Child-count changes can move a message even when the outer root list
  -- is unchanged. Resolve its new coordinate before choosing the child
  -- window, queries and paints for this frame.
  if b > 4 || s.restoreAnchor || s.ownSends.head.isSome then
    let s ← get
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        bv := Lifecycle.offset ((bottoms s).1[i]! + heightOf s x) off
      else if s.restoreAnchor && ((← takeBoard).get? (.row s.me.c s.me.adm x)).any (fun (v, _) => v == .row none) then
        anchor := none
        b := 0
        bv := 0
        s.io.scrollTo 0
        modify fun s => { s with mark := none, anchor := none, restoreAnchor := false }
  let s ← get
  let (bots0, _) := bottoms s
  let vh := viewH s
  let fetch := vh
  let lo := if bv ≥ over + fetch then bv - over - fetch else 0
  let hi := bv + vh + over + fetch
  -- the rows the fetch distance needs: the reader's wants, the ids first
  let mut win := #[]
  for i in [0:s.ids.size] do
    let bot := bots0[i]!
    if bot > hi then break
    if bot + heightOf s s.ids[i]!.2 ≥ lo && !s.spacers.contains s.ids[i]!.2 then win := win.push s.ids[i]!.2
  if let some e := s.ownSends.head then
    win := #[e.message.2] ++ win.filter (· != e.message.2)
  for x in win do
    let visible := s.ownSends.head.any (·.message.2 == x) ||
      Raster.near ((s.ids.findIdx? (·.2 == x)).map (fun i => bots0[i]!) |>.getD 0)
      (heightOf s x) bv vh 0
    discard <| query ⟨Raster.messageOwner s.me.c x, visible⟩ (.row s.me.c s.me.adm x)
    -- A collection already knows its owning message's identity. Mount
    -- it alongside the message, rather than waiting a frame for its text.
    let scope : Component.Scope := ⟨Raster.messageOwner s.me.c x, visible⟩
    let old := (s.rows[x]?).map (·.data.pics) |>.getD []
    let ids ← Component.attachments (scope.child "attachments" x) s.me.c x (old.map (·.attachment))
    for id in ids do
      discard <| Component.attachment (scope.child "attachment" id) s.me.c id (old.find? (·.attachment == id))
    -- Collections that determine a message's first measured height can
    -- start from its identity, concurrently with its own text query.
    if !s.rows.contains x then
      discard <| Component.emojis (scope.child "reactions" x) s.me.c x []
  modify fun s => { s with b := bv }
  readerPass
  let bd ← takeBoard
  for x in win do mount bd x
  let mounted ← get
  let (childBots, _) := bottoms mounted
  for i in [0:mounted.ids.size] do
    let x := mounted.ids[i]!.2
    if win.contains x then mountChildren x childBots[i]! bv vh
  -- the window follows the viewport: once its edge with messages beyond
  -- comes within the fetch distance, it is read again about the row at
  -- the viewport (or its nearest end); pinned to the newest, it is the
  -- newest, and away from it always about a row, so arrivals cannot push
  -- the row being read out of it (Lifecycle.follow_away)
  projectClumps bv vh
  let s ← get
  let (bots, _) := bottoms s
  if fresh.isSome || ((← takeBoard).get? idsW).isSome then
    let winLo := bots[0]?.getD (bottomPad + s.newer * est)
    let winHi := match s.ids.back? with
      | some (_, x) => bots.back!.add (heightOf s x)
      | none => winLo
    let near := (s.newer > 0 && lo < winLo) || (s.older > 0 && hi > winHi)
    let next := Lifecycle.follow s.anchor s.newer (bv ≤ 4) near
      ((rowAt s bv).bind fun (x, _) => s.cellRoot[x]?.bind fun r => s.roots.find? (·.2 == r))
      (if bv < winLo then s.roots[0]? else s.roots.back?)
    if s.ownSends.head.isNone && next != s.anchor then modify fun s => { s with anchor := next }
  followClumps bv vh
  let tMount ← (← get).io.nowUs
  -- 5. keep the anchor still (unless pinned to the newest)
  if let some e := s.ownSends.head then
    anchor := some (e.message.2, presentationOffset s e.message.2)
  if b > 4 || s.restoreAnchor || s.ownSends.head.isSome then
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        let b' := Lifecycle.offset (bots[i]! + heightOf s x) off
        if b' != b then
          -- the content's new range first (a new window, its placeholders):
          -- a shell clamps a shift to the range it was last told
          let cur ← s.io.scroll (bottoms s).2.toUInt32 (geom s).viewNow.toUInt32
          s.io.scrollBy (b'.toFloat - cur)
          b := b'
  -- 6. paint what the frame shows
  let flo := if b ≥ over then b - over else 0
  let fhi := b + vh + over
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    if bot > fhi then break
    if bot + heightOf s s.ids[i]!.2 ≥ flo then paintRow s.ids[i]!.2 bot b vh
  let tPaint ← (← get).io.nowUs
  -- Retire paints when their row leaves the retained window.
  let s ← get
  let mut rows := s.rows
  for (x, r) in s.rows.toList do
    if !win.contains x then
      retireRow r
      rows := rows.erase x
  modify fun s => { s with
    rows, b, mark := anchor,
    restoreAnchor := s.restoreAnchor && !(s.ids.any fun p => some p.2 == anchor.map (·.1)) }
  modify fun s => { s with mark := if s.restoreAnchor then s.mark else captureAnchor s }
  return (b, bots, tIds, tMount, tPaint)

/-- One frame; the twin's events for the next one, or none when the
window closes. -/
def frame (evs : List Event) (lease : Lifecycle.Lease) (inputPage : PageId × Id) : M (Option (List Event)) := do
  let t0 ← (← get).io.nowUs
  -- 1. notices
  let s ← get
  let (fs, vs) ← takeChanges
  if !fs.isEmpty || !vs.isEmpty then
    -- an op whose verdict the store recorded leaves the outbox (the store
    -- answers for it, same id)
    let judged : Std.HashSet Id := vs.foldl (fun a (x, _) => a.insert x) {}
    let decided := s.out.filter fun p => judged.contains p.op.id
    -- the store changed: an image waiting for its chunk ops tries again now
    modify fun s => { s with
      out := s.out.filter fun p => !judged.contains p.op.id }
    if !decided.isEmpty then noticeLocal decided.toList
  flushNode
  -- the reader's acts: their writes go to the node (or the writer)
  let _ ← takeDone
  chaosStep
  let tNotices ← (← get).io.nowUs
  -- 2. events and commands
  for e in evs do
    match e with
    | .ime h =>
      let s ← get
      if s.active && s.surface && s.life.mounted && inputPage == (s.page, s.cur) then
        discard <| onEvent (.ime h)
    | .action _ _ _ [.send] => if !(← onEvent e) then return none
    | .action ticket owner refusal events =>
      match ← owned lease (onEvent e) with
      | some false => return none
      | some true => pure ()
      | none => discard <| onEvent (.action ticket owner 6 events)
    | _ =>
      if let some false ← owned lease (onEvent e) then return none
  let cmds ← (← get).io.ctlPoll
  modify fun s => { s with ctl := s.ctl ++ cmds }
  let mut queue := (← get).ctl
  while !queue.isEmpty do
    if ← command queue[0]! then queue := queue.extract 1 queue.size else break
  modify fun s => { s with ctl := queue }
  -- the native field holds the string it now edits (a page or sheet
  -- change chose another)
  syncText
  photoStep
  let tCommands ← (← get).io.nowUs
  mountPage
  let (b, bots, tIds, tMount, tPaint) ← if (← get).page == .chat then chatFrame else do
    readerPass
    let t ← (← get).io.nowUs
    pure (0, #[], t, t, t)
  -- the sheet's fling: its velocity carries the grid, decaying
  let s ← get
  if let some sh := s.sheet then
    if sh.catalog && sh.drag.isNone && (sh.vel > 0.05 || sh.vel < -0.05) then
      let c := catOf s sh
      let next := (Int.ofNat sh.scroll + (sh.vel * 16.0).toInt64.toInt).toNat
      let sh' := { sh with scroll := c.grid.clamp next, vel := sh.vel * 0.95 }
      modify fun s => { s with sheet := some sh' }
  -- join requests for the current community, and admissions they complete
  refreshComms
  refreshAsking
  refreshMembers
  refreshHomeCount
  let viewPage := (← get).page
  observeSettings ["page".toUTF8, (← get).cur, "settings".toUTF8]
    (viewPage == .you || viewPage == .home) (viewPage == .communitySettings || viewPage == .channelSettings)
  netStep
  scanStep
  -- admitted in a community I joined: my first profile (the name I chose),
  -- in every community this device is admitted to, not only the current
  -- one (a join approved while another is on screen still introduces
  -- itself). introduce is a view run through the live cache, so it is
  -- re-evaluated only when a list it read changes, and writes nothing once
  -- a profile is filed or in the outbox
  let s ← get
  for m in s.comms do
    if m.waiting then continue
    if let some (.writes ops) ← query ⟨["session".toUTF8, m.acc, "maintenance".toUTF8], false⟩ (.maintenance m.c) then
      if (s.serviceSeen[m.c]?).getD [] != ops then
        if ← writeAll ⟨ops.filterMap Op.decode⟩ then
          modify fun s => { s with serviceSeen := s.serviceSeen.insert m.c ops }
  let tRefresh ← (← get).io.nowUs
  -- a frame over 20 ms says where its time went (logcat / stderr)
  let slow (t1 : UInt64) : IO Unit := do
    if t1 - t0 > 20000 then
      let ms (a b : UInt64) := s!"{(b - a) / 1000}"
      s.io.log s!"slow frame {ms t0 t1} ms: notices {ms t0 tNotices} commands {ms tNotices tCommands} ids {ms tCommands tIds} mount {ms tIds tMount} paint {ms tMount tPaint} refresh {ms tPaint tRefresh} frame {ms tRefresh t1}"
  -- a community this device waits to join shows Waiting in place of its
  -- conversation (read: no admission for my device there)
  let s ← get
  if (s.page == .chat || s.page == .home) && s.me.waiting && !s.me.c.isEmpty then
    modify fun s => { s.withNav (Nav.swap .waiting s.nav) with pageKey := none }
  if s.page == .waiting && !s.me.waiting then
    modify fun s => { s.withNav (Nav.swap .home s.nav) with pageKey := none }
    say "You're in."
  mountPage
  -- a page instead of the conversation: its bar, its content in the list
  -- layer (which does not scroll on a page), a one-row composer layer
  let s ← get
  if s.page != .chat then
    let key := pageIn s
    if some key != s.pageKey then
      let (pg, top) := drawPage s.font s.bgRow s.camView key
      let bot := Bitmap.blank s.W 1 s.bgRow
      modify fun s => { s with pageNow := some pg, pageKey := some key }
      modify fun s => { s with topBmp := top, botBmp := bot, chromeKey := "" }
    let s ← get
    let vh := viewH s
    let height := scrollHeight s
    let maxB := height - vh
    if s.page.scrolls && !s.pageScrollStarted then
      -- Publish the extent before moving: native scrollTo clamps to it.
      discard <| s.io.scroll height.toUInt32 vh.toUInt32
      s.io.scrollTo maxB.toFloat
      modify fun s => { s with pageScrollStarted := true }
    let sample ← s.io.scroll height.toUInt32 vh.toUInt32
    let input := Input.sampleOffset maxB s.input sample.toInt64.toInt
    let b := if s.page.scrolls then input.offset else 0
    let top := height - vh - b
    let mut fr := Array.replicate (vh + 2 * over) s.bgRow
    if let some pg := s.pageNow then
      for k in [0:fr.size] do
        if top + k ≥ over then
          if let some row := pg.bmp.rows[top + k - over]? then fr := fr.set! k row
    let shown := withToast s fr vh
    modify fun s => { s with input }
    let t1 ← s.io.nowUs
    slow t1
    modify fun s => { s with b, frames := s.frames + 1, times := s.times.push (t1 - t0).toNat }
    return some (← present shown b (!s.page.scrolls))
  -- 7. chrome and the frame
  let s ← get
  let sheetKey := match s.sheet, s.selected with
    | some sh, some m => s!"{sh.catalog}|{sh.cat}|{sh.tone}|{sh.query}|{sh.searching}|{sh.scroll}|{mineOn s m}"
    | _, _ => ""
  let key := s!"{s.W}|{s.insetTop}|{s.total}|{s.people}|{s.peopleAll}|{s.text}|{s.sel}|{sheetKey}|{s.me.name}|{s.asking.size}|{s.chips.size}|{s.photoRequest.isSome}|{photoLoading s}|{if photoLoading s then s.frames / 4 % 8 else 0}"
  if key != s.chromeKey then
    let bot ← match s.sheet, s.selected with
      | some sh, some m => sheetBitmap sh (mineOn s m)
      | _, _ => pure (composer s)
    modify fun s => { s with topBmp := header s, botBmp := bot, chromeKey := key }
  let s ← get
  let input := Input.sampleOffset ((bottoms s).2 - (geom s).viewNow) s.input b
  modify fun s => { s with input }
  let b := input.offset
  let fr := withToast s (listFrame s b bots) (viewH s)
  let t1 ← s.io.nowUs
  slow t1
  let times := (if s.times.size ≥ 600 then s.times.extract 300 s.times.size else s.times).push (t1 - t0).toNat
  modify fun s => { s with
    b := b
    frames := s.frames + 1
    times := times
    mark := if s.restoreAnchor then s.mark else captureAnchor { s with b } }
  return some (← present fr b false)

/-- One frame, in one read transaction: every read it makes, and the
notices it takes (`takeChanges`, its first read), are of one moment of the
store, so no part of the screen is newer than another. -/
def stepCore (evs : List Event) : M (Option (List Event)) := do
  let io := (← get).io
  let polled ← pollInput
  try
    let incoming := evs ++ polled ++ (← io.links).toList.map Event.deepLink
    let lease := (← get).life.lease
    let inputPage := ((← get).page, (← get).cur)
    let mut input := []
    for e in incoming do
      match e with
      | .background | .foreground | .surface _ | .resize | .deepLink _ | .close =>
        if !(← onEvent e) then return none
      | _ => input := input ++ [e]
    reap
    let s ← get
    if !s.active || !s.surface || s.netStop.isSome then
      IO.sleep 16
      return some []
    let sc ← io.screen
    systemTheme (Theme.ofWord (sc[5]?.getD 0))
    resize sc
    modify fun s =>
      if s.notices.head? != s.noticeClock.map (·.1) then
        { s with noticeClock := s.notices.head?.map fun t => (t, s.nowMs + Toast.life) }
      else if s.noticeClock.isSome && (Toast.showing s.nowMs s.noticeClock).isNone then
        { s with notices := s.notices.drop 1, noticeClock := none }
      else s
    -- A complete snapshot outranks keyboard events queued for an older frame.
    if sc.size ≥ 9 then input := input.filter fun e => match e with | .ime _ => false | _ => true
    mountPage
    let links := (← get).pendingLinks
    modify fun s => { s with pendingLinks := [] }
    for url in links do
      match Community.Invite.parse url with
      | some i => takeInvite i
      | none => say "That isn't a Quiet invite link."
    let rd := (← get).rd
    rd.exec "BEGIN"
    let r ← try
      let r ← frame input lease inputPage
      rd.exec "COMMIT"
      pure r
    catch e =>
      rd.exec "ROLLBACK"
      throw e
    let mut queued := []
    for bytes in (← get).queuedWrites do
      if let some op := Op.decode bytes then
        if (← (Q.op op.id).run rd #[]) == .bytes none then queued := queued ++ [bytes]
    modify fun s => { s with queuedWrites := queued }
    saveCheckpoint
    return r
  finally
    for ticket in Input.actionTickets (evs ++ polled) do discard <| io.editorIo.action ticket 5

/-- Raster work remains enabled during frame assembly. Repeated frames
must not revoke its service opportunity; demand tickets still revoke obsolete
publication, and the worker never holds its bookkeeping lock during paint. -/
def step (evs : List Event) (roots : Array (Demand.Need Reader.Want) := #[]) : M (Option (List Event)) := do
  modify fun s => { s with
    rasterNeeds := #[], queryNeeds := roots,
    querySeen := roots.foldl (fun out n => out.insert (n.owner, n.key, n.visible)) {}, imgWaiting := {} }
  try stepCore evs
  catch error =>
    -- Revoke even a token returned by the final publication if a later
    -- checkpoint/IO exception prevents the next consumer turn.
    discard <| (← get).io.editorIo.exchange 3 0 0 ""
    throw error

partial def loop (evs : List Event) : M Unit := do
  match ← step evs with
  | none => pure ()
  | some evs => loop evs

/-- The app's state at start: the window's size, the font, both
connections, this node's identity (the community founded on first run). -/
def start (io : Io) (screen : Array UInt32) (dbPath : String) (net : Option (Nat × Bool) := none) :
    IO St := do
  let window := SafeFrame.report screen
  let safe := Safe.content { window with ime := {} }
  let W := safe.w
  let Hs := window.h
  let font ← Font.load (density := (screen[4]?.getD 420).toNat)
  let font := font.atSize (((screen[4]?.getD 420).toNat * 15 + 80) / 160)
  let rd ← openDb dbPath
  Lifecycle.init rd
  let saved ← Lifecycle.load rd
  if let some (_, _, _, _, _, bs) := saved then
    let queued := (Codec.decode (bs[10]?.getD .empty) : Option (List ByteArray)).getD []
    let ops := queued.filterMap Op.decode
    if !ops.isEmpty then (receive fam (intake fam true ops)).run rd
  let setting ← Theme.load rd
  let wr ← Writer.start dbPath commitCheckpoint
  let theme : Theme.State := ⟨setting, Theme.ofWord (screen[5]?.getD 0)⟩
  io.appearance (Theme.effective theme == .dark) (Palette.color (Theme.effective theme) .bg)
  -- the communities are this device's accepted facts: read them once
  -- here to choose the first page
  let sh ← Reader.Shared.new wr.count
  let raster ← Work.Pool.new
  let ((all, _), _) ← (Kinds.Accepted.read : Reader.RM _).run { rd }
  let comms := Kinds.Accepted.listed all
  let me := comms[0]?.getD default
  let catalog ← match ← (Sheet.loadCatalog).toBaseIO with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"no emoji catalogue: {e}"; pure #[]
  let initial : St := {
           io := io, theme := theme, W := W, Hs := Hs, insetTop := safe.y, window, imeH := window.ime.bottom, catalog := catalog,
           dim := ⟨(screen[4]?.getD 420).toNat, font.cell, Theme.effective theme, none⟩,
           insetBot := Hs - safe.bottom, font := font, bgRow := solid (Palette.color (Theme.effective theme) .bg) W, rd := rd,
           wr := wr, me := me, comms := comms, cur := me.acc, page := if comms.isEmpty then .getStarted else .home,
           -- a removal already in the store at launch is not announced
           goneSeen := (all.toList.filter (·.removed)).map (·.acc),
           dbPath := dbPath, netCfg := net, sh := sh, raster, rst := some { rd := ← openDb dbPath } }
  let mut initial := initial
  if let some cp := saved then
    let (version, _, acc, _, _, _) := cp
    if version == 1 then
      if acc.isEmpty && comms.isEmpty then initial := applyCheckpoint initial cp
      else if (Kinds.Accepted.select comms acc).isSome then
        initial := (← (switchToAcc acc).run initial).2
        initial := applyCheckpoint initial cp
  initial.io.setText (if fieldPage initial.page then initial.field else initial.text)
  return initial

/-- On a device: the reader's passes on a thread of their own (never the
shared task pool), so the frame only takes the board. -/
def spawnReader (s : St) : IO St := do
  return (← resumeReader.run { s with threaded := true }).2

end App

end

section

namespace App

def Io.platform : Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log, (fun t => Platform.setText t), Platform.poll, Platform.links, Platform.motion, Platform.appearance, Platform.bars, Platform.pickPhoto, Platform.photoResult, ⟨Platform.editor, Platform.editorAction⟩⟩

end App

end
