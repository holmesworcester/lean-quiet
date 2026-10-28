/-
A chaos generator, as libquiet's: a community's worth of people and
talk, made of real ops (signed, judged, stored like any sync).

- **People:** names in many scripts, each admitted the way the engine
  admits anyone: an invitation from this node's founder, the newcomer's
  request, the founder's approval, and the admission tallying it. Each
  has a profile and an avatar: an identicon, or a crop of a photo.
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
import Quiet.Data
import Quiet.Image

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

/-! ## The community -/

/-- This device in one community: its device there (per-community device
keys, as libquiet's), the community, its admission (the root for a
community it founded), the community's name, and the seed the device
derives from. -/
structure Me where
  dev : Device
  c : Id
  adm : Id
  name : String
  seed : ByteArray
  deriving Inhabited

/-- A new community: a fresh seed's device founds it (the root) and
names itself in it. -/
def Me.found (name : String) (seed : ByteArray) : Me × List Op :=
  let dev := Device.ofSeed seed
  let r := root dev
  let mine := profile r.id r.id dev "Me".toUTF8 0 []
  (⟨dev, r.id, r.id, name, seed⟩, [r, mine])

/-- The communities this device is in, kept in the meta table until the
engine's local-only `accept` ops land: (seed, community, admission, name). -/
def Me.saveAll (db : Db) (ms : Array Me) : IO Unit :=
  Data.Db.setMeta db "comms" (Codec.encode (ms.toList.map fun m => (m.seed, m.c, m.adm, m.name.toUTF8)))

def Me.loadAll (db : Db) : IO (Array Me) := do
  match ← Data.Db.meta db "comms" with
  | some b =>
    match (Codec.decode b : Option (List (ByteArray × ByteArray × ByteArray × ByteArray))) with
    | some l => return (l.map fun (seed, c, adm, n) =>
        ({ dev := Device.ofSeed seed, c, adm, name := (String.fromUTF8? n).getD "?", seed } : Me)).toArray
    | none => return #[]
  | none =>
    -- a database from before communities were a list: its one community
    match ← Data.Db.meta db "seed" with
    | some seed =>
      let ms := #[(Me.found "general" seed).1]
      Me.saveAll db ms
      return ms
    | none => return #[]

/-- A fresh seed. -/
def freshSeed (salt : String) : IO ByteArray := do
  return sha256 s!"lean-quiet {salt} {← Data.nowUs}".toUTF8

/-- Minutes since 2026-10-01, for message times. -/
def epoch : Nat := 29330000

/-- The jobs that make a community of about n messages. -/
def make (me : Me) (srcs : Array Image.Src) (seed n : Nat) (start : Nat) : Array Job := Id.run do
  let c := me.c
  let f := me.dev
  let mut g : Rng := ⟨seed.toUInt64 * 7919 + 17⟩
  let mut jobs : Array Job := #[]
  let mut batch : Array Op := #[]
  let mut blobs : Array ByteArray := #[]
  -- people
  let nUsers := max 6 (min names.size (n / 20))
  let mut people : Array (Id × Device) := #[(me.adm, f)]
  for i in [0:nUsers] do
    let d := Device.named s!"chaos-{seed}-{i}"
    let bearer := Device.named s!"chaos-bearer-{seed}-{i}"
    -- invited by the founder, who then approves the request (threshold 1)
    let inv := invite c me.adm f bearer.pk false 1
    let rq := request c inv.id d bearer.sk
    let ap := approve c rq.id me.adm f
    let j := admit c rq.id [ap.id]
    -- an avatar: an identicon, or a square crop of a photo
    let (kind, g1) := g.below 3
    g := g1
    let (bytes, g2) := if kind == 0 && !srcs.isEmpty then
        let (si, g2) := g.below srcs.size
        let s := srcs[si]!
        let m := min s.w s.h
        let (fx, g3) := g2.below (s.w - m / 2 + 1)
        let (fy, g4) := g3.below (s.h - m / 2 + 1)
        let side := min (m / 2) (min (s.w - fx) (s.h - fy))
        (Image.encode 128 128 (cropPx s fx fy side side 128 128), g4)
      else
        let (px, g2) := identicon g 128
        (Image.encode 128 128 px, g2)
    g := g2
    let b := blob c bytes 128 128
    let p := profile c j.id d names[i % names.size]!.toUTF8 start [b.id]
    batch := batch ++ #[inv, rq, ap, j, b, p]
    blobs := blobs.push bytes
    people := people.push (j.id, d)
  jobs := jobs.push ⟨batch.toList, blobs.toList, false⟩
  batch := #[]
  blobs := #[]
  -- a pool of pictures, reused across messages
  let mut pics : Array (Id × Nat × Nat) := #[]
  if !srcs.isEmpty then
    for _ in [0:min 24 (n / 30 + 4)] do
      let ((w, h, bytes), g1) := photo srcs g
      g := g1
      let b := blob c bytes w h
      batch := batch.push b
      blobs := blobs.push bytes
      pics := pics.push (b.id, w, h)
    jobs := jobs.push ⟨batch.toList, blobs.toList, false⟩
    batch := #[]
    blobs := #[]
  -- messages and reactions
  let mut t := start
  let mut posts : Array Id := #[]
  let mut pending : Array Op := #[]
  for i in [0:n] do
    let (gap, g1) := g.below 100
    let (ai, g2) := g1.below people.size
    let (ti, g3) := g2.below texts.size
    let (more, g4) := g3.below 6
    let (ti2, g5) := g4.below texts.size
    let (att, g6) := g5.below 100
    g := g6
    t := t + (if gap < 60 then 1 else if gap < 90 then 7 else 90)
    let (u, d) := people[ai]!
    let text := if more == 0 then texts[ti]! ++ " " ++ texts[ti2]! else
      if more == 1 then texts[ti]! ++ "\n\n" ++ texts[ti2]! else texts[ti]!
    let mut atts : List Id := []
    if att < 12 && !pics.isEmpty then
      let (k, g7) := g.below 3
      g := g7
      for j in [0:k + 1] do
        let (pi, g8) := g.below pics.size
        g := g8
        if !atts.contains pics[pi]!.1 then atts := atts ++ [pics[pi]!.1]
        let _ := j
    let o := post c u d "k".toUTF8 (s!"{text}").toUTF8 t atts
    pending := pending.push o
    posts := posts.push o.id
    -- reactions on this message, arriving with it
    let (r, g9) := g.below 3
    g := g9
    if r == 0 then
      let (ne, g10) := g.below 4
      g := g10
      for k in [0:ne + 1] do
        let e := emoji[(i + k * 3) % emoji.size]!
        let (nr, g11) := g.below 5
        g := g11
        for z in [0:nr + 1] do
          let (u2, d2) := people[(ai + z * 7 + k) % people.size]!
          pending := pending.push (react c u2 o.id d2 e.toUTF8 (t + z))
    if pending.size ≥ 100 then
      -- a little shuffled within the batch: replies before what they cite
      let (rot, g12) := g.below pending.size
      g := g12
      let shuffled := pending.extract rot pending.size ++ pending.extract 0 rot
      jobs := jobs.push ⟨shuffled.toList, [], false⟩
      pending := #[]
  if !pending.isEmpty then jobs := jobs.push ⟨pending.toList, [], false⟩
  let _ := posts
  return jobs

end Chaos
