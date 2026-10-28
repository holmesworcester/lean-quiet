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
import engine.renderer.Data
import engine.renderer.Image
import ops.community.membership.AcceptedView

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

/-- A fresh seed. -/
def freshSeed (salt : String) : IO ByteArray := do
  return sha256 s!"lean-quiet {salt} {← Data.nowUs}".toUTF8

/-- Minutes since 2026-10-01, for message times. -/
def epoch : Nat := 29330000

/-- The jobs that make a community of about n messages, their bodies
sealed under the community's content key k; a few carry photos, each an
attachment with its chunks (at most `maxFiles` files in all). -/
def make (me : Me) (k : ByteArray) (srcs : Array Image.Src) (seed n : Nat) (start : Nat) : Array Job := Id.run do
  let c := me.c
  let f := me.dev
  let mut g : Rng := ⟨seed.toUInt64 * 7919 + 17⟩
  let mut jobs : Array Job := #[]
  let mut batch : Array Op := #[]
  -- people: invited by the founder, who approves each request (threshold 1)
  let nUsers := max 6 (min names.size (n / 20))
  let mut people : Array (Id × Device) := #[(me.adm, f)]
  for i in [0:nUsers] do
    let d := Device.named s!"chaos-{seed}-{i}"
    let bearer := Device.named s!"chaos-bearer-{seed}-{i}"
    let inv := invite c me.adm f bearer.pk false 1
    let rq := request c inv.id d (cryptoSeal.pub (sha256 s!"chaos-node-{seed}-{i}".toUTF8)) bearer.sk
    let ap := approve c rq.id me.adm f
    let j := admit c rq.id [ap.id]
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
    t := t + (if gap < 60 then 1 else if gap < 90 then 7 else 90)
    let (u, d) := people[ai]!
    let text := if more == 0 then texts[ti]! ++ " " ++ texts[ti2]! else
      if more == 1 then texts[ti]! ++ "\n\n" ++ texts[ti2]! else texts[ti]!
    let tag := s!"chaos {seed} {i}"
    let o := sealedPost c u d k (bytesOf (tag ++ " nonce") 24) text.toUTF8 t
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
