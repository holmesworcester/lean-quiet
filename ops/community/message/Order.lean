/-
A channel's order, as laws over the code that runs (`sortOf`,
`readable`, `send`, `receiptFor`). The user's decisions (2026-10-27,
2026-10-28): a channel sorts by a counter its devices share, the time
breaking ties; time is real minutes, for display; a saturated counter
falls back on this device's receipts, and that exception is a law.

- `msg_cmp`: two messages compare by counter, then time (each capped),
  then id.
- `time_is_display`: a message's claimed time never moves it past a
  message with another counter.
- `order_total`: a channel's list is in its order, and rows naming
  different messages are never level.
- `send_after`: the post `send` writes sorts after every message the
  device lists in that channel when it writes.
- `arrival_order` (the saturation law): a receipt sorts after every
  receipt the device held when it wrote it, so past the cap a channel is
  in this device's own arrival order; `receipt_once`: one per message.
- `order_local`: the exception to "every device sees the same": below
  the cap a message's place is its post's own claims, the same wherever
  the post is held; past it, a receipt this device wrote itself.
- `display_agrees`: so two devices holding the same posts order any two
  of them alike unless both are saturated (tests/engine/Lifecycle.lean
  shows two that differ there).

`time_is_display` and `msg_cmp` rest on the byte order of sort keys
(`lexCmp_be64`: eight bytes, most significant first, order numbers below
2^64) and the engine's `Engine.bcmp_eq_lexCmp`.
-/
import ops.community.Intents
import engine.core.Order

namespace Community
open Engine Codec

/-! ## Sort keys in byte order -/

/-- The bytes `be64` lays out for n: digit i (base 256) for each i in is. -/
def digits (n : Nat) (is : List Nat) : List UInt8 := is.map fun i => (n >>> (8 * i)).toUInt8

theorem digit_toNat (n i : Nat) : ((n >>> (8 * i)).toUInt8).toNat = n / 256 ^ i % 256 := by
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- x + P·d against y + P·e, for x and y below P: by d and e, then x
and y. -/
theorem compare_place {x y d e P : Nat} (hx : x < P) (hy : y < P) :
    compare (x + P * d) (y + P * e) = (compare d e).then (compare x y) := by
  rcases Nat.lt_trichotomy d e with h | rfl | h
  · have : P * (d + 1) ≤ P * e := Nat.mul_le_mul_left P h
    rw [Nat.mul_succ] at this
    rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]; rfl
  · rw [Nat.compare_eq_eq.2 rfl]
    simp only [Ordering.then]
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]
    · simp
    · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]
  · have : P * (e + 1) ≤ P * d := Nat.mul_le_mul_left P h
    rw [Nat.mul_succ] at this
    rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]; rfl

/-- k digits, most significant first, compare as the numbers mod 256^k. -/
theorem lexCmp_digits (a b : Nat) : ∀ k, lexCmp (digits a (List.range k).reverse) (digits b (List.range k).reverse) =
    compare (a % 256 ^ k) (b % 256 ^ k)
  | 0 => by simp [digits, lexCmp, Nat.mod_one]
  | k + 1 => by
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, digits, List.map_cons]
    have ih := lexCmp_digits a b k
    simp only [digits] at ih
    simp only [lexCmp]
    have hp : 0 < 256 ^ k := Nat.pow_pos_iff.2 (.inl (by decide))
    rw [Nat.pow_succ, Nat.mod_mul, Nat.mod_mul, compare_place (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)]
    have e1 : (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 ↔ a / 256 ^ k % 256 < b / 256 ^ k % 256 := by
      rw [UInt8.lt_iff_toNat_lt, digit_toNat, digit_toNat]
    have e2 : (b >>> (8 * k)).toUInt8 < (a >>> (8 * k)).toUInt8 ↔ b / 256 ^ k % 256 < a / 256 ^ k % 256 := by
      rw [UInt8.lt_iff_toNat_lt, digit_toNat, digit_toNat]
    rcases Nat.lt_trichotomy (a / 256 ^ k % 256) (b / 256 ^ k % 256) with h | h | h
    · simp only [e1.2 h, ite_true, Nat.compare_eq_lt.2 h]; rfl
    · have n1 : ¬ (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 := fun x => by have := e1.1 x; omega
      have n2 : ¬ (b >>> (8 * k)).toUInt8 < (a >>> (8 * k)).toUInt8 := fun x => by have := e2.1 x; omega
      simp only [n1, n2, ite_false, h, Nat.compare_eq_eq.2 rfl, ih]; rfl
    · have n1 : ¬ (a >>> (8 * k)).toUInt8 < (b >>> (8 * k)).toUInt8 := fun x => by have := e1.1 x; omega
      simp only [n1, e2.2 h, ite_false, ite_true, Nat.compare_eq_gt.2 h]; rfl

theorem be64_toList (n : Nat) : (be64 n).data.toList = digits n (List.range 8).reverse := rfl

theorem be64_length (n : Nat) : (be64 n).data.toList.length = 8 := by
  rw [be64_toList]; simp [digits]

theorem be64_len_eq (a b : Nat) : (be64 a).data.toList.length = (be64 b).data.toList.length := by
  rw [be64_length, be64_length]

/-- **Eight bytes, most significant first, order numbers below 2^64.** -/
theorem lexCmp_be64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    lexCmp (be64 a).data.toList (be64 b).data.toList = compare a b := by
  rw [be64_toList, be64_toList, lexCmp_digits, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem toList_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

theorem countCap_lt : countCap < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)

theorem timeCap_lt : timeCap < 2 ^ 64 := Nat.sub_lt (Nat.pow_pos_iff.2 (.inl (by decide))) (by decide)

theorem min_lt {n cap : Nat} (h : cap < 2 ^ 64) : min n cap < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.min_le_right _ _) h

theorem bcmp_msgKey (n tm n' tm' : Nat) :
    bcmp (msgKey n tm) (msgKey n' tm') =
      (compare (min n countCap) (min n' countCap)).then (compare (min tm timeCap) (min tm' timeCap)) := by
  rw [bcmp_eq_lexCmp, msgKey, msgKey, toList_append, toList_append,
    lexCmp_append _ _ (be64_len_eq _ _), lexCmp_be64 (min_lt countCap_lt) (min_lt countCap_lt),
    lexCmp_be64 (min_lt timeCap_lt) (min_lt timeCap_lt)]

theorem recKey_toList (k : Nat) (m : Id) :
    (recKey k m).data.toList = (be64 countCap).data.toList ++ ((be64 k).data.toList ++ m.data.toList) := by
  rw [recKey, toList_append, toList_append, List.append_assoc]

theorem bcmp_recKey {k k' : Nat} (hk : k < 2 ^ 64) (hk' : k' < 2 ^ 64) (m m' : Id) :
    bcmp (recKey k m) (recKey k' m') = (compare k k').then (bcmp m m') := by
  rw [bcmp_eq_lexCmp, bcmp_eq_lexCmp, recKey_toList, recKey_toList, lexCmp_append _ _ (be64_len_eq _ _),
    lexCmp_append _ _ (be64_len_eq _ _), lexCmp_be64 countCap_lt countCap_lt, lexCmp_be64 hk hk',
    Nat.compare_eq_eq.2 rfl]
  rfl

/-- Every message below the cap sorts before every receipt. -/
theorem bcmp_msg_rec {n : Nat} (hn : n < countCap) (tm k : Nat) (m : Id) :
    bcmp (msgKey n tm) (recKey k m) = .lt := by
  rw [bcmp_eq_lexCmp, msgKey, recKey_toList, toList_append, lexCmp_append _ _ (be64_len_eq _ _),
    lexCmp_be64 (min_lt countCap_lt) countCap_lt, Nat.min_eq_left (Nat.le_of_lt hn), Nat.compare_eq_lt.2 hn]
  rfl

/-! ## The order of a channel -/

/-- **Messages sort by counter, then time, then id.** Two message facts
compare, where a list files them (`sortOf`, ties by id), by their
counters (capped at `countCap`), then their times (capped at `timeCap`),
then their ids. -/
theorem msg_cmp {clump clump' : Option Id} {c u d kid sealed c' u' d' kid' sealed' : ByteArray} {n tm n' tm' : Nat} (x y : Id) :
    Pos.cmp (sortOf (.message c u d kid sealed n tm clump), x) (sortOf (.message c' u' d' kid' sealed' n' tm' clump'), y) =
      ((compare (min n countCap) (min n' countCap)).then
        (compare (min tm timeCap) (min tm' timeCap))).then (bcmp x y) := by
  show (bcmp (msgKey n tm) (msgKey n' tm')).then (bcmp x y) = _
  rw [bcmp_msgKey]

/-- **Time is for display.** Between two messages whose counters differ
(below the cap, or one of them past it), the counters alone decide:
neither claimed time nor id moves one past the other. -/
theorem time_is_display {clump clump' : Option Id} {c u d kid sealed c' u' d' kid' sealed' : ByteArray} {n n' : Nat}
    (h : min n countCap ≠ min n' countCap) (tm tm' : Nat) (x y : Id) :
    Pos.cmp (sortOf (.message c u d kid sealed n tm clump), x) (sortOf (.message c' u' d' kid' sealed' n' tm' clump'), y) =
      compare (min n countCap) (min n' countCap) := by
  rw [msg_cmp]
  cases hc : compare (min n countCap) (min n' countCap)
  · rfl
  · exact absurd (Nat.compare_eq_eq.1 hc) h
  · rfl

/-- Row a comes before row b of a list read newest first (`desc`) or
oldest first: at or before it, and strictly when they name different
messages. -/
def InOrder (desc : Bool) (a b : Pos × Fact) : Prop :=
  (if desc then Pos.cmp b.1 a.1 else Pos.cmp a.1 b.1) ≠ .gt ∧
    (a.1.2 ≠ b.1.2 → (if desc then Pos.cmp b.1 a.1 else Pos.cmp a.1 b.1) = .lt)

/-- A receipt's sort key names its message. -/
theorem recKey_inj {k k' : Nat} {m m' : Id} (h : recKey k m = recKey k' m') : m = m' := by
  have h1 := congrArg (·.data.toList) h
  simp only [recKey_toList] at h1
  have h2 := List.append_cancel_left h1
  have h3 := (List.append_inj h2 (by rw [be64_length, be64_length])).2
  exact ByteArray.ext (Array.toList_inj.1 h3)

theorem orient_map {α β} (f : α → β) (desc : Bool) (l : List α) :
    orient desc (l.map f) = (orient desc l).map f := by
  cases desc <;> simp [orient, List.map_reverse]

theorem orient_orient {α} (desc : Bool) (l : List α) : orient desc (orient desc l) = l := by
  cases desc <;> simp [orient]

section
variable {s : DB Fact} {C : Crypto}

/-- Renaming a receipt list's rows by their messages (`asMsg`) keeps
them in order: a receipt's sort key names its message (`recKey_inj`),
so two rows level on it name one message. -/
theorem asMsg_sorted (h : Inv (family C) s) (hq : s.queue = []) {c kid : ByteArray} {lim : Option Nat}
    {desc : Bool} {after before : Option Pos} :
    let a := Engine.eval s (received.byKey.query [c, kid] lim desc after before)
    (orient desc (a.rows.map asMsg)).Pairwise (fun p q => posLE p q = true) := by
  intro a
  have ho : (orient desc a.rows).Pairwise (fun p q => posLE p q = true) :=
    eval_oriented s (received.byKey.query [c, kid] lim desc after before)
  rw [orient_map, List.pairwise_map]
  refine ho.imp_of_mem fun {x y} hx hy hxy => ?_
  have row : ∀ {r}, r ∈ orient desc a.rows →
      ∃ k m z clump, r = ((recKey k m, z), .received c kid m k clump) := fun {r} hr => by
    obtain ⟨he, _, hargs⟩ := row_at (C := C) (r := received.byKey) (by simp [rels]) h hq (mem_orient.1 hr)
    obtain ⟨⟨sk, z⟩, f⟩ := r
    cases f with
    | received c' kid' m k clump =>
      simp only [received.byKey, Option.some.injEq, List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      exact ⟨k, m, z, clump, by simpa [SortKey.sortOf, sortOf] using he⟩
    | _ => simp [received.byKey] at hargs
  obtain ⟨k, m, z, clump, rfl⟩ := row hx
  obtain ⟨k', m', z', clump', rfl⟩ := row hy
  rw [posLE_iff] at hxy ⊢
  simp only [asMsg, Pos.cmp] at hxy ⊢
  cases e : bcmp (recKey k m) (recKey k' m')
  · simp
  · rw [recKey_inj (bcmp_eq e), (bcmp_eq_iff m' m').2 rfl]; simp
  · simp [e] at hxy

/-- **A channel's list is a strict total order on its messages.**
`readable`'s rows are in its order, newest first or oldest first as
asked, and two rows naming different messages are never level: one is
strictly before the other (with equal counter and time, by id:
`msg_cmp`). Sorting before is a strict total order on positions
(`Pos.cmp_eq_iff`, `Pos.cmp_swap`, `Pos.cmp_lt_trans`). Nothing sorts it:
each of its lists comes in order (`eval_oriented`, `asMsg_sorted`) and
the union merges them (`union_sorted`). -/
theorem order_total (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat) (desc : Bool)
    (after before : Option Pos) :
    ((readable c lim desc after before).eval s).rows.Pairwise (InOrder desc) := by
  rw [eval_readable]
  simp only
  have hu := union_sorted (desc := desc) (limit := lim) (F := Fact) (as :=
    ((heldKids c).eval s).map (fun kid => Engine.eval s (message.byKey.query [c, kid] lim desc after before)) ++
      ((heldKids c).eval s).map fun kid =>
        let a := Engine.eval s (received.byKey.query [c, kid] lim desc (after.map afterRec)
          (before.map beforeRec))
        { a with rows := a.rows.map asMsg }) (fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨kid, _, rfl⟩ := List.mem_map.1 ha
      exact eval_oriented s (message.byKey.query [c, kid] lim desc after before)
    · obtain ⟨kid, _, rfl⟩ := List.mem_map.1 ha
      exact asMsg_sorted h hq)
  have one : ∀ a b : Pos × Fact, Pos.cmp a.1 b.1 ≠ .gt → InOrder false a b := fun a b h =>
    ⟨h, fun hne => strict_of h fun e => hne (congrArg Prod.snd e)⟩
  rw [← orient_orient desc (unionAnswers ..).rows]
  generalize orient desc (unionAnswers ..).rows = l at hu ⊢
  cases desc
  · exact hu.imp fun {a b} h => one a b (posLE_iff.1 h)
  · simp only [orient, ite_true]
    rw [List.pairwise_reverse]
    refine hu.imp fun {a b} h => ?_
    have h := posLE_iff.1 h
    exact ⟨h, fun hne => strict_of h fun e => hne (congrArg Prod.snd e).symm⟩


/-- Where message x of c sits in this device's list (`readable_held`):
below the counter cap at its own key, past it at a receipt of it this
device holds. -/
def Listed (C : Crypto) (ops : Id → Option Op) (c x : Id) (sk : ByteArray) : Prop :=
  (∃ u d kid sealed n tm clump, V C ops x (.message c u d kid sealed n tm clump) ∧ n < countCap ∧ sk = msgKey n tm) ∨
    ∃ z kid k clump, V C ops z (.received c kid x k clump) ∧ sk = recKey k x

/-- Every row of a channel's list is a listed message, at its place. -/
theorem readable_listed (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat) (desc : Bool)
    (after before : Option Pos) {pf : Pos × Fact} (hp : pf ∈ ((readable c lim desc after before).eval s).rows) :
    Listed C s.ops c pf.1.2 pf.1.1 := by
  obtain ⟨u, d, kid, sealed, n, tm, clump, hv, _, hw⟩ := readable_held h hq c lim desc after before hp
  rcases hw with ⟨hn, he⟩ | ⟨_, z, k, hz, he⟩
  · exact .inl ⟨u, d, kid, sealed, n, tm, clump, hv, hn, by rw [he]⟩
  · exact .inr ⟨z, kid, k, clump, hz, by rw [he]⟩

/-- The first row of a relation's list, read newest first with limit 1,
is at or after every fact filed in it. -/
theorem first_after {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {y : Id} {f : Fact} (hv : V C s.ops y f) (ha : r.args f = some as) :
    ∃ y' f', (Engine.eval s (r.query as (some 1))).rows.head? = some ((sortOf f', y'), f') ∧
      V C s.ops y' f' ∧ r.args f' = some as ∧ Pos.cmp (sortOf f, y) (sortOf f', y') ≠ .gt := by
  have hm : ((sortOf f, y), f) ∈ matching s (r.query as (some 1)) := by
    rw [matching_also_nil _ rfl, mem_matching]
    have hf := (filed (C := C) hr h hq as y f).2 ⟨hv, ha⟩
    exact ⟨y, _, rfl, hf.1, hf.2⟩
  obtain ⟨t, ht, htm, hle⟩ := top_max rfl rfl rfl (by simp [Rel.query]) hm
  rw [matching_also_nil _ rfl, mem_matching] at htm
  obtain ⟨y', f', rfl, hy', hf'⟩ := htm
  obtain ⟨hv', ha'⟩ := (filed (C := C) hr h hq as y' f').1 ⟨hy', hf'⟩
  exact ⟨y', f', ht, hv', ha', hle⟩

/-- **`send`'s counter is past every message's.** The counter it starts
from is at least every Valid message's of c, capped. -/
theorem topCount_ge (h : Inv (family C) s) (hq : s.queue = []) {c y : Id} {u d kid sealed : ByteArray}
    {clump : Option Id} {n tm : Nat} (hv : V C s.ops y (.message c u d kid sealed n tm clump)) :
    min n countCap ≤ (topCount c).eval s := by
  obtain ⟨y', f', ht, _, ha', hle⟩ :=
    first_after (r := message.all) (as := [c]) (by simp [rels]) h hq hv (by simp [message.all])
  cases f' with
  | message c' u' d' kid' sealed' n' tm' clump' => ?_
  | _ => simp [message.all] at ha'
  have hc : (topCount c).eval s = min n' countCap := by
    simp only [topCount, Rel.read, View.eval_bind, View.eval_read, View.eval_pure, ht]
  rw [hc]
  rw [msg_cmp] at hle
  refine Nat.not_lt.1 fun hlt => hle ?_
  rw [Nat.compare_eq_gt.2 hlt]; rfl

/-- **A receipt's counter is past every held receipt's.** -/
theorem topReceived_ge (h : Inv (family C) s) (hq : s.queue = []) {c z : Id} {kid m : ByteArray} {j : Nat} {clump : Option Id}
    (hall : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j < 2 ^ 64)
    (hv : V C s.ops z (.received c kid m j clump)) :
    j ≤ (topReceived c).eval s ∧ ∃ z' kid' m' clump', V C s.ops z' (.received c kid' m' ((topReceived c).eval s) clump') := by
  obtain ⟨y', f', ht, hv', ha', hle⟩ :=
    first_after (r := received.all) (as := [c]) (by simp [rels]) h hq hv (by simp [received.all])
  cases f' with
  | received c' kid' m' j' clump' => ?_
  | _ => simp [received.all] at ha'
  simp [received.all] at ha'
  subst ha'
  have hc : (topReceived c').eval s = j' := by
    simp only [topReceived, Rel.read, View.eval_bind, View.eval_read, View.eval_pure, ht]
  rw [hc]
  refine ⟨?_, y', kid', m', clump', hv'⟩
  have e : Pos.cmp (sortOf (Fact.received c' kid m j clump), z) (sortOf (Fact.received c' kid' m' j' clump'), y') =
      ((compare j j').then (bcmp m m')).then (bcmp z y') := by
    show (bcmp (recKey j m) (recKey j' m')).then (bcmp z y') = _
    rw [bcmp_recKey (hall _ _ _ _ _ hv) (hall _ _ _ _ _ hv')]
  rw [e] at hle
  refine Nat.not_lt.1 fun hlt => hle ?_
  rw [Nat.compare_eq_gt.2 hlt]; rfl

/-- The counter `receiptFor` writes is past every held receipt's in c,
and below 2^64 while every held one's successor is. -/
theorem receipt_past (h : Inv (family C) s) (hq : s.queue = []) {c : Id}
    (hk : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j + 1 < 2 ^ 64) :
    (topReceived c).eval s + 1 < 2 ^ 64 ∧
      ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → Pos.cmp (recKey j m, m) (recKey ((topReceived c).eval s + 1) m', m') = .lt := by
  have hall : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j < 2 ^ 64 :=
    fun z kid m j clump hv => Nat.lt_of_succ_lt (hk z kid m j clump hv)
  have hb : (topReceived c).eval s + 1 < 2 ^ 64 := by
    simp only [topReceived, Rel.read, View.eval_bind, View.eval_read, View.eval_pure]
    cases ht : (Engine.eval s (received.all.query [c] (some 1))).rows.head? with
    | none => decide
    | some t =>
      obtain ⟨⟨sk, z⟩, f⟩ := t
      obtain ⟨_, hv, ha⟩ := row_at (C := C) (r := received.all) (by simp [rels]) h hq (List.mem_of_mem_head? ht)
      cases f with
      | received c' kid m j clump =>
        simp [received.all] at ha; subst ha
        exact hk _ _ _ _ _ hv
      | _ => simp [received.all] at ha
  refine ⟨hb, fun z kid m j clump hv => ?_⟩
  have hj := (topReceived_ge h hq hall hv).1
  rw [Pos.cmp, bcmp_recKey (hall _ _ _ _ _ hv) hb, Nat.compare_eq_lt.2 (by omega)]
  rfl

/-- **One receipt per message.** A device holding a receipt of o writes
no other. -/
theorem receipt_once (h : Inv (family C) s) (hq : s.queue = []) {o : Op} {z : Id} {c kid : ByteArray} {j : Nat} {clump : Option Id}
    (hz : V C s.ops z (.received c kid o.id j clump)) : (receiptFor o).eval s = [] := by
  have hpos : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total ≠ 0 := by
    have hf := (filed (C := C) (r := received.byMsg) (by simp [rels]) h hq [o.id] z _).2
      ⟨hz, by simp [received.byMsg]⟩
    show (matching s _).length ≠ 0
    rw [matching_also_nil _ rfl]
    exact Nat.pos_iff_ne_zero.1 (List.length_pos_iff_exists_mem.2 ⟨_, (mem_matching _ _).2 ⟨z, _, rfl, hf.1, hf.2⟩⟩)
  unfold receiptFor
  by_cases hk : o.kind ≠ 23
  · simp [hk]
  simp only [hk, ite_false]
  split
  · rename_i n _ _ _
    by_cases hn : n < countCap
    · simp [hn]
    · simp [hn, Rel.read, View.eval_bind, hpos]
  · rfl

/-- What `receiptFor` writes for a saturated post it holds no receipt of:
one receipt, one past the newest in the post's community. -/
theorem receipt_post (h : Inv (family C) s) (hq : s.queue = []) {o : Op} {kid sealed sig : ByteArray}
    {n tm : Nat} (hkind : o.kind = 23) (hb : (decode o.body : Option Body) = some (.post kid sealed n tm sig))
    (hn : countCap ≤ n) (hnew : s.ops o.id = none) :
    (receiptFor o).eval s = [receipt o.id ((topReceived (o.reqs.headD .empty)).eval s + 1)] := by
  have hzero : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total = 0 := by
    show (matching s _).length = 0
    rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
    intro pf hp
    rw [matching_also_nil _ rfl, mem_matching] at hp
    obtain ⟨z, f, rfl, hz, hf⟩ := hp
    obtain ⟨hv, ha⟩ := (filed (C := C) (r := received.byMsg) (by simp [rels]) h hq [o.id] z f).1 ⟨hz, hf⟩
    cases f <;> simp [received.byMsg] at ha
    subst ha
    obtain ⟨_, _, _, _, _, _, _, _, _, hm⟩ := received_of_message hv
    obtain ⟨o', _, _, hx, _⟩ := valid_inv hm
    rw [hnew] at hx; cases hx
  unfold receiptFor
  rw [hb]
  simp [hkind, Nat.not_lt.2 hn, Rel.read, View.eval_bind, hzero]

/-- **Past the cap, a channel is in this device's arrival order.** A
receipt `receiptFor` writes for op o sorts after every receipt this device
held in o's community when it wrote it, so saturated messages are listed
in the order this device received them (`readable_held`), at the grain
of its writes: receipts written in one write read the same receipts, so
they share a counter and fall back on their messages' ids. The counter
must stay below 2^64: the device has received fewer saturated messages
there. -/
theorem arrival_order (h : Inv (family C) s) (hq : s.queue = []) (o : Op)
    (hk : ∀ z kid m j clump, V C s.ops z (.received (o.reqs.headD .empty) kid m j clump) → j + 1 < 2 ^ 64)
    {r : Op} (hr : r ∈ (receiptFor o).eval s) :
    ∃ j, r = receipt o.id j ∧ ∀ z kid m j' clump, V C s.ops z (.received (o.reqs.headD .empty) kid m j' clump) →
      Pos.cmp (recKey j' m, m) (recKey j o.id, o.id) = .lt := by
  refine ⟨(topReceived (o.reqs.headD .empty)).eval s + 1, ?_, (receipt_past h hq hk).2⟩
  unfold receiptFor at hr
  by_cases hkind : o.kind ≠ 23
  · simp [hkind] at hr
  simp only [hkind, ite_false] at hr
  split at hr
  · rename_i n _ _ _
    by_cases hn : n < countCap
    · simp [hn] at hr
    · simp only [hn, Rel.read, View.eval_bind, View.eval_read, ite_false] at hr
      by_cases ht : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total ≠ 0
      · simp [ht] at hr
      · simp only [ht, ite_false, View.eval_bind, View.eval_pure, List.mem_singleton] at hr
        exact hr
  · simp at hr

/-- **What `send` writes sorts after everything the device lists in
that channel.** The post `send` writes (the first op of its write)
claims a counter n. If the post is new to this store, then below the
cap it sorts at its own key, and past it at the receipt the same write
holds; either way after every message this device lists in c when it
writes (`Listed`, which every row of `readable c` is). The receipt
counter must stay below 2^64, as in `arrival_order`. -/
theorem send_after (h : Inv (family C) s) (hq : s.queue = []) (c myAdm : Id) (d : Device) (k nonce text : ByteArray)
    (now : Nat) (files : List NewFile)
    (hk : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j + 1 < 2 ^ 64) :
    let group := (Clump.choose c myAdm now).eval s
    ∃ n, ((send c myAdm d k nonce text now files).eval s).ops.head? =
        some (sealedPost c myAdm d k nonce text n now group) ∧
      (s.ops (sealedPost c myAdm d k nonce text n now group).id = none →
        ∃ sk, (n < countCap ∧ sk = msgKey n now ∨
            ∃ j, receipt (sealedPost c myAdm d k nonce text n now group).id j ∈
              ((send c myAdm d k nonce text now files).eval s).ops ∧
              sk = recKey j (sealedPost c myAdm d k nonce text n now group).id) ∧
          ∀ x sk', Listed C s.ops c x sk' →
            Pos.cmp (sk', x) (sk, (sealedPost c myAdm d k nonce text n now group).id) = .lt) := by
  dsimp only
  let group := (Clump.choose c myAdm now).eval s
  let T := (topCount c).eval s
  let n := min (T + 1) countCap
  let p := sealedPost c myAdm d k nonce text n now group
  have hw : (send c myAdm d k nonce text now files).eval s =
      ⟨p :: (receiptFor p).eval s ++ files.flatMap (fun f =>
        let (a, cs) := attach c myAdm p.id d k f; a :: cs)⟩ := by
    simp only [send, View.eval_bind, View.eval_pure]; rfl
  refine ⟨n, by rw [hw]; rfl, fun hnew => ?_⟩
  -- every message of c the device lists is at most T
  have hmsg : ∀ y u d kid sealed n' tm' clump, V C s.ops y (.message c u d kid sealed n' tm' clump) → min n' countCap ≤ T :=
    fun _ _ _ _ _ _ _ _ hv => topCount_ge h hq hv
  by_cases hn : T + 1 < countCap
  · have hn' : n = T + 1 := Nat.min_eq_left (Nat.le_of_lt hn)
    refine ⟨msgKey n now, .inl ⟨by omega, rfl⟩, fun x sk' hl => ?_⟩
    rcases hl with ⟨u, d, kid, sealed, n', tm', clump, hv, hlt, rfl⟩ | ⟨z, kid, j, clump, hz, _⟩
    · have hle := hmsg _ _ _ _ _ _ _ _ hv
      have e := time_is_display (clump := clump) (clump' := none) (c := c) (u := u) (d := d) (kid := kid) (sealed := sealed) (c' := c) (u' := .empty)
        (d' := .empty) (kid' := .empty) (sealed' := .empty) (n := n') (n' := n) (by omega) tm' now x p.id
      show Pos.cmp (sortOf (Fact.message c u d kid sealed n' tm' clump), x) (sortOf (Fact.message c .empty .empty .empty .empty n now), p.id) = .lt
      rw [e, Nat.compare_eq_lt.2 (by omega)]
    · obtain ⟨_, _, _, _, n'', _, _, _, hcap, hm⟩ := received_of_message hz
      have := hmsg _ _ _ _ _ _ _ _ hm
      omega
  · have hsat : countCap ≤ n := by simp only [n]; omega
    have hp : (decode p.body : Option Body) = some (.post (kidOf cryptoSeal k)
        (nonce ++ sealBody cryptoSeal k nonce c (kidOf cryptoSeal k) text) n now
        (sig d.sk ([c, myAdm] ++ group.toList) (.post (kidOf cryptoSeal k)
          (nonce ++ sealBody cryptoSeal k nonce c (kidOf cryptoSeal k) text) n now .empty))) :=
      body_mkOp _ _
    have hc : p.reqs.headD .empty = c := rfl
    have hr := receipt_post h hq rfl hp hsat hnew
    rw [hc] at hr
    refine ⟨recKey ((topReceived c).eval s + 1) p.id, .inr ⟨_, by rw [hw, hr]; simp; exact .inr (.inl rfl), rfl⟩,
      fun x sk' hl => ?_⟩
    rcases hl with ⟨u, d, kid, sealed, n', tm', clump, hv, hlt, rfl⟩ | ⟨z, kid, j, clump, hz, rfl⟩
    · show (bcmp (msgKey n' tm') _).then _ = .lt
      rw [bcmp_msg_rec hlt]; rfl
    · exact (receipt_past h hq hk).2 z kid x j clump hz

/-- **The exception to "every device sees the same", as a law.** Below
the counter cap, a message's place in a channel's list is its post's own
claims: the counter and time its op's bytes carry, so every device
holding the post puts it in the same place. Past the cap, its place is a
receipt that is this device's own op: in a node fed by its own writes
and peers' jobs, one of its own writes (`local_fact_mine`), which never
leaves it. So two devices may order saturated messages differently,
each in its own arrival order (`arrival_order`). -/
theorem order_local {M : List Op} (hf : Fed (family C) M s) {c x : Id} {sk : ByteArray}
    (hl : Listed C s.ops c x sk) :
    (∃ o kid sealed n tm sig, s.ops x = some o ∧ (decode o.body : Option Body) = some (.post kid sealed n tm sig) ∧
        n < countCap ∧ sk = msgKey n tm) ∨
      ∃ z o kid k clump, o ∈ M ∧ s.ops z = some o ∧ V C s.ops z (.received c kid x k clump) ∧ sk = recKey k x := by
  rcases hl with ⟨u, d, kid, sealed, n, tm, clump, hv, hn, rfl⟩ | ⟨z, kid, k, clump, hz, rfl⟩
  · obtain ⟨o, sig, _, _, hx, hb, _⟩ := message_authorized hv
    exact .inl ⟨o, kid, sealed, n, tm, sig, hx, hb, hn, rfl⟩
  · obtain ⟨o, hm, hx⟩ := local_fact_mine hf hz rfl
    exact .inr ⟨z, o, kid, k, clump, hm, hx, hz, rfl⟩

/-- Post x claims counter n and time tm: its op's body says so. -/
def Posted (ops : Id → Option Op) (x : Id) (n tm : Nat) : Prop :=
  ∃ o kid sealed sig, ops x = some o ∧ (decode o.body : Option Body) = some (.post kid sealed n tm sig)

theorem posted_unique {ops : Id → Option Op} {x : Id} {n tm n' tm' : Nat} (h : Posted ops x n tm)
    (h' : Posted ops x n' tm') : n = n' ∧ tm = tm' := by
  obtain ⟨o, _, _, _, hx, hb⟩ := h
  obtain ⟨o', _, _, _, hx', hb'⟩ := h'
  rw [hx] at hx'; cases hx'
  rw [hb] at hb'; cases hb'
  exact ⟨rfl, rfl⟩

/-- A listed message's place, by what its post claims: its own key
below the cap, a receipt's past it. -/
theorem listed_cases {ops : Id → Option Op} {c x : Id} {sk : ByteArray} (hl : Listed C ops c x sk) :
    ∃ n tm, Posted ops x n tm ∧ (n < countCap ∧ sk = msgKey n tm ∨ countCap ≤ n ∧ ∃ k, sk = recKey k x) := by
  rcases hl with ⟨u, d, kid, sealed, n, tm, clump, hv, hn, rfl⟩ | ⟨z, kid, k, clump, hz, rfl⟩
  · obtain ⟨o, sig, _, _, hx, hb, _⟩ := message_authorized hv
    exact ⟨n, tm, ⟨o, kid, sealed, sig, hx, hb⟩, .inl ⟨hn, rfl⟩⟩
  · obtain ⟨_, u, d, sealed, n, tm, _, _, hn, hm⟩ := received_of_message hz
    obtain ⟨o, sig, _, _, hx, hb, _⟩ := message_authorized hm
    exact ⟨n, tm, ⟨o, kid, sealed, sig, hx, hb⟩, .inr ⟨hn, k, rfl⟩⟩

/-- **Devices holding the same posts order them alike, unless both are
saturated.** Two devices (ops, ops') each list messages x and y of c,
and hold the same op under each id. Unless both claim the counter cap or
more, the two put them in the same order: below the cap a place is the
post's own claims (`order_local`), and every message below the cap sorts
before every receipt. -/
theorem display_agrees {ops ops' : Id → Option Op} {c x y : Id} {sx sy sx' sy' : ByteArray}
    (hx : ops x = ops' x) (hy : ops y = ops' y)
    (lx : Listed C ops c x sx) (ly : Listed C ops c y sy) (lx' : Listed C ops' c x sx') (ly' : Listed C ops' c y sy')
    (hsat : (∃ n tm, Posted ops x n tm ∧ n < countCap) ∨ ∃ n tm, Posted ops y n tm ∧ n < countCap) :
    Pos.cmp (sx, x) (sy, y) = Pos.cmp (sx', x) (sy', y) := by
  have same {z : Id} (hz : ops z = ops' z) {n tm : Nat} (h : Posted ops' z n tm) : Posted ops z n tm := by
    obtain ⟨o, kid, sealed, sig, ho, hb⟩ := h
    exact ⟨o, kid, sealed, sig, hz.trans ho, hb⟩
  obtain ⟨nx, tx, px, cx⟩ := listed_cases lx
  obtain ⟨ny, ty, py, cy⟩ := listed_cases ly
  obtain ⟨nx', tx', px', cx'⟩ := listed_cases lx'
  obtain ⟨ny', ty', py', cy'⟩ := listed_cases ly'
  obtain ⟨rfl, rfl⟩ := posted_unique px (same hx px')
  obtain ⟨rfl, rfl⟩ := posted_unique py (same hy py')
  have below {n tm k : Nat} {z w : Id} (hn : n < countCap) : Pos.cmp (msgKey n tm, z) (recKey k w, w) = .lt := by
    show (bcmp (msgKey n tm) (recKey k w)).then _ = .lt
    rw [bcmp_msg_rec hn]; rfl
  have above {n tm k : Nat} {z w : Id} (hn : n < countCap) : Pos.cmp (recKey k w, w) (msgKey n tm, z) = .gt := by
    rw [Pos.cmp_swap, below hn]; rfl
  rcases cx with ⟨hnx, rfl⟩ | ⟨hnx, kx, rfl⟩ <;> rcases cx' with ⟨_, rfl⟩ | ⟨hnx', kx', rfl⟩ <;>
    rcases cy with ⟨hny, rfl⟩ | ⟨hny, ky, rfl⟩ <;> rcases cy' with ⟨_, rfl⟩ | ⟨hny', ky', rfl⟩ <;>
    first
    | omega
    | rfl
    | rw [below hnx, below hnx]
    | rw [above hny, above hny]
    | (exfalso; rcases hsat with ⟨n, tm, hp, hn⟩ | ⟨n, tm, hp, hn⟩
       · obtain ⟨rfl, -⟩ := posted_unique px hp; omega
       · obtain ⟨rfl, -⟩ := posted_unique py hp; omega)

/-! ## A window's two sides

A window anchored at row p reads the rows past p (`after`) and the rows
before p's successor (`before`: at or before p). Each of `readable`'s
lists is split by them, each row on exactly one side
(`count_partition`), and the anchor is on its own older side
(`anchor_read`), past the counter cap too, where its row is a receipt
named by its message (`afterRec`, `beforeRec`). -/

/-- A receipt's sort key names its message. -/
theorem recMsg_recKey (k : Nat) (m : Id) : recMsg (recKey k m) = m := by
  unfold recMsg
  rw [recKey_toList, ← List.append_assoc,
    List.drop_left' (by rw [List.length_append, be64_length, be64_length])]

/-- A receipt list's bounds for p's two sides are a position and its
successor. -/
theorem rec_succ (p : Pos) : beforeRec (p.1, p.2.push 0) = ((afterRec p).1, (afterRec p).2.push 0) := by
  unfold afterRec beforeRec
  simp only
  congr 1
  cases e : bcmp (recMsg p.1) p.2
  · have : bcmp (recMsg p.1) (p.2.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [e]; decide)
    simp [this]
  · have : bcmp (recMsg p.1) (p.2.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [e]; decide)
    simp [this]
  · have : bcmp (recMsg p.1) (p.2.push 0) ≠ .lt := fun h => absurd ((bcmp_push_zero _ _).1 h) (by rw [e]; decide)
    simp [this]

theorem sum_map_add {α : Type} (l : List α) (f g h : α → Nat) (hfg : ∀ x ∈ l, f x + g x = h x) :
    (l.map f).sum + (l.map g).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hfg x (List.mem_cons_self ..)
    have := ih fun y hy => hfg y (List.mem_cons_of_mem _ hy)
    omega

/-- **A window's two sides partition what this device can read.** For
any anchor p, the rows past it and the rows at or before it (before its
successor) are together all of `readable`'s rows, each counted once:
in every list, a message's or a receipt's. -/
theorem count_partition (s : DB Fact) (c : Id) (lim : Option Nat) (desc : Bool) (p : Pos) :
    ((readable c lim desc (some p)).eval s).inRange +
      ((readable c lim desc none (some (p.1, p.2.push 0))).eval s).inRange =
    ((readable c lim desc).eval s).total := by
  rw [eval_readable, eval_readable, eval_readable]
  simp only [unionAnswers, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have hm := sum_map_add ((heldKids c).eval s)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc (some p) none)).inRange)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc none (some (p.1, p.2.push 0)))).inRange)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc none none)).total)
    (fun kid _ => eval_partition s p rfl rfl rfl rfl rfl rfl rfl rfl)
  have hr := sum_map_add ((heldKids c).eval s)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc (some (afterRec p)) none)).inRange)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc none
      (some (beforeRec (p.1, p.2.push 0))))).inRange)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc none none)).total)
    (fun kid _ => by
      rw [rec_succ]
      exact eval_partition s (afterRec p) rfl rfl rfl rfl rfl rfl rfl rfl)
  simp only [Option.map_some, Option.map_none] at hm hr ⊢
  omega

theorem mem_eval_unlimited {q : ListQ} (hl : q.limit = none) {pf : Pos × Fact} :
    pf ∈ (Engine.eval s q).rows ↔ pf ∈ matching s q ∧ q.inside pf.1 = true := by
  unfold Engine.eval ListQ.cut
  simp only [hl]
  split <;> simp [List.mem_filter]

/-- **A window holds its own anchor**: a row this device can read is in
the read of the rows at or before it, below the counter cap (its
message's row) and past it (its receipt's, named by its message). -/
theorem anchor_read (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (desc : Bool) {pf : Pos × Fact}
    (hp : pf ∈ ((readable c none desc).eval s).rows) :
    pf ∈ ((readable c none desc none (some (pf.1.1, pf.1.2.push 0))).eval s).rows := by
  rw [eval_readable] at hp ⊢
  simp only at hp ⊢
  rw [mem_union_all] at hp ⊢
  obtain ⟨a, ha, hpa⟩ := hp
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), ?_⟩
    rw [mem_eval_unlimited rfl] at hpa ⊢
    refine ⟨hpa.1, ?_⟩
    simp only [ListQ.inside, Rel.query, Bool.true_and, beq_iff_eq]
    exact (Pos.cmp_succ pf.1 pf.1).2 (by rw [(Pos.cmp_eq_iff _ _).2 rfl]; decide)
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), ?_⟩
    simp only [Option.map_none] at hpa
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hpa
    obtain ⟨he, _, hargs⟩ := row_at (C := C) (r := received.byKey) (by simp [rels]) h hq hr
    obtain ⟨⟨sk, z⟩, f⟩ := r
    cases f with
    | received c' kid' m k clump =>
      simp only [received.byKey, Option.some.injEq, List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      have hsk : sk = recKey k m := by simpa [SortKey.sortOf, sortOf] using congrArg (·.1.1) he
      subst hsk
      refine List.mem_map.2 ⟨_, ?_, rfl⟩
      rw [mem_eval_unlimited rfl] at hr ⊢
      refine ⟨hr.1, ?_⟩
      simp only [ListQ.inside, Rel.query, Bool.true_and, beq_iff_eq, Option.map_some, asMsg, beforeRec,
        recMsg_recKey]
      have hm : bcmp m (m.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [(bcmp_eq_iff m m).2 rfl]; decide)
      have hk : bcmp (recKey k m) ((recKey k m).push 0) = .lt :=
        (bcmp_push_zero _ _).2 (by rw [(bcmp_eq_iff _ _).2 rfl]; decide)
      simp [hm, Pos.cmp, hk, Ordering.then]
    | _ => simp [received.byKey] at hargs

end

end Community
