import engine.core.Order
import app.community.Family
import app.community.channel.message.Commands
import app.community.channel.message.receipt.Proofs

namespace Community
open Engine Codec

theorem check_message {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {d k t : ByteArray} {n tm : Nat}
    (h : check C o b fs = some (.message c u d k t n tm)) :
    ∃ s d0 e0 e ka, b = .post k t n tm s ∧ fs = [.admission c c d0 e0 k, .admission c u d e ka] ∧
      o.reqs.head? = some c ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  · rename_i b r a
    rcases b with ⟨k', t', n', tm', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d', e, ka⟩
    simp only [Post.check] at h
    split at h
    · rename_i hc
      simp only [Option.map_some, Option.some.injEq, Fact.ofMessage.injEq, Post.Fact.mk.injEq, and_true] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨h1, rfl, rfl, rfl, h4⟩ := hc
      exact ⟨_, _, _, _, _, rfl, rfl, h1, h4⟩
    · simp at h
  · rename_i b r a p
    rcases b with ⟨k', t', n', tm', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d', e, ka⟩
    rcases p with ⟨c2, u2, d2, k2, t2, n2, tm2, _ | root⟩
    · simp only [Post.check] at h; split at h <;> simp at h
    · simp [Post.check] at h

/-- A child is signed by an admitted device of its root's user. Only a
root can be cited: the final fact's clump is explicitly `none`. -/
theorem check_child {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u root : Id}
    {d k t : ByteArray} {n tm : Nat}
    (h : check C o b fs = some (.message c u d k t n tm (some root))) :
    ∃ s d0 e0 e ka d2 k2 t2 n2 tm2, b = .post k t n tm s ∧
      fs = [.admission c c d0 e0 k, .admission c u d e ka, .message c u d2 k2 t2 n2 tm2 none] ∧
      o.reqs.head? = some c ∧ root = o.reqs.getD 2 .empty ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  · rename_i b r a
    rcases b with ⟨k', t', n', tm', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d', e, ka⟩
    simp only [Post.check] at h; split at h <;> simp at h
  · rename_i b r a p
    rcases b with ⟨k', t', n', tm', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d', e, ka⟩
    rcases p with ⟨c2, u2, d2, k2, t2, n2, tm2, _ | root'⟩
    · simp only [Post.check] at h
      split at h
      · rename_i hc
        simp only [Option.map_some, Option.some.injEq, Fact.ofMessage.injEq, Post.Fact.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hr⟩ := h
        try simp only [Option.some.injEq] at hr
        subst root
        obtain ⟨h1, rfl, rfl, rfl, rfl, rfl, hs⟩ := hc
        exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, hs⟩
      · simp at h
    · simp [Post.check] at h
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- A Valid message's op claims the message's time: sync sorts it there. -/
theorem message_order {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) : ∃ o, ops x = some o ∧ orderOf o = tm := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  refine ⟨o, hx, ?_⟩
  cases clump with
  | none => obtain ⟨_, _, _, _, rfl, _⟩ := check_message hv; simp [orderOf, hb]
  | some r => obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := check_child hv; simp [orderOf, hb]

/-- A Valid message cites an admission of its author's device into its
author's user, and that device signed it. -/
theorem message_authorized {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) :
    ∃ o s e ka y, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t n tm s) ∧
      o.reqs.take 2 = [c, y] ∧ V C ops y (.admission c u d e ka) ∧
      C.verify d (signed o (.post k t n tm s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  cases clump with
  | none =>
    obtain ⟨s, d0, e0, e, ka, rfl, rfl, hh, hs⟩ := check_message hv
    obtain ⟨a, y, hreq, _, hy⟩ := all2_two hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨o, s, e, ka, y, hx, hb, by rw [hreq]; rfl, hy, hs⟩
  | some root =>
    obtain ⟨s, d0, e0, e, ka, d2, k2, t2, n2, tm2, rfl, rfl, hh, _, hs⟩ := check_child hv
    obtain ⟨a, y, rest, hreq, _, hy, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨o, s, e, ka, y, hx, hb, by rw [hreq]; rfl, hy, hs⟩

/-- Every child has one Valid root by the same user in the same community.
This is about the running validator and signed requirement graph. -/
theorem child_has_root {x c u root : Id} {d k t : ByteArray} {n tm : Nat}
    (h : V C ops x (.message c u d k t n tm (some root))) :
    ∃ d2 k2 t2 n2 tm2, V C ops root (.message c u d2 k2 t2 n2 tm2 none) := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, d2, k2, t2, n2, tm2, _, rfl, _, he, _⟩ := check_child hv
  obtain ⟨a, y, rest, hreq, _, _, hrest⟩ := all2_cons2 hr
  cases hrest with
  | cons hroot hnil =>
    cases hnil
    rw [hreq] at he
    simp only [List.getD_cons_succ, List.getD_cons_zero] at he
    subst root
    exact ⟨d2, k2, t2, n2, tm2, hroot⟩
open Engine Codec

theorem timeCap_lt : timeCap < 2 ^ 64 := Nat.sub_lt (Nat.pow_pos_iff.2 (.inl (by decide))) (by decide)

theorem bcmp_msgKey (n tm n' tm' : Nat) :
    bcmp (msgKey n tm) (msgKey n' tm') =
      (compare (min n countCap) (min n' countCap)).then (compare (min tm timeCap) (min tm' timeCap)) := by
  rw [bcmp_eq_lexCmp, msgKey, msgKey, toList_append, toList_append,
    lexCmp_append _ _ (be64_len_eq _ _), lexCmp_be64 (min_lt countCap_lt) (min_lt countCap_lt),
    lexCmp_be64 (min_lt timeCap_lt) (min_lt timeCap_lt)]

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

theorem orient_orient {α} (desc : Bool) (l : List α) : orient desc (orient desc l) = l := by
  cases desc <;> simp [orient]
open Engine Codec
section
variable {s : DB Fact} {C : Crypto}

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
  · obtain ⟨o, sig, _, _, _, hx, hb, _⟩ := message_authorized hv
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
  · obtain ⟨o, sig, _, _, _, hx, hb, _⟩ := message_authorized hv
    exact ⟨n, tm, ⟨o, kid, sealed, sig, hx, hb⟩, .inl ⟨hn, rfl⟩⟩
  · obtain ⟨_, u, d, sealed, n, tm, _, _, hn, hm⟩ := received_of_message hz
    obtain ⟨o, sig, _, _, _, hx, hb, _⟩ := message_authorized hm
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

theorem sum_map_add {α : Type} (l : List α) (f g h : α → Nat) (hfg : ∀ x ∈ l, f x + g x = h x) :
    (l.map f).sum + (l.map g).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hfg x (List.mem_cons_self ..)
    have := ih fun y hy => hfg y (List.mem_cons_of_mem _ hy)
    omega

theorem mem_eval_unlimited {q : ListQ} (hl : q.limit = none) {pf : Pos × Fact} :
    pf ∈ (Engine.eval s q).rows ↔ pf ∈ matching s q ∧ q.inside pf.1 = true := by
  unfold Engine.eval ListQ.cut
  simp only [hl]
  split <;> simp [List.mem_filter]
end
end Community
namespace Community.Clump
open Engine

theorem within_iff (rootTime now : Nat) :
    within rootTime now = true ↔ rootTime ≤ now ∧ now < rootTime + 5 := by simp [within]

theorem expired (rootTime now : Nat) (h : rootTime + 5 ≤ now) : within rootTime now = false := by
  simp [within]; omega

theorem backwards (rootTime now : Nat) (h : now < rootTime) : within rootTime now = false := by
  simp [within]; omega

end Community.Clump
