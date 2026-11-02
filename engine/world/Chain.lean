/-
The send half of `Edge` over time, in the plain World (docs/PROOFS.md,
"What a send costs"): each hop of an op across a live session, from a
packet in flight to its effect at the far end within Δ, by the network's
timely delivery (`Net.Admits.timely`) and the frame laws at the delivery
(Link.lean).

- `op_hop` (H3 over time): an op in flight to a node on an open session
  of a shown room is held there within Δ of its sending.
- `want_hop` (H2 over time): a want in flight to the op's holder leaves
  the id queued there, or the op in flight back, within Δ.
- `write_hop`: a write puts a have of each new op in flight on every
  session showing its room, at the write's time.
-/
import engine.world.Link

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

theorem mem_packets_src {n : Nat} (i : Fin n) (origin : ByteArray) (t : Nat) :
    ∀ (L : List (ByteArray × ByteArray)) (s : Nat) (p : Packet n), p ∈ packets i origin t s L →
      p.src = some i ∧ p.origin = origin ∧ p.sent = t := by
  intro L
  induction L with
  | nil => intro s p h; cases h
  | cons q rest ih =>
    intro s p h
    obtain ⟨d, b⟩ := q
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, rfl⟩
    · exact ih (s + 1) p h

namespace Plain
variable {Q : Plain F}

/-- With distinct addresses, the node at node j's address is j. -/
theorem at_addr (hinj : ∀ a b, Q.addr a = Q.addr b → a = b) (j : Fin Q.n) : Q.setup.at? (Q.addr j) = some j := by
  unfold Setup.at?
  cases h : (List.finRange Q.n).find? (fun i => Decidable.decide (Q.addr i = Q.addr j)) with
  | none =>
    have := List.find?_eq_none.1 h j (List.mem_finRange j)
    simp at this
  | some i =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    rw [hinj _ _ this]

/-- What an entry point puts in flight says who sent it. -/
theorem enter_origin (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hw : ∀ p ∈ w.flight, ∀ l, p.src = some l → p.origin = Q.addr l) :
    ∀ p ∈ (w.enter Q.setup i t f).flight, ∀ l, p.src = some l → p.origin = Q.addr l := by
  intro p hp l hl
  simp only [World.enter] at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hw p hp l hl
  · obtain ⟨e1, e2, -⟩ := mem_packets_src i (Q.addr i) t _ _ p hp
    rw [hl] at e1; cases e1; exact e2

/-- **A packet from a node says it comes from that node's address**, in
every execution: only entry points put packets in flight with a sender,
and a duplicate has none. -/
theorem origin_src {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ p ∈ w₀.flight, ∀ l, p.src = some l → p.origin = Q.addr l) :
    ∀ k, ∀ p ∈ (E.world k).flight, ∀ l, p.src = some l → p.origin = Q.addr l := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [Exec.world_succ]
    cases E.act k with
    | deliver idx t =>
      simp only [World.step]
      cases hp : (E.world k).flight[idx]? with
      | none => exact ih
      | some q =>
        dsimp only
        have ih' : ∀ p ∈ ((E.world k).flight.eraseIdx idx), ∀ l, p.src = some l → p.origin = Q.addr l :=
          fun p hp l hl => ih p (List.mem_of_mem_eraseIdx hp) l hl
        cases hj : Q.setup.at? q.dst with
        | none => dsimp only; exact ih'
        | some j =>
          dsimp only
          exact enter_origin ({ E.world k with flight := (E.world k).flight.eraseIdx idx }) j t _ ih'
    | dup idx =>
      simp only [World.step]
      cases (E.world k).flight[idx]? with
      | none => exact ih
      | some q =>
        intro p hp l hl
        rcases List.mem_append.1 hp with hp | hp
        · exact ih p hp l hl
        · rw [List.mem_singleton.1 hp] at hl; cases hl
    | drop idx =>
      simp only [World.step]
      exact fun p hp l hl => ih p (List.mem_of_mem_eraseIdx hp) l hl
    | tick i t => simp only [World.step]; exact enter_origin _ i t _ ih
    | write i ops t => simp only [World.step]; exact enter_origin _ i t _ ih
    | restart i t => simp only [World.step]; exact ih
    | close i a t => simp only [World.step]; exact enter_origin _ i t _ ih
    | connect i j cid dl t => simp only [World.step]; exact enter_origin _ i t _ ih
    | inject i o b t => simp only [World.step]; exact enter_origin _ i t _ ih

/-- A delivery's time is the world's time after it. -/
theorem deliver_now (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) :
    (w.step Q.setup (.deliver idx t)).now = t := by
  simp only [World.step, hp, hj, World.enter]

/-- **H3 over time.** An op in flight from a to b, on a session b holds
open from then on, of a room b shows there, sent after gst across a live
edge: within Δ of its sending, b holds it. -/
theorem op_hop {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {N : Net Q.n} (hN : N.Admits E) (hinj : ∀ a b, Q.addr a = Q.addr b → a = b)
    {a b : Fin Q.n} {cid r : Id} {k : Nat} (hJ : ∀ m, k ≤ m → (((E.world m).node b).conn? cid).isSome = true)
    (hG : N.G a b) (hs : r ∈ Q.rooms b cid)
    {p : Packet Q.n} (hp : p ∈ (E.world k).flight) (hsrc : p.src = some a) (hdst : p.dst = Q.addr b)
    {g : List ByteArray} (hb : p.bytes = plainFrame cid g) {o : Op} (ho : o.bytes ∈ g) (hw : isWire o.kind = false)
    (hr : Q.fam.room o = some r) (hcp : o.capped = true) (hgst : N.gst ≤ p.sent)
    (hlive : N.Live a b p.sent (p.sent + N.Δ))
    (hpre : ∀ m o', ((E.world m).box b).db.ops o.id = some o' → o' = o)
    (hfr : ∀ c ∈ g, ∀ o', Op.decode c = some o' → o'.id = o.id → o' = o) :
    ∃ k', k < k' ∧ (E.world k').now ≤ p.sent + N.Δ ∧ ((E.world k').box b).db.ops o.id = some o := by
  have hj : Q.setup.at? p.dst = some b := by rw [hdst]; exact at_addr hinj b
  obtain ⟨k', idx, t, hk', ha, hp', ht⟩ := hN.timely k p a b hp hsrc hj hG hgst hlive
  refine ⟨k' + 1, by omega, ?_, ?_⟩
  · rw [Exec.world_succ, ha, deliver_now _ idx t p b hp' hj]; exact ht
  · rw [Exec.world_succ, ha]
    exact deliver_takes (E.world k') idx t p b cid g o r hp' hj hb ho (hJ k' hk') hw hr hs hcp (hpre k') hfr

/-- **H2 over time.** A want naming x in flight from b to a, x an op a
holds from then on in a room the session shows and a's index lists, on a
session a holds open, sent after gst across a live edge: within Δ of its
sending, x is in a's queue for the session, or a's op is in flight back
to b, sent then. -/
theorem want_hop {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {N : Net Q.n} (hN : N.Admits E) (hinj : ∀ a b, Q.addr a = Q.addr b → a = b)
    {a b : Fin Q.n} {cid r x : Id} {o : Op} {k : Nat}
    (hJ : ∀ m, k ≤ m → ∃ c, ((E.world m).node a).conn? cid = some c ∧ OwesQueued c)
    (hm : ∀ m, ((E.world m).node a).managed = [])
    (hG : N.G b a) (hs : r ∈ Q.rooms a cid) (hr : Q.fam.room o = some r)
    (hx : ∀ m, k ≤ m → ((E.world m).box a).db.ops x = some o ∧ ∃ it ∈ ((E.world m).node a).ix.items r, it.2 = x)
    {p : Packet Q.n} (hp : p ∈ (E.world k).flight) (hsrc : p.src = some b) (hdst : p.dst = Q.addr a)
    (hor : p.origin = Q.addr b)
    {g : List ByteArray} (hb : p.bytes = plainFrame cid g) {L : List Id} (hw : (Msg.want L).op.bytes ∈ g)
    (hxL : x ∈ L) (hL : L.length ≤ Q.cfg.maxIds)
    (hroom : ∀ m c, k ≤ m → ((E.world m).node a).conn? cid = some c →
      c.owed.length + (g.map wantsOf).sum ≤ Q.cfg.maxKnown)
    (hgst : N.gst ≤ p.sent) (hlive : N.Live b a p.sent (p.sent + N.Δ)) :
    ∃ k', k < k' ∧ (E.world k').now ≤ p.sent + N.Δ ∧
      ((∃ c', ((E.world k').node a).conn? cid = some c' ∧ x ∈ c'.owed) ∨
        ∃ sr g', o.bytes ∈ g' ∧
          (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g', (E.world k').now⟩ : Packet Q.n) ∈ (E.world k').flight) := by
  have hj : Q.setup.at? p.dst = some a := by rw [hdst]; exact at_addr hinj a
  obtain ⟨k', idx, t, hk', ha, hp', ht⟩ := hN.timely k p b a hp hsrc hj hG hgst hlive
  obtain ⟨c0, hc0, hq0⟩ := hJ k' hk'
  obtain ⟨hg, hix⟩ := hx k' hk'
  have hnow : (E.world (k' + 1)).now = t := by rw [Exec.world_succ, ha, deliver_now _ idx t p a hp' hj]
  refine ⟨k' + 1, by omega, by rw [hnow]; exact ht, ?_⟩
  rw [hnow, Exec.world_succ, ha]
  rcases deliver_queues (E.world k') idx t p a cid g x o r L c0 hp' hj hb hw hxL hL hg hr hs hix hc0 (hm k') hq0
    (hroom k' c0 hk' hc0) with e | ⟨sr, g', ho, hf⟩
  · exact Or.inl e
  · rw [hor] at hf; exact Or.inr ⟨sr, g', ho, hf⟩

theorem conn_mem {n : Node} {cid : Id} {c : Conn} (h : n.conn? cid = some c) : (cid, c) ∈ n.conns := by
  unfold Node.conn? at h
  cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some e
    have hk := List.find?_some e
    simp only [decide_eq_true_eq] at hk
    obtain ⟨p1, p2⟩ := p
    simp only at hk h
    subst hk; subst h; exact hm

/-- **A write is offered at once:** an op a node writes, new to its store,
of a room its session shows, not known to the peer nor offered on the
session, goes in flight in a have to the session's address at the
write's time. -/
theorem write_hop {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {i : Fin Q.n} {cid r : Id} {k : Nat} {ops : List Op} {t : Nat} {o : Op}
    (ha : E.act k = .write i ops t) (hm : ((E.world k).node i).managed = [])
    (hcps : ∀ y ∈ ops, y.capped = true) (ho : o ∈ ops) (hn : ((E.world k).box i).db.ops o.id = none) (hu : ∀ y ∈ ops, y.id = o.id → y = o)
    {c : Conn} (hc : ((E.world k).node i).conn? cid = some c) (hr : Q.fam.room o = some r) (hs : r ∈ Q.rooms i cid)
    (hk : o.id ∉ c.known) (hof : o.id ∉ c.offered) {dst : ByteArray} (hd : ((E.world k).node i).addr? cid = some dst)
    (hmax : 0 < Q.cfg.maxIds) :
    ∃ sr ps l, (⟨sr, some i, Q.addr i, dst, plainFrame cid ps, t⟩ : Packet Q.n) ∈ (E.world (k + 1)).flight ∧
      (Msg.hold r l).op.bytes ∈ ps ∧ o.id ∈ l := by
  obtain ⟨ps, l, hf, hps, hol⟩ := write_offers_all (Q.two i) .a ((E.world k).node i) ops t ((E.world k).box i) hm hcps o ho hn hu
    cid c (conn_mem hc) r hr hs hk hof dst hd hmax
  obtain ⟨sr, hsr⟩ := enter_sends (E.world k) i t (fun nd => nd.onWrite ((Q.two i).sync .a) ops t) dst _ hf
  refine ⟨sr, ps, l, ?_, hps, hol⟩
  rw [Exec.world_succ, ha]
  exact hsr

/-- No op the execution carries (in a store, or in a frame in flight)
shares op o's id: the crypto assumption behind ids, for o. -/
def NoClash {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n} (E : Exec Q.setup adv w₀)
    (o : Op) : Prop :=
  (∀ m l o', ((E.world m).box l).db.ops o.id = some o' → o' = o) ∧
  (∀ m q, q ∈ (E.world m).flight → ∀ cid g, q.bytes = plainFrame cid g →
    ∀ c ∈ g, ∀ o', Op.decode c = some o' → o'.id = o.id → o' = o)

theorem Net.Live.symm {n : Nat} {N : Net n} {i j : Fin n} {a b : Nat} (h : N.Live i j a b) : N.Live j i a b :=
  fun t h1 h2 => let ⟨x, y, z, u⟩ := h t h1 h2; ⟨y, x, u, z⟩

/-- **A packet in flight was sent no later than now**, in every execution. -/
theorem sent_le_now {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ p ∈ w₀.flight, p.sent ≤ w₀.now) :
    ∀ k, ∀ p ∈ (E.world k).flight, p.sent ≤ (E.world k).now := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hle := step_now (E.world k) (E.act k) (E.legal k)
    rw [Exec.world_succ]
    have enter : ∀ (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects)),
        (∀ p ∈ w.flight, p.sent ≤ t) → ∀ p ∈ (w.enter Q.setup i t f).flight, p.sent ≤ (w.enter Q.setup i t f).now := by
      intro w i t f hw p hp
      simp only [World.enter] at hp ⊢
      rcases List.mem_append.1 hp with hp | hp
      · exact hw p hp
      · exact Nat.le_of_eq (mem_packets_src i (Q.addr i) t _ _ p hp).2.2
    cases ha : E.act k with
    | deliver idx t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      cases hp : (E.world k).flight[idx]? with
      | none => rw [hp] at hle; simpa [hp] using ih
      | some q =>
        rw [hp] at hle; dsimp only at hle ⊢
        cases hj : Q.setup.at? q.dst with
        | none =>
          rw [hj] at hle; dsimp only at hle ⊢
          exact fun p hp' => Nat.le_trans (ih p (List.mem_of_mem_eraseIdx hp')) hle
        | some j =>
          rw [hj] at hle; dsimp only at hle ⊢
          exact enter _ j t _ (fun p hp' => Nat.le_trans (ih p (List.mem_of_mem_eraseIdx hp')) (by
            simp only [World.enter] at hle; exact hle))
    | dup idx =>
      simp only [World.step]
      cases (E.world k).flight[idx]? with
      | none => exact ih
      | some q =>
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ih p hp
        · rw [List.mem_singleton.1 hp]; exact Nat.le_refl _
    | drop idx => simp only [World.step]; exact fun p hp => ih p (List.mem_of_mem_eraseIdx hp)
    | tick i t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact enter _ i t _ (fun p hp => Nat.le_trans (ih p hp) (by simp only [World.enter] at hle; exact hle))
    | write i ops t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact enter _ i t _ (fun p hp => Nat.le_trans (ih p hp) (by simp only [World.enter] at hle; exact hle))
    | restart i t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact fun p hp => Nat.le_trans (ih p hp) hle
    | close i a t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact enter _ i t _ (fun p hp => Nat.le_trans (ih p hp) (by simp only [World.enter] at hle; exact hle))
    | connect i j cid dl t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact enter _ i t _ (fun p hp => Nat.le_trans (ih p hp) (by simp only [World.enter] at hle; exact hle))
    | inject i o b t =>
      rw [ha] at hle; simp only [World.step] at hle ⊢
      exact enter _ i t _ (fun p hp => Nat.le_trans (ih p hp) (by simp only [World.enter] at hle; exact hle))

/-- **A want gets its op across, in two hops.** A want naming x in flight
from b to a, where a holds x (op o) from then on in a room both ends show
and a's index lists it, on a session both ends hold open from then on,
sent after gst across an edge live for 2Δ: within 2Δ of the want's
sending, b holds x, or x waits in a's queue for the session (the
backlog case, which `owed_within` bounds by its queue position). -/
theorem want_to_op {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {N : Net Q.n} (hN : N.Admits E) (hinj : ∀ a b, Q.addr a = Q.addr b → a = b)
    (hs0 : ∀ p ∈ w₀.flight, p.sent ≤ w₀.now)
    {a b : Fin Q.n} {cid r x : Id} {o : Op} {k : Nat}
    (hJa : ∀ m, k ≤ m → ∃ c, ((E.world m).node a).conn? cid = some c ∧ OwesQueued c)
    (hJb : ∀ m, k ≤ m → (((E.world m).node b).conn? cid).isSome = true)
    (hm : ∀ m, ((E.world m).node a).managed = [])
    (hGab : N.G a b) (hGba : N.G b a) (hsa : r ∈ Q.rooms a cid) (hsb : r ∈ Q.rooms b cid)
    (hr : Q.fam.room o = some r) (hw : isWire o.kind = false) (hcp : o.capped = true) (hox : o.id = x)
    (hcl : NoClash E o)
    (hx : ∀ m, k ≤ m → ((E.world m).box a).db.ops x = some o ∧ ∃ it ∈ ((E.world m).node a).ix.items r, it.2 = x)
    {p : Packet Q.n} (hp : p ∈ (E.world k).flight) (hsrc : p.src = some b) (hdst : p.dst = Q.addr a)
    (hor : p.origin = Q.addr b) {g : List ByteArray} (hb : p.bytes = plainFrame cid g) {L : List Id}
    (hwL : (Msg.want L).op.bytes ∈ g) (hxL : x ∈ L) (hL : L.length ≤ Q.cfg.maxIds)
    (hroom : ∀ m c, k ≤ m → ((E.world m).node a).conn? cid = some c →
      c.owed.length + (g.map wantsOf).sum ≤ Q.cfg.maxKnown)
    (hgst : N.gst ≤ p.sent) (hlive : N.Live a b p.sent (p.sent + 2 * N.Δ)) :
    ∃ k', k < k' ∧ (E.world k').now ≤ p.sent + 2 * N.Δ ∧
      (((E.world k').box b).db.ops x = some o ∨ ∃ c', ((E.world k').node a).conn? cid = some c' ∧ x ∈ c'.owed) := by
  obtain ⟨k1, hk1, ht1, h1⟩ := want_hop E hN hinj hJa hm hGba hsa hr hx hp hsrc hdst hor hb hwL hxL hL hroom hgst
    ((Net.Live.symm hlive).mono (Nat.le_refl _) (by omega))
  rcases h1 with hq | ⟨sr, g', ho, hf⟩
  · exact ⟨k1, hk1, by omega, Or.inr hq⟩
  · have hk1t : p.sent ≤ (E.world k1).now :=
      Nat.le_trans (sent_le_now E hs0 k p hp) (Exec.now_mono E (Nat.le_of_lt hk1))
    obtain ⟨k2, hk2, ht2, h2⟩ := op_hop E hN hinj (a := a) (b := b) (cid := cid) (r := r) (k := k1)
      (fun m hm' => hJb m (by omega)) hGab hsb hf rfl rfl rfl ho hw hr hcp (by simp only; omega)
      (hlive.mono (by simp only; omega) (by simp only; omega)) (fun m o' h => hcl.1 m b o' h)
      (hcl.2 k1 _ hf cid g' rfl)
    refine ⟨k2, by omega, by simp only at ht2; omega, Or.inl ?_⟩
    rw [← hox]; exact h2

end Plain

end Engine.World
