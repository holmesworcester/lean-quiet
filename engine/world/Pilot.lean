/-
The pilot, proven of the running code: a round's claim of ids, from i to
j on a session joined from then on, that lists an op x which i holds,
gets x to j within 3Δ of the claim's sending, whatever else the
execution does (`pilot`; `claim_delivers` over any walk with the walk's
laws, which main's `walkN` has, `walk_proof`). It is
`round_stmt`'s first leg in the leaf regime, for any number of nodes,
sessions and rooms around it.

The proof is an obligation chain over three hops (engine/world/Hops.lean):
the claim arrives within Δ (`timely`), and j wants x unless it has it
(`claim_wants`); the want arrives within Δ, and i sends x (`want_sends`);
x arrives within Δ, and j stores it (`op_taken`). Between hops, any
steps: what i holds it keeps (`grows_proof`), every node keeps the node
invariant (`reach_ok`), and the network's packets say when and from
whom they were sent (`reach_flight`).
-/
import engine.world.Hops
import engine.world.Epidemic
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-! ## The world's packets -/

theorem mem_packets {n : Nat} (i : Fin n) (o : ByteArray) (t : Nat) : ∀ (s : Nat) (l : List (ByteArray × ByteArray)) d b,
    (d, b) ∈ l → ∃ s', (⟨s', some i, o, d, b, t⟩ : Packet n) ∈ packets i o t s l := by
  intro s l
  induction l generalizing s with
  | nil => intro d b h; cases h
  | cons x t' ih =>
    intro d b h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨s, List.mem_cons_self ..⟩
    · obtain ⟨s', hs'⟩ := ih (s + 1) d b h
      exact ⟨s', List.mem_cons_of_mem _ hs'⟩

theorem packets_inv {n : Nat} (i : Fin n) (o : ByteArray) (t : Nat) : ∀ (s : Nat) (l : List (ByteArray × ByteArray)) q,
    q ∈ packets i o t s l → q.sent = t ∧ q.src = some i ∧ q.origin = o := by
  intro s l
  induction l generalizing s with
  | nil => intro q h; cases h
  | cons x t' ih =>
    intro q h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, rfl⟩
    · exact ih _ q h

theorem at_addr (Q : Plain F) (ok : PlainOk Q) (j : Fin Q.n) : Q.setup.at? (Q.addr j) = some j := by
  unfold Setup.at?
  cases e : (List.finRange Q.setup.n).find? (fun i => Decidable.decide (Q.setup.addr i = Q.addr j)) with
  | none =>
    have := List.find?_eq_none.1 e j (List.mem_finRange j)
    simp [Plain.setup] at this
  | some i =>
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    exact congrArg some (ok.addr_inj i j this)

/-- What the network carries: every packet in flight was sent no later
than now, and one an honest node sent says it came from that node's
address. -/
def FlightOk (Q : Plain F) (w : World (Held F) Q.n) : Prop :=
  ∀ q ∈ w.flight, q.sent ≤ w.now ∧ ∀ l, q.src = some l → q.origin = Q.addr l

theorem flight_enter (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hle : w.now ≤ t) (ok : FlightOk Q w) : FlightOk Q (w.enter Q.setup i t f) := by
  intro q hq
  unfold World.enter at hq ⊢
  dsimp only at hq ⊢
  rcases List.mem_append.1 hq with hq | hq
  · exact ⟨Nat.le_trans (ok q hq).1 hle, (ok q hq).2⟩
  · obtain ⟨e1, e2, e3⟩ := packets_inv i _ t _ _ q hq
    refine ⟨by omega, fun l hl => ?_⟩
    rw [e2] at hl; cases hl; exact e3

theorem reach_flight' (Q : Plain F) (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0 : FlightOk Q w₀) (hr : Reachable Q.setup adv w₀ w) : FlightOk Q w := by
  induction hr with
  | init => exact h0
  | @step w a _ hl ih =>
    have hn := step_now w a hl
    cases a with
    | deliver k t =>
      simp only [Legal] at hl
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        split
        · intro q hq
          simp only at hq ⊢
          have := ih q (List.mem_of_mem_eraseIdx hq)
          exact ⟨Nat.le_trans this.1 hl.2, this.2⟩
        · rename_i j' _
          intro q hq
          have := flight_enter Q { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => Node.onFrame (Q.setup.sync j') nd p.origin p.bytes t) hl.2
            (fun q hq => ih q (List.mem_of_mem_eraseIdx hq)) q hq
          exact this
    | dup k =>
      simp only [World.step]
      split
      · exact ih
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact ih q hq
        · have e := List.mem_singleton.1 hq
          rw [e]
          exact ⟨Nat.le_refl _, fun l hl => by cases hl⟩
    | drop k =>
      intro q hq
      exact ih q (List.mem_of_mem_eraseIdx hq)
    | tick i t => exact flight_enter Q w i t (fun nd => nd.onTick (Q.setup.sync i) t) hl ih
    | write i ops t =>
      intro q hq
      exact flight_enter Q w i t (fun nd => nd.onWrite (Q.setup.sync i) ops t) hl.1 ih q hq
    | restart i t =>
      intro q hq
      exact ⟨Nat.le_trans (ih q hq).1 hl, (ih q hq).2⟩
    | connect i j cid d t =>
      exact flight_enter Q w i t (fun nd => nd.connect (Q.setup.sync i) cid (Q.setup.addr j) d t) hl.2 ih
    | inject i o b t =>
      intro q hq
      exact flight_enter Q w i t (fun nd => nd.onFrame (Q.setup.sync i) o b t) hl.2 ih q hq

theorem reach_flight (Q : Plain F) (adv : World (Held F) Q.n → ByteArray → Prop) (w : World (Held F) Q.n)
    (hr : Q.Reach adv w) : FlightOk Q w :=
  reach_flight' Q adv Q.start w (fun q hq => by cases hq) hr

/-- A delivery to the node at a packet's address runs its frame there:
that node and its store move on, time is the delivery's, and what it
sends is in flight, from it. -/
theorem deliver_at (Q : Plain F) (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) :
    (w.step Q.setup (.deliver idx t)).node j =
      (((w.node j).onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t).run (w.box j)).1.1 ∧
    (w.step Q.setup (.deliver idx t)).box j =
      (((w.node j).onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t).run (w.box j)).2 ∧
    (w.step Q.setup (.deliver idx t)).now = t ∧
    ∀ d b, (d, b) ∈ (((w.node j).onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t).run (w.box j)).1.2.send →
      ∃ s, (⟨s, some j, Q.addr j, d, b, t⟩ : Packet Q.n) ∈ (w.step Q.setup (.deliver idx t)).flight := by
  have hp' : (@World.flight (Held F) Q.setup.n w)[idx]? = some p := hp
  simp only [World.step, hp', hj, World.enter]
  refine ⟨by simp only [upd]; exact if_pos rfl, by simp only [upd]; exact if_pos rfl, trivial,
    fun d b hdb => ?_⟩
  obtain ⟨s, hs⟩ := mem_packets j (Q.addr j) t w.serial _ d b hdb
  exact ⟨s, List.mem_append_right _ hs⟩

theorem holds_named (Q : Plain F) (w : World (Held F) Q.n) (hu : Unclashed w) (i j : Fin Q.n) (r x : Id)
    (hi : Q.Holds w i r x) (hn : Named (w.box j) x) : Q.Holds w j r x := by
  obtain ⟨o, ho, hr⟩ := hi
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hn
  exact ⟨o', ho', by rw [← hu i j x o o' ho ho']; exact hr⟩

theorem Net.Live.symm {n : Nat} {N : Net n} {i j : Fin n} {a b : Nat} (h : N.Live i j a b) : N.Live j i a b :=
  fun t h1 h2 => let e := h t h1 h2; ⟨e.2.1, e.1, e.2.2.2, e.2.2.1⟩

/-- **The pilot, proven of the running code** (given the walk's laws): a
round's claim of ids, from i to j on a session joined from then on, that
lists x, which i holds, gets x to j within 3Δ of its sending. The
obligation chain: the claim arrives (Δ); j wants x unless it has it
(`claim_wants`); the want arrives (Δ); i sends x (`want_sends`); x
arrives (Δ) and j stores it (`op_taken`). Whatever else the execution
does meanwhile. -/
theorem claim_delivers (hw : walk_stmt) : claim_delivers_stmt := by
  intro F Q N E W i j cid r k kr p ps cs rg L x hf hG hJ hgst hlive hrooms hp hsrc hdst hpeek hclaim hcs hxL hx
  have wl := hw F Q.fam Q.cfg
  have hok : ∀ m l, NodeOk Q.fam ((E.world m).node l) ((E.world m).box l) := fun m => reach_ok Q wl noAdv _ (E.reachable m)
  have hfl : ∀ m, FlightOk Q (E.world m) := fun m => reach_flight Q noAdv _ (E.reachable m)
  have hmax := hf.ok.maxIds
  have atj : Q.setup.at? (Q.addr j) = some j := at_addr Q hf.ok j
  have ati : Q.setup.at? (Q.addr i) = some i := at_addr Q hf.ok i
  have grow : ∀ l m m', m ≤ m' → Q.Holds (E.world m) l r x → Q.Holds (E.world m') l r x := fun l m m' hle h =>
    held_on E (fun m hm => grows_proof hw F Q noAdv _ _ l r x (E.reachable m) (E.legal m) hm) m m' hle h
  -- The claim arrives at j within Δ.
  have hsentk : p.sent ≤ (E.world k).now := (hfl k p hp).1
  have horig : p.origin = Q.addr i := (hfl k p hp).2 i hsrc
  obtain ⟨k1, idx1, t1, hk1, hact1, hfl1, ht1⟩ := hf.net.timely k p i j hp hsrc (by rw [hdst]; exact atj) hG hgst
    (hlive.mono (Nat.le_refl _) (by omega))
  have hle1 : (E.world k1).now ≤ t1 := by have := E.legal k1; rw [hact1] at this; exact this.2
  have hk1now := Exec.now_mono E hk1
  have e1 : E.world (k1 + 1) = (E.world k1).step Q.setup (.deliver idx1 t1) := by rw [← hact1]; rfl
  obtain ⟨n1, b1, now1, sent1⟩ := deliver_at Q (E.world k1) idx1 t1 p j hfl1 (by rw [hdst]; exact atj)
  obtain ⟨⟨c1, hc1, -⟩, -⟩ := (hJ k1 hk1).2
  rcases claim_wants Q.fam Q.cfg (Q.rooms j) wl _ _ (hok k1 j) p.origin p.bytes t1 cid ps hpeek c1 hc1 r
      (fun h' => (hrooms h').2) kr cs rg L x hclaim hcs hxL hmax with hn | ⟨Wn, g, hxW, hWl, hWg, hsend⟩
  · -- j already holds x when the claim's frame is done.
    refine ⟨k1 + 1, by omega, by rw [e1, now1]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k1 + 1)) i j r x (grow i k (k1 + 1) (by omega) hx)
    rw [e1, b1]; exact hn
  · -- The want goes back to i.
    obtain ⟨s1, hq⟩ := sent1 _ _ hsend
    rw [← e1, horig] at hq
    obtain ⟨k2, idx2, t2, hk2, hact2, hfl2, ht2⟩ := hf.net.timely (k1 + 1) _ j i hq rfl ati (hf.symm i j hG)
      (show N.gst ≤ t1 by omega)
      ((hlive.mono (show p.sent ≤ t1 by omega) (show t1 + N.Δ ≤ p.sent + 3 * N.Δ by omega)).symm)
    simp only at ht2
    have hnow1 : (E.world (k1 + 1)).now = t1 := by rw [e1, now1]
    have hk2now := Exec.now_mono E hk2
    have hle2 : (E.world k2).now ≤ t2 := by have := E.legal k2; rw [hact2] at this; exact this.2
    have e2 : E.world (k2 + 1) = (E.world k2).step Q.setup (.deliver idx2 t2) := by rw [← hact2]; rfl
    obtain ⟨n2, b2, now2, sent2⟩ := deliver_at Q (E.world k2) idx2 t2 _ i hfl2 ati
    obtain ⟨⟨c2, hc2, -⟩, -⟩ := hJ k2 (by omega)
    obtain ⟨o, ho, hor⟩ := grow i k k2 (by omega) hx
    obtain ⟨g', hog, hsend'⟩ := want_sends Q.fam Q.cfg (Q.rooms i) wl _ _ (hok k2 i) (Q.addr j) _ t2 cid g
      (peek_plainFrame cid g) c2 hc2 r (fun h' => (hrooms h').1) Wn x o hWg hWl hxW ho hor
    -- x goes to j.
    obtain ⟨s2, hq'⟩ := sent2 _ _ hsend'
    rw [← e2] at hq'
    obtain ⟨k3, idx3, t3, hk3, hact3, hfl3, ht3⟩ := hf.net.timely (k2 + 1) _ i j hq' rfl atj hG
      (show N.gst ≤ t2 by omega)
      (hlive.mono (show p.sent ≤ t2 by omega) (show t2 + N.Δ ≤ p.sent + 3 * N.Δ by omega))
    simp only at ht3
    have hnow2 : (E.world (k2 + 1)).now = t2 := by rw [e2, now2]
    have hk3now := Exec.now_mono E hk3
    have e3 : E.world (k3 + 1) = (E.world k3).step Q.setup (.deliver idx3 t3) := by rw [← hact3]; rfl
    obtain ⟨-, b3, now3, -⟩ := deliver_at Q (E.world k3) idx3 t3 _ j hfl3 atj
    obtain ⟨⟨c3, hc3, -⟩, -⟩ := (hJ k3 (by omega)).2
    have hor' : Q.fam.room o = some r := hor
    have hshared : Q.fam.shared o = true := by simp [Family.shared, hor']
    have hstored := op_taken Q.fam Q.cfg (Q.rooms j) wl _ _ (hok k3 j) (Q.addr i) _ t3 cid g'
      (peek_plainFrame cid g') c3 hc3 r (fun h' => (hrooms h').2) o hog (hf.ok.wire o hshared) hor
    have hid : o.id = x := (hok k2 i).ids x o ho
    refine ⟨k3 + 1, by omega, by rw [e3, now3]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k3 + 1)) i j r x (grow i k (k3 + 1) (by omega) hx)
    rw [e3, b3, ← hid]; exact hstored

/-- **The pilot, with no premise left:** main's walk has the laws it
needs (`walk_proof`). -/
theorem pilot : claim_delivers_stmt := claim_delivers walk_proof

/-- **Shared stores only grow**, with no premise left. -/
theorem grows_all : grows_stmt := grows_proof walk_proof

/-- **L-offered, its first half, proven: the room index is the store.**
At every world the plain world reaches, against any attacker, each
node's index of room r names exactly the ops of room r it stores. -/
theorem index_store_proof : index_store_stmt := by
  intro F Q adv w hr i r x
  exact (reach_ok Q (walk_proof F Q.fam Q.cfg) adv w hr i).exact r x

/-- **L-restart, proven: a restart loses only memory.** -/
theorem restart_proof : restart_stmt := by
  intro F Q adv w i t hr hl
  have hr' : Q.Reach adv (w.step Q.setup (.restart i t)) := Reachable.step hr hl
  have hb : (w.step Q.setup (.restart i t)).box i = w.box i := by
    show upd w.box i (Q.setup.crash (w.box i)) i = w.box i
    simp only [upd, ite_true]; rfl
  refine ⟨fun r x => ?_, fun r x => (reach_ok Q (walk_proof F Q.fam Q.cfg) adv _ hr' i).exact r x, ?_⟩
  · show (∃ o, (w.box i).db.ops x = some o ∧ _) ↔ (∃ o, ((w.step Q.setup (.restart i t)).box i).db.ops x = some o ∧ _)
    rw [hb]
  · show (upd w.node i (Node.boot _ _ _) i).conns = []
    simp only [upd, ite_true]; rfl

/-- **L-round's forward leg, proven in the leaf regime.** Every op of the
window i's index named when the round opened is listed by the opening's
claim for its range, and i still holds it, so the pilot carries it. -/
theorem round_forward : round_forward_stmt := by
  intro F Q N E W i j cid r kr k p X hf hleaf hG hJ hgst hlive hrooms hop it hit hwin
  obtain ⟨hp, hsrc, hdst, ⟨k₀, hk₀, hX⟩, ps, hpeek, hmsg⟩ := hop
  obtain ⟨rg, hrg, hhas⟩ := hwin
  have hlen : (within Prod.fst rg X).length ≤ Q.cfg.params.leaf := by
    have h1 : (within Prod.fst rg X).length ≤ X.length := List.length_filter_le _ _
    have h2 : X.length ≤ W := by rw [hX]; exact hf.bounded r k₀ i
    omega
  have hcl : Claim.ids rg ((within Prod.fst rg X).map Prod.snd) ∈
      (window (max ((E.world k).node i).floor ((E.world k).node j).floor)).map
        (opening Prod.fst Prod.snd sha256 Q.cfg.params X) := by
    refine List.mem_map.2 ⟨rg, hrg, ?_⟩
    simp only [opening, hlen, ↓reduceIte]
  have hxL : it.2 ∈ (within Prod.fst rg X).map Prod.snd := List.mem_map.2 ⟨it, mem_within.2 ⟨hit, hhas⟩, rfl⟩
  have hx0 : Q.Holds (E.world k₀) i r it.2 :=
    ((reach_ok Q (walk_proof F Q.fam Q.cfg) noAdv _ (E.reachable k₀) i).exact r it.2).1 ⟨it, by rw [← hX]; exact hit, rfl⟩
  have hx : Q.Holds (E.world k) i r it.2 :=
    held_on E (fun m hm => grows_all F Q noAdv _ _ i r it.2 (E.reachable m) (E.legal m) hm) k₀ k hk₀ hx0
  exact pilot F Q N E W i j cid r k kr p ps _ rg _ it.2 hf hG hJ hgst hlive hrooms hp hsrc hdst hpeek hmsg hcl hxL hx

end Engine.World
