/-
The send half of the user's target theorem, with every node invariant
discharged by the running node (docs/PROOFS.md, "What a send costs"):
what is left are the session's facts, the network's, the queue's room and
the crypto assumption.
-/
import engine.world.InvOwed

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

namespace Plain
variable {Q : Plain F}

/-- **An op of a room a node holds, it holds at every later step**, the
same op (no purge takes an op of a room; `step_keeps`). -/
theorem keeps_op {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {i : Fin Q.n} {x r : Id} {o : Op} {k : Nat}
    (hg : ((E.world k).box i).db.ops x = some o) (hr : Q.fam.room o = some r) :
    ∀ m, k ≤ m → ((E.world m).box i).db.ops x = some o := by
  intro m hm
  induction m with
  | zero => rw [show k = 0 by omega] at hg; exact hg
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with h | h
    · rw [Exec.world_succ]; exact step_keeps (E.world m) (E.act m) i x o r (ih (by omega)) hr
    · rw [show k = m + 1 by omega] at hg; exact hg

/-- **A want in flight gets its op across** (the send half's last two
hops and the queue), from empty stores, with no attacker: a want naming
x in flight from b to a on session cid, which both hold open from then on
with a's address for it b's, nobody reopening it at a; a holds x (op o)
in a room both show; the edge is live from the want's sending until T
after gst; the queue has room for the want's frame; no hash clash on x.
Then within 3Δ + maxKnown · τ of the want's sending, b holds x. The
node's invariants (queues owe only what they hold, at most `maxKnown`;
no managed sessions; the index covers the store; stores keep room ops)
are the running node's, over every execution. -/
theorem want_reaches (E : Q.Run) {N : Net Q.n} (hN : N.Admits E) (hinj : ∀ i j, Q.addr i = Q.addr j → i = j)
    {a b : Fin Q.n} {cid r x : Id} {o : Op} {k T : Nat}
    (hca : ∀ m, k ≤ m → (((E.world m).node a).conn? cid).isSome = true)
    (hcb : ∀ m, k ≤ m → (((E.world m).node b).conn? cid).isSome = true)
    (haddr : ∀ m, k ≤ m → ((E.world m).node a).addr? cid = some (Q.addr b))
    (hGab : N.G a b) (hGba : N.G b a) (hra : r ∈ Q.rooms a cid) (hrb : r ∈ Q.rooms b cid)
    (hno : ∀ m j dl t, k ≤ m → E.act m ≠ .connect a j cid dl t) (hburst : 0 < Q.cfg.burst)
    (hr : Q.fam.room o = some r) (hw : isWire o.kind = false) (hcp : o.capped = true) (hox : o.id = x)
    (hcl : NoClash E o) (hg : ((E.world k).box a).db.ops x = some o)
    {p : Packet Q.n} (hp : p ∈ (E.world k).flight) (hsrc : p.src = some b) (hdst : p.dst = Q.addr a)
    {g : List ByteArray} (hb : p.bytes = plainFrame cid g) {Lw : List Id} (hwL : (Msg.want Lw).op.bytes ∈ g)
    (hxL : x ∈ Lw) (hL : Lw.length ≤ Q.cfg.maxIds)
    (hroom : ∀ m c, k ≤ m → ((E.world m).node a).conn? cid = some c →
      c.owed.length + (g.map wantsOf).sum ≤ Q.cfg.maxKnown)
    (hgst : N.gst ≤ p.sent) (hlive : N.Live a b p.sent T) (hT : p.sent + 3 * N.Δ + Q.cfg.maxKnown * N.τ ≤ T) :
    ∃ k', k < k' ∧ (E.world k').now ≤ p.sent + 3 * N.Δ + Q.cfg.maxKnown * N.τ ∧
      ((E.world k').box b).db.ops x = some o := by
  have hs0 : ∀ q ∈ Q.start.flight, q.sent ≤ Q.start.now := fun q hq => by simp [Plain.start, World.init] at hq
  have hsent : p.sent ≤ (E.world k).now := sent_le_now E hs0 k p hp
  have hm : ∀ m l, ((E.world m).node l).managed = [] :=
    managed_nil E (fun _ => by simp [Plain.start, World.init, Node.boot])
  have L : Link E N a b cid r k T :=
    { inj := hinj, admits := hN, Gab := hGab, Gba := hGba
      conn_a := fun m hm' => by
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hca m hm')
        exact ⟨c, hc, owes_queued_start E m a cid c hc, owed_bounded_start E m a cid c hc⟩
      conn_b := hcb, addr_a := haddr, rooms_a := hra, rooms_b := hrb, managed := hm, noreopen := hno
      gst := Nat.le_trans hgst hsent
      live := hlive.mono hsent (Nat.le_refl _)
      burst := hburst }
  refine want_delivers E L hs0 hr hw hcp hox hcl (fun m hm' => ⟨keeps_op E hg hr m hm', ?_⟩) hp hsrc hdst hb hwL hxL hL
    hroom hgst hlive hT
  obtain ⟨it, hit, e⟩ := ix_covers_start E m a r x o (keeps_op E hg hr m hm') hr
  exact ⟨it, hit, e⟩

end Plain

end Engine.World
