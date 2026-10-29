/-
Which rooms a connection carries: the laws of `roomsV`, the view the
`rooms` hook runs (Connection/Intents.lean), and so the rooms every
connection step uses (`Node.refresh`, Engine/Sync/Node.lean).

- `trusts_live`: for a node that is a live member of c, the trust rule
  is `allowPeer`: the link's inviter clause applies only before
  admission.
- `rooms_trusted`: a room is carried synced (`.sync c`) only if this
  node holds it and is in it (its key, while `Community.mine` names a
  device of it), and the trust rule takes a peer key the connection
  names.
- `rooms_cut`: so a live member's connection carries no synced room
  whose peer keys `allowPeer` refuses (it may carry its notices:
  RemovalLaws, `rooms_removed`).
- `rooms_model`: the `rooms` hook runs `roomsV` and gives its synced
  rooms.

With `recv_send` and `recv_take`, nothing of that room then goes out on
the connection or is taken from it. `Community.removal_cuts_off` says
`allowPeer` refuses a removed user's devices, over the Community
family's own store; `rooms_cut_node` (ops/connection/NodeLaws.lean)
carries it to the composed store the node runs, by `sum_project`.
-/
import ops.connection.Intents

namespace Connection
open Engine Engine.Sync

section
variable {A B : Type} [SortKey (A ⊕ B)]

theorem eval_liftL_pure {α : Type} (s : DB (A ⊕ B)) (a : α) :
    ((Pure.pure a : View A α).liftL : View (A ⊕ B) α).eval s = a := rfl

theorem eval_liftL_bind {α β : Type} (s : DB (A ⊕ B)) (v : View A α) (f : α → View A β) :
    ((v >>= f).liftL : View (A ⊕ B) β).eval s =
      ((f ((v.liftL : View (A ⊕ B) α).eval s)).liftL : View (A ⊕ B) β).eval s := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih _

end

/-- **For a live member, the trust rule is `allowPeer`.** The link
clause (trust the inviter a pending join names) holds only before this
device is admitted. -/
theorem trusts_live (s : DB F) {c me peer : B}
    (h : ((Community.allowPeer c me).liftL : View F Bool).eval s = true) :
    ((trusts c me peer).liftL : View F Bool).eval s =
      ((Community.allowPeer c peer).liftL : View F Bool).eval s := by
  unfold trusts
  rw [eval_liftL_bind]
  cases hp : ((Community.allowPeer c peer).liftL : View F Bool).eval s
  · simp only [Bool.false_eq_true, ite_false]
    rw [eval_liftL_bind]
    split
    · rfl
    · rw [eval_liftL_bind, h, eval_liftL_bind]
      simp [eval_liftL_pure]
  · rfl

theorem eval_roomFor (s : DB F) (given : List Id) (c peer : B) :
    (roomFor given c peer).eval s =
      match (meV c).eval s with
      | some me =>
        if ((trusts c me peer).liftL : View F Bool).eval s then [Room.sync c]
        else ((((Community.removalsAt c peer).liftL : View F (List Id)).eval s).filter
          fun x => !has given x).map (Room.notice c)
      | none => [] := by
  unfold roomFor
  rw [View.eval_bind]
  cases (meV c).eval s with
  | none => rfl
  | some me =>
    simp only [View.eval_bind]
    cases ((trusts c me peer).liftL : View F Bool).eval s <;> simp [View.eval_bind]

theorem eval_roomsOf (s : DB F) (given : List Id) (ps : List (B × B)) :
    (roomsOf given ps).eval s = ps.flatMap fun (c, peer) => (roomFor given c peer).eval s := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨c, peer⟩ := p
    simp only [roomsOf, View.eval_bind, View.eval_pure, List.flatMap_cons, ih]

/-- A room cid carries, with the (community, peer) pair it is for. -/
theorem mem_roomsV (s : DB F) {cid : Id} {rm : Room} (h : rm ∈ (roomsV cid).eval s) :
    ∃ c peer, peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])) ∧ c ∈ heldV.eval s ∧
      rm ∈ (roomFor ((givenOn cid).eval s) c peer).eval s := by
  simp only [roomsV, View.eval_bind, View.eval_read, eval_roomsOf, List.mem_flatMap] at h
  obtain ⟨⟨c, peer⟩, hp, hm⟩ := h
  obtain ⟨peer', hpeer, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨c', hheld, he⟩ := hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨c', peer', hpeer, hheld, hm⟩

/-- **A room is carried synced only if trusted.** If connection cid
carries room c synced, this node holds c and is in it as its key `me`,
one of cid's established facts names a peer key, and the trust rule
takes it. -/
theorem rooms_trusted (s : DB F) {cid c : Id} (h : Room.sync c ∈ (roomsV cid).eval s) :
    ∃ peer me, peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])) ∧
      c ∈ heldV.eval s ∧
      (meV c).eval s = some me ∧ ((trusts c me peer).liftL : View F Bool).eval s = true := by
  obtain ⟨c', peer, hpeer, hheld, hm⟩ := mem_roomsV s h
  rw [eval_roomFor] at hm
  cases hme : (meV c').eval s with
  | none => simp only [hme, List.not_mem_nil] at hm
  | some me =>
    cases ht : ((trusts c' me peer).liftL : View F Bool).eval s
    · simp only [hme, ht, Bool.false_eq_true, ite_false, List.mem_map] at hm
      obtain ⟨_, _, hn⟩ := hm; cases hn
    · simp only [hme, ht, ite_true, List.mem_singleton, Room.sync.injEq] at hm
      subst hm
      exact ⟨peer, me, hpeer, hheld, hme, ht⟩

/-- **A live member's connection carries no synced room whose peer
`allowPeer` refuses.** If this node is a live member of c, and
`allowPeer` refuses, for c, every peer key cid's established facts name,
then cid carries no room c synced: no step of it sends an op of c by
sync or takes one (`recv_send`, `recv_take`). It may carry c's notices
(`rooms_removed`). -/
theorem rooms_cut (s : DB F) {cid c : Id}
    (hme : ∀ me, (meV c).eval s = some me →
      ((Community.allowPeer c me).liftL : View F Bool).eval s = true)
    (hpeer : ∀ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])),
      ((Community.allowPeer c peer).liftL : View F Bool).eval s = false) :
    Room.sync c ∉ (roomsV cid).eval s := by
  intro h
  obtain ⟨peer, me, hp, _, hm, ht⟩ := rooms_trusted s h
  rw [trusts_live s (hme me hm), hpeer peer hp] at ht
  cases ht

/-- The hook runs the view: on the model, `rooms` gives `roomsV`, its
synced rooms and its notices, and reads only. -/
theorem rooms_model (s : DB F) (cid : Id) :
    ((rooms cid : Model F (List Room))).run s = ((roomsV cid).eval s, s) := by
  unfold rooms
  exact View.run_model _ s

end Connection
