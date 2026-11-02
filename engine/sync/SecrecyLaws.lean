/-
Secrecy of the real offer paths: filed stream writes and the closure walk.
Every id they advertise names a stored, shared op. No unused offer model.
-/
import engine.sync.OfferLaws
import engine.wire.WorldLaws

namespace Engine.Sync
variable {F : Type} (fam : Family F) (cfg : Config)

/-- The stream's output comes from the actual loop's stored, shown pairs. -/
theorem filed_origin (c : Conn) (ids : List Id) (h : Held F) :
    ∃ pairs, ((c.filed fam cfg ids : HeldM F Step) h).1.send = holdsOf cfg pairs ∧
      ∀ p ∈ pairs, Shown fam h.db c p.2 := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam cfg h.db)]
  · refine ⟨_, rfl, ?_⟩
    have hi := foldl_inv (fun b : List (Id × Id) × Conn => b.2.rooms = c.rooms ∧
        ∀ p ∈ b.1, Shown fam h.db c p.2) (fileOffer fam cfg h.db) (by
          intro b i ⟨hr, hi⟩
          unfold fileOffer
          split
          · split
            · rename_i o hg
              split
              · rename_i hs
                refine ⟨hr, ?_⟩
                intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · exact ⟨o, hg, by rw [← shows_rooms fam hr]; exact hs⟩
                · exact hi p hp
              · exact ⟨hr, hi⟩
            · exact ⟨hr, hi⟩
          · exact ⟨hr, hi⟩) ids ([], c) ⟨rfl, by simp⟩
    exact fun p hp => hi.2 p (List.mem_reverse.mp hp)
  · intro a b
    unfold fileOffer
    split
    · rw [HeldM.bind_apply, HeldM.getOp_apply]
      cases h.db.ops a with
      | none => rfl
      | some o => dsimp only; split <;> rfl
    · rfl

theorem holdsOf_shown {h : Held F} {c : Conn} {pairs : List (Id × Id)}
    (hp : ∀ p ∈ pairs, Shown fam h.db c p.2) {r i : Id} {ids : List Id}
    (hm : (Msg.hold r ids).op ∈ holdsOf cfg pairs) (hi : i ∈ ids) : Shown fam h.db c i := by
  obtain ⟨room, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨part, ht, he⟩ := List.mem_map.mp hm
  have eq := congrArg Msg.ofOp he
  simp only [ofOp_hold, Option.some.injEq, Msg.hold.injEq] at eq
  obtain ⟨rfl, rfl⟩ := eq
  have hx := mem_pieceIds ht i hi
  obtain ⟨p, hp', he⟩ := List.mem_filterMap.mp hx
  split at he
  · cases he; exact hp p hp'
  · cases he

/-- Every advertisement the running offer path (the stream, `filed`)
makes names a stored op in one of this connection's rooms: a shared op
the peer may see. (A windowed round's closure is offered by its round
answers, `answer_offers`; there is no walk left to offer it.) -/
theorem offer_shared (c : Conn) (news : List Id) (h : Held F) (r i : Id) (ids : List Id)
    (hm : (Msg.hold r ids).op ∈ ((c.filed fam cfg news : HeldM F Step) h).1.send) (hi : i ∈ ids) :
    ∃ o r, h.db.ops i = some o ∧ fam.room o = some r ∧ has c.rooms r = true := by
  have shown : Shown fam h.db c i := by
    obtain ⟨pairs, he, hp⟩ := filed_origin fam cfg c news h
    rw [he] at hm
    exact holdsOf_shown fam cfg hp hm hi
  obtain ⟨o, ho, hs⟩ := shown
  unfold Conn.shows at hs
  cases hr : fam.room o with
  | none => simp [hr] at hs
  | some room => simp only [hr] at hs; exact ⟨o, room, ho, hr, hs⟩

/-- Pending writes and absent closure ids cannot be advertised as stored. -/
theorem offer_stored (c : Conn) (news : List Id) (h : Held F) (r i : Id) (ids : List Id)
    (hm : (Msg.hold r ids).op ∈ ((c.filed fam cfg news : HeldM F Step) h).1.send) (hi : i ∈ ids) :
    ∃ o, h.db.ops i = some o := by
  obtain ⟨o, _, ho, _⟩ := offer_shared fam cfg c news h r i ids hm hi
  exact ⟨o, ho⟩
end Engine.Sync
