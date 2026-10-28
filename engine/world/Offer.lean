/-
An offer delivers, proven of the running code (`offer_delivers`): a have
of room r naming y, from j to i on a joined session, gets y to i within
3Δ, provided y is not already asked on i's side while the have is in
flight. The stream, a round's reverse leg and closure offers all end
with such a have, so each of them is this law plus the step that sends
the have.

- **H4** (`have_wants`, engine/world/Asks.lean): a have of an op the
  node lacks and has not asked for is answered with a want, over frames
  of any payloads, when the session's asks have room (finding 7).
- Then H2 (`want_sends`) and H3 (`op_taken`) carry y back, as in the
  pilot.
-/
import engine.world.Pilot
import ops.sync.OfferLaws
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq


theorem joined_conns {F : Type} {Q : Plain F} {E : Q.Run} {i j : Fin Q.n} {cid : Id} {k : Nat}
    (hJ : Joined E i j cid k ∨ Joined E j i cid k) (k' : Nat) (hk : k ≤ k') :
    (∃ c, ((E.world k').node i).conn? cid = some c) ∧ (∃ c, ((E.world k').node j).conn? cid = some c) := by
  rcases hJ with hJ | hJ
  · obtain ⟨⟨c, hc, -⟩, ⟨c', hc', -⟩, -⟩ := hJ k' hk
    exact ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
  · obtain ⟨⟨c, hc, -⟩, ⟨c', hc', -⟩, -⟩ := hJ k' hk
    exact ⟨⟨c', hc'⟩, ⟨c, hc⟩⟩

/-- **An offer delivers, proven of the running code.** The have arrives
within Δ and i wants y unless it has it (`have_wants`); the want arrives
within Δ and j sends y (`want_sends`); y arrives within Δ and i stores it
(`op_taken`). -/
theorem offer_delivers : offer_delivers_stmt := by
  intro F Q N E W B i j cid r k q qs H y hf hG hJ hgst hlive hrooms hq hsrc hdst hpeek hhave hyH hHl hy hsmall hroomy
  have wl := walk_proof F Q.fam Q.cfg
  have hok : ∀ m l, NodeOk Q.fam ((E.world m).node l) ((E.world m).box l) := fun m =>
    reach_ok Q wl noAdv _ (E.reachable m)
  have hfl : ∀ m, FlightOk Q (E.world m) := fun m => reach_flight Q noAdv _ (E.reachable m)
  have hmax := hf.ok.maxIds
  have atj : Q.setup.at? (Q.addr j) = some j := at_addr Q hf.ok j
  have ati : Q.setup.at? (Q.addr i) = some i := at_addr Q hf.ok i
  have grow : ∀ l m m', m ≤ m' → Q.Holds (E.world m) l r y → Q.Holds (E.world m') l r y := fun l m m' hle h =>
    held_on E (fun m hm => grows_all F Q noAdv _ _ l r y (E.reachable m) (E.legal m) hm) m m' hle h
  have hsentk : q.sent ≤ (E.world k).now := (hfl k q hq).1
  have horig : q.origin = Q.addr j := (hfl k q hq).2 j hsrc
  -- The have arrives at i.
  obtain ⟨k1, idx1, t1, hk1, hact1, hfl1, ht1⟩ := hf.net.timely k q j i hq hsrc (by rw [hdst]; exact ati) hG hgst
    (hlive.mono (Nat.le_refl _) (by omega))
  have hle1 : (E.world k1).now ≤ t1 := by have := E.legal k1; rw [hact1] at this; exact this.2
  have hk1now := Exec.now_mono E hk1
  have e1 : E.world (k1 + 1) = (E.world k1).step Q.setup (.deliver idx1 t1) := by rw [← hact1]; rfl
  obtain ⟨n1, b1, now1, sent1⟩ := deliver_at Q (E.world k1) idx1 t1 q i hfl1 (by rw [hdst]; exact ati)
  obtain ⟨⟨c1, hc1⟩, -⟩ := joined_conns hJ k1 hk1
  have hq1 : q ∈ (E.world k1).flight := List.mem_of_getElem? hfl1
  obtain ⟨ha1, hroom1⟩ := hroomy k1 c1 hk1 hq1 hc1
  rw [show frameAsks q.bytes = qs.flatMap asksOf by simp [frameAsks, hpeek]] at hroom1
  rcases have_wants Q.fam Q.cfg (Q.rooms i) wl _ _ (hok k1 i) q.origin q.bytes t1 cid qs hpeek c1 hc1 r
      (fun h' => (hrooms h').1) H y hhave hyH ha1 hmax hHl hroom1 with hn | ⟨Wn, g, hxW, hWl, hWg, hsend⟩
  · refine ⟨k1 + 1, by omega, by rw [e1, now1]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k1 + 1)) j i r y (grow j k (k1 + 1) (by omega) hy)
    rw [e1, b1]; exact hn
  · -- The want goes back to j.
    obtain ⟨s1, hq'⟩ := sent1 _ _ hsend
    rw [← e1, horig] at hq'
    obtain ⟨k2, idx2, t2, hk2, hact2, hfl2, ht2⟩ := hf.net.timely (k1 + 1) _ i j hq' rfl atj (hf.symm j i hG)
      (show N.gst ≤ t1 by omega)
      ((hlive.mono (show q.sent ≤ t1 by omega) (show t1 + N.Δ ≤ q.sent + 3 * N.Δ by omega)).symm)
    simp only at ht2
    have hnow1 : (E.world (k1 + 1)).now = t1 := by rw [e1, now1]
    have hk2now := Exec.now_mono E hk2
    have hle2 : (E.world k2).now ≤ t2 := by have := E.legal k2; rw [hact2] at this; exact this.2
    have e2 : E.world (k2 + 1) = (E.world k2).step Q.setup (.deliver idx2 t2) := by rw [← hact2]; rfl
    obtain ⟨n2, b2, now2, sent2⟩ := deliver_at Q (E.world k2) idx2 t2 _ j hfl2 atj
    obtain ⟨-, ⟨c2, hc2⟩⟩ := joined_conns hJ k2 (by omega)
    obtain ⟨o, ho, hor⟩ := grow j k k2 (by omega) hy
    have hsm2 : Small Q.cfg B (((E.world k2).node j).onFrame (psync Q.fam Q.cfg (Q.rooms j)) (Q.addr i)
        (plainFrame cid g) t2 |>.run ((E.world k2).box j)).2 := by
      have := hsmall (k2 + 1); rw [e2, b2] at this; exact this
    obtain ⟨g', hog, hsend'⟩ := want_sends Q.fam Q.cfg (Q.rooms j) wl _ _ (hok k2 j) (Q.addr i) _ t2 cid g
      (peek_plainFrame cid g) c2 hc2 r (fun h' => (hrooms h').2) Wn y o hWg hWl hxW ho hor B hsm2
    -- y goes to i.
    obtain ⟨s2, hq''⟩ := sent2 _ _ hsend'
    rw [← e2] at hq''
    obtain ⟨k3, idx3, t3, hk3, hact3, hfl3, ht3⟩ := hf.net.timely (k2 + 1) _ j i hq'' rfl ati hG
      (show N.gst ≤ t2 by omega)
      (hlive.mono (show q.sent ≤ t2 by omega) (show t2 + N.Δ ≤ q.sent + 3 * N.Δ by omega))
    simp only at ht3
    have hnow2 : (E.world (k2 + 1)).now = t2 := by rw [e2, now2]
    have hk3now := Exec.now_mono E hk3
    have e3 : E.world (k3 + 1) = (E.world k3).step Q.setup (.deliver idx3 t3) := by rw [← hact3]; rfl
    obtain ⟨-, b3, now3, -⟩ := deliver_at Q (E.world k3) idx3 t3 _ i hfl3 ati
    obtain ⟨⟨c3, hc3⟩, -⟩ := joined_conns hJ k3 (by omega)
    have hor' : Q.fam.room o = some r := hor
    have hshared : Q.fam.shared o = true := by simp [Family.shared, hor']
    have hstored := op_taken Q.fam Q.cfg (Q.rooms i) wl _ _ (hok k3 i) (Q.addr j) _ t3 cid g'
      (peek_plainFrame cid g') c3 hc3 r (fun h' => (hrooms h').1) o hog (hf.ok.wire o hshared) hor
    have hid : o.id = y := (hok k2 j).ids y o ho
    refine ⟨k3 + 1, by omega, by rw [e3, now3]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k3 + 1)) j i r y (grow j k (k3 + 1) (by omega) hy)
    rw [e3, b3, ← hid]; exact hstored

/-! ## The index law, two ways -/

/-- **holmes-a3's cache law gives this world's.** NodeLaws' `Cached` says
a node's index is, structurally, the index booting from the store's
stored ops computes; with the engine's `Inv` it names exactly the stored
ops of each room (`cached_items`), which is `IxExact`. The n-node world
keeps `IxExact` itself (in `NodeOk`), because a restart here boots from
the store's log, whose order differs from `stored`'s, so the index is
equal as a set of items per room but not as a structure. -/
theorem cached_exact (fam : Family F) (n : Node) (h : Held F) (hi : Inv fam h.db) (hc : Cached fam n h.db) :
    IxExact fam n.ix h := by
  intro r x
  constructor
  · rintro ⟨it, hit, e⟩
    obtain ⟨o, ho, hr, _⟩ := (cached_items fam hi hc r it).1 hit
    exact ⟨o, e ▸ ho, hr⟩
  · rintro ⟨o, ho, hr⟩
    exact ⟨(keyOf fam o, x), (cached_items fam hi hc r _).2 ⟨o, ho, hr, rfl⟩, rfl⟩

end Engine.World
