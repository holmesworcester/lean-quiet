/-
What a connection offers, proven of `Conn`'s code run on held data
(`HeldM`), as the node runs it.

- **`have_shown`: every offered id names a stored op in one of the
  peer's rooms.** Each step a connection takes (a frame's payload, the
  clock, ops just stored) sends sync messages and stored ops only, and
  every id a message offers (a have's, or an id claim's in a round) is a
  stored op of one of the connection's rooms, so shared (`Discloses`).
- It rests on the cache law (`Cached`, engine/wire/NodeLaws.lean): the
  rounds answer from the node's room index, and that is the index of the
  ops stored (`cached_shown`). A round's snapshot, taken from the index,
  stays the index's (`SnapsIn`): every step keeps it, new rooms keep it
  (`setRooms_snaps`), and a write turn only grows the index
  (`write_snaps`), while a purge leaves it alone.
- Each step reads only (`Keeps`): it changes no table.
- **`hold_reply_local`: a peer's haves reveal nothing outside its
  rooms.** A have names its room; one for a room the peer may not see is
  ignored, and the reply reads only this node's ops of that room, so two
  stores that hold the same ops of the connection's rooms answer it
  alike. With the cache law, that is the room's index (`heldIn_index`).
-/
import engine.wire.NodeLaws

namespace Engine.Sync

/-! ## What a connection offers -/

/-- The ids a claim offers: an id claim's; a fingerprint names none. -/
def Claim.offers : Claim → List Id
  | .ids _ xs => xs
  | .fp .. => []

/-- The ids a sync message offers: a have's, and its id claims'. -/
def Msg.offers : Msg → List Id
  | .hold _ ids => ids
  | .rbsr _ _ cs => cs.flatMap Claim.offers
  | .hello _ => []
  | .want _ => []

section
variable {F : Type} (fam : Family F)

/-- Id i names a stored op connection c may show: an op of one of its
rooms, so shared. -/
def Shown (s : DB F) (c : Conn) (i : Id) : Prop := ∃ o, s.ops i = some o ∧ c.shows fam o = true

/-- What a connection may send: a sync message each id of which it
offers is `Shown`, or a stored op it may show. -/
def Discloses (s : DB F) (c : Conn) (o : Op) : Prop :=
  (∃ m : Msg, o = m.op ∧ ∀ i ∈ m.offers, Shown fam s c i) ∨
    ((∃ x, s.ops x = some o) ∧ c.shows fam o = true)

/-- Every item of every room's list names a stored op of that room. -/
def IxShown (ix : Index) (s : DB F) : Prop :=
  ∀ r a, a ∈ ix.items r → ∃ o, s.ops a.2 = some o ∧ fam.room o = some r

/-- A connection's round snapshots are of the index's rooms. -/
def SnapsIn (ix : Index) (c : Conn) : Prop := ∀ p ∈ c.snaps, ∀ a ∈ p.2, a ∈ ix.items p.1.1

theorem cached_shown {n : Node} {s : DB F} (hi : Inv fam s) (hc : Cached fam n s) : IxShown fam n.ix s :=
  fun r a ha => let ⟨o, ho, hr, _⟩ := (cached_items fam hi hc r a).1 ha; ⟨o, ho, hr⟩

theorem shows_rooms {c d : Conn} (e : c.rooms = d.rooms) (o : Op) : c.shows fam o = d.shows fam o := by
  unfold Conn.shows; rw [e]

theorem shown_rooms {s : DB F} {c d : Conn} (e : c.rooms = d.rooms) {i : Id} (h : Shown fam s c i) :
    Shown fam s d i :=
  let ⟨o, ho, hs⟩ := h; ⟨o, ho, by rw [← shows_rooms fam e]; exact hs⟩

theorem discloses_rooms {s : DB F} {c d : Conn} (e : c.rooms = d.rooms) {o : Op}
    (h : Discloses fam s c o) : Discloses fam s d o := by
  rcases h with ⟨m, rfl, hm⟩ | ⟨hx, hs⟩
  · exact Or.inl ⟨m, rfl, fun i hi => shown_rooms fam e (hm i hi)⟩
  · exact Or.inr ⟨hx, by rw [← shows_rooms fam e]; exact hs⟩

/-- An item of room r, in one of c's rooms, is shown. -/
theorem shown_item {ix : Index} {s : DB F} (hx : IxShown fam ix s) {c : Conn} {r : Id} (hr : r ∈ c.rooms)
    {a : Item} (ha : a ∈ ix.items r) : Shown fam s c a.2 := by
  obtain ⟨o, ho, hor⟩ := hx r a ha
  refine ⟨o, ho, ?_⟩
  unfold Conn.shows; rw [hor]; exact (Engine.has_iff _ _).2 hr

theorem mem_pieceIds {n k : Nat} {ids l : List Id} (h : l ∈ pieceIds n k ids) : ∀ i ∈ l, i ∈ ids := by
  induction k generalizing ids with
  | zero => cases h
  | succ k ih =>
    cases ids with
    | nil => cases h
    | cons y t =>
      simp only [pieceIds, List.mem_cons] at h
      intro i hi
      rcases h with rfl | h
      · exact List.mem_of_mem_take hi
      · exact List.mem_of_mem_drop (ih h i hi)

theorem chunks_hold (cfg : Config) {s : DB F} {c : Conn} {ids : List Id} (h : ∀ i ∈ ids, Shown fam s c i)
    (r : Id) : ∀ o ∈ chunks cfg ids (.hold r), Discloses fam s c o := by
  intro o ho
  simp only [chunks, List.mem_map] at ho
  obtain ⟨l, hl, rfl⟩ := ho
  exact Or.inl ⟨.hold r l, rfl, fun i hi => h i (mem_pieceIds hl i hi)⟩

theorem holdsOf_hold (cfg : Config) {s : DB F} {c : Conn} {offer : List (Id × Id)}
    (h : ∀ p ∈ offer, Shown fam s c p.2) : ∀ o ∈ holdsOf cfg offer, Discloses fam s c o := by
  intro o ho
  simp only [holdsOf, List.mem_flatMap] at ho
  obtain ⟨r, _, ho⟩ := ho
  refine chunks_hold fam cfg (fun i hi => ?_) r o ho
  obtain ⟨p, hp, e⟩ := List.mem_filterMap.1 hi
  split at e
  · cases e; exact h p hp
  · cases e

theorem chunks_want (cfg : Config) {s : DB F} {c : Conn} (ids : List Id) :
    ∀ o ∈ chunks cfg ids .want, Discloses fam s c o := by
  intro o ho
  simp only [chunks, List.mem_map] at ho
  obtain ⟨l, _, rfl⟩ := ho
  exact Or.inl ⟨.want l, rfl, fun i hi => by simp [Msg.offers] at hi⟩

/-- The ids an answer offers: an id claim's, and a hold's. -/
def Out.offers : Out → List Id
  | .claim c => c.offers
  | .hold xs => xs
  | .want _ => []

theorem answer_offers {key : Item → Key} {P : Params} {mine : List Item} {cl : Claim} {o : Out}
    (ho : o ∈ answer key Prod.snd sha256 P mine cl) : ∀ i ∈ o.offers, ∃ a ∈ mine, a.2 = i := by
  intro i hi
  cases cl with
  | fp r n l =>
    simp only [answer] at ho
    split at ho
    · cases ho
    · split at ho
      · simp only [List.mem_singleton] at ho; subst ho
        simp only [Out.offers, Claim.offers, List.mem_map] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        exact ⟨a, (mem_within.1 ha).1, rfl⟩
      · simp only [List.mem_map] at ho
        obtain ⟨q, _, rfl⟩ := ho
        simp [Out.offers, Claim.offers] at hi
  | ids r xs =>
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Out.offers, List.mem_map, List.mem_filter] at hi
      obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hi
      exact ⟨a, (mem_within.1 ha).1, rfl⟩
    · simp [Out.offers] at hi

theorem opening_offers {key : Item → Key} {P : Params} {mine : List Item} {r : Range} :
    ∀ i ∈ (opening key Prod.snd sha256 P mine r).offers, ∃ a ∈ mine, a.2 = i := by
  intro i hi
  unfold opening at hi
  dsimp only at hi
  split at hi
  · simp only [Claim.offers, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    exact ⟨a, (mem_within.1 ha).1, rfl⟩
  · simp [Claim.offers] at hi

theorem start_keeps (cfg : Config) {ix : Index} {s : DB F} (hx : IxShown fam ix s) {c : Conn}
    (hs : SnapsIn ix c) (now : Nat) :
    (c.start cfg ix now).conn.rooms = c.rooms ∧ SnapsIn ix (c.start cfg ix now).conn ∧
      ∀ o ∈ (c.start cfg ix now).send, Discloses fam s c o := by
  unfold Conn.start
  split
  · exact ⟨rfl, hs, by simp⟩
  · dsimp only
    refine ⟨rfl, ?_, ?_⟩
    · intro p hp a ha
      simp only [List.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      exact ha
    · intro o ho
      simp only [List.mem_map] at ho
      obtain ⟨⟨⟨r, k⟩, items⟩, hp, rfl⟩ := ho
      obtain ⟨r', hr', e⟩ := hp
      simp only [Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      refine Or.inl ⟨_, rfl, fun i hi => ?_⟩
      simp only [Msg.offers, List.mem_flatMap, List.mem_map] at hi
      obtain ⟨cl, ⟨q, _, rfl⟩, hi⟩ := hi
      obtain ⟨a, ha, rfl⟩ := opening_offers i hi
      exact shown_item fam hx hr' ha

theorem onRbsr_keeps (cfg : Config) {ix : Index} {s : DB F} (hx : IxShown fam ix s) {c : Conn}
    (hs : SnapsIn ix c) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (c.onRbsr cfg ix r k cs now).conn.rooms = c.rooms ∧ SnapsIn ix (c.onRbsr cfg ix r k cs now).conn ∧
      ∀ o ∈ (c.onRbsr cfg ix r k cs now).send, Discloses fam s c o := by
  unfold Conn.onRbsr
  by_cases h1 : (!has c.rooms r) = true
  · rw [ite_eq_left h1]; exact ⟨rfl, hs, by simp⟩
  rw [ite_eq_right h1]
  have hr : r ∈ c.rooms := by
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h1; exact (Engine.has_iff _ _).1 h1
  dsimp only
  have hoth : ∀ p ∈ c.snaps.filter (fun p => !Decidable.decide (p.1.1 = r)), ∀ a ∈ p.2, a ∈ ix.items p.1.1 :=
    fun p hp => hs p (List.mem_filter.1 hp).1
  by_cases h2 : cs.isEmpty = true
  · rw [ite_eq_left h2]; exact ⟨rfl, hoth, by simp⟩
  rw [ite_eq_right h2]
  have hsn : ∀ a ∈ c.snap ix r k, a ∈ ix.items r := by
    unfold Conn.snap
    split
    · rename_i p q hp
      have hpk := List.find?_some hp
      simp only [decide_eq_true_eq] at hpk
      intro a ha
      have := hs _ (List.mem_of_find?_eq_some hp) a ha
      rw [hpk] at this; exact this
    · exact fun a ha => ha
  generalize c.snap ix r k = snap at hsn ⊢
  generalize hos : cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params snap) = outs
  have hout : ∀ o ∈ outs, ∀ i ∈ o.offers, Shown fam s c i := by
    rw [← hos]
    intro o ho i hi
    obtain ⟨cl, _, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨a, ha, rfl⟩ := answer_offers ho i hi
    exact shown_item fam hx hr (hsn a ha)
  refine ⟨?_, ?_, ?_⟩
  · split <;> rfl
  · split
    · exact hoth
    · intro p hp a ha
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hsn a ha
      · exact hoth p hp a ha
  · intro o hm
    rcases List.mem_cons.1 hm with rfl | hm
    · refine Or.inl ⟨_, rfl, fun i hi => ?_⟩
      simp only [Msg.offers, List.mem_flatMap, List.mem_filterMap] at hi
      obtain ⟨cl, ⟨out, hout', e⟩, hi⟩ := hi
      cases out with
      | claim x =>
        simp only [Option.some.injEq] at e; subst e
        exact hout _ hout' i hi
      | hold => cases e
      | want => cases e
    · rcases List.mem_append.1 hm with hm | hm
      · refine chunks_hold fam cfg (fun i hi => ?_) r o hm
        simp only [List.mem_flatMap] at hi
        obtain ⟨out, hout', hi⟩ := hi
        cases out with
        | hold xs => exact hout _ hout' i hi
        | claim => cases hi
        | want => cases hi
      · exact chunks_want fam cfg _ o hm

/-- What a walk returns, run at h from c: h unchanged, c's rooms and
snapshots, and offers of shown ids only. -/
def WalkOk (h : Held F) (c : Conn) (r : (Conn × List (Id × Id)) × Held F) : Prop :=
  r.2 = h ∧ r.1.1.rooms = c.rooms ∧ r.1.1.snaps = c.snaps ∧ ∀ p ∈ r.1.2, Shown fam h.db c p.2

theorem walkN_keeps (h : Held F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    (∀ p ∈ offer, Shown fam h.db c p.2) → WalkOk fam h c ((c.walkN fam offer k : HeldM F _) h) := by
  intro k
  induction k with
  | zero => intro c offer ho; exact ⟨rfl, rfl, rfl, fun i hi => ho i (List.mem_reverse.1 hi)⟩
  | succ k ih =>
    intro c offer ho
    have leaf : ∀ (c' : Conn) (offer' : List (Id × Id)), c'.rooms = c.rooms → c'.snaps = c.snaps →
        (∀ p ∈ offer', Shown fam h.db c p.2) → WalkOk fam h c ((c'.walkN fam offer' k : HeldM F _) h) := by
      intro c' offer' e1 e2 ho'
      obtain ⟨a, b, d, f⟩ := ih c' offer' fun p hp => shown_rooms fam e1.symm (ho' p hp)
      exact ⟨a, b.trans e1, d.trans e2, fun p hp => shown_rooms fam e1 (f p hp)⟩
    rw [Conn.walkN]
    cases hf : c.frontier with
    | nil => exact ⟨rfl, rfl, rfl, fun i hi => ho i (List.mem_reverse.1 hi)⟩
    | cons x rest =>
      dsimp only
      have esh : ∀ o, Conn.shows fam { c with frontier := rest } o = c.shows fam o := fun _ => rfl
      by_cases h1 : (!c.closed.contains x) = true
      · rw [ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
        dsimp only
        cases hx : h.db.ops x with
        | none => exact leaf _ _ rfl rfl ho
        | some o =>
          dsimp only
          rw [esh]
          by_cases hsh : c.shows fam o = true
          · have hxs : Shown fam h.db c x := ⟨o, hx, hsh⟩
            rw [ite_eq_left hsh]
            by_cases h2 : (!c.known.contains x && !c.offered.contains x) = true
            · rw [ite_eq_left h2, HeldM.bind_apply, HeldM.getStatus_apply]
              have ho' : ∀ p ∈ ((fam.room o).getD .empty, x) :: offer, Shown fam h.db c p.2 := fun p hp => by
                rcases List.mem_cons.1 hp with rfl | hp
                · exact hxs
                · exact ho p hp
              rcases h.db.status x with _ | _ | _
              · exact leaf _ _ rfl rfl ho'
              · exact leaf _ _ rfl rfl ho'
              · exact leaf _ _ rfl rfl ho'
            · rw [ite_eq_right h2, HeldM.bind_apply, HeldM.getStatus_apply]
              rcases h.db.status x with _ | _ | _
              · exact leaf _ _ rfl rfl ho
              · exact leaf _ _ rfl rfl ho
              · exact leaf _ _ rfl rfl ho
          · rw [ite_eq_right hsh]; exact leaf _ _ rfl rfl ho
      · rw [ite_eq_right h1]; exact leaf _ _ rfl rfl ho

theorem walk_keeps (cfg : Config) (h : Held F) (c : Conn) : WalkOk fam h c ((c.walk fam cfg : HeldM F _) h) :=
  walkN_keeps fam h _ c [] (by simp)

/-- What a connection step keeps, run on held data at h from c: it reads
only, keeps c's rooms and its snapshots of the index, and sends only
what `Discloses` allows. -/
def Keeps (ix : Index) (c : Conn) (h : Held F) (r : Step × Held F) : Prop :=
  r.2 = h ∧ r.1.conn.rooms = c.rooms ∧ SnapsIn ix r.1.conn ∧ ∀ o ∈ r.1.send, Discloses fam h.db c o

theorem finish_conn (s : Step) : (Conn.finish s).conn.rooms = s.conn.rooms ∧
    (Conn.finish s).conn.snaps = s.conn.snaps ∧ (Conn.finish s).send = s.send := by
  by_cases hA : s.conn.asked.isEmpty = true
  · simp [Conn.finish, Conn.report, hA]
  · simp [Conn.finish, Conn.report, hA]

theorem keeps_finish {ix : Index} {c : Conn} {h : Held F} {s : Step}
    (hk : Keeps fam ix c h (s, h)) : Keeps fam ix c h (Conn.finish s, h) := by
  obtain ⟨_, h1, h2, h3⟩ := hk
  obtain ⟨e1, e2, e3⟩ := finish_conn s
  refine ⟨rfl, e1.trans h1, fun p hp => h2 p (e2 ▸ hp), fun o ho => h3 o (e3 ▸ ho)⟩

theorem foldl_inv {α β} (P : β → Prop) (g : β → α → β) (hg : ∀ b a, P b → P (g b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl g b)
  | [], _, hb => hb
  | a :: t, b, hb => foldl_inv P g hg t (g b a) (hg b a hb)

theorem filterMapM_getOp (h : Held F) (l : List Id) (bs : List Op) :
    (List.filterMapM.loop (fun i => (Store.getOp i : HeldM F (Option Op))) l bs) h =
      (bs.reverse ++ l.filterMap h.db.ops, h) := by
  induction l generalizing bs with
  | nil => simp [List.filterMapM.loop]
  | cons i t ih =>
    rw [List.filterMapM.loop, HeldM.bind_apply, HeldM.getOp_apply]
    cases hi : h.db.ops i with
    | none => dsimp only; rw [ih, List.filterMap_cons, hi]
    | some o => dsimp only; rw [ih, List.filterMap_cons, hi]; simp

/-- Whether store s holds op i in room r: what `holdsIn` reads. -/
def heldIn (s : DB F) (r i : Id) : Bool :=
  match s.ops i with
  | some o => Decidable.decide (fam.room o = some r)
  | none => false

theorem holdsIn_apply (r i : Id) (h : Held F) :
    (holdsIn fam r i : HeldM F Bool) h = (heldIn fam h.db r i, h) := by
  unfold holdsIn heldIn
  rw [HeldM.bind_apply, HeldM.getOp_apply]
  cases h.db.ops i <;> rfl

/-- One step of `onHold`'s loop. -/
def wantStep (s : DB F) (c : Conn) (r : Id) (want : List Id) (i : Id) : List Id :=
  if (!c.asked.contains i) = true then (if (!heldIn fam s r i) = true then i :: want else want) else want

/-- What `onHold` does, as data. -/
theorem onHold_apply (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    (c.onHold fam cfg r ids : HeldM F Step) h =
      (if (!has c.rooms r) = true then { conn := c } else
        { conn := { c with
            known := ids.foldl (·.insert ·) c.known
            asked := (ids.foldl (wantStep fam h.db c r) []).foldl (·.insert ·) c.asked }
          send := chunks cfg (ids.foldl (wantStep fam h.db c r) []).reverse .want }, h) := by
  unfold Conn.onHold
  by_cases h0 : (!has c.rooms r) = true
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0, HeldM.bind_apply]
    rw [HeldM.forIn_reads (g := wantStep fam h.db c r)]
    · rfl
    · intro a b
      unfold wantStep
      by_cases h1 : (!c.asked.contains a) = true
      · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, holdsIn_apply]
        by_cases h2 : (!heldIn fam h.db r a) = true
        · rw [ite_eq_left h2, ite_eq_left h2]; rfl
        · rw [ite_eq_right h2, ite_eq_right h2]; rfl
      · rw [ite_eq_right h1, ite_eq_right h1]; rfl

theorem onHold_keeps (cfg : Config) {ix : Index} {c : Conn} (hs : SnapsIn ix c) (r : Id) (ids : List Id)
    (h : Held F) : Keeps fam ix c h ((c.onHold fam cfg r ids : HeldM F Step) h) := by
  rw [onHold_apply]
  split
  · exact ⟨rfl, rfl, hs, by simp⟩
  · exact ⟨rfl, rfl, hs, chunks_want fam cfg _⟩

theorem onWant_keeps (cfg : Config) {ix : Index} {c : Conn} (hs : SnapsIn ix c) (ids : List Id) (h : Held F) :
    Keeps fam ix c h ((c.onWant fam cfg ids : HeldM F Step) h) := by
  unfold Conn.onWant
  split
  · exact ⟨rfl, rfl, hs, by simp⟩
  · rw [HeldM.bind_apply]
    have e : (List.filterMapM (fun i => (Store.getOp i : HeldM F (Option Op))) ids) h = (ids.filterMap h.db.ops, h) := by
      unfold List.filterMapM
      rw [filterMapM_getOp]; simp
    rw [e]
    dsimp only
    rw [HeldM.bind_apply]
    have hsent : ∀ o ∈ (ids.filterMap h.db.ops).filter (c.shows fam), Discloses fam h.db c o := by
      intro o ho
      obtain ⟨ho, hsh⟩ := List.mem_filter.1 ho
      obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 ho
      exact Or.inr ⟨⟨x, hx⟩, hsh⟩
    generalize (ids.filterMap h.db.ops).filter (c.shows fam) = sent at hsent ⊢
    obtain ⟨w1, w2, w3, w4⟩ := walk_keeps fam cfg h { c with
      known := sent.foldl (fun k o => k.insert o.id) c.known
      offered := sent.foldl (fun k o => k.insert o.id) c.offered
      frontier := c.frontier ++ sent.flatMap Op.reqs }
    generalize (Conn.walk fam cfg { c with
      known := sent.foldl (fun k o => k.insert o.id) c.known
      offered := sent.foldl (fun k o => k.insert o.id) c.offered
      frontier := c.frontier ++ sent.flatMap Op.reqs } : HeldM F (Conn × List (Id × Id))) h = r at w1 w2 w3 w4 ⊢
    obtain ⟨⟨c', offer⟩, h'⟩ := r
    dsimp only at w1 w2 w3 w4 ⊢
    subst w1
    refine ⟨rfl, w2, fun p hp => hs p (w3 ▸ hp), fun o ho => ?_⟩
    rcases List.mem_append.1 ho with ho | ho
    · exact hsent o ho
    · exact holdsOf_hold fam cfg (fun p hp => shown_rooms fam rfl (w4 p hp)) o ho

theorem keeps_rooms {ix : Index} {c d : Conn} {h : Held F} {r : Step × Held F} (e : d.rooms = c.rooms)
    (hk : Keeps fam ix d h r) : Keeps fam ix c h r :=
  let ⟨a, b, d', f⟩ := hk
  ⟨a, b.trans e, d', fun o ho => discloses_rooms fam e (f o ho)⟩

/-- One step of `filed`'s loop. -/
def fileOffer (s : DB F) (b : List (Id × Id) × Conn) (i : Id) : List (Id × Id) × Conn :=
  if (!b.2.known.contains i && !b.2.offered.contains i) = true then
    match s.ops i with
    | some o => if b.2.shows fam o = true then
        (((fam.room o).getD .empty, i) :: b.1, { b.2 with offered := b.2.offered.insert i }) else b
    | none => b
  else b

theorem filed_keeps (cfg : Config) {ix : Index} {c : Conn} (hs : SnapsIn ix c) (ids : List Id) (h : Held F) :
    Keeps fam ix c h ((c.filed fam cfg ids : HeldM F Step) h) := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam h.db)]
  · have := foldl_inv (fun b : List (Id × Id) × Conn => b.2.rooms = c.rooms ∧ b.2.snaps = c.snaps ∧
        ∀ p ∈ b.1, Shown fam h.db c p.2) (fileOffer fam h.db) (by
          intro b i ⟨e1, e2, e3⟩
          unfold fileOffer
          split
          · split
            · next o hx =>
              split
              · next hsh =>
                refine ⟨e1, e2, fun j hj => ?_⟩
                rcases List.mem_cons.1 hj with rfl | hj
                · exact ⟨o, hx, by rw [← shows_rooms fam e1]; exact hsh⟩
                · exact e3 j hj
              · exact ⟨e1, e2, e3⟩
            · exact ⟨e1, e2, e3⟩
          · exact ⟨e1, e2, e3⟩) ids ([], c) ⟨rfl, rfl, by simp⟩
    generalize ids.foldl (fileOffer fam h.db) ([], c) = b at this ⊢
    obtain ⟨e1, e2, e3⟩ := this
    apply keeps_finish
    exact ⟨rfl, e1, fun p hp => hs p (e2 ▸ hp),
      holdsOf_hold fam cfg fun p hp => e3 p (List.mem_reverse.1 hp)⟩
  · intro a b
    unfold fileOffer
    by_cases h1 : (!b.2.known.contains a && !b.2.offered.contains a) = true
    · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
      dsimp only
      cases h.db.ops a with
      | none => rfl
      | some o =>
        dsimp only
        by_cases h2 : b.2.shows fam o = true
        · rw [ite_eq_left h2, ite_eq_left h2]; rfl
        · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

theorem recv_keeps (cfg : Config) {ix : Index} {h : Held F} (hx : IxShown fam ix h.db) {c : Conn}
    (hs : SnapsIn ix c) (bytes : ByteArray) (now : Nat) :
    Keeps fam ix c h ((c.recv fam cfg ix bytes now : HeldM F Step) h) := by
  unfold Conn.recv
  cases Op.decode bytes with
  | none => exact ⟨rfl, rfl, hs, by simp⟩
  | some o =>
    dsimp only
    have hs' : SnapsIn ix { c with heard := now } := hs
    apply keeps_rooms fam (d := { c with heard := now }) rfl
    cases Msg.ofOp o with
    | none =>
      dsimp only
      split
      · exact ⟨rfl, rfl, hs', by simp⟩
      · exact keeps_finish fam ⟨rfl, rfl, hs', by simp⟩
    | some m =>
      cases m with
      | hello f =>
        dsimp only
        apply keeps_finish
        split
        · obtain ⟨a, b, d⟩ := start_keeps fam cfg hx (c := { c with heard := now, peerFloor := some f }) hs' now
          exact ⟨rfl, a, b, fun o ho => discloses_rooms fam rfl (d o ho)⟩
        · exact ⟨rfl, rfl, hs', by simp⟩
      | rbsr r k cs =>
        dsimp only
        apply keeps_finish
        obtain ⟨a, b, d⟩ := onRbsr_keeps fam cfg hx hs' r k cs now
        exact ⟨rfl, a, b, d⟩
      | hold r ids =>
        dsimp only
        rw [HeldM.bind_apply]
        obtain ⟨a, b, d, e⟩ := onHold_keeps fam cfg hs' r ids h
        rw [a]
        exact keeps_finish fam ⟨rfl, b, d, e⟩
      | want ids =>
        dsimp only
        rw [HeldM.bind_apply]
        obtain ⟨a, b, d, e⟩ := onWant_keeps fam cfg hs' ids h
        rw [a]
        exact keeps_finish fam ⟨rfl, b, d, e⟩

theorem tick_keeps (cfg : Config) {ix : Index} {h : Held F} (hx : IxShown fam ix h.db) {c : Conn}
    (hs : SnapsIn ix c) (now : Nat) :
    Keeps fam ix c h ((c.tick fam cfg ix now : HeldM F Step) h) := by
  unfold Conn.tick
  split
  · exact ⟨rfl, rfl, hs, by simp⟩
  · rw [HeldM.bind_apply]
    obtain ⟨w1, w2, w3, w4⟩ := walk_keeps fam cfg h c
    generalize (c.walk fam cfg : HeldM F (Conn × List (Id × Id))) h = r at w1 w2 w3 w4 ⊢
    obtain ⟨⟨c', offer⟩, h'⟩ := r
    dsimp only at w1 w2 w3 w4 ⊢
    subst h'
    have hs' : SnapsIn ix c' := fun p hp => hs p (w3 ▸ hp)
    have ho : ∀ o ∈ holdsOf cfg offer, Discloses fam h.db c o := holdsOf_hold fam cfg w4
    apply keeps_finish
    split
    · obtain ⟨a, b, d⟩ := start_keeps fam cfg hx hs' now
      refine ⟨rfl, a.trans w2, b, fun o hm => ?_⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact discloses_rooms fam w2 (d o hm)
      · exact ho o hm
    · exact ⟨rfl, w2, hs', fun o hm => ho o (by simpa using hm)⟩

/-- A connection opens with its hello, which offers nothing, and no
snapshot. -/
theorem open_keeps {ix : Index} {s : DB F} (dialer : Bool) (rooms : List Id) (floor now : Nat) :
    SnapsIn ix (Conn.open dialer rooms floor now).conn ∧
      ∀ o ∈ (Conn.open dialer rooms floor now).send, Discloses fam s (Conn.open dialer rooms floor now).conn o := by
  refine ⟨fun p hp => (by cases hp), fun o ho => ?_⟩
  simp only [Conn.open, List.mem_singleton] at ho
  exact Or.inl ⟨_, ho, fun i hi => by simp [Msg.offers] at hi⟩

/-- New rooms keep the snapshots of the rooms kept. -/
theorem setRooms_snaps {ix : Index} {c : Conn} (hs : SnapsIn ix c) (rooms : List Id) :
    SnapsIn ix (c.setRooms rooms) := fun p hp => hs p (List.mem_filter.1 hp).1

/-- **Every offered id names a stored op in one of the peer's rooms.**
On held data whose node index is the cache of the store (`Cached`), each
step a connection takes as the node runs it (a frame's payload, the
clock, ops just stored) sends only sync messages each id of which it
offers (a have's, an id claim's) is a stored op of one of the
connection's rooms, and stored ops of those rooms. It reads only, keeps
the connection's rooms, and keeps its round snapshots of the index, so
the next step may rely on them too. -/
theorem have_shown (cfg : Config) {n : Node} {h : Held F} (hi : Inv fam h.db) (hc : Cached fam n h.db)
    {c : Conn} (hs : SnapsIn n.ix c) :
    (∀ bytes now, Keeps fam n.ix c h ((c.recv fam cfg n.ix bytes now : HeldM F Step) h)) ∧
    (∀ now, Keeps fam n.ix c h ((c.tick fam cfg n.ix now : HeldM F Step) h)) ∧
    (∀ ids, Keeps fam n.ix c h ((c.filed fam cfg ids : HeldM F Step) h)) :=
  ⟨recv_keeps fam cfg (cached_shown fam hi hc) hs, tick_keeps fam cfg (cached_shown fam hi hc) hs,
    fun ids => filed_keeps fam cfg hs ids h⟩

theorem snaps_grow {ix : Index} {c : Conn} (hs : SnapsIn ix c) (L : List Op) :
    SnapsIn (L.foldl (Index.add fam) ix) c :=
  fun p hp a ha => items_foldl_mono fam (hs p hp a ha)

/-- A write turn only adds to the index. -/
theorem write_ix (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    ∃ L : List Op, (n.write x ops h).1.1.ix = L.foldl (Index.add x.fam) n.ix := by
  unfold Node.write
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := absentStep h.db)]
  · dsimp only
    generalize ops.foldl (absentStep h.db) [] = absent
    by_cases he : absent.isEmpty = true
    · rw [ite_eq_left he]; exact ⟨[], rfl⟩
    · rw [ite_eq_right he]
      simp only [HeldM.bind_apply]
      generalize (Turn.turn x.fam absent.reverse : HeldM F Unit) h = t
      rw [HeldM.forIn_reads (g := fileStep x.fam t.2.db)]
      · exact foldl_inv (fun b : Index × List Id => ∃ L : List Op, b.1 = L.foldl (Index.add x.fam) n.ix)
          (fileStep x.fam t.2.db) (by
            intro b o ⟨L, hL⟩
            unfold fileStep
            split
            · exact ⟨L ++ [o], by rw [List.foldl_append, ← hL]; rfl⟩
            · exact ⟨L, hL⟩) _ _ ⟨[], rfl⟩
      · intro a b
        rw [HeldM.bind_apply, HeldM.getOp_apply]
        unfold fileStep
        by_cases h1 : (t.2.db.ops a.id).isSome = true
        · rw [ite_eq_left h1, ite_eq_left h1]; rfl
        · rw [ite_eq_right h1, ite_eq_right h1]; rfl
  · intro a b
    unfold absentStep
    by_cases h1 : (!b.any fun p => p.id == a.id) = true
    · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
      by_cases h2 : (h.db.ops a.id).isNone = true
      · rw [ite_eq_left h2, ite_eq_left h2]; rfl
      · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

/-- **A connection's snapshots stay of the index across a write turn**
(the index only grows), and a purge does not touch the index. -/
theorem write_snaps (x : Sync F (HeldM F)) {n : Node} {c : Conn} (hs : SnapsIn n.ix c) (ops : List Op)
    (h : Held F) : SnapsIn (n.write x ops h).1.1.ix c := by
  obtain ⟨L, hL⟩ := write_ix x n ops h
  rw [hL]; exact snaps_grow _ hs L

/-! ## What a peer's have reveals -/

/-- Two stores hold the same ops of these rooms. -/
def RoomsAgree (rooms : List Id) (s t : DB F) : Prop :=
  ∀ x o r, r ∈ rooms → fam.room o = some r → (s.ops x = some o ↔ t.ops x = some o)

theorem heldIn_local {rooms : List Id} {s t : DB F} (ha : RoomsAgree fam rooms s t) {r : Id}
    (hr : r ∈ rooms) (i : Id) : heldIn fam s r i = heldIn fam t r i := by
  unfold heldIn
  cases hs : s.ops i with
  | none =>
    cases ht : t.ops i with
    | none => rfl
    | some p =>
      by_cases hp : fam.room p = some r
      · have := (ha i p r hr hp).2 ht; rw [hs] at this; cases this
      · simp [hp]
  | some o =>
    by_cases ho : fam.room o = some r
    · rw [(ha i o r hr ho).1 hs]
    · cases ht : t.ops i with
      | none => simp [ho]
      | some p =>
        by_cases hp : fam.room p = some r
        · have := (ha i p r hr hp).2 ht; rw [hs] at this; cases this; exact absurd hp ho
        · simp [ho, hp]

/-- A have is answered from the connection's rooms only: two stores
that hold the same ops of its rooms give the same reply. -/
theorem onHold_local (cfg : Config) (c : Conn) (r : Id) (ids : List Id) {h₁ h₂ : Held F}
    (ha : RoomsAgree fam c.rooms h₁.db h₂.db) :
    ((c.onHold fam cfg r ids : HeldM F Step) h₁).1 = ((c.onHold fam cfg r ids : HeldM F Step) h₂).1 := by
  rw [onHold_apply, onHold_apply]
  dsimp only
  by_cases h0 : (!has c.rooms r) = true
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    have hr : r ∈ c.rooms := by
      simp only [Bool.not_eq_true', Bool.not_eq_false] at h0; exact (Engine.has_iff _ _).1 h0
    have e : wantStep fam h₁.db c r = wantStep fam h₂.db c r := by
      funext w i; unfold wantStep; rw [heldIn_local fam ha hr i]
    rw [e]

/-- **A peer's haves reveal nothing outside its rooms.** Whatever bytes
of a have (for any room, naming any ids) a peer sends, the connection's
reply is the same over any two stores that hold the same ops of the
connection's rooms, and it changes neither. So a peer cannot learn
whether this node holds an op of another room, or a local op. -/
theorem hold_reply_local (cfg : Config) (ix : Index) (c : Conn) {bytes : ByteArray} (now : Nat)
    {o : Op} {r : Id} {ids : List Id} (hd : Op.decode bytes = some o) (hm : Msg.ofOp o = some (.hold r ids))
    {h₁ h₂ : Held F} (ha : RoomsAgree fam c.rooms h₁.db h₂.db) :
    ((c.recv fam cfg ix bytes now : HeldM F Step) h₁).1 = ((c.recv fam cfg ix bytes now : HeldM F Step) h₂).1 ∧
      ((c.recv fam cfg ix bytes now : HeldM F Step) h₁).2 = h₁ ∧
      ((c.recv fam cfg ix bytes now : HeldM F Step) h₂).2 = h₂ := by
  unfold Conn.recv
  rw [hd]
  dsimp only
  rw [hm]
  dsimp only
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  have ha' : RoomsAgree fam ({ c with heard := now } : Conn).rooms h₁.db h₂.db := ha
  refine ⟨?_, ?_, ?_⟩
  · rw [onHold_local fam cfg _ r ids ha']
  · rw [onHold_apply]
  · rw [onHold_apply]

/-- With the cache law, a have is answered from the room's index: this
side wants an id in room r exactly when the index's list for r lacks it. -/
theorem heldIn_index {n : Node} {s : DB F} (hi : Inv fam s) (hc : Cached fam n s) (r i : Id) :
    heldIn fam s r i = true ↔ ∃ a ∈ n.ix.items r, a.2 = i := by
  constructor
  · intro h
    unfold heldIn at h
    split at h
    · rename_i o ho
      have hr : fam.room o = some r := by simpa using h
      exact ⟨(keyOf fam o, i), (cached_items fam hi hc r _).2 ⟨o, ho, hr, rfl⟩, rfl⟩
    · cases h
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨o, ho, hr, _⟩ := (cached_items fam hi hc r a).1 ha
    unfold heldIn
    rw [ho]; simp [hr]

end
end Engine.Sync
