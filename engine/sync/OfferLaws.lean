/-
What a connection offers, proven of `Conn`'s code run on held data
(`HeldM`), as the node runs it.

- **`have_shown`: every offered id names a stored op in one of the
  peer's rooms.** Each step a connection takes (a frame's payload, the
  clock, ops just stored) sends sync messages and stored ops only, and
  every id a message offers (a have's, or an id claim's in a round) is a
  stored op of one of the connection's rooms, so shared (`Discloses`).
- It rests on the cache law (`Cached`, engine/wire/NodeLaws.lean): the
  rounds answer from the node's room index as it is at that instant
  (no connection keeps a copy of a room), and that is the index of the
  ops stored (`cached_shown`).
- Each step reads only (`Keeps`): it changes no table.
- **`hold_reply_local`: a peer's haves reveal nothing outside its
  rooms.** A have names its room; one for a room the peer may not see is
  ignored, and the reply reads only this node's ops of that room, so two
  stores that hold the same ops of the connection's rooms answer it
  alike. With the cache law, that is the room's index (`heldIn_index`).
-/
import engine.sync.ServeLaws
import engine.sync.RoundLaws

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
    (now : Nat) :
    (c.start cfg ix now).conn.rooms = c.rooms ∧
      ∀ o ∈ (c.start cfg ix now).send, Discloses fam s c o := by
  unfold Conn.start
  split
  · exact ⟨rfl, by simp⟩
  · dsimp only
    split
    · exact ⟨rfl, by simp⟩
    refine ⟨rfl, ?_⟩
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨r, hr', rfl⟩ := ho
    refine Or.inl ⟨_, rfl, fun i hi => ?_⟩
    simp only [Msg.offers, List.mem_flatMap, List.mem_map, Index.opening_fun] at hi
    obtain ⟨cl, ⟨q, _, rfl⟩, hi⟩ := hi
    obtain ⟨a, ha, rfl⟩ := opening_offers i hi
    exact shown_item fam hx (List.mem_filter.mp hr').1 ha

/-- The responder's asks name rooms and offer no id. -/
theorem ask_keeps {s : DB F} (c : Conn) (now : Nat) :
    (c.ask now).conn.rooms = c.rooms ∧ ∀ o ∈ (c.ask now).send, Discloses fam s c o := by
  unfold Conn.ask
  split
  · exact ⟨rfl, by simp⟩
  · dsimp only
    split
    · exact ⟨rfl, by simp⟩
    refine ⟨rfl, ?_⟩
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨r, _, rfl⟩ := ho
    exact Or.inl ⟨_, rfl, by simp [Msg.offers]⟩

theorem onRbsr_keeps (cfg : Config) {ix : Index} {s : DB F} (hx : IxShown fam ix s) {c : Conn}
    (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (c.onRbsr cfg ix r k cs now).conn.rooms = c.rooms ∧
      ∀ o ∈ (c.onRbsr cfg ix r k cs now).send, Discloses fam s c o := by
  unfold Conn.onRbsr
  by_cases h1 : (!has c.rooms r) = true
  · rw [ite_eq_left h1]
    refine ⟨rfl, ?_⟩
    intro o ho
    obtain rfl := List.mem_singleton.mp ho
    exact Or.inl ⟨_, rfl, by simp [Msg.offers]⟩
  rw [ite_eq_right h1]
  by_cases stale : c.oldRound r k = true
  · rw [ite_eq_left stale]
    exact ⟨rfl, by simp⟩
  rw [ite_eq_right stale]
  have hr : r ∈ c.rooms := by
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h1; exact (Engine.has_iff _ _).1 h1
  dsimp only
  by_cases h2 : cs.isEmpty = true
  · rw [ite_eq_left h2]; exact ⟨rfl, by simp⟩
  rw [ite_eq_right h2, Index.answer_fun]
  generalize hos : cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (ix.items r)) = outs
  have hout : ∀ o ∈ outs, ∀ i ∈ o.offers, Shown fam s c i := by
    rw [← hos]
    intro o ho i hi
    obtain ⟨cl, _, ho⟩ := List.mem_flatMap.1 ho
    obtain ⟨a, ha, rfl⟩ := answer_offers ho i hi
    exact shown_item fam hx hr ha
  refine ⟨?_, ?_⟩
  · split <;> rfl
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

/-- What a walk returns, run at h from c: h unchanged, c's rooms, and
offers of shown ids only. -/
def WalkOk (h : Held F) (c : Conn) (r : (Conn × List (Id × Id)) × Held F) : Prop :=
  r.2 = h ∧ r.1.1.rooms = c.rooms ∧ ∀ p ∈ r.1.2, Shown fam h.db c p.2

theorem walkN_keeps (cfg : Config) (h : Held F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    (∀ p ∈ offer, Shown fam h.db c p.2) → WalkOk fam h c ((c.walkN fam cfg offer k : HeldM F _) h) := by
  intro k
  induction k with
  | zero => intro c offer ho; exact ⟨rfl, rfl, fun i hi => ho i (List.mem_reverse.1 hi)⟩
  | succ k ih =>
    intro c offer ho
    have leaf : ∀ (c' : Conn) (offer' : List (Id × Id)), c'.rooms = c.rooms →
        (∀ p ∈ offer', Shown fam h.db c p.2) → WalkOk fam h c ((c'.walkN fam cfg offer' k : HeldM F _) h) := by
      intro c' offer' e1 ho'
      obtain ⟨a, b, f⟩ := ih c' offer' fun p hp => shown_rooms fam e1.symm (ho' p hp)
      exact ⟨a, b.trans e1, fun p hp => shown_rooms fam e1 (f p hp)⟩
    rw [Conn.walkN]
    cases hf : c.frontier with
    | nil => exact ⟨rfl, rfl, fun i hi => ho i (List.mem_reverse.1 hi)⟩
    | cons x rest =>
      dsimp only
      split
      · exact leaf _ _ rfl ho
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases hx : h.db.ops x with
        | none => exact leaf _ _ rfl ho
        | some o =>
          dsimp only
          split
          · next hs =>
            split
            · apply leaf
              · rfl
              intro p hp
              rcases List.mem_cons.1 hp with rfl | hp
              · exact ⟨o, hx, hs⟩
              · exact ho p hp
            · exact leaf _ _ rfl ho
          · exact leaf _ _ rfl ho

theorem walk_keeps (cfg : Config) (h : Held F) (c : Conn) : WalkOk fam h c ((c.walk fam cfg : HeldM F _) h) :=
  walkN_keeps fam cfg h _ c [] (by simp)

/-- What a connection step keeps, run on held data at h from c: it reads
only, keeps c's rooms, and sends only what `Discloses` allows. -/
def Keeps (c : Conn) (h : Held F) (r : Step × Held F) : Prop :=
  r.2 = h ∧ r.1.conn.rooms = c.rooms ∧ ∀ o ∈ r.1.send, Discloses fam h.db c o

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
        if ids.length > cfg.maxIds then { conn := c } else
        let missing := ids.foldl (wantStep fam h.db c r) []
        let want := admitAsks cfg.maxKnown c.asked missing.reverse
        {
          conn := { c with
            known := (ids.filter fun i => !missing.contains i || want.contains i).foldl (remember cfg.maxKnown) c.known
            asked := want.foldl (·.insert ·) c.asked
            askTime := want.foldl (fun ts i => ts.insert i c.heard) c.askTime },
          send := chunks cfg want .want }, h) := by
  unfold Conn.onHold
  by_cases h0 : (!has c.rooms r) = true
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hm : ids.length > cfg.maxIds
    · simp [hm]
    rw [ite_eq_right hm, ite_eq_right hm, HeldM.bind_apply]
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

theorem onHold_keeps (cfg : Config) {c : Conn} (r : Id) (ids : List Id)
    (h : Held F) : Keeps fam c h ((c.onHold fam cfg r ids : HeldM F Step) h) := by
  rw [onHold_apply]
  split
  · exact ⟨rfl, rfl, by simp⟩
  · split
    · exact ⟨rfl, rfl, by simp⟩
    · exact ⟨rfl, rfl, chunks_want fam cfg _⟩

theorem onWant_keeps (cfg : Config) (ix : Index) {c : Conn} (ids : List Id) (h : Held F) :
    Keeps fam c h (c.onWant cfg ix ids, h) := by
  unfold Conn.onWant
  split <;> exact ⟨rfl, rfl, by simp⟩

theorem keeps_rooms {c d : Conn} {h : Held F} {r : Step × Held F} (e : d.rooms = c.rooms)
    (hk : Keeps fam d h r) : Keeps fam c h r :=
  let ⟨a, b, f⟩ := hk
  ⟨a, b.trans e, fun o ho => discloses_rooms fam e (f o ho)⟩

/-- One step of `filed`'s loop. -/
def fileOffer (cfg : Config) (s : DB F) (b : List (Id × Id) × Conn) (i : Id) : List (Id × Id) × Conn :=
  if (!b.2.known.contains i && !b.2.offered.contains i) = true then
    match s.ops i with
    | some o => if b.2.shows fam o = true then
        (((fam.room o).getD .empty, i) :: b.1, { b.2 with offered := remember cfg.maxKnown b.2.offered i }) else b
    | none => b
  else b

theorem filed_keeps (cfg : Config) {c : Conn} (ids : List Id) (h : Held F) :
    Keeps fam c h ((c.filed fam cfg ids : HeldM F Step) h) := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam cfg h.db)]
  · have := foldl_inv (fun b : List (Id × Id) × Conn => b.2.rooms = c.rooms ∧
        ∀ p ∈ b.1, Shown fam h.db c p.2) (fileOffer fam cfg h.db) (by
          intro b i ⟨e1, e3⟩
          unfold fileOffer
          split
          · split
            · next o hx =>
              split
              · next hsh =>
                refine ⟨e1, fun j hj => ?_⟩
                rcases List.mem_cons.1 hj with rfl | hj
                · exact ⟨o, hx, by rw [← shows_rooms fam e1]; exact hsh⟩
                · exact e3 j hj
              · exact ⟨e1, e3⟩
            · exact ⟨e1, e3⟩
          · exact ⟨e1, e3⟩) ids ([], c) ⟨rfl, by simp⟩
    generalize ids.foldl (fileOffer fam cfg h.db) ([], c) = b at this ⊢
    obtain ⟨e1, e3⟩ := this
    exact ⟨rfl, e1, holdsOf_hold fam cfg fun p hp => e3 p (List.mem_reverse.1 hp)⟩
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
    (bytes : ByteArray) (now : Nat) :
    Keeps fam c h ((c.recv fam cfg ix bytes now : HeldM F Step) h) := by
  unfold Conn.recv
  cases Op.decode bytes with
  | none => exact ⟨rfl, rfl, by simp⟩
  | some o =>
    dsimp only
    apply keeps_rooms fam (d := { c with heard := now }) rfl
    cases Msg.ofOp o with
    | none =>
      dsimp only
      split
      · exact ⟨rfl, rfl, by simp⟩
      · exact ⟨rfl, rfl, by simp⟩
    | some m =>
      cases m with
      | hello f =>
        dsimp only
        split
        · obtain ⟨a, d⟩ := start_keeps fam cfg hx (c := { c with heard := now, peerFloor := some f, session := c.session.hearHello }) now
          exact ⟨rfl, a, fun o ho => discloses_rooms fam rfl (d o ho)⟩
        · refine ⟨rfl, rfl, ?_⟩
          intro o ho
          change o ∈ [(Msg.hello c.floor).op] at ho
          simp only [List.mem_singleton] at ho
          subst o
          exact Or.inl ⟨.hello c.floor, rfl, by simp [Msg.offers]⟩
      | rbsr r k cs =>
        dsimp only
        obtain ⟨a, d⟩ := onRbsr_keeps fam cfg hx r k cs now
        exact ⟨rfl, a, d⟩
      | hold r ids =>
        dsimp only
        split
        · exact ⟨rfl, Conn.onAsk_rooms _ r, by simp⟩
        · exact onHold_keeps fam cfg r ids h
      | want ids => exact onWant_keeps fam cfg ix ids h

theorem work_keeps (cfg : Config) {ix : Index} {h : Held F} (hx : IxShown fam ix h.db) {c : Conn}
    (now : Nat) :
    Keeps fam c h ((c.work fam cfg ix now : HeldM F Step) h) := by
  unfold Conn.work
  rw [HeldM.bind_apply]
  obtain ⟨w1, w2, w4⟩ := walk_keeps fam cfg h c
  generalize (c.walk fam cfg : HeldM F (Conn × List (Id × Id))) h = r at w1 w2 w4 ⊢
  obtain ⟨⟨c', offer⟩, h'⟩ := r
  dsimp only at w1 w2 w4 ⊢
  subst h'
  let d := c'.expireAsks cfg now
  have ho : ∀ o ∈ holdsOf cfg offer, Discloses fam h.db c o := holdsOf_hold fam cfg w4
  have htail : ∀ o ∈ holdsOf cfg offer ++ chunks cfg (d.retryIds cfg now) .want,
      Discloses fam h.db c o := by
    intro o hm
    rcases List.mem_append.1 hm with hm | hm
    · exact ho o hm
    · exact chunks_want fam cfg _ o hm
  split
  · obtain ⟨a, d⟩ := start_keeps fam cfg hx (c := d) now
    refine ⟨rfl, a.trans w2, fun o hm => ?_⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact discloses_rooms fam w2 (d o hm)
    · exact htail o hm
  · obtain ⟨a, d⟩ := ask_keeps fam (s := h.db) d now
    refine ⟨rfl, a.trans w2, fun o hm => ?_⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact discloses_rooms fam w2 (d o hm)
    · exact htail o hm

theorem tick_keeps (cfg : Config) {ix : Index} {h : Held F} (hx : IxShown fam ix h.db) {c : Conn}
    (now : Nat) :
    Keeps fam c h ((c.tick fam cfg ix now : HeldM F Step) h) := by
  unfold Conn.tick
  split
  · exact ⟨rfl, rfl, by simp⟩
  · simp only [HeldM.bind_apply, HeldM.pure_apply]
    obtain ⟨a, b, e⟩ := work_keeps fam cfg hx now
    refine ⟨a, by simpa using b, ?_⟩
    unfold Step.pulse
    split
    · intro o ho
      obtain rfl := List.mem_singleton.mp ho
      exact Or.inl ⟨_, rfl, by simp [Msg.offers]⟩
    · exact e

/-- A connection opens with its hello, which offers nothing. -/
theorem open_keeps {s : DB F} (dialer : Bool) (rooms : List Id) (floor now : Nat) :
    ∀ o ∈ (Conn.open dialer rooms floor now).send, Discloses fam s (Conn.open dialer rooms floor now).conn o := by
  intro o ho
  simp only [Conn.open, List.mem_singleton] at ho
  exact Or.inl ⟨_, ho, fun i hi => by simp [Msg.offers] at hi⟩

/-- **Every offered id names a stored op in one of the peer's rooms.**
On held data whose node index is the cache of the store (`Cached`), each
step a connection takes as the node runs it (a frame's payload, the
clock, ops just stored) sends only sync messages each id of which it
offers (a have's, an id claim's) is a stored op of one of the
connection's rooms, and stored ops of those rooms. It reads only and
keeps the connection's rooms. Rounds answer from the index as it is,
so no premise about the connection's past is needed: any connection
state will do. -/
theorem have_shown (cfg : Config) {n : Node} {h : Held F} (hi : Inv fam h.db) (hc : Cached fam n h.db)
    (c : Conn) :
    (∀ bytes now, Keeps fam c h ((c.recv fam cfg n.ix bytes now : HeldM F Step) h)) ∧
    (∀ now, Keeps fam c h ((c.tick fam cfg n.ix now : HeldM F Step) h)) ∧
    (∀ ids, Keeps fam c h ((c.filed fam cfg ids : HeldM F Step) h)) :=
  ⟨recv_keeps fam cfg (cached_shown fam hi hc), tick_keeps fam cfg (cached_shown fam hi hc),
    fun ids => filed_keeps fam cfg ids h⟩

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

/-- **A write turn keeps every item of the index** (the index only grows). -/
theorem write_items (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) (r : Id) (a : Item)
    (ha : a ∈ n.ix.items r) : a ∈ (n.write x ops h).1.1.ix.items r := by
  obtain ⟨L, hL⟩ := write_ix x n ops h
  rw [hL]; exact items_foldl_mono _ ha

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
  have ha' : RoomsAgree fam ({ c with heard := now } : Conn).rooms h₁.db h₂.db := ha
  split
  · exact ⟨rfl, rfl, rfl⟩
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

/-! ## Not vacuous -/

/-- `have_shown`'s premises hold: of a node booted from an empty store,
with a connection just opened. -/
theorem have_shown_premises (floor : Nat) :
    Inv fam (({} : Held F).db) ∧ Cached fam (Node.boot fam [] floor) ({} : Held F).db :=
  ⟨inv_empty, boot_cached fam DB.empty floor⟩

/-- `hold_reply_local`'s premises hold: a have's own bytes decode to it,
for any room and ids. -/
theorem hold_reply_local_premises (r : Id) (ids : List Id) :
    Op.decode (Msg.hold r ids).op.bytes = some (Msg.hold r ids).op ∧
      Msg.ofOp (Msg.hold r ids).op = some (.hold r ids) := by
  refine ⟨Op.decode_bytes _, ?_⟩
  simp [Msg.ofOp, Msg.op, kRbsr, kHave, Codec.decode_encode]

end
end Engine.Sync
