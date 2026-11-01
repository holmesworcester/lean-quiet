/-
What applying a connection step does to a plain node's acts and
sessions, proven of the running node: the step's own sends go out on
its session (either lane), no retries ride along (the plain node has no
catalog), the node's managed sessions and addresses stay, and the
session's asks are the step's (`apply_facts`). With `finish_sends`,
whatever a frame's steps send on a session goes out sealed to its
address.
-/
import engine.world.Hops

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## Asks and wants on a session -/

/-- The acts carry, on session cid, a want naming x (either lane). -/
def WantsOn (out : Acts) (cid x : Id) : Prop :=
  ∃ L, x ∈ L ∧ ((Route.conn cid, (Msg.want L).op.bytes) ∈ out.send ∨
    (Route.conn cid, (Msg.want L).op.bytes) ∈ out.serve)

theorem WantsOn.append_left {a : Acts} {cid x : Id} (h : WantsOn a cid x) (b : Acts) : WantsOn (a ++ b) cid x := by
  obtain ⟨L, hx, hm | hm⟩ := h
  · exact ⟨L, hx, Or.inl (List.mem_append_left _ hm)⟩
  · exact ⟨L, hx, Or.inr (List.mem_append_left _ hm)⟩

theorem WantsOn.append_right {b : Acts} {cid x : Id} (a : Acts) (h : WantsOn b cid x) : WantsOn (a ++ b) cid x := by
  obtain ⟨L, hx, hm | hm⟩ := h
  · exact ⟨L, hx, Or.inl (List.mem_append_right _ hm)⟩
  · exact ⟨L, hx, Or.inr (List.mem_append_right _ hm)⟩

/-! ## What a connection asks -/

attribute [local instance] byteArray_lawfulBEq

/-- The ids a round's claims list. -/
def claimIds (cs : List Claim) : List Id := cs.flatMap fun
  | .ids _ xs => xs
  | .fp .. => []

/-- How many ids a payload can make a connection ask: a have's ids, or
the ids a round message's claims list. -/
def asksOf (b : ByteArray) : Nat :=
  match Op.decode b with
  | some o =>
    match Msg.ofOp o with
    | some (.hold _ ids) => ids.length
    | some (.rbsr _ _ cs) => (claimIds cs).length
    | _ => 0
  | none => 0

/-- Some want among ops names x. -/
def WantIn (ops : List Op) (x : Id) : Prop := ∃ L, x ∈ L ∧ (Msg.want L).op ∈ ops

theorem foldl_insert_mem {x : Id} : ∀ (L : List Id) (A : Std.HashSet Id),
    x ∈ L.foldl (·.insert ·) A ↔ x ∈ A ∨ x ∈ L := by
  intro L
  induction L with
  | nil => intro A; simp
  | cons a t ih =>
    intro A
    rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
    constructor
    · rintro ((e | h) | h)
      · exact Or.inr (List.mem_cons.2 (Or.inl (eq_of_beq e).symm))
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rintro (h | h)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl (Or.inl (beq_self_eq_true _))
        · exact Or.inr h

theorem foldl_insert_size : ∀ (L : List Id) (A : Std.HashSet Id),
    (L.foldl (·.insert ·) A).size ≤ A.size + L.length := by
  intro L
  induction L with
  | nil => intro A; simp
  | cons a t ih =>
    intro A
    rw [List.foldl_cons]
    have := ih (A.insert a)
    have := Std.HashSet.size_insert_le (m := A) (k := a)
    simp only [List.length_cons]; omega

theorem admitAsks_length (cap : Nat) (asked : Std.HashSet Id) (ids : List Id) :
    (admitAsks cap asked ids).length ≤ ids.length := by
  unfold admitAsks
  have h1 := eraseDups_length_le (ids.filter fun i => !asked.contains i)
  have h2 := List.length_filter_le (fun i => !asked.contains i) ids
  simp only [List.length_take]; omega

theorem admitAsks_sub {cap : Nat} {asked : Std.HashSet Id} {ids : List Id} {x : Id}
    (h : x ∈ admitAsks cap asked ids) : x ∈ ids := by
  unfold admitAsks at h
  exact (List.mem_filter.1 (List.mem_eraseDups.1 (List.mem_of_mem_take h))).1

/-- With room for every id offered, an id not asked yet is admitted. -/
theorem admitAsks_mem (cap : Nat) (asked : Std.HashSet Id) (ids : List Id) {x : Id} (hx : x ∈ ids)
    (hn : x ∉ asked) (hroom : asked.size + ids.length ≤ cap) : x ∈ admitAsks cap asked ids := by
  unfold admitAsks
  have hle : ((ids.filter fun i => !asked.contains i).eraseDups).length ≤ cap - asked.size := by
    have := eraseDups_length_le (ids.filter fun i => !asked.contains i)
    have := List.length_filter_le (fun i => !asked.contains i) ids
    omega
  rw [List.take_of_length_le hle]
  refine List.mem_eraseDups.2 (List.mem_filter.2 ⟨hx, ?_⟩)
  simp [hn]

theorem chunks_want (cfg : Config) (ids : List Id) (hmax : 0 < cfg.maxIds) {x : Id} (hx : x ∈ ids) :
    WantIn (chunks cfg ids .want) x := by
  obtain ⟨l, hl, hxl⟩ := chunks_cover cfg ids .want hmax hx
  exact ⟨l, hxl, hl⟩

/-- `onHold`'s loop collects at most one id per offered id, each offered. -/
theorem wantStep_fold (fam : Family F) (db : DB F) (c : Conn) (r : Id) : ∀ (L acc : List Id),
    (L.foldl (wantStep fam db c r) acc).length ≤ acc.length + L.length ∧
      ∀ x, x ∈ L.foldl (wantStep fam db c r) acc ↔ x ∈ acc ∨ (x ∈ L ∧ x ∉ c.asked ∧ heldIn fam db r x = false) := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (wantStep fam db c r acc a)
    refine ⟨?_, fun x => ?_⟩
    · have : (wantStep fam db c r acc a).length ≤ acc.length + 1 := by
        unfold wantStep; split
        · split <;> simp
        · simp
      simp only [List.length_cons]; omega
    · rw [h2]
      unfold wantStep
      by_cases ha : (!c.asked.contains a) = true
      · by_cases hh : (!heldIn fam db r a) = true
        · simp only [ha, hh, ↓reduceIte, List.mem_cons]
          simp only [Bool.not_eq_true', Std.HashSet.contains_eq_false_iff_not_mem] at ha hh
          constructor
          · rintro ((rfl | h) | ⟨h, h', h''⟩)
            · exact Or.inr ⟨Or.inl rfl, ha, hh⟩
            · exact Or.inl h
            · exact Or.inr ⟨Or.inr h, h', h''⟩
          · rintro (h | ⟨rfl | h, h', h''⟩)
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr ⟨h, h', h''⟩
        · simp only [ha, hh, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hh
          constructor
          · rintro (h | ⟨h, h', h''⟩)
            · exact Or.inl h
            · exact Or.inr ⟨Or.inr h, h', h''⟩
          · rintro (h | ⟨rfl | h, h', h''⟩)
            · exact Or.inl h
            · rw [hh] at h''; cases h''
            · exact Or.inr ⟨h, h', h''⟩
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        simp only [Bool.not_eq_true', Bool.not_eq_false, Std.HashSet.contains_iff_mem] at ha
        constructor
        · rintro (h | ⟨h, h', h''⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, h', h''⟩
        · rintro (h | ⟨rfl | h, h', h''⟩)
          · exact Or.inl h
          · exact absurd ha h'
          · exact Or.inr ⟨h, h', h''⟩

/-- **H4 at a connection:** a have in a room the connection shows, of an
op it neither holds there nor has asked for, is answered with a want of
it, when its asks have room for the have's ids. -/
theorem hold_wants (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) {x : Id}
    (hr : r ∈ c.rooms) (hl : ids.length ≤ cfg.maxIds) (hx : x ∈ ids) (hq : x ∉ c.asked)
    (hh : heldIn fam h.db r x = false) (hroom : c.asked.size + ids.length ≤ cfg.maxKnown) :
    WantIn ((c.onHold fam cfg r ids : HeldM F Step) h).1.send x := by
  rw [onHold_apply]
  have hr' : (!has c.rooms r) = false := by simp [has_of_mem hr]
  have hl' : ¬ ids.length > cfg.maxIds := by omega
  simp only [hr', Bool.false_eq_true, ↓reduceIte, hl']
  obtain ⟨hlen, hmem⟩ := wantStep_fold fam h.db c r ids []
  have hm : x ∈ (ids.foldl (wantStep fam h.db c r) []).reverse :=
    List.mem_reverse.2 ((hmem x).2 (Or.inr ⟨hx, hq, hh⟩))
  have hmax : 0 < cfg.maxIds := Nat.lt_of_lt_of_le (List.length_pos_of_mem hx) hl
  exact chunks_want cfg _ hmax (admitAsks_mem _ _ _ hm hq (by simp at hlen ⊢; omega))

/-! ## The stream keeps a connection's asks -/

theorem filedStep_asked (cfg : Config) (fam : Family F) (db : DB F) (st : List (Id × Id) × Conn) (i : Id) :
    (filedStep cfg fam db st i).2.asked = st.2.asked := by
  unfold filedStep; split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem filed_asked (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.asked = c.asked := by
  simp only [Conn.filed, HeldM.run_bind]
  rw [forIn_yield ids _ (fun i st => filedStep cfg fam h.db st i) h (fun j _ st => by
    simp only [filedStep]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      cases h.db.ops j with
      | none => rfl
      | some p => by_cases hs : st.2.shows fam p = true <;> simp [hs]
    · rfl)]
  simp only [HeldM.run_pure]
  have : ∀ (L : List Id) (st : List (Id × Id) × Conn),
      (L.foldl (fun st i => filedStep cfg fam h.db st i) st).2.asked = st.2.asked := by
    intro L
    induction L with
    | nil => intro st; rfl
    | cons a t ih => intro st; rw [List.foldl_cons, ih, filedStep_asked]
  exact this ids ([], c)

section
variable (S : Engine.Sync.Setup F) (s : Who)

/-- The fanout steps each session in place: its new connection is the
stream's step on the old one, and its acts carry no retries. -/
theorem fanout_facts (n : Node) (ids : List Id) (h : Held F) :
    ((n.fanout (S.sync s) ids).run h).1.1.conns = n.conns.map (fun p =>
      (p.1, ((({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn).filed S.fam S.cfg ids :
        HeldM F Step).run h).1.conn)) ∧
      ((n.fanout (S.sync s) ids).run h).1.2.retry = [] ∧
      ((n.fanout (S.sync s) ids).run h).1.1.managed = n.managed ∧
      ((n.fanout (S.sync s) ids).run h).1.1.addrs = n.addrs := by
  simp only [Node.fanout, HeldM.run_bind]
  rw [forIn_yield n.conns _ (fun p st => fanoutStep S s ids h p st) h (fun p _ st => by
    simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, sync_fam, sync_cfg]
    rw [filedGive_quiet _ _ _ _ _ rfl, filed_reads _ _ _ _ h]; rfl)]
  simp only [recordGiven_run, HeldM.run_pure]
  have : ∀ (L : List (Id × Conn)) st, (L.foldl (fun b a => fanoutStep S s ids h a b) st).1 =
      (L.map (fun p => (p.1, ((({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn).filed S.fam S.cfg ids :
        HeldM F Step).run h).1.conn))).reverse ++ st.1 ∧
      (L.foldl (fun b a => fanoutStep S s ids h a b) st).2.1.retry = st.2.1.retry := by
    intro L
    induction L with
    | nil => intro st; simp
    | cons p t ih =>
      intro st
      rw [List.foldl_cons, (ih _).1, (ih _).2]
      simp [fanoutStep, sends, Acts.append_def]
  refine ⟨?_, ?_, by simp, by simp⟩
  · rw [(this _ _).1]; simp
  · rw [(this _ _).2]

/-- A node's session, after the fanout, is the stream's step on it: the
same asks. -/
theorem fanout_asked (n : Node) (ids : List Id) (h : Held F) (cid : Id) (c' : Conn)
    (hc : ((n.fanout (S.sync s) ids).run h).1.1.conn? cid = some c') :
    ∃ c, n.conn? cid = some c ∧ c'.asked = c.asked := by
  rw [Node.conn?, (fanout_facts S s n ids h).1, List.find?_map] at hc
  simp only [Option.map_map] at hc
  cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none =>
    have : (n.conns.find? ((fun p => Decidable.decide (p.1 = cid)) ∘ fun p =>
        (p.1, ((({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn).filed S.fam S.cfg ids :
          HeldM F Step).run h).1.conn))) = none := by
      rw [← e]; rfl
    rw [this] at hc; cases hc
  | some p =>
    have : (n.conns.find? ((fun p => Decidable.decide (p.1 = cid)) ∘ fun p =>
        (p.1, ((({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn).filed S.fam S.cfg ids :
          HeldM F Step).run h).1.conn))) = some p := by
      rw [← e]; rfl
    rw [this] at hc
    simp only [Option.map_some, Option.some.injEq, Function.comp_apply] at hc
    refine ⟨p.2, by simp [Node.conn?, e], ?_⟩
    rw [← hc, filed_asked]
    rfl

/-- Storing keeps a node's managed sessions and addresses, adds no
retries, and keeps each session's asks. -/
theorem store_facts (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    ((n.store (S.sync s) ops mine).run h).1.2.retry = [] ∧
      ((n.store (S.sync s) ops mine).run h).1.1.managed = n.managed ∧
      ((n.store (S.sync s) ops mine).run h).1.1.addrs = n.addrs ∧
      (∀ cid c', ((n.store (S.sync s) ops mine).run h).1.1.conn? cid = some c' →
        ∃ c, n.conn? cid = some c ∧ c'.asked = c.asked) := by
  rw [store_run]
  dsimp only
  have hw := write_conns (S.sync s) n (intake (S.sync s).fam mine ops) h
  have hm := write_keeps (S.sync s) n (intake (S.sync s).fam mine ops) h
  split
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · unfold Node.put; exact hm
    · unfold Node.put; exact write_addrs _ _ _ _
    · intro cid c' hc
      refine ⟨c', ?_, rfl⟩
      unfold Node.put at hc
      simp only [Node.conn?] at hc ⊢; rw [hw] at hc; exact hc
  · obtain ⟨f1, f2, f3, f4⟩ := fanout_facts S s (Node.put (S.sync s) n ops mine |>.run h).1.1
      (Node.put (S.sync s) n ops mine |>.run h).1.2 (Node.put (S.sync s) n ops mine |>.run h).2
    refine ⟨f2, ?_, ?_, ?_⟩
    · rw [f3]; unfold Node.put; exact hm
    · rw [f4]; unfold Node.put; exact write_addrs _ _ _ _
    · intro cid c' hc
      obtain ⟨c, hc1, e⟩ := fanout_asked S s _ _ _ cid c' hc
      refine ⟨c, ?_, e⟩
      unfold Node.put at hc1
      simp only [Node.conn?] at hc1 ⊢; rw [hw] at hc1; exact hc1

end

end Engine.World
