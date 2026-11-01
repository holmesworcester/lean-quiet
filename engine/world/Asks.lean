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
theorem onHold_wants (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) {x : Id}
    (hr : r ∈ c.rooms) (hl : ids.length ≤ cfg.maxIds) (hx : x ∈ ids) (hq : x ∉ c.asked)
    (hh : heldIn fam h.db r x = false) (hroom : c.asked.size + ids.length ≤ cfg.maxKnown) :
    WantIn ((c.onHold fam cfg r ids : HeldM F Step) h).1.send x := by
  rw [onHold_apply]
  have hr' : (!has c.carried r) = false := by simp [Conn.has_carried_eq, has_of_mem hr]
  have hl' : ¬ ids.length > cfg.maxIds := by omega
  simp only [hr', Bool.false_eq_true, ↓reduceIte, hl']
  obtain ⟨hlen, hmem⟩ := wantStep_fold fam h.db c r ids []
  have hm : x ∈ (ids.foldl (wantStep fam h.db c r) []).reverse :=
    List.mem_reverse.2 ((hmem x).2 (Or.inr ⟨hx, hq, hh⟩))
  have hmax : 0 < cfg.maxIds := Nat.lt_of_lt_of_le (List.length_pos_of_mem hx) hl
  exact chunks_want cfg _ hmax (admitAsks_mem _ _ _ hm hq (by simp at hlen ⊢; omega))

/-- A round's answers want only ids its claims list. Stated for any
reading `f` of an answer's wants (the node's own lambda among them). -/
theorem answer_wants_le {α : Type} (key : α → Key) (ident : α → ByteArray) (hh : ByteArray → ByteArray)
    (P : Params) (mine : List α) (f : Out → List Id) (fw : ∀ xs, f (.want xs) = xs)
    (fh : ∀ xs, f (.hold xs) = []) (fc : ∀ c, f (.claim c) = []) (cs : List Claim) :
    ((cs.flatMap (answer key ident hh P mine)).flatMap f).length ≤ (claimIds cs).length := by
  have hcl : ∀ (L : List Range) (g : Range → Claim), ((L.map fun q => Out.claim (g q)).flatMap f) = [] := by
    intro L g; induction L with
    | nil => rfl
    | cons _ _ ih => simp [fc, ih]
  induction cs with
  | nil => simp [claimIds]
  | cons c t ih =>
    have e : claimIds (c :: t) = claimIds [c] ++ claimIds t := by simp [claimIds]
    rw [e, List.flatMap_cons, List.flatMap_append, List.length_append, List.length_append]
    have : ((answer key ident hh P mine c).flatMap f).length ≤ (claimIds [c]).length := by
      cases c with
      | fp r n l =>
        simp only [answer]
        split
        · simp
        · split
          · simp [fc]
          · rw [hcl]; simp
      | ids r xs =>
        simp only [answer, List.flatMap_cons, List.flatMap_nil, fh, fw, List.nil_append, List.append_nil]
        simp only [claimIds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact List.length_filter_le _ _
    omega

/-- Admitting asks into a step that sends their wants: the new asks are
the old ones or wanted in the step, and they grow by at most the ids
offered. -/
theorem admit_goal (cfg : Config) (A : Std.HashSet Id) (raw : List Id) (q : Op) (B : List Op) (n : Nat)
    (hmax : 0 < cfg.maxIds) (hn : raw.length ≤ n) :
    (∀ x, x ∈ (admitAsks cfg.maxKnown A raw).foldl (·.insert ·) A →
        x ∈ A ∨ WantIn (q :: (B ++ chunks cfg (admitAsks cfg.maxKnown A raw) .want)) x) ∧
      ((admitAsks cfg.maxKnown A raw).foldl (·.insert ·) A).size ≤ A.size + n := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases (foldl_insert_mem _ _).1 hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨L, hxL, hL⟩ := chunks_want cfg _ hmax hx
      exact Or.inr ⟨L, hxL, List.mem_cons_of_mem _ (List.mem_append_right _ hL)⟩
  · have h1 := foldl_insert_size (admitAsks cfg.maxKnown A raw) A
    have h2 := admitAsks_length cfg.maxKnown A raw
    omega

/-- The same of a connection's own answers (`Conn.answer`): a shown
room's are `answer`'s; a taken room's want nothing (`Conn.answer_blank`). -/
theorem conn_answer_wants_le (P : Params) (ix : Index) (c : Conn) (r : Id) (f : Out → List Id)
    (fw : ∀ xs, f (.want xs) = xs) (fh : ∀ xs, f (.hold xs) = []) (fc : ∀ c, f (.claim c) = [])
    (cs : List Claim) :
    ((cs.flatMap (Conn.answer P ix c r)).flatMap f).length ≤ (claimIds cs).length := by
  cases h : has c.rooms r
  · have hn : (cs.flatMap (Conn.answer P ix c r)).flatMap f = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro i hi
      simp only [List.mem_flatMap] at hi
      obtain ⟨o, ⟨cl, _, ho⟩, hi⟩ := hi
      obtain ⟨q, rfl⟩ := Conn.answer_blank h cl o ho
      rw [fc] at hi; cases hi
    rw [hn]; exact Nat.zero_le _
  · rw [Conn.answer_shown h, Index.answer_fun]
    exact answer_wants_le _ _ _ P _ f fw fh fc cs

/-- **What a round message makes a connection ask**, it wants on the wire
in the same step; and its asks grow by at most the ids the claims list. -/
theorem rbsr_asked (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hmax : 0 < cfg.maxIds) :
    (∀ x, x ∈ (c.onRbsr cfg ix r k cs now).conn.asked → x ∈ c.asked ∨ WantIn (c.onRbsr cfg ix r k cs now).send x) ∧
      (c.onRbsr cfg ix r k cs now).conn.asked.size ≤ c.asked.size + (claimIds cs).length := by
  unfold Conn.onRbsr
  split
  · exact ⟨fun x hx => Or.inl hx, Nat.le_add_right _ _⟩
  · split
    · exact ⟨fun x hx => Or.inl hx, Nat.le_add_right _ _⟩
    · dsimp only
      split
      · exact ⟨fun x hx => Or.inl hx, Nat.le_add_right _ _⟩
      · have e : (c.beginRound k).asked = c.asked := rfl
        split
        all_goals
          dsimp only
          simp only [e]
          refine admit_goal cfg _ _ _ _ (claimIds cs).length hmax ?_
          apply conn_answer_wants_le <;> intro _ <;> rfl

/-- The dialer's rounds change no ask. -/
theorem start_asked (cfg : Config) (ix : Index) (c : Conn) (now : Nat) :
    (c.start cfg ix now).conn.asked = c.asked := by
  rcases Conn.start_conn cfg ix c now with e | ⟨k, a, rs, ss, es, e⟩ <;> rw [e]; rfl

/-- **What a payload's step asks**, it asked before or wants on the wire
in the same step; and its asks grow by at most the payload's `asksOf`. -/
theorem recv_asked (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) (hmax : 0 < cfg.maxIds) :
    (∀ x, x ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.asked →
        x ∈ c.asked ∨ WantIn ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send x) ∧
      ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.asked.size ≤ c.asked.size + asksOf b := by
  unfold Conn.recv asksOf
  cases hd : Op.decode b with
  | none => exact ⟨fun x hx => Or.inl hx, by simp⟩
  | some o =>
    simp only
    cases hm : Msg.ofOp o with
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        split
        · refine ⟨fun x hx => Or.inl ?_, ?_⟩
          · rw [start_asked] at hx; exact hx
          · rw [start_asked]; exact Nat.le_add_right _ _
        · exact ⟨fun x hx => Or.inl hx, by simp⟩
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        exact rbsr_asked cfg ix { c with heard := now } r k cs now hmax
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        split
        · obtain ⟨rs, e⟩ := Conn.onAsk_eq ({ c with heard := now } : Conn) r
          simp only [HeldM.run_pure, e]
          exact ⟨fun x hx => Or.inl hx, Nat.le_add_right _ _⟩
        simp only [show ∀ m : HeldM F Step, m.run h = m h from fun _ => rfl]
        rw [onHold_apply]
        generalize hc' : ({ c with heard := now } : Conn) = c'
        have hca : c'.asked = c.asked := by rw [← hc']
        split
        · exact ⟨fun x hx => Or.inl (hca ▸ hx), by rw [hca]; exact Nat.le_add_right _ _⟩
        · split
          · exact ⟨fun x hx => Or.inl (hca ▸ hx), by rw [hca]; exact Nat.le_add_right _ _⟩
          · obtain ⟨hlen, _⟩ := wantStep_fold fam h.db c' r ids []
            refine ⟨fun x hx => ?_, ?_⟩
            · rcases (foldl_insert_mem _ _).1 hx with hx | hx
              · exact Or.inl (hca ▸ hx)
              · exact Or.inr (chunks_want cfg _ hmax hx)
            · have h1 := foldl_insert_size (admitAsks cfg.maxKnown c'.asked
                (ids.foldl (wantStep fam h.db c' r) []).reverse) c'.asked
              have h2 := admitAsks_length cfg.maxKnown c'.asked (ids.foldl (wantStep fam h.db c' r) []).reverse
              simp only [List.length_reverse, List.length_nil, Nat.zero_add] at h2 hlen
              simp only [hca] at h1 h2 ⊢
              omega
      | want ids =>
        simp only [HeldM.run_pure, Conn.onWant]
        split <;> exact ⟨fun x hx => Or.inl hx, by simp⟩
    | none =>
      simp only
      split
      · exact ⟨fun x hx => Or.inl hx, by simp⟩
      · refine ⟨fun x hx => Or.inl (Std.HashSet.mem_of_mem_erase hx), ?_⟩
        exact Nat.le_trans (Std.HashSet.size_erase_le (m := c.asked) (k := o.id)) (Nat.le_add_right _ _)

/-! ## The stream keeps a connection's asks -/

theorem filedStep_asked (cfg : Config) (fam : Family F) (db : DB F) (st : List (Id × Id) × Conn) (i : Id) :
    (filedStep cfg fam db st i).2.asked = st.2.asked := by
  unfold filedStep; split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- The stream changes only what a connection has offered. -/
theorem filed_shape (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ∃ off, ((c.filed fam cfg ids : HeldM F Step).run h).1.conn = { c with offered := off } := by
  simp only [Conn.filed, HeldM.run_bind]
  rw [forIn_yield ids _ (fun i st => filedStep cfg fam h.db st i) h (fun j _ st => by
    simp only [filedStep]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      cases h.db.ops j with
      | none => rfl
      | some p => by_cases hs : st.2.shows fam p = true <;> simp [hs]
    · rfl)]
  simp only [HeldM.run_pure]
  have : ∀ (L : List Id) (st : List (Id × Id) × Conn), (∃ off, st.2 = { c with offered := off }) →
      ∃ off, (L.foldl (fun st i => filedStep cfg fam h.db st i) st).2 = { c with offered := off } := by
    intro L
    induction L with
    | nil => intro st hs; exact hs
    | cons a t ih =>
      intro st ⟨off, hs⟩
      rw [List.foldl_cons]
      apply ih
      unfold filedStep; split
      · split
        · split
          · exact ⟨_, by rw [hs]⟩
          · exact ⟨off, hs⟩
        · exact ⟨off, hs⟩
      · exact ⟨off, hs⟩
  exact this ids ([], c) ⟨c.offered, rfl⟩

theorem filed_asked (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.asked = c.asked := by
  obtain ⟨off, e⟩ := filed_shape fam cfg c ids h; rw [e]

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
    ∃ c, n.conn? cid = some c ∧ c'.asked = c.asked ∧ c'.owed = c.owed ∧ c'.owing = c.owing := by
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
    rw [← hc]
    obtain ⟨off, e'⟩ := filed_shape S.fam S.cfg ({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn) ids h
    rw [e']
    exact ⟨rfl, rfl, rfl⟩

/-- Storing keeps a node's managed sessions and addresses, adds no
retries, and keeps each session's asks. -/
theorem store_facts (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    ((n.store (S.sync s) ops mine).run h).1.2.retry = [] ∧
      ((n.store (S.sync s) ops mine).run h).1.1.managed = n.managed ∧
      ((n.store (S.sync s) ops mine).run h).1.1.addrs = n.addrs ∧
      (∀ cid c', ((n.store (S.sync s) ops mine).run h).1.1.conn? cid = some c' →
        ∃ c, n.conn? cid = some c ∧ c'.asked = c.asked ∧ c'.owed = c.owed ∧ c'.owing = c.owing) := by
  rw [store_run]
  dsimp only
  have hw := write_conns (S.sync s) n (intake (S.sync s).fam mine ops) h
  have hm := write_keeps (S.sync s) n (intake (S.sync s).fam mine ops) h
  split
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · unfold Node.put; exact hm
    · unfold Node.put; exact write_addrs _ _ _ _
    · intro cid c' hc
      refine ⟨c', ?_, rfl, rfl, rfl⟩
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

/-- Replacing a session's connection: the node then holds the new one
under that id. -/
theorem conn_replace (n : Node) (cid : Id) (c : Conn) :
    Node.conn? { n with conns := n.conns.map fun p => if p.1 = cid then (cid, c) else p } cid =
      (n.conn? cid).map fun _ => c := by
  simp only [Node.conn?]
  induction n.conns with
  | nil => rfl
  | cons p t ih => by_cases e : p.1 = cid <;> simp_all

/-- **What applying a session's step does to the node:** the step's
sends go out on the session (either lane), no retries ride along,
managed sessions and addresses stay, and the session's asks are the
step's. -/
theorem apply_facts (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (hd : st.drop = false)
    (hc : (n.conn? cid).isSome = true) :
    ((n.apply (S.sync s) cid st now).run h).1.2.retry = [] ∧
      ((n.apply (S.sync s) cid st now).run h).1.1.managed = n.managed ∧
      ((n.apply (S.sync s) cid st now).run h).1.1.addrs = n.addrs ∧
      (∀ q ∈ st.send, (Route.conn cid, q.bytes) ∈ ((n.apply (S.sync s) cid st now).run h).1.2.send ∨
        (Route.conn cid, q.bytes) ∈ ((n.apply (S.sync s) cid st now).run h).1.2.serve) ∧
      (∀ c', ((n.apply (S.sync s) cid st now).run h).1.1.conn? cid = some c' →
        c'.asked = st.conn.asked ∧ c'.owed = st.conn.owed ∧ c'.owing = st.conn.owing) := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  simp only [hd, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, recordGiven_run]
  rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
    simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
  simp only [HeldM.run_pure]
  obtain ⟨r1, r2, r3, r4⟩ := store_facts S s { n with conns := n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p }
    st.take false h
  refine ⟨?_, r2, r3, ?_, ?_⟩
  · simp [Acts.append_def, split, r1]
  · intro q hq
    simp only [Acts.append_def, split, List.mem_append, List.mem_map, List.mem_filter]
    cases hl : wireLane (S.sync s) q with
    | urgent => exact Or.inl (Or.inl (Or.inl ⟨q, ⟨hq, by simp [hl]⟩, rfl⟩))
    | serve => exact Or.inr (Or.inl (Or.inl ⟨q, ⟨hq, by simp [hl]⟩, rfl⟩))
  · intro c' hc'
    obtain ⟨c, hc1, e⟩ := r4 cid c' hc'
    rw [conn_replace] at hc1
    obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hc
    rw [hc0] at hc1
    simp only [Option.map_some, Option.some.injEq] at hc1
    subst hc1; exact e

/-- Serving a session's queue keeps a node's managed sessions and
addresses, and adds no retries. -/
theorem serveOwed_facts (n : Node) (cid : Id) (now : Nat) (h : Held F) :
    ((n.serveOwed (S.sync s) cid now).run h).1.2.retry = [] ∧
      ((n.serveOwed (S.sync s) cid now).run h).1.1.managed = n.managed ∧
      ((n.serveOwed (S.sync s) cid now).run h).1.1.addrs = n.addrs := by
  unfold Node.serveOwed
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · simp only [HeldM.run_bind, refresh_run, HeldM.run_pure]
      exact ⟨by simp, by simp, by simp⟩

/-- **What a step's acts carry goes out:** at a node with no managed
sessions, every payload of the acts on a session with an address is in a
frame to that address (the plain node seals no retries). -/
theorem finish_sends (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) (hr : out.retry = [])
    (cid : Id) (p a : ByteArray) (hp : (Route.conn cid, p) ∈ out.send ∨ (Route.conn cid, p) ∈ out.serve)
    (ha : n.addr? cid = some a) :
    ∃ g, p ∈ g ∧ (a, plainFrame cid g) ∈ ((n.finish (S.sync s) out now).run h).1.2.send := by
  have e := finish_run S s n out now h hm
  have hf : out.serve.filter (fun _ => true) = out.serve := List.filter_eq_self.2 (fun _ _ => rfl)
  simp only [hr, List.filter_nil, List.any_nil, Bool.not_false, hf] at e
  rw [e]
  rcases hp with hp | hp
  · obtain ⟨g, hg, hm'⟩ := seal_mem S s n out h cid p a hp ha
    exact ⟨g, hg, List.mem_append_left _ (List.mem_append_left _ hm')⟩
  · obtain ⟨g, hg, hm'⟩ := seal_mem S s n { send := out.serve } h cid p a hp ha
    exact ⟨g, hg, List.mem_append_left _ (List.mem_append_right _ hm')⟩

/-! ## H4 over a frame -/

/-- A loop whose every turn yields, with an invariant P that may depend
on the turns still to come: P and a Q that the turn on a makes and every
turn keeps under P hold at the end once a is in the list. -/
theorem forIn_suffix {α β} (f : α → β → HeldM F (ForInStep β)) (P : List α → Held F → β → Prop)
    (Q : Held F → β → Prop) (a : α)
    (hy : ∀ a' b h, ∃ b', ((f a' b).run h).1 = .yield b')
    (hP : ∀ a' t b h, P (a' :: t) h b → P t ((f a' b).run h).2 ((f a' b).run h).1.value)
    (hQ : ∀ a' t b h, P (a' :: t) h b → Q h b → Q ((f a' b).run h).2 ((f a' b).run h).1.value)
    (ha : ∀ t b h, P (a :: t) h b → Q ((f a b).run h).2 ((f a b).run h).1.value) :
    ∀ (l : List α), a ∈ l → ∀ b h, P l h b → Q ((forIn l b f).run h).2 ((forIn l b f).run h).1 := by
  have keep : ∀ (l : List α) b h, P l h b → Q h b → Q ((forIn l b f).run h).2 ((forIn l b f).run h).1 := by
    intro l
    induction l with
    | nil => intro b h _ hq; exact hq
    | cons a' t ih =>
      intro b h hp hq
      rw [List.forIn_cons, HeldM.run_bind]
      obtain ⟨b', e⟩ := hy a' b h
      have hp' := hP a' t b h hp
      have hq' := hQ a' t b h hp hq
      rw [e] at hp' hq' ⊢
      exact ih b' _ hp' hq'
  intro l
  induction l with
  | nil => intro hm; cases hm
  | cons a' t ih =>
    intro hm b h hp
    rw [List.forIn_cons, HeldM.run_bind]
    obtain ⟨b', e⟩ := hy a' b h
    have hp' := hP a' t b h hp
    rw [e] at hp' ⊢
    rcases List.mem_cons.1 hm with rfl | hm
    · have hq' := ha t b h hp
      rw [e] at hq'
      exact keep t b' _ hp' hq'
    · exact ih hm b' _ hp'

theorem asksOf_hold (r : Id) (l : List Id) : asksOf (Msg.hold r l).op.bytes = l.length := by
  simp [asksOf, Op.decode_bytes, ofOp_hold]

theorem setAddr_addr (n : Node) (cid : Id) (a : ByteArray) : (n.setAddr cid a).addr? cid = some a := by
  simp [Node.setAddr, Node.addr?]

theorem addr_of_addrs {n n' : Node} (h : n'.addrs = n.addrs) (cid : Id) : n'.addr? cid = n.addr? cid := by
  simp [Node.addr?, h]

/-- A write turn keeps what a store holds in a room. -/
theorem heldIn_turnH (fam : Family F) (ops : List Op) (h : Held F) {r x : Id} (hh : heldIn fam h.db r x = true) :
    heldIn fam (turnH fam ops h).db r x = true := by
  unfold heldIn at hh ⊢
  cases e : h.db.ops x with
  | none => rw [e] at hh; cases hh
  | some o => rw [e] at hh; rw [turnH_some fam ops h e]; exact hh

/-- **H4 at a session's frame.** A node whose session cid is open takes
a frame on it carrying a have, in a room the session shows, of an op x it
had not asked for when the frame came. Then after the frame it holds x
in that room, or the frame it sends back to the frame's sender carries a
want naming x, wherever the have sits in the frame and whatever else the
frame carries, when the session's asks have room for every id the frame
offers (finding 7's premise, for the whole frame). -/
theorem onSealed_wants (n : Node) (src : ByteArray) (cid : Id) (inner : List ByteArray) (r x : Id) (l : List Id)
    (now : Nat) (h : Held F) (c0 : Conn) (hc : n.conn? cid = some c0) (hm : n.managed = [])
    (hb : (Msg.hold r l).op.bytes ∈ inner) (hx : x ∈ l) (hs : r ∈ S.rooms s cid) (hl : l.length ≤ S.cfg.maxIds)
    (hq : x ∉ c0.asked) (hroom : c0.asked.size + (inner.map asksOf).sum ≤ S.cfg.maxKnown)
    (hmax : 0 < S.cfg.maxIds) :
    heldIn S.fam ((n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now).run h).2.db r x = true ∨
      ∃ g L, x ∈ L ∧ (Msg.want L).op.bytes ∈ g ∧
        (src, plainFrame cid g) ∈ ((n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now).run h).1.2.send := by
  unfold Node.onSealed
  simp only [hc, Codec.decode_encode, HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
    ((n.setAddr cid src, {}) : Node × Acts) _) h = R
  have key : R.1.1.managed = [] ∧ R.1.1.addr? cid = some src ∧ R.1.2.retry = [] ∧
      (heldIn S.fam R.2.db r x = true ∨ WantsOn R.1.2 cid x) := by
    rw [← hR]
    refine forIn_suffix _ (fun rem h' (st : Node × Acts) => (st.1.conn? cid).isSome = true ∧ st.1.managed = [] ∧
        st.1.addr? cid = some src ∧ st.2.retry = [] ∧
        ∀ c, st.1.conn? cid = some c → (x ∈ c.asked → WantsOn st.2 cid x) ∧
          c.asked.size + (rem.map asksOf).sum ≤ S.cfg.maxKnown)
      (fun h' st => st.1.managed = [] ∧ st.1.addr? cid = some src ∧ st.2.retry = [] ∧
        (heldIn S.fam h'.db r x = true ∨ WantsOn st.2 cid x)) (Msg.hold r l).op.bytes ?_ ?_ ?_ ?_ inner hb _ h ?_
    · intro a st h'
      split
      · simp only [HeldM.run_bind, HeldM.run_pure]; exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · intro a t st h' ⟨hc', hm', ha', hr', hk⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h'
        obtain ⟨f1, f2, f3, f4, f5⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        obtain ⟨g1, g2⟩ := recv_asked S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h' hmax
        obtain ⟨hk1, hk2⟩ := hk c hcs
        refine ⟨(payload_run S s st.1 cid c a now h' hcs).1, by rw [f2]; exact hm', by rw [addr_of_addrs f3]; exact ha',
          by simp [Acts.append_def, hr', f1], fun c' hc'' => ⟨fun hx' => ?_, ?_⟩⟩
        · rw [(f5 c' hc'').1] at hx'
          rcases g1 x hx' with hx' | ⟨L, hxL, hL⟩
          · exact (hk1 hx').append_left _
          · rcases f4 _ hL with hq' | hq'
            · exact WantsOn.append_right _ ⟨L, hxL, Or.inl hq'⟩
            · exact WantsOn.append_right _ ⟨L, hxL, Or.inr hq'⟩
        · rw [(f5 c' hc'').1]
          simp only [List.map_cons, List.sum_cons] at hk2
          have : ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).asked = c.asked := rfl
          rw [this] at g2; omega
      · rename_i hcn
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hc'
        exact (hcn c hcc).elim
    · intro a t st h' ⟨hc', _, _, _, _⟩ ⟨qm, qa, qr, qh⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h'
        obtain ⟨f1, f2, f3, -, -⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        refine ⟨by rw [f2]; exact qm, by rw [addr_of_addrs f3]; exact qa, by simp [Acts.append_def, qr, f1], ?_⟩
        rcases qh with qh | qh
        · left
          rcases (payload_run S s st.1 cid c a now h' hcs).2 with e | ⟨o', _, _, e⟩
          · rw [e]; exact qh
          · rw [e]; exact heldIn_turnH _ _ _ qh
        · exact Or.inr (qh.append_left _)
      · exact ⟨qm, qa, qr, qh⟩
    · intro t st h' ⟨hc', hm', ha', hr', hk⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] }
          (Msg.hold r l).op.bytes now h'
        rw [recv_hold] at hd ⊢
        have hne : l.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hx)
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hd ⊢
        obtain ⟨f1, f2, f3, f4, -⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        refine ⟨by rw [f2]; exact hm', by rw [addr_of_addrs f3]; exact ha', by simp [Acts.append_def, hr', f1], ?_⟩
        obtain ⟨hk1, hk2⟩ := hk c hcs
        by_cases hh : heldIn S.fam h'.db r x = true
        · left
          rw [apply_reads S s st.1 cid _ now (onHold_take S.fam _ S.cfg r l h') h']
          exact hh
        · right
          by_cases hxa : x ∈ c.asked
          · exact (hk1 hxa).append_left _
          · simp only [List.map_cons, List.sum_cons, asksOf_hold] at hk2
            obtain ⟨L, hxL, hL⟩ := onHold_wants S.fam S.cfg
              ({ ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn) with heard := now } : Conn) r l h'
              (by simp [Conn.setRooms, hs]) hl hx hxa (by simpa using hh) (by simp [Conn.setRooms]; omega)
            rcases f4 _ hL with hq' | hq'
            · exact WantsOn.append_right _ ⟨L, hxL, Or.inl hq'⟩
            · exact WantsOn.append_right _ ⟨L, hxL, Or.inr hq'⟩
      · rename_i hcn
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hc'
        exact (hcn c hcc).elim
    · have e0 : (n.setAddr cid src).conn? cid = n.conn? cid := rfl
      refine ⟨by show ((n.setAddr cid src).conn? cid).isSome = true; rw [e0, hc]; rfl, hm,
        setAddr_addr n cid src, rfl, fun c hcs => ⟨fun hx' => ?_, ?_⟩⟩
      · have : c = c0 := by
          have e : (n.setAddr cid src).conn? cid = n.conn? cid := rfl
          rw [e, hc] at hcs; exact (Option.some.inj hcs).symm
        subst this; exact absurd hx' hq
      · have e : (n.setAddr cid src).conn? cid = n.conn? cid := rfl
        rw [e, hc] at hcs; cases hcs; exact hroom
  obtain ⟨k1, k2, k3, k4⟩ := key
  obtain ⟨s1, s2, s3⟩ := serveOwed_facts S s R.1.1 cid now R.2
  have hS := serveOwed_reads S s R.1.1 cid now R.2
  generalize HeldM.run (Node.serveOwed (S.sync s) R.1.1 cid now) R.2 = B at hS s1 s2 s3 ⊢
  rw [finish_reads S s B.1.1 _ now B.2, hS]
  rcases k4 with k4 | ⟨L, hxL, hL⟩
  · exact Or.inl k4
  · right
    have hp : (Route.conn cid, (Msg.want L).op.bytes) ∈ (R.1.2 ++ B.1.2).send ∨
        (Route.conn cid, (Msg.want L).op.bytes) ∈ (R.1.2 ++ B.1.2).serve := by
      rcases hL with hL | hL
      · exact Or.inl (List.mem_append_left _ hL)
      · exact Or.inr (List.mem_append_left _ hL)
    obtain ⟨g, hg, hf⟩ := finish_sends S s B.1.1 (R.1.2 ++ B.1.2) now B.2 (by rw [s2, k1])
      (by simp [Acts.append_def, k3, s1]) cid _ src hp (by rw [addr_of_addrs s3]; exact k2)
    rw [hS] at hf
    exact ⟨g, L, hxL, hg, hf⟩

end

end Engine.World
