/-
Claim trees, one hop (docs/PROOFS.md, "Claim trees"): what a side's
answer to an honest claim does with an item of the two sides'
difference over the claim's range, proven of holmes-a3's `answer`, the
function `Conn.onRbsr` runs. Either the answer settles it (a have of it,
or a want of it, when the claim listed ids), or it passes it on in a
claim of its own that is honest for the answering side: an id claim over
the same range, or a fingerprint over a piece of it that holds fewer of
the two sides' items (`answer_step`). Sound fingerprints rule out an
empty answer (`same_of_fp`). So every item of the difference is settled
within the tree's depth on its path, which `exchange_complete` bounds.
-/
import engine.world.Leaf
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

/-- Id i is in the two sides' difference over range q, either way. -/
def Diff (key : α → Key) (ident : α → ByteArray) (X Y : List α) (q : Range) (i : ByteArray) : Prop :=
  (named ident (within key q X) i = true ∧ named ident (within key q Y) i = false) ∨
  (named ident (within key q Y) i = true ∧ named ident (within key q X) i = false)

/-- **One hop of a claim tree.** X's answer to Y's honest claim over q,
for an id i of the two sides' difference over q: a have of i, a want of
i, an id claim over q honest for X, or a fingerprint over a piece of q,
honest for X, whose difference still holds i and which holds fewer of
the two sides' items. -/
theorem answer_step (X Y : List α) (q : Range) (c : Claim) (sX : Engine.Sync.Sorted key X)
    (nm : Engine.Sync.Named key ident (X ++ Y)) (so : Sound key ident h X Y) (hc : Honest key ident h Y q c)
    (i : ByteArray) (hd : Diff key ident X Y q i) :
    (∃ xs, Out.hold xs ∈ answer key ident h P X c ∧ i ∈ xs) ∨
    (∃ xs, Out.want xs ∈ answer key ident h P X c ∧ i ∈ xs) ∨
    (Out.claim (.ids q ((within key q X).map ident)) ∈ answer key ident h P X c) ∨
    (∃ q', Out.claim (.fp q' (fp key ident h (within key q' X)).1 (fp key ident h (within key q' X)).2) ∈
        answer key ident h P X c ∧ (∀ k, q'.has k = true → q.has k = true) ∧ Diff key ident X Y q' i ∧
        (within key q' X).length + (within key q' Y).length < (within key q X).length + (within key q Y).length) := by
  cases c with
  | ids r xs =>
    obtain ⟨rfl, rfl⟩ := hc
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨_, Or.inl rfl, ?_⟩
      obtain ⟨a, ha, rfl⟩ := named_iff.1 h1
      refine List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, ?_⟩, rfl⟩
      simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, List.mem_map]
      rintro _ ⟨b, hb, rfl⟩ e
      exact absurd (named_iff.2 ⟨b, hb, e.symm⟩) (by rw [h2]; simp)
    · right; left
      refine ⟨_, Or.inr rfl, ?_⟩
      obtain ⟨a, ha, rfl⟩ := named_iff.1 h1
      exact List.mem_filter.2 ⟨List.mem_map.2 ⟨a, ha, rfl⟩, by simp [h2]⟩
  | fp r n l =>
    obtain ⟨rfl, hfp⟩ := hc
    by_cases hf : fp key ident h (within key r X) = (n, l)
    · exfalso
      have hs := same_of_fp nm so (hf.trans hfp)
      rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hs i, h2] at h1; cases h1
      · rw [← hs i, h2] at h1; cases h1
    · by_cases hl : (within key r X).length ≤ P.leaf
      · right; right; left
        simp [answer, hf, hl]
      · right; right; right
        have hl' : P.leaf < (within key r X).length := by omega
        have hcut : ∀ c ∈ cutsOf key P (within key r X), r.has c = true := by
          intro c hc
          simp only [cutsOf, List.mem_map] at hc
          obtain ⟨p, hp, rfl⟩ := hc
          exact (mem_within.mp (pick_sub _ _ _ p hp)).2
        have hq : ∃ q' ∈ pieces r (cutsOf key P (within key r X)), Diff key ident X Y q' i := by
          rcases hd with hd | hd
          · obtain ⟨q', hq', hq''⟩ := (pieces_diff nm hcut i).2 hd
            exact ⟨q', hq', Or.inl hq''⟩
          · obtain ⟨q', hq', hq''⟩ := (pieces_diff (named_symm nm) hcut i).2 hd
            exact ⟨q', hq', Or.inr hq''⟩
        obtain ⟨q', hq', hdq⟩ := hq
        obtain ⟨hlt, hsub⟩ := pieces_shrink (P := P) sX hl' q' hq'
        have hY : (within key q' Y).length ≤ (within key r Y).length :=
          filter_len_le (fun a ha => hsub _ ha)
        refine ⟨q', ?_, hsub, hdq, by omega⟩
        simp only [answer, hf, hl, ite_false]
        exact List.mem_map.2 ⟨q', hq', rfl⟩

end


/-! ## One hop at a connection -/

/-- **One hop of a claim tree, at a connection**: `onRbsr` answers a
round message whose claim cl is honest for the claimant's items Y over q,
from its snapshot X of the round, for an id i of the difference over q:
it sends a have of i, or a want of i (not yet asked, with room), or the
round's reply carrying an id claim over q honest for X, or a fingerprint
over a smaller piece of q honest for X whose difference holds i. -/
theorem onRbsr_step (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hr : r ∈ c.rooms) (cl : Claim) (hcl : cl ∈ cs) (Y : List Item) (q : Range)
    (sX : Engine.Sync.Sorted Prod.fst (Conn.snap ix c r k))
    (nm : Engine.Sync.Named Prod.fst Prod.snd (Conn.snap ix c r k ++ Y))
    (so : Sound Prod.fst Prod.snd sha256 (Conn.snap ix c r k) Y)
    (hc : Honest Prod.fst Prod.snd sha256 Y q cl) (i : Id) (hd : Diff Prod.fst Prod.snd (Conn.snap ix c r k) Y q i)
    (hmax : 0 < cfg.maxIds) (ha : i ∉ c.asked) (hroom : c.asked.size + (claimIds cs).length ≤ cfg.maxKnown) :
    (∃ H, i ∈ H ∧ (Msg.hold r H).op ∈ (c.onRbsr cfg ix r k cs now).send) ∨
    (∃ W, i ∈ W ∧ (Msg.want W).op ∈ (c.onRbsr cfg ix r k cs now).send) ∨
    ∃ claims, (Msg.rbsr r k claims).op ∈ (c.onRbsr cfg ix r k cs now).send ∧
      ((.ids q ((within Prod.fst q (Conn.snap ix c r k)).map Prod.snd)) ∈ claims ∨
       ∃ q', .fp q' (fp Prod.fst Prod.snd sha256 (within Prod.fst q' (Conn.snap ix c r k))).1
          (fp Prod.fst Prod.snd sha256 (within Prod.fst q' (Conn.snap ix c r k))).2 ∈ claims ∧
        (∀ kk, q'.has kk = true → q.has kk = true) ∧ Diff Prod.fst Prod.snd (Conn.snap ix c r k) Y q' i ∧
        (within Prod.fst q' (Conn.snap ix c r k)).length + (within Prod.fst q' Y).length <
          (within Prod.fst q (Conn.snap ix c r k)).length + (within Prod.fst q Y).length) := by
  have hne : cs.isEmpty = false := by
    cases cs with
    | nil => cases hcl
    | cons _ _ => rfl
  rcases answer_step (P := cfg.params) _ Y q cl sX nm so hc i hd with ⟨xs, hxs, hi⟩ | ⟨xs, hxs, hi⟩ | hids | ⟨q', hq', hsub, hdq, hlt⟩
  · -- a have
    left
    have hh : i ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
        (fun | .hold xs => xs | _ => [] : Out → List Id) :=
      List.mem_flatMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hxs⟩, hi⟩
    obtain ⟨H, hxH, -, hm⟩ := chunks_cover cfg _ (Msg.hold r) hmax hh
    refine ⟨H, hxH, ?_⟩
    unfold Conn.onRbsr
    simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
    split
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
  · -- a want
    right; left
    have hw : i ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
        (fun | .want xs => xs | _ => [] : Out → List Id) :=
      List.mem_flatMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hxs⟩, hi⟩
    have hlen := answer_wants_len cfg.params (Conn.snap ix c r k) cs
    obtain ⟨W, hxW, -, hm⟩ := chunks_cover cfg _ Msg.want hmax (admit_mem cfg.maxKnown c.asked _ i hw ha
      (Nat.le_trans (Nat.add_le_add_left hlen _) hroom))
    refine ⟨W, hxW, ?_⟩
    unfold Conn.onRbsr
    simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
    split
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)
  · -- an id claim over q
    right; right
    refine ⟨((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).filterMap
      (fun | .claim x => some x | _ => none : Out → Option Claim)), ?_, Or.inl ?_⟩
    · unfold Conn.onRbsr
      simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
      split <;> exact List.mem_cons_self ..
    · exact List.mem_filterMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hids⟩, rfl⟩
  · -- a fingerprint over a smaller piece
    right; right
    refine ⟨((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).filterMap
      (fun | .claim x => some x | _ => none : Out → Option Claim)), ?_, Or.inr ⟨q', ?_, hsub, hdq, hlt⟩⟩
    · unfold Conn.onRbsr
      simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
      split <;> exact List.mem_cons_self ..
    · exact List.mem_filterMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hq'⟩, rfl⟩


/-! ## The index keeps its items sorted by key -/

/-- Every room's items sorted by key, as the round needs them. -/
def IxSorted (ix : Index) : Prop := ∀ r, Engine.Sync.Sorted Prod.fst (ix.items r)

theorem mem_ins' (a : Item) : ∀ (l : List Item) (b : Item), b ∈ Engine.Sync.ins a l → b ∈ l ∨ b = a := by
  intro l
  induction l with
  | nil => intro b hb; simp [Engine.Sync.ins] at hb; exact Or.inr hb
  | cons c t ih =>
    intro b hb
    simp only [Engine.Sync.ins] at hb
    split at hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inr rfl
      · exact Or.inl hb
    · split at hb
      · exact Or.inl hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact Or.inl (List.mem_cons_self ..)
        · rcases ih b hb with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h

/-- Inserting in key order keeps a list sorted. -/
theorem ins_sorted (a : Item) : ∀ (l : List Item), Engine.Sync.Sorted Prod.fst l →
    Engine.Sync.Sorted Prod.fst (Engine.Sync.ins a l) := by
  intro l
  induction l with
  | nil => intro _; simp [Engine.Sync.ins, Engine.Sync.Sorted]
  | cons c t ih =>
    intro hs
    unfold Engine.Sync.Sorted at hs ⊢
    rw [List.pairwise_cons] at hs
    simp only [Engine.Sync.ins]
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 hs⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hlt
      · exact Key.lt_trans hlt (hs.1 b hb)
    · split
      · exact List.pairwise_cons.2 hs
      · rename_i hnlt hne
        have hgt : c.1 < a.1 := by
          rcases Key.lt_trichotomy a.1 c.1 with h | h | h
          · exact absurd h hnlt
          · exact absurd h hne
          · exact h
        refine List.pairwise_cons.2 ⟨?_, ih hs.2⟩
        intro b hb
        rcases mem_ins' a t b hb with hb | rfl
        · exact hs.1 b hb
        · exact hgt

theorem add_sorted (fam : Family F) (ix : Index) (o : Op) (hx : IxSorted ix) : IxSorted (ix.add fam o) := by
  intro r
  rw [items_add_eq]
  split
  · exact ins_sorted _ _ (hx r)
  · exact hx r

theorem addStep_sorted (fam : Family F) (db : DB F) : ∀ (l : List Op) (st : Index × List Id), IxSorted st.1 →
    IxSorted (l.foldl (addStep fam db) st).1 := by
  intro l
  induction l with
  | nil => intro st h; exact h
  | cons o t ih =>
    intro st h
    apply ih
    unfold addStep
    split
    · exact add_sorted fam st.1 o h
    · exact h

theorem empty_sorted : IxSorted ({} : Index) := by
  intro r
  simp [Index.items, Engine.Sync.Sorted]

theorem ofOps_sorted (fam : Family F) (ops : List Op) : IxSorted (Index.ofOps fam ops) := by
  unfold Index.ofOps
  have : ∀ (l : List Op) (ix : Index), IxSorted ix → IxSorted (l.foldl (Index.add fam) ix) := by
    intro l
    induction l with
    | nil => intro ix h; exact h
    | cons o t ih => intro ix h; exact ih _ (add_sorted fam ix o h)
  exact this ops {} empty_sorted


/-! ## Every round snapshot is sorted -/

/-- Every snapshot a connection keeps is sorted by key. -/
def SnapsSorted (c : Conn) : Prop := ∀ e ∈ c.snaps, Engine.Sync.Sorted Prod.fst e.2

theorem start_sorted (cfg : Config) (ix : Index) (hx : IxSorted ix) (c : Conn) (now : Nat) (hc : SnapsSorted c) :
    SnapsSorted (c.start cfg ix now).conn := by
  unfold Conn.start
  split
  · exact hc
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨r, -, rfl⟩ := he
    exact hx r

theorem snap_sorted (ix : Index) (hx : IxSorted ix) (c : Conn) (hc : SnapsSorted c) (r : Id) (k : Nat) :
    Engine.Sync.Sorted Prod.fst (Conn.snap ix c r k) := by
  unfold Conn.snap
  split
  · rename_i q s' e
    exact hc _ (List.mem_of_find?_eq_some e)
  · exact hx r

theorem onRbsr_sorted (cfg : Config) (ix : Index) (hx : IxSorted ix) (c : Conn) (r : Id) (k : Nat) (cs : List Claim)
    (now : Nat) (hc : SnapsSorted c) : SnapsSorted (c.onRbsr cfg ix r k cs now).conn := by
  have hothers : ∀ e ∈ c.snaps.filter (fun p => !Decidable.decide (p.1.1 = r)), Engine.Sync.Sorted Prod.fst e.2 :=
    fun e he => hc e ((List.mem_filter.1 he).1)
  unfold Conn.onRbsr
  split
  · exact hc
  · split
    · exact hothers
    · intro e he
      simp only [Step.limit_snaps] at he
      rcases mem_ite_snaps he with he | he
      · exact hothers e he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact snap_sorted ix hx c hc r k
        · exact hothers e he

section
variable (fam : Family F) (cfg : Config)

theorem recv_sorted (ix : Index) (hx : IxSorted ix) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F)
    (hc : SnapsSorted c) : SnapsSorted ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn := by
  unfold Conn.recv
  split
  · exact hc
  · rename_i o _
    have hc' : SnapsSorted ({ c with heard := now } : Conn) := hc
    dsimp only
    split
    · rename_i f _
      simp only [HeldM.run_pure]
      intro e he; rw [finish_snaps] at he
      split at he
      · exact start_sorted cfg ix hx ({ c with heard := now, peerFloor := some f } : Conn) now hc e he
      · exact hc e he
    · simp only [HeldM.run_pure]
      intro e he; rw [finish_snaps] at he
      exact onRbsr_sorted cfg ix hx _ _ _ _ now hc' e he
    · simp only [HeldM.run_bind, HeldM.run_pure]
      intro e he; rw [finish_snaps, onHold_snaps] at he; exact hc e he
    · simp only [HeldM.run_bind, HeldM.run_pure]
      intro e he; rw [finish_snaps, onWant_snaps fam cfg] at he; exact hc e he
    · split
      · exact hc
      · simp only [HeldM.run_pure]
        intro e he; rw [finish_snaps, Step.limit_snaps] at he; exact hc e he

theorem tick_sorted (hw : WalkLaws (F := F) fam cfg) (ix : Index) (hx : IxSorted ix) (c : Conn) (now : Nat)
    (h : Held F) (hc : SnapsSorted c) : SnapsSorted ((c.tick fam cfg ix now : HeldM F Step).run h).1.conn := by
  unfold Conn.tick
  split
  · exact hc
  · simp only [HeldM.run_bind, HeldM.run_pure]
    have e := hw.same c h
    have hw' : SnapsSorted (((c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h).1.1.expireAsks cfg now) := by
      intro x hx'
      have hx'' : x ∈ ((c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h).1.1.snaps := hx'
      rw [e.snaps] at hx''; exact hc x hx''
    intro x hx'
    rw [finish_snaps] at hx'
    dsimp only at hx'
    split at hx'
    · exact start_sorted cfg ix hx _ now hw' x hx'
    · exact hw' x hx'

theorem filed_sorted (c : Conn) (ids : List Id) (h : Held F) (hc : SnapsSorted c) :
    SnapsSorted ((c.filed fam cfg ids : HeldM F Step).run h).1.conn := by
  intro e he; rw [filed_snaps] at he; exact hc e he

theorem setRooms_sorted (c : Conn) (rs : List Id) (hc : SnapsSorted c) : SnapsSorted (c.setRooms rs) := by
  intro e he
  simp only [Conn.setRooms, List.mem_filter] at he
  exact hc e he.1

end


/-! ## In every reachable world, every index and snapshot is sorted -/

/-- A node's index and every snapshot it keeps are sorted by key. -/
def SortOk (n : Node) : Prop := IxSorted n.ix ∧ ∀ p ∈ n.conns, SnapsSorted p.2

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem write_sorted (n : Node) (ops : List Op) (h : Held F) (hn : SortOk n) :
    SortOk ((n.write (psync fam cfg rms) ops).run h).1.1 := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [write_run]; dsimp only
    split
    · exact hn.1
    · dsimp only; exact addStep_sorted _ _ _ (n.ix, []) hn.1
  · rw [(write_node fam cfg rms n ops h).1] at hp; exact hn.2 p hp

theorem store_sorted (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (hn : SortOk n) :
    SortOk ((n.store (psync fam cfg rms) ops mine).run h).1.1 := by
  rw [store_run]
  simp only [Node.put, psync_fam]
  have hw := write_sorted fam cfg rms n (intake fam mine ops) h hn
  by_cases hc : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · simp only [hc, ↓reduceIte]; exact hw
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    have fn := fanout_node fam cfg rms ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.1
      ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2 ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2
    refine ⟨by rw [fn.2.1]; exact hw.1, fun p hp => ?_⟩
    rw [fn.2.2.2.2] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact filed_sorted fam cfg _ _ _ (setRooms_sorted _ _ (hw.2 q hq))

theorem setConn_sorted (n : Node) (cid : Id) (c : Conn) (hn : SortOk n) (hc : SnapsSorted c) :
    SortOk (setConn n cid c) := by
  refine ⟨hn.1, fun p hp => ?_⟩
  simp only [setConn, List.mem_map] at hp
  obtain ⟨q, hq, e⟩ := hp
  split at e
  · rw [← e]; exact hc
  · rw [← e]; exact hn.2 q hq

theorem apply_sorted (n : Node) (cid : Id) (s : Step) (now : Nat) (h : Held F) (hn : SortOk n)
    (hs : SnapsSorted s.conn) : SortOk ((n.apply (psync fam cfg rms) cid s now).run h).1.1 := by
  by_cases hd : s.drop = true
  · simp only [Node.apply, hd, ↓reduceIte, HeldM.run_pure]
    refine ⟨hn.1, fun p hp => ?_⟩
    simp only [Node.drop, Node.close, List.mem_filter] at hp
    exact hn.2 p hp.1
  · rw [apply_run fam cfg rms _ _ _ _ _ (by simpa using hd)]
    exact store_sorted fam cfg rms _ _ _ _ (setConn_sorted _ _ _ hn hs)

theorem frameStep_sorted (hw : WalkLaws (F := F) fam cfg) (cid : Id) (now : Nat) (st : (Node × Acts) × Held F)
    (b : ByteArray) (hn : SortOk st.1.1) : SortOk (frameStep fam cfg rms cid now st b).1.1 := by
  unfold frameStep
  split
  · rename_i c hc
    exact apply_sorted fam cfg rms _ _ _ _ _ hn (recv_sorted fam cfg _ hn.1 _ b now st.2
      (setRooms_sorted _ _ (hn.2 _ (conn_mem hc))))
  · exact hn

theorem tickStep_sorted (hw : WalkLaws (F := F) fam cfg) (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn)
    (hn : SortOk st.1.1) : SortOk (tickStep fam cfg rms now st p).1.1 := by
  unfold tickStep
  split
  · rename_i c hc
    exact apply_sorted fam cfg rms _ _ _ _ _ hn (tick_sorted fam cfg hw _ hn.1 _ now st.2
      (setRooms_sorted _ _ (hn.2 _ (conn_mem hc))))
  · exact hn

theorem finish_sorted (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) (hn : SortOk n) :
    SortOk ((n.finish (psync fam cfg rms) out now).run h).1.1 := by
  rw [finish_run fam cfg rms _ _ _ _ hm]; exact hn

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onFrame_sorted (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (hn : SortOk n) :
    SortOk ((n.onFrame (psync fam cfg rms) a b now).run h).1.1 := by
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact hn
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
                exact hn
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
                  exact hn
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi,
                      HeldM.run_pure]
                    exact hn
          | some inner =>
            rw [onFrame_fold fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            have ok0 := setAddr_ok fam n cid a h ok
            obtain ⟨okE, -, -, -, -⟩ := frame_fold fam cfg rms hw cid now inner ((n.setAddr cid a, {}), h) ok0
            apply finish_sorted fam cfg rms _ _ _ _ okE.managed
            have : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F), SortOk st.1.1 →
                SortOk (l.foldl (frameStep fam cfg rms cid now) st).1.1 := by
              intro l
              induction l with
              | nil => intro st h; exact h
              | cons b' t ih => intro st h; exact ih _ (frameStep_sorted fam cfg rms hw cid now st b' h)
            exact this inner _ hn
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]; exact hn
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]; exact hn
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            have wok := write_ok fam cfg rms n (intakeConn fam [o]) h ok
            exact finish_sorted fam cfg rms _ _ _ _ wok.managed (write_sorted fam cfg rms _ _ _ hn)
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · exact hn

theorem onTick_sorted (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (hn : SortOk n) :
    SortOk ((n.onTick (psync fam cfg rms) now).run h).1.1 := by
  rw [onTick_run fam cfg rms hw]
  have okf := tick_fold_ok fam cfg rms hw now n.conns ((n, {}), h) ok
  apply finish_sorted fam cfg rms _ _ _ _ okf.managed
  have : ∀ (l : List (Id × Conn)) (st : (Node × Acts) × Held F), SortOk st.1.1 →
      SortOk (l.foldl (tickStep fam cfg rms now) st).1.1 := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons p t ih => intro st h; exact ih _ (tickStep_sorted fam cfg rms hw now st p h)
  exact this _ _ hn

omit hw in
theorem onWrite_sorted (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (hn : SortOk n) :
    SortOk ((n.onWrite (psync fam cfg rms) ops now).run h).1.1 := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  exact finish_sorted fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok).managed
    (store_sorted fam cfg rms _ _ _ _ hn)

omit hw in
theorem connect_sorted (n : Node) (cid : Id) (a : ByteArray) (dl : Bool) (now : Nat) (h : Held F)
    (ok : NodeOk fam n h) (hn : SortOk n) : SortOk ((n.connect (psync fam cfg rms) cid a dl now).run h).1.1 := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  apply finish_sorted fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, ok.managed])
  refine ⟨hn.1, fun p hp => ?_⟩
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · intro e he; simp [Conn.open] at he
  · simp only [Node.setAddr, Node.close, List.mem_filter] at hp
    exact hn.2 p hp.1

end

theorem enter_sorted (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) (hf : SortOk ((f (w.node i)).run (w.box i)).1.1)
    (hs : ∀ j, SortOk (w.node j)) : ∀ j, SortOk ((w.enter Q.setup i t f).node j) := by
  intro j
  simp only [World.enter, upd]
  by_cases e : j = i
  · subst e; simp only [ite_true]; exact hf
  · simp only [e, ite_false]; exact hs j

theorem boot_sorted (fam : Family F) (ops : List Op) (floor : Nat) : SortOk (Node.boot fam ops floor) :=
  ⟨ofOps_sorted fam ops, fun p hp => by simp [Node.boot] at hp⟩

theorem reach_sorted' (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg)
    (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0ok : ∀ i, NodeOk Q.fam (w₀.node i) (w₀.box i)) (h0 : ∀ i, SortOk (w₀.node i))
    (hr : Reachable Q.setup adv w₀ w) : ∀ i, SortOk (w.node i) := by
  induction hr with
  | init => exact h0
  | @step w a hr' _ ih =>
    have ok := reach_ok' Q hw adv w₀ w h0ok hr'
    cases a with
    | deliver k t =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        split
        · exact ih
        · rename_i j' _
          exact enter_sorted Q { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j')) p.origin p.bytes t)
            (onFrame_sorted Q.fam Q.cfg (Q.rooms j') hw _ _ _ _ _ (ok j') (ih j')) ih
    | dup k => simp only [World.step]; split <;> exact ih
    | drop k => exact ih
    | tick i t =>
      exact enter_sorted Q w i t (fun nd => nd.onTick (psync Q.fam Q.cfg (Q.rooms i)) t)
        (onTick_sorted Q.fam Q.cfg (Q.rooms i) hw _ _ _ (ok i) (ih i)) ih
    | write i ops t =>
      exact enter_sorted Q w i t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms i)) ops t)
        (onWrite_sorted Q.fam Q.cfg (Q.rooms i) _ _ _ _ (ok i) (ih i)) ih
    | restart i t =>
      intro j
      simp only [World.step, upd]
      by_cases e : j = i
      · subst e; simp only [ite_true]; exact boot_sorted _ _ _
      · simp only [e, ite_false]; exact ih j
    | connect i j cid d t =>
      exact enter_sorted Q w i t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms i)) cid (Q.setup.addr j) d t)
        (connect_sorted Q.fam Q.cfg (Q.rooms i) _ _ _ _ _ _ (ok i) (ih i)) ih
    | inject i o b t =>
      exact enter_sorted Q w i t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms i)) o b t)
        (onFrame_sorted Q.fam Q.cfg (Q.rooms i) hw _ _ _ _ _ (ok i) (ih i)) ih

/-- **In every world the plain world reaches, every node's index and
every snapshot it keeps are sorted by key**, as the claim tree needs. -/
theorem reach_sorted (Q : Plain F) (adv : World (Held F) Q.n → ByteArray → Prop) (w : World (Held F) Q.n)
    (hr : Q.Reach adv w) : ∀ i, SortOk (w.node i) :=
  reach_sorted' Q (walk_proof F Q.fam Q.cfg) adv Q.start w
    (fun _ => boot_ok Q.fam {} (fun x o h => by cases h) (fun o ho => by cases ho)
      (fun o ho => by cases ho) (fun x o h => by cases h) _) (fun _ => boot_sorted _ _ _) hr

end Engine.World
