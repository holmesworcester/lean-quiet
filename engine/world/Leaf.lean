/-
The leaf regime, at one connection, proven of the running code: with
every room's index at most `leaf` items, every round message a
connection sends lists ids only, given that every one it took did.

- An opening of a window over at most `leaf` items lists ids only
  (`opening_ids`, `start_leaf`).
- A reply to round messages of ids only lists no claims
  (`onRbsr_leaf`), and haves, wants and served ops are no round messages
  (`recv_leaf`, `tick_leaf`, `filed_leaf`).
-/
import engine.world.Round
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-- An op that, read as a round message, lists ids only. -/
def LeafOp (o : Op) : Prop := ∀ r k cs, Msg.ofOp o = some (.rbsr r k cs) → IdsOnly cs

/-- A payload that, read as a round message, lists ids only. -/
def LeafOk (b : ByteArray) : Prop := ∀ o, Op.decode b = some o → LeafOp o

theorem leafOk_bytes {o : Op} (h : LeafOp o) : LeafOk o.bytes := fun o' hd => by
  rw [Op.decode_bytes] at hd; cases hd; exact h

theorem leafOp_hold (r : Id) (l : List Id) : LeafOp (Msg.hold r l).op := fun _ _ _ h => by
  rw [ofOp_have] at h; cases h

theorem leafOp_want (l : List Id) : LeafOp (Msg.want l).op := fun _ _ _ h => by
  rw [ofOp_want] at h; cases h

theorem leafOp_hello (f : Nat) : LeafOp (Msg.hello f).op := fun _ _ _ h => by
  simp [Msg.ofOp, Msg.op, Codec.decode_encode] at h

theorem leafOp_rbsr (r : Id) (k : Nat) (cs : List Claim) (hcs : IdsOnly cs) : LeafOp (Msg.rbsr r k cs).op :=
  fun _ _ _ h => by rw [ofOp_rbsr] at h; cases h; exact hcs

theorem leafOp_data {o : Op} (h : isWire o.kind = false) : LeafOp o := fun _ _ _ e => by
  rw [ofOp_data h] at e; cases e

theorem chunks_leaf (cfg : Config) (ids : List Id) (mk : List Id → Msg) (hmk : ∀ l, LeafOp (mk l).op) :
    ∀ o ∈ chunks cfg ids mk, LeafOp o := by
  intro o ho
  simp only [chunks, List.mem_map] at ho
  obtain ⟨l, -, rfl⟩ := ho
  exact hmk l

theorem holdsOf_leaf (cfg : Config) (offer : List (Id × Id)) : ∀ o ∈ holdsOf cfg offer, LeafOp o := by
  intro o ho
  simp only [holdsOf, List.mem_flatMap] at ho
  obtain ⟨r, -, ho⟩ := ho
  exact chunks_leaf cfg _ _ (fun l => leafOp_hold r l) o ho

/-- An opening of a window over at most `leaf` items lists ids only. -/
theorem opening_ids (P : Params) (X : List Item) (hX : X.length ≤ P.leaf) (ws : List Range) :
    IdsOnly (ws.map (opening Prod.fst Prod.snd sha256 P X)) := by
  intro cl hcl
  obtain ⟨rg, -, rfl⟩ := List.mem_map.1 hcl
  have : (within Prod.fst rg X).length ≤ P.leaf := Nat.le_trans (List.length_filter_le _ _) hX
  exact ⟨rg, (within Prod.fst rg X).map Prod.snd, by simp only [opening, this, ↓reduceIte]⟩

/-- The rooms of an index all have at most n items. -/
def IxSmall (ix : Index) (n : Nat) : Prop := ∀ r, (ix.items r).length ≤ n

theorem start_leaf (cfg : Config) (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (now : Nat) :
    ∀ o ∈ (c.start cfg ix now).send, LeafOp o := by
  intro o ho
  unfold Conn.start at ho
  split at ho
  · cases ho
  · simp only [List.mem_map] at ho
    obtain ⟨⟨⟨r, k⟩, s⟩, hs, rfl⟩ := ho
    simp only [List.mem_map, Prod.mk.injEq] at hs
    obtain ⟨r', -, ⟨rfl, rfl⟩, rfl⟩ := hs
    exact leafOp_rbsr _ _ _ (opening_ids cfg.params _ (hx r') _)

/-- **A reply to round messages of ids only lists no claims.** -/
theorem onRbsr_leaf (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hcs : IdsOnly cs) : ∀ o ∈ (c.onRbsr cfg ix r k cs now).send, LeafOp o := by
  intro o ho
  unfold Conn.onRbsr at ho
  split at ho
  · cases ho
  · dsimp only at ho
    split at ho
    · cases ho
    · simp only [Step.limit_send] at ho
      rw [answer_ids_noclaims cfg.params _ cs hcs] at ho
      rotate_left
      · intro _; rfl
      · intro _; rfl
      rcases List.mem_cons.1 ho with rfl | ho
      · exact leafOp_rbsr _ _ _ (fun _ h => by cases h)
      · rcases List.mem_append.1 ho with ho | ho
        · exact chunks_leaf cfg _ _ (fun l => leafOp_hold r l) o ho
        · exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho

section
variable (fam : Family F) (cfg : Config)

theorem tick_leaf (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (now : Nat) (h : Held F) :
    ∀ o ∈ ((c.tick fam cfg ix now : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  unfold Conn.tick at ho
  split at ho
  · cases ho
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
    rcases List.mem_append.1 ho with ho | ho
    · split at ho
      · exact start_leaf cfg ix hx _ now o ho
      · cases ho
    · rcases List.mem_append.1 ho with ho | ho
      · exact holdsOf_leaf cfg _ o ho
      · exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho

theorem filed_leaf (c : Conn) (ids : List Id) (h : Held F) :
    ∀ o ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  rw [filed_run, Conn.finish_send] at ho
  exact holdsOf_leaf cfg _ o ho

/-- **What a connection sends on a payload that lists ids only, if a
round message, lists ids only**, its index at most `leaf` items per
room, every op it serves a data op. -/
theorem recv_leaf (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F)
    (hb : LeafOk b) (hdata : ∀ o, c.shows fam o = true → isWire o.kind = false) :
    ∀ o ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  unfold Conn.recv at ho
  cases hd : Op.decode b with
  | none => simp only [hd, HeldM.run_pure] at ho; cases ho
  | some o0 =>
    simp only [hd] at ho
    cases hm : Msg.ofOp o0 with
    | none =>
      simp only [hm] at ho
      split at ho
      · cases ho
      · simp only [HeldM.run_pure, Conn.finish_send, Step.limit_send] at ho; cases ho
    | some m =>
      simp only [hm] at ho
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, Conn.finish_send] at ho
        split at ho
        · exact start_leaf cfg ix hx _ now o ho
        · cases ho
      | rbsr r k cs =>
        simp only [HeldM.run_pure, Conn.finish_send] at ho
        exact onRbsr_leaf cfg ix _ r k cs now (hb o0 hd r k cs hm) o ho
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        change o ∈ ((Conn.onHold fam cfg _ r ids : HeldM F Step) h).1.send at ho
        rw [onHold_apply] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · simp only [Step.limit_send] at ho; exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        unfold Conn.onWant at ho
        split at ho
        · cases ho
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure, Step.limit_send] at ho
          exact leafOp_data (hdata o (serve_shownW _ _ _ _ o ho).1)

end

end Engine.World
