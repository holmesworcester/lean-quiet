/-
Take rooms (docs/TAKE-ROOM.md), proven of `Conn`'s code:

- `take_unshown`: an op of a room the connection does not show is never
  shown, however the room is carried; so no step offers, serves or
  streams it (`recv_send`, `serveOwed_send`, `have_shown`).
- `start_take_blank`, `onRbsr_take_blank`: the rounds of a room the
  connection does not show are opened from the empty index and answered
  blank (`Conn.answer`): every claim they send is an empty id claim
  (`.ids q []`), no fingerprint, and they send no have and no want. A
  take room's round says nothing of what this side holds; it wants only
  from the peer's haves (`onHold`, reading the store).
- `take_opens`: a take room that is due opens like any other, with one
  empty id claim per window range.
- `take_round_offers`: the peer that syncs the room answers that opening
  by ending the round and offering, as haves, every id it holds in the
  window, newest first; `recv_takes_taken`: a take room's ops received are taken. So a
  take room learns all the peer may show it: a joiner learns of its
  admission.
-/
import engine.sync.OfferLaws
import engine.sync.ConnLaws

namespace Engine.Sync

/-- A round message's op names its room, epoch and claims. -/
theorem rbsr_op_inj {r r' : Id} {k k' : Nat} {cs cs' : List Claim}
    (e : (Msg.rbsr r' k' cs').op = (Msg.rbsr r k cs).op) : r' = r ∧ k' = k ∧ cs' = cs := by
  have h1 : Msg.ofOp (Msg.rbsr r' k' cs').op = some (.rbsr r' k' cs') := by
    simp [Msg.ofOp, Msg.op, kRbsr, Codec.decode_encode]
  have h2 : Msg.ofOp (Msg.rbsr r k cs).op = some (.rbsr r k cs) := by
    simp [Msg.ofOp, Msg.op, kRbsr, Codec.decode_encode]
  rw [e, h2] at h1
  simp only [Option.some.injEq, Msg.rbsr.injEq] at h1
  exact ⟨h1.1.symm, h1.2.1.symm, h1.2.2.symm⟩

section
variable {F : Type} (fam : Family F) (cfg : Config)

/-- **A room not shown shows nothing (`take_unshown`).** -/
theorem take_unshown (c : Conn) {r : Id} (hr : has c.rooms r = false) {o : Op}
    (ho : fam.room o = some r) : c.shows fam o = false := by
  simp [Conn.shows, ho, hr]

/-- The claim this side opens a round of a room it does not show with:
an empty id claim over the range. -/
theorem view_opening (ix : Index) (c : Conn) {r : Id} (hr : has c.rooms r = false) (P : Params)
    (f : Nat) (w : Range) : (Conn.view ix c r).opening P r f w = .ids w [] := by
  simp [Conn.view, hr, Index.opening_eq, opening, within]

/-- Chunks of ids are sent only if there is an id. -/
theorem chunks_some {ids : List Id} {mk : List Id → Msg} {o : Op} (h : o ∈ chunks cfg ids mk) :
    ∃ i, i ∈ ids := by
  cases ids with
  | nil => simp [chunks, pieceIds] at h
  | cons i t => exact ⟨i, List.mem_cons_self ..⟩

/-- Asks are admitted only if there is an id to ask for. -/
theorem admitAsks_some {cap : Nat} {asked : Std.HashSet Id} {ids : List Id} {i : Id}
    (h : i ∈ admitAsks cap asked ids) : ∃ j, j ∈ ids := by
  cases ids with
  | nil => simp [admitAsks] at h
  | cons j t => exact ⟨j, List.mem_cons_self ..⟩

/-- A data op's message: none. -/
theorem ofOp_data {o : Op} (hw : isWire o.kind = false) : Msg.ofOp o = none := by
  simp only [isWire, Bool.or_eq_false_iff] at hw
  obtain ⟨⟨h1, h2⟩, h3⟩ := hw
  simp [Msg.ofOp, h1, h2, h3]

/-- **A take room takes (`recv_takes_taken`).** A data op of a room the
connection takes, received, is handed to the writer: so a joiner's
session with its inviter takes the inviter's ops of the community, its
own admission among them. -/
theorem recv_takes_taken (ix : Index) (c : Conn) (now : Nat) (s : DB F) {o : Op} {r : Id}
    (hroom : fam.room o = some r) (ht : has c.takes r = true) (hw : isWire o.kind = false) :
    ((Conn.recv fam cfg ix c o.bytes now : Model F Step).run s).1.take = [o] := by
  rw [recv_cases fam cfg ix c o.bytes now s o (Op.decode_bytes o)]
  dsimp only
  rw [ofOp_data hw]
  dsimp only
  have hk : Conn.takesOp fam ({ c with heard := now } : Conn) o = true := by
    simp [Conn.takesOp, hroom, ht]
  rw [ite_eq_right (by simp [hw, hk])]

/-- **A take room's rounds open blank (`start_take_blank`).** Every
round `start` opens in a room the connection does not show claims only
empty id lists. -/
theorem start_take_blank (ix : Index) (c : Conn) (now : Nat) {r : Id} (hr : has c.rooms r = false)
    {k : Nat} {cs : List Claim} (ho : (Msg.rbsr r k cs).op ∈ (c.start cfg ix now).send) :
    ∀ cl ∈ cs, ∃ q, cl = .ids q [] := by
  unfold Conn.start at ho
  split at ho
  · cases ho
  · dsimp only at ho
    split at ho
    · cases ho
    · simp only [List.mem_map] at ho
      obtain ⟨r', _, e⟩ := ho
      obtain ⟨rfl, _, rfl⟩ := rbsr_op_inj e
      intro cl hcl
      simp only [List.mem_map] at hcl
      obtain ⟨q, _, rfl⟩ := hcl
      exact ⟨q, view_opening ix c hr cfg.params _ q⟩

/-- **A take room's rounds answer blank (`onRbsr_take_blank`).** A round
message about a room the connection does not show is answered with one
round message whose every claim is an empty id list: no fingerprint, no
have, and no want (a take room wants only from haves, by `onHold`, which
reads the store). -/
theorem onRbsr_take_blank (ix : Index) (c : Conn) {r : Id} (k now : Nat) (cs : List Claim)
    (hr : has c.rooms r = false) :
    ∀ o ∈ (c.onRbsr cfg ix r k cs now).send,
      ∃ cs', o = (Msg.rbsr r k cs').op ∧ ∀ cl ∈ cs', ∃ q, cl = .ids q [] := by
  intro o ho
  unfold Conn.onRbsr at ho
  split at ho
  · simp only [List.mem_singleton] at ho
    exact ⟨[], ho, by simp⟩
  split at ho
  · cases ho
  dsimp only at ho
  split at ho
  · cases ho
  have hv : ∀ f cl, ∀ o ∈ Conn.answer cfg.params ix c r f cl, ∃ q, o = .claim (.ids q []) :=
    fun _ cl => Conn.answer_blank hr cl
  simp only [List.mem_cons, List.mem_append] at ho
  rcases ho with rfl | ho | ho
  · refine ⟨_, rfl, fun cl hcl => ?_⟩
    simp only [claimsOf, List.mem_filterMap, List.mem_flatMap] at hcl
    obtain ⟨out, ⟨cl', _, hout⟩, e⟩ := hcl
    obtain ⟨q, rfl⟩ := hv _ cl' out hout
    cases e; exact ⟨q, rfl⟩
  · exfalso
    obtain ⟨i, hi⟩ := chunks_some cfg ho
    simp only [List.mem_flatMap] at hi
    obtain ⟨out, ⟨cl', _, hout⟩, hi⟩ := hi
    obtain ⟨q, rfl⟩ := hv _ cl' out hout
    simp [holdIds] at hi
  · exfalso
    obtain ⟨i, hi⟩ := chunks_some cfg ho
    obtain ⟨j, hj⟩ := admitAsks_some hi
    simp only [List.mem_flatMap] at hj
    obtain ⟨out, ⟨cl', _, hout⟩, hj⟩ := hj
    obtain ⟨q, rfl⟩ := hv _ cl' out hout
    simp at hj

/-- **A take room that is due opens (`take_opens`).** Its round is
opened like a shown room's, one empty id claim per window range. -/
theorem take_opens (ix : Index) (c : Conn) (r : Id) (now pf : Nat)
    (hp : c.peerFloor = some pf) (hr : r ∈ c.takes) (hn : has c.rooms r = false)
    (due : (c.due cfg r now || c.retake cfg r) = true) :
    (Msg.rbsr r (c.round + 1) ((window 0).map fun q => .ids q [])).op ∈
      (c.start cfg ix now).send := by
  have hm : r ∈ c.carried.filter fun r => c.due cfg r now || c.retake cfg r :=
    List.mem_filter.mpr ⟨List.mem_append_right _ hr, due⟩
  have hne : (c.carried.filter fun r => c.due cfg r now || c.retake cfg r).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hm)
  have hv : (Conn.view ix c r).opening cfg.params r (max c.floor pf) = fun q => .ids q [] :=
    funext (view_opening ix c hn cfg.params _)
  simp only [Conn.start, hp, hne, Bool.false_eq_true, ite_false, List.mem_map]
  exact ⟨r, hm, by rw [hv]⟩

/-- An answer batch's wants, as `onRbsr` reads them. -/
def outWants (outs : List Out) : List Id := outs.flatMap fun | .want xs => xs | _ => []

theorem blank_claims (P : Params) (Y : List Item) : ∀ w : List Range,
    claimsOf ((w.map fun q => Claim.ids q []).flatMap (answer Prod.fst Prod.snd sha256 P Y)) = []
  | [] => rfl
  | q :: t => by simpa [claimsOf, answer] using blank_claims P Y t

theorem blank_holds (P : Params) (Y : List Item) : ∀ w : List Range,
    ((w.map fun q => Claim.ids q []).flatMap (answer Prod.fst Prod.snd sha256 P Y)).flatMap holdIds =
      w.flatMap fun q => ((within Prod.fst q Y).map Prod.snd).reverse
  | [] => rfl
  | q :: t => by
    have ih := blank_holds P Y t
    have ht : (within Prod.fst q Y).filter (fun _ => true) = within Prod.fst q Y := List.filter_eq_self.2 (by simp)
    simp [answer, holdIds, ht, ih]

theorem blank_wants (P : Params) (Y : List Item) : ∀ w : List Range,
    outWants ((w.map fun q => Claim.ids q []).flatMap (answer Prod.fst Prod.snd sha256 P Y)) = []
  | [] => rfl
  | q :: t => by simpa [outWants, answer] using blank_wants P Y t

/-- **The peer that syncs a room answers a take room's opening with all
it holds there (`take_round_offers`).** A round of r opened with one
empty id claim per range of w, at a side that shows r, ends there, and
offers as haves every id of r's live index in those ranges (at the
round's floor, `Index.over`), newest first; it wants nothing. -/
theorem take_round_offers (ix : Index) (p : Conn) (r : Id) (k now : Nat) (w : List Range)
    (hr : has p.rooms r = true) (fresh : p.oldRound r k = false) (hw : w ≠ []) :
    (p.onRbsr cfg ix r k (w.map fun q => .ids q []) now).send =
      (Msg.rbsr r k []).op ::
        (chunks cfg (w.flatMap fun q => ((within Prod.fst q (ix.over cfg.params.depth r (p.beginRound k).roundFloor)).map Prod.snd).reverse) (.hold r) ++
          chunks cfg [] .want) := by
  have hc : (w.map fun q => Claim.ids q []).isEmpty = false := by
    cases w with
    | nil => exact absurd rfl hw
    | cons _ _ => rfl
  simp only [Conn.onRbsr, Conn.has_carried_eq, hr, Bool.true_or, Bool.not_true, Bool.false_eq_true,
    ite_false, fresh, hc, Conn.answer_shown hr, Index.answer_fun]
  have e : (Msg.rbsr r k []).op ::
      (chunks cfg (w.flatMap fun q => ((within Prod.fst q (ix.over cfg.params.depth r (p.beginRound k).roundFloor)).map Prod.snd).reverse) (.hold r) ++
        chunks cfg [] .want) =
      (Msg.rbsr r k (claimsOf ((w.map fun q => Claim.ids q []).flatMap
          (answer Prod.fst Prod.snd sha256 cfg.params (ix.over cfg.params.depth r (p.beginRound k).roundFloor))))).op ::
        (chunks cfg (((w.map fun q => Claim.ids q []).flatMap
            (answer Prod.fst Prod.snd sha256 cfg.params (ix.over cfg.params.depth r (p.beginRound k).roundFloor))).flatMap holdIds) (.hold r) ++
          chunks cfg (admitAsks cfg.maxKnown p.asked (outWants ((w.map fun q => Claim.ids q []).flatMap
            (answer Prod.fst Prod.snd sha256 cfg.params (ix.over cfg.params.depth r (p.beginRound k).roundFloor))))) .want) := by
    rw [blank_claims, blank_holds, blank_wants]
    simp [admitAsks]
  rw [e]
  dsimp only [outWants]
  split <;> rfl

end

end Engine.Sync
