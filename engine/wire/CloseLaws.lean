/-
Every finish, including transport loss, retirement and clock drops,
runs the same close step. It asks closing for the ids, purges them with
scrubbing enabled, and on held stores those local/conn ops are gone.
-/
import engine.wire.NodeLaws

namespace Engine.Sync

variable {F : Type}

/-- The step used for each ended session purges exactly closing's ids,
with scrubbing. This is independent of the reason it ended and the store. -/
theorem endSession_purges {m : Type → Type} [Monad m] [Store F m] [Turn F m]
    (x : Sync F m) (cid : Id) :
    Node.endSession x cid = (do
      let ids ← x.hooks.closing cid
      if !ids.isEmpty then Turn.purge x.fam ids true) := rfl

/-- No local or connection op named by closing survives the close step. -/
theorem close_gone (x : Sync F (HeldM F)) (cid : Id) (h : Held F) (ids : List Id)
    (hc : x.hooks.closing cid h = (ids, h)) (i : Id) (o : Op)
    (hi : i ∈ ids) (ho : h.db.ops i = some o) (hr : x.fam.room o = none) :
    ((Node.endSession x cid : HeldM F Unit) h).2.db.ops i = none := by
  have he : ids.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hi)
  rw [endSession_purges, HeldM.bind_apply, hc]
  simp only [he, Bool.not_false, ite_true]
  change (drainS x.fam _ (purgeS x.fam ids h.db)).ops i = none
  rw [drainS_ops]
  exact (purge_named (fam := x.fam) h.db hi ho hr).1

/-- The runner's finish executes the purge step for every drop, every
session removed from established, and every retirement. -/
theorem close_purges {m : Type → Type} [Monad m] [Store F m] [Turn F m]
    (x : Sync F m) (n : Node) (out : Acts) (now : Nat) :
    n.finish x out now = (do
      let (n, o) ← n.follow x now
      let (n, out) ← n.flush x out
      let retired ← x.hooks.retired
      let n := retired.foldl Node.drop n
      let out := { out ++ o with drop := (out ++ o).drop ++ retired }
      let sent ← n.seal x out
      let served ← n.seal x { send := out.serve }
      for cid in out.drop do
        (x.hooks.closing cid >>= fun ids =>
          if !ids.isEmpty then Turn.purge x.fam ids true else pure ())
      return ({ n with fresh := [] },
        { send := sent ++ served, drop := out.drop, stored := n.fresh, serve := served.length })) := rfl

end Engine.Sync
