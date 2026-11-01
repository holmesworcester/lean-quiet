/- Stable shared log positions for the read-only Held catalog. -/
import engine.core.Catalog
import engine.sync.StoreEvolution

namespace Engine.Sync
variable {F : Type}

/-- The writer logs exactly the bytes it stores, not rejected duplicate ids. -/
def Held.LogAgrees (h : Held F) : Prop := ∀ o ∈ h.log, h.db.ops o.id = some o

theorem empty_log_agrees : ({} : Held F).LogAgrees := by
  intro o ho
  cases ho

theorem shared_log_turn (fam : Family F) (h : Held F) (ops : List Op) :
    Catalog.shared fam ((Turn.turn fam ops : HeldM F Unit) h).2 =
      Catalog.shared fam h ++ ops.filter (fun o => (fam.room o).isSome) := by
  simp only [Catalog.shared, turn_apply, List.filter_append]

/-- Purges do not renumber shared positions. Agreement is necessary here:
an arbitrary raw ingest history may contain shadow bytes for a colliding id,
whereas Node.write logs only the new absent operations it actually accepts. -/
theorem shared_log_purge (fam : Family F) (h : Held F) (ids : List Id) (scrub : Bool)
    (ha : h.LogAgrees) :
    Catalog.shared fam ((Turn.purge fam ids scrub : HeldM F Unit) h).2 = Catalog.shared fam h := by
  simp only [Catalog.shared, purge_apply, List.filter_filter]
  apply List.filter_congr
  intro o ho
  by_cases hs : (fam.room o).isSome = true
  · have hn : o.id ∉ purgeSet fam h.db ids := by
      intro hp
      obtain ⟨_, p, hp, hl⟩ := mem_purgeSet_iff.mp hp
      rw [ha o ho] at hp
      cases hp
      rw [hl] at hs
      cases hs
    have hb : has (purgeSet fam h.db ids) o.id = false :=
      Bool.eq_false_iff.mpr (fun hp => hn ((Engine.has_iff _ _).mp hp))
    simp [hs, hb]
  · simp [hs]

theorem purge_log_agrees (fam : Family F) (h : Held F) (ids : List Id) (scrub : Bool)
    (ha : h.LogAgrees) : (((Turn.purge fam ids scrub : HeldM F Unit) h).2).LogAgrees := by
  intro o ho
  rw [purge_apply] at ho ⊢
  obtain ⟨ho, hn⟩ := List.mem_filter.mp ho
  change (drainS fam _ _).ops o.id = some o
  rw [drainS_ops, purgeS_ops_not]
  · exact ha o ho
  · intro hm
    have := (Engine.has_iff _ _).mpr hm
    rw [this] at hn
    cases hn

/-- The actual deduplicating Node writer preserves log/store agreement.
This does not assume that hashes are globally injective. -/
theorem write_log_agrees (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    (hi : Inv x.fam h.db) (ha : h.LogAgrees) : ((n.write x ops h).2).LogAgrees := by
  rw [write_store]
  dsimp only
  split
  · exact ha
  · intro o ho
    rw [turn_apply] at ho ⊢
    simp only [drainS_ops]
    rcases List.mem_append.mp ho with ho | ho
    · exact foldl_ingest_keep _ (ha o ho)
    · obtain ⟨hnew, hdistinct⟩ := absentOf_new h.db ops
      exact (foldl_ingest_new x.fam hi (ops.foldl (absentStep h.db) []).reverse
        (fun q hq => hnew q (List.mem_reverse.mp hq))
        (by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hdistinct)).2.2 o ho

end Engine.Sync
