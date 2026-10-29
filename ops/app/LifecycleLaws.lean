/-
Laws at the app's call sites: an unmounted state's reads and writes are
pure no-ops; a callback from an earlier mount cannot execute even after
remount; checkpoints restore the page and anchor read by the app. Geometry
is quantified over every fitting viewport, including a changed keyboard.
-/
import App

namespace LifecycleLaws
open App Engine Data

/-- No query is run on behalf of an unmounted page. -/
theorem unmount_read (s : St) (q : Q) :
    (App.read q).run (unmountState s) = pure (default, unmountState s) := by rfl

/-- No write is submitted on behalf of an unmounted page. -/
theorem unmount_write (s : St) (w : Community.Write) :
    (App.writeAll w).run (unmountState s) = pure (false, unmountState s) := by rfl

/-- No old callback can read, paint or write after the page is remounted. -/
theorem old_callback (s : St) (action : M α) :
    (App.owned s.life.lease action).run { unmountState s with life := s.life.unmount.mount } =
      pure (none, { unmountState s with life := s.life.unmount.mount }) := by
  change (Lifecycle.owned s.life.unmount.mount s.life.lease action).run _ = _
  rw [Lifecycle.old_quiet]
  rfl

/-- The serialized op restores the page and anchor that the app saves.
This states the round trip at the call sites, not just for an arbitrary
codec; the native SQLite read/commit is tested separately. -/
theorem restore_page_anchor (s : St) :
    (Lifecycle.restore (Codec.encode (checkpoint s))).map (fun cp =>
      (PageId.ofCode cp.2.1, cp.2.2.2.1, cp.2.2.2.2.1)) =
    some (s.page, (s.mark.getD (.empty, 0)).1, (s.mark.getD (.empty, 0)).2) := by
  rw [Lifecycle.restore_checkpoint]
  by_cases h : s.me.acc.isEmpty <;> simp [checkpoint, stashDraft, h, page_round]

/-- The actual restore function returns the saved page and anchor. Real
anchors are op ids, which are nonempty; no saved anchor is also allowed. -/
theorem apply_page_anchor (s target : St)
    (valid : ∀ x off, s.mark = some (x, off) → x.isEmpty = false) :
    (applyCheckpoint target (checkpoint s)).page = s.page ∧
    (applyCheckpoint target (checkpoint s)).mark = s.mark := by
  cases ha : s.mark with
  | none =>
    by_cases h : s.me.acc.isEmpty <;>
      simp [applyCheckpoint, St.withNav, Nav.go_page, checkpoint, stashDraft, useDraft, h, ha, page_round] <;> rfl
  | some a =>
    rcases a with ⟨x, off⟩
    have hx := valid x off ha
    by_cases h : s.me.acc.isEmpty <;>
      simp [applyCheckpoint, St.withNav, Nav.go_page, checkpoint, stashDraft, useDraft, h, ha, hx, page_round]

/-- Both placement and page hit inversion hold at every fitting size,
without a portrait, DPI or keyboard-height restriction. -/
theorem viewport_geometry (g : Geometry.Geom) (fits : g.Fits) (over bf bn r y : Nat) :
    Geometry.Seam.place g over bf bn r = Geometry.Seam.home g bn (Geometry.Seam.frameRow g over bf r) ∧
    Geometry.Seam.tapRow g y = (y : Int) - g.top :=
  ⟨Geometry.placed_row g fits over bf bn r, Geometry.pinned_tap g fits y⟩

/-- A fitting viewport with a visible keyboard exists. -/
theorem viewport_possible : (Geometry.Geom.mk 1280 24 300 80 100).Fits := by
  unfold Geometry.Geom.Fits; decide

end LifecycleLaws
