/-
The desktop root's laws over App's running frame.

- `pinned_bottom`: pinned to the newest message, the scrollbar's thumb rests
  on the bottom of its track (the bar App's state gives `Desktop.scrollbar`).
- `settled_no_hold`: once `framePainted` holds (what `settleFrame` waits for
  after a resize), no position of the list frame App.listFrame draws
  shows a row's placeholder: the frame shown at a new size is never one
  whose rows flash to placeholders.
- `no_sidebar_outside_community`, `stage_full_window`: until the node is a
  member of a community, and on every stage (Get started, the join and
  create doors, waiting), the running driver's tracks are one pane over
  the whole window: no sidebar and no drawer, at any width or zoom.
- `no_sidebar_controls`: then no control the driver hit-tests is a
  sidebar control, so nothing of a sidebar can be clicked either.
- `member_sidebar`: a member off the stages, from 45rem, has the 220 px
  sidebar.
-/
import platforms.desktop.Driver
import engine.renderer.desktop.Laws
import engine.renderer.desktop.ZoomLaws

namespace Desktop

/-- **A settled frame holds no placeholder.** -/
theorem settled_no_hold (s : App.St) (h : framePainted s = true) (hc : s.page = .chat)
    (pad bottom : Nat) (more : Bool) (p j : Nat) :
    Cover.seen pad bottom more (App.frameSlice s s.b (App.bottoms s).1).2.1.toList p ≠ .hold j := by
  apply Cover.painted_no_hold
  intro r hr
  unfold framePainted at h
  simp only [hc, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h
  have := (Array.all_eq_true_iff_forall_mem.1 h.1) r (by simpa using hr)
  simpa using this

/-- **Pinned to the newest message, the thumb rests on the track's bottom**:
the bar `Desktop.scrollbar` returns for the running app (with no seek
pending: while one is, the thumb is where the drag put it). -/
theorem pinned_bottom (g : Layout) (s : App.St) (bar : Scrollbar.Bar) (hb : s.b = 0)
    (hs : s.seek = none) (h : scrollbar g s = some bar) :
    bar.thumb.y + bar.thumb.h = bar.track.y + bar.track.h := by
  unfold scrollbar at h
  split at h
  · simp at h
  · have hr := _root_.Scrollbar.ranks_newest (column s) (App.geom s).viewNow
    rcases hq : _root_.Scrollbar.ranks (column s) s.b (App.geom s).viewNow with ⟨n, k, r⟩
    rw [hb] at hq h
    rw [hq] at hr h
    simp only [hs] at hr h
    subst hr
    exact newest_bottom h

/-- **No community, no sidebar.** -/
theorem no_sidebar_outside_community (d : Driver) (h : d.app.member = false) :
    d.layout = ⟨d.width, ⟨0, 0⟩, ⟨0, d.width⟩, ⟨d.width, 0⟩⟩ := by
  simp [Driver.layout, App.St.shell, h, zoomLayout]

/-- **Stages fill the window**, for a member too (libquiet walks the doors
to another community full-window, over the app). -/
theorem stage_full_window (d : Driver) (h : d.app.page.stage = true) :
    d.layout = ⟨d.width, ⟨0, 0⟩, ⟨0, d.width⟩, ⟨d.width, 0⟩⟩ := by
  simp [Driver.layout, App.St.shell, h, zoomLayout]

/-- **Nothing of a sidebar is clickable** without the shell: every control
the driver hit-tests (`scene`, which `tap` uses) is outside `.nav`. -/
theorem no_sidebar_controls (d : Driver) (h : d.app.shell = false)
    (c : Control Action) (hc : c ∈ scene d.layout d.height d.ui d.app) : c.pane ≠ .nav := by
  intro hp
  have hf : Fits d.layout d.height c.pane c.box (max 1 (d.app.dim.px 24)) := by
    simpa [scene, controls] using (List.mem_filter.mp hc).2
  have hl : d.layout = ⟨d.width, ⟨0, 0⟩, ⟨0, d.width⟩, ⟨d.width, 0⟩⟩ := by
    simp [Driver.layout, h, zoomLayout]
  rw [hl, hp] at hf
  simp [Fits, Layout.track] at hf
  omega

/-- **A member has the sidebar** off the stages, from 45rem. -/
theorem member_sidebar (d : Driver) (hm : d.app.member = true) (hs : d.app.page.stage = false)
    (hw : (720 * d.dpi + 80) / 160 ≤ d.width) :
    d.layout.nav = ⟨0, (220 * d.dpi + 80) / 160⟩ := by
  have : d.app.shell = true := by simp [App.St.shell, hm, hs]
  simp only [Driver.layout, this]
  exact zoom_shell_sidebar d.width d.dpi _ hw

end Desktop
