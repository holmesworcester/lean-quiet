/-
The app's navigation laws, over the running code: App.openSt, backSt and
switchSt, which openPage, back and switchToAcc run (and onPageAct's
channel, join, Stop waiting and removal steps through Nav too).

- `back_open`: **back goes back.** Back after opening a page that is
  neither shown nor under it gives the state before, but for what back
  always clears: the page's one-line field and refusal. The composer's
  draft and everything else are as they were.
- `back_root`: at a root, back keeps the page and the state.
- `back_switch`: after a switch, any number of backs stays on the new
  community's home: back never reaches the community before.
- `draft_open`, `draft_back`: no navigation step changes the composer's
  draft, its selection or its photos.
- `inv_open`, `inv_back`, `inv_switch`: no page is twice in the page and
  its stack; so (`depth`) after any open, fewer than 18 backs reach a root.
-/
import App

namespace NavLaws
open App

theorem nav_open (p : PageId) (s : St) : (openSt p s).nav = Nav.go p s.nav := rfl

theorem nav_back (s : St) : (backSt s).nav = Nav.back s.nav := rfl

theorem nav_switch (a : Engine.Id) (s : St) : (switchSt a s).nav = Nav.reset PageId.home := rfl

/-- **Back goes back.** -/
theorem back_open (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) :
    backSt (openSt p s) = { s with field := "", refusal := none, pageKey := none } := by
  have h := Nav.back_go p s.nav hp hs
  unfold backSt
  rw [nav_open, h]
  rfl

/-- **Back at a root keeps the page.** -/
theorem back_root (s : St) (h : s.backStack = []) :
    backSt s = { s with field := "", refusal := none, pageKey := none } := by
  have hb := Nav.back_root s.nav h
  unfold backSt
  rw [hb]
  rfl

theorem backs_root (k : Nat) (s : St) (h : s.backStack = []) :
    (Nat.repeat backSt k s).nav = s.nav := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (backSt (Nat.repeat backSt k s)).nav = s.nav
    rw [nav_back, ih]
    exact Nav.back_root s.nav h

/-- **A switch is a root.** However many times back is pressed after a
switch, the page is the new community's home, with nothing under it. -/
theorem back_switch (k : Nat) (a : Engine.Id) (s : St) :
    (Nat.repeat backSt k (switchSt a s)).nav = Nav.reset PageId.home :=
  (backs_root k (switchSt a s) rfl).trans (nav_switch a s)

/-- **Opening a page keeps the draft.** -/
theorem draft_open (p : PageId) (s : St) :
    (openSt p s).text = s.text ∧ (openSt p s).sel = s.sel ∧ (openSt p s).chips = s.chips :=
  ⟨rfl, rfl, rfl⟩

/-- **Back keeps the draft.** -/
theorem draft_back (s : St) :
    (backSt s).text = s.text ∧ (backSt s).sel = s.sel ∧ (backSt s).chips = s.chips :=
  ⟨rfl, rfl, rfl⟩

theorem inv_open (p : PageId) (s : St) (h : Nav.Inv s.nav) : Nav.Inv (openSt p s).nav :=
  Nav.go_inv p s.nav h

theorem inv_back (s : St) (h : Nav.Inv s.nav) : Nav.Inv (backSt s).nav :=
  Nav.back_inv s.nav h

theorem inv_switch (a : Engine.Id) (s : St) : Nav.Inv (switchSt a s).nav := by
  rw [nav_switch]; exact Nav.reset_inv _

theorem all_pages (p : PageId) : p ∈ PageId.all := by
  cases p <;> simp [PageId.all]

/-- **Back reaches a root** in fewer than 19 steps (there are 19 pages):
opening a page never stacks more. -/
theorem depth (p : PageId) (s : St) (h : Nav.Inv s.nav) : (openSt p s).backStack.length < PageId.all.length :=
  Nav.depth PageId.all all_pages (openSt p s).nav (inv_open p s h)

end NavLaws
