/-
The app's navigation laws, over the running code: App.openSt, backSt and
switchSt, which openPage, back and switchToAcc run (and onPageAct's
channel, join, Stop waiting and removal steps through Nav too).

- `back_open`: **back goes back.** Back after opening a page that is
  neither shown nor under it gives the state before, but for what back
  always clears: the page's one-line field, refusal and viewport initialization. The composer's
  draft and everything else are as they were. `back_open_all` is the same
  for the switcher too, whose opening also composes the backdrop drawn
  behind it; `open_keeps_backdrop`: opening any other page keeps that
  backdrop.
- `shipped_back_open_fails`: the negative control, `openSt` as 566e566
  shipped it (opening any page emptied the switcher's backdrop), breaks
  `back_open`. This law caught it: see docs/CAUGHT.md.
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

/-- Back after opening any page, the switcher included: the state before,
but for what back clears and the backdrop opening the switcher composes
(drawn only on the switcher). -/
theorem back_open_all (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) :
    backSt (openSt p s) =
      { s with
        field := "", refusal := none, pageKey := none, pageScrollStarted := false,
        switcherBackdrop := (openSt p s).switcherBackdrop } := by
  have h := Nav.back_go p s.nav hp hs
  unfold backSt
  rw [nav_open, h]
  -- Name the backdrop, so `rfl` never unfolds the switcher's composition.
  generalize hb : (openSt p s).switcherBackdrop = b
  have ho : openSt p s = { s.withNav (Nav.go p s.nav) with
      refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := b } := by
    rw [← hb]; rfl
  rw [ho]
  rfl

/-- Opening any page but the switcher keeps the switcher's backdrop. -/
theorem open_keeps_backdrop (p : PageId) (s : St) (hw : p ≠ .switcher) :
    (openSt p s).switcherBackdrop = s.switcherBackdrop := by
  have hne : (p == PageId.switcher) = false := by simpa using hw
  simp only [openSt, hne]
  rfl

/-- **Back goes back.** -/
theorem back_open (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) (hw : p ≠ .switcher) :
    backSt (openSt p s) = { s with field := "", refusal := none, pageKey := none, pageScrollStarted := false } := by
  rw [back_open_all p s hp hs, open_keeps_backdrop p s hw]

/-- **Back at a root keeps the page.** -/
theorem back_root (s : St) (h : s.backStack = []) :
    backSt s = { s with field := "", refusal := none, pageKey := none, pageScrollStarted := false } := by
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

/-! ## Negative control: `openSt` as 566e566 shipped it

Opening any page but the switcher emptied the switcher's backdrop, so
switcher → gear (or Join, Create, Add members) → back drew the switcher
over the plain background instead of the dimmed screen behind it.
`back_open` stopped proving (its `rfl` timed out trying to equate the
composed backdrop with the old one), which is how it was found. Kept so
the law stays able to tell. -/

/-- `openSt` at 566e566. A mutant: nothing runs it. -/
def openStShipped (p : PageId) (s : St) : St :=
  let backdrop := if p == .switcher then
    match s.lastDisplay with
    | some (words, rows, top, bot) => Surface.compose words s.Hs s.bgRow rows top bot
    | none => #[]
    else #[]
  { s.withNav (Nav.go p s.nav) with
    refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := backdrop }

/-- The shipped `openSt` breaks `back_open` from every state that holds a
switcher backdrop, whichever other page is opened. -/
theorem shipped_back_open_fails (p : PageId) (s : St) (hw : p ≠ .switcher)
    (hb : s.switcherBackdrop ≠ #[]) :
    backSt (openStShipped p s) ≠
      { s with field := "", refusal := none, pageKey := none, pageScrollStarted := false } := by
  intro h
  have h2 := congrArg St.switcherBackdrop h
  have hne : (p == PageId.switcher) = false := by simpa using hw
  simp only [backSt, openStShipped, hne, St.withNav] at h2
  exact hb h2.symm

end NavLaws
