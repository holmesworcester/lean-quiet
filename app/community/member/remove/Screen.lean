import engine.renderer.Page

/-!
Removing a member: confirm, then the outcome.
-/

namespace Pages
open Paint Text Font Row

/-- Removing a member, asked twice (libquiet's): first what it does, then
that it cannot be undone; while it is written, that it is; a refusal
with its reason and Try again. Nothing is written before the second
confirmation (Remove.writes_only_after_two). -/
def removeConfirm {α : Type} [BEq α] [Inert α] (onYes : α) (onCancel : α) (f : Font) (dm : Dim) (W h : Nat) (name : String) (stage : Nat) (why : String) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let mut y := dm.px 24
  let (title, body) := match stage with
    | 1 => (s!"Remove {name}?",
            s!"{name} will stop receiving this community's messages once their devices learn of the removal. Copies they already have are not deleted.")
    | 2 => ("This can't be undone",
            s!"{name} can only come back with a new invitation, approved again.")
    | 3 => ("Removing…", s!"Telling the community that {name} is removed.")
    | _ => ("Couldn't remove", why)
  let (b1, hh) := heading f dm b title y
  y := y + hh + dm.px 12
  let (b2, ph) := para f dm b1 body (dm.px 24) y (W - dm.px 48) (if stage == 4 then (Palette.color dm.theme .error) else (Palette.color dm.theme .muted))
  b := b2
  y := y + ph + dm.px 32
  let mut taps := #[]
  match stage with
  | 1 =>
    let (b3, t1, h1) := button f dm b "Continue" y true onYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false onCancel
    b := b4; taps := #[t1, t2]
  | 2 =>
    let (b3, t1, h1) := dangerButton f dm b s!"Remove {name}" y onYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false onCancel
    b := b4; taps := #[t1, t2]
  | 3 => pure ()
  | _ =>
    let (b3, t1, h1) := dangerButton f dm b "Try again" y onYes
    let (b4, t2, _) := button f dm b3 "Cancel" (y + h1 + dm.px 12) false onCancel
    b := b4; taps := #[t1, t2]
  return ⟨b, taps⟩

end Pages
