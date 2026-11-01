import tests.engine.Checks
import tests.vacuity.RendererText
import app.community.channel.message.reaction.View
import app.community.channel.message.attachment.Screen
import app.community.channel.message.attachment.View

namespace Vacuity.ChatPresentation
open Engine Row RowLaws Arrival ArrivalLaws
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.defProp false

def f := Vacuity.RendererText.font
def dm : Row.Dim := { dpi := 160, cell := 20 }
def pic : Row.Pic := { hash := "attachment".toUTF8, w := 4032, h := 3024, len := 262144, got := 2, total := 4 }
def row : Row.RowData := { name := "Alice", avatar := none, text := "Hello Bob", time := 765, pics := [pic], tallies := [⟨"👍", 2, true⟩], pending := false, selected := false, namesake := true }

def pictureAspect := RowLaws.picBox_aspect dm 300 pic
def timestamp := RowLaws.time_shown f dm 400 row
def authorName := RowLaws.name_placed f dm 400 row
def duplicateLabel := RowLaws.twin_shown f dm 400 row

noncomputable def placed := Row.layout f dm 400 row
noncomputable def twin := placed.twin.getD (default, #[])
theorem twinPresent : placed.twin = some twin := by
  have h : placed.twin.isSome = true := by decide +kernel
  cases he : placed.twin with
  | none => simp [he] at h
  | some v => simp [twin, he]

def duplicateBeforeTime := RowLaws.twin_before_time f dm 400 row twinPresent

def authorStarts (f : Font.Font) := if h : (Row.layout f dm 400 row).name.size ≠ 0 then
  some (PLift.up (RowLaws.name_starts f dm 400 row h)) else none

def tappedLabel (f : Font.Font) : Option (PLift (∃ bx ln,
    (Row.layout f dm 400 row).twin = some (bx, ln) ∧
    Row.hit (Row.layout f dm 400 row) bx.x bx.y = .twin)) :=
  match hp : (Row.layout f dm 400 row).twin with
  | none => none
  | some (bx, ln) => if h : bx.has bx.x bx.y = true then
      some ⟨bx, ln, rfl, RowLaws.hit_twin hp h⟩ else none

def line : Text.Line := #[⟨65, 10⟩, ⟨66, 20⟩]
def flushed := RowLaws.flush_shows line

def reactions : List (String × Id) := [("👍", "alice".toUTF8), ("👍", "bob".toUTF8), ("👍", "alice".toUTF8), ("❤️", "bob".toUTF8)]
def noDuplicateReactors := RowLaws.tally_nodup reactions
def exactReactors := RowLaws.tally_mem reactions "👍" "alice".toUTF8
example : (Kinds.React.tally reactions).map (fun p => (p.1, p.2.length)) = [("👍", 2), ("❤️", 1)] := by decide +kernel
example : Row.clock row.time = "12:45" := by decide
example : Row.picBox dm 300 pic = (280, 210) := by decide

def zeroRing := ArrivalLaws.lit_zero 8 2 4 8 0
theorem growing : Arrival.lit 8 2 3 4 8 0 = true :=
  ArrivalLaws.lit_mono (got := 1) (by decide) (by decide)
def fullRing := ArrivalLaws.lit_full 8 2 4 8 0 (by decide)
theorem clockwise : Arrival.lit 8 2 3 4 8 0 = true :=
  ArrivalLaws.lit_clockwise (i := 15) (j := 8) (by decide) (by decide) (by decide)

def exactRing (f : Font.Font) : Option (PLift (∃ p, Arrival.layout f dm.arrival 0 0 280 210 2 4 262144 = some p ∧
    Arrival.lit dm.arrival.ring dm.arrival.stroke p.got p.total 7 0 = Arrival.lit dm.arrival.ring dm.arrival.stroke 2 4 7 0)) :=
  match hp : Arrival.layout f dm.arrival 0 0 280 210 2 4 262144 with
  | none => none
  | some p => some ⟨p, rfl, ArrivalLaws.ring_counts hp 7 0⟩
example : Arrival.caption 2 4 262144 = some "50% of 256 KiB" := by decide
example : Arrival.caption 4 4 262144 = none := by decide
example : Arrival.lit 8 2 0 4 8 0 = false := by decide
def main : IO UInt32 := do
  let t ← Tests.Checks.new
  let f ← Font.load "assets/font.bin" 160
  t.ok "nonempty author name starts at its box" (authorStarts f).isSome
  t.ok "duplicate label is tappable" (tappedLabel f).isSome
  t.ok "nonempty progress pill reflects counts" (exactRing f).isSome
  t.ok "name glyphs exist" ((Row.layout f dm 400 row).name.size > 0)
  t.ok "normal row omits duplicate label" ((Row.layout f dm 400 {row with namesake := false}).twin.isNone)
  t.ok "completed picture omits progress pill" ((Arrival.layout f dm.arrival 0 0 280 210 4 4 262144).isNone)
  return ← t.finish "chat presentation vacuity"
end Vacuity.ChatPresentation
