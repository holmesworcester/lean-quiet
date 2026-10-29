/-
Full labels behind compact rows. The detail view wraps, pages through
every line, and copies the original string. `line_reachable` states
that every wrapped line has a page; `copy_exact` keeps the source text.
-/
import engine.renderer.Row

namespace Label
open Paint Font Row

def capacity (dm : Dim) (h : Nat) : Nat := max 1 ((h - dm.px 160) / dm.lineH)

def lines (f : Font) (dm : Dim) (W : Nat) (text : String) : Array Text.Line :=
  Text.layout f (W - 2 * dm.pad) text

def window (ls : Array Text.Line) (count page : Nat) : Array Text.Line :=
  ls.extract (page * count) ((page + 1) * count)

def copied (text : String) : String := text

theorem copy_exact (text : String) : copied text = text := rfl

theorem line_reachable (ls : Array Text.Line) (i count : Nat)
    (hc : 0 < count) (hi : i < ls.size) :
    (window ls count (i / count))[i % count]? = ls[i]? := by
  have hm := Nat.mod_lt i hc
  have hd := Nat.mod_add_div i count
  have he : i / count * count + i % count = i := by
    rw [Nat.mul_comm (i / count) count]; omega
  have hb : i % count < min ((i / count + 1) * count) ls.size - i / count * count := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  simp only [window, Array.getElem?_extract, if_pos hb, he]


def paint (f : Font) (dm : Dim) (W h : Nat) (text : String) (page : Nat) : Bitmap := Id.run do
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .bg) W)
  let ls := window (lines f dm W text) (capacity dm h) page
  for i in [0:ls.size] do
    b := b.line f ls[i]! dm.pad (dm.px 16 + i * dm.lineH) (Palette.color dm.theme .fg)
  return b

end Label
