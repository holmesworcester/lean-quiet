import ops.app.Pics

set_option linter.defProp false
namespace Vacuity.RendererPics
open Engine Paint

def picture : Row.Pic := { hash := ByteArray.mk #[42], w := 2, h := 1, len := 8, preview := ByteArray.mk #[1, 2], got := 2, total := 2, chunks := [ByteArray.mk #[7], ByteArray.mk #[8]] }
def bitmap : Bitmap := Bitmap.blank 2 1 (solid 0xFFFFFF 2)
def task : Task Bitmap := Task.pure bitmap

def steady : Pics.World := { imgs := fun _ => some task, retry := fun _ => none, frames := 10, done := fun _ => false, store := fun _ => none }
def fresh : Pics.World := { imgs := fun _ => none, retry := fun _ => none, frames := 10, done := fun _ => false, store := fun _ => none }

-- A real pre-existing task suppresses a start which would charge a spawn.
def started := Pics.decoded_started (picture.hash.push 0, 2, 1)
  (fun _ => Pics.startPre picture 2 1 .dark) steady (t := task) rfl

private theorem isSteady : Pics.Steady picture 2 1 steady := by
  constructor
  · intro hp; trivial
  · intro hc; exact Or.inl (by trivial)
def noWork := Pics.image_steady (theme := .dark) picture 2 1 steady isSteady

def settles := Pics.image_settles (theme := .dark) picture 2 1 fresh
def twice := Pics.image_twice (theme := .dark) picture 2 1 fresh

end Vacuity.RendererPics
