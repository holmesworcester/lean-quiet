import app.community.Op
import engine.renderer.Chars

/-
A member's name: a register, the newest by (time, id) current.
-/

namespace Community
open Engine Codec

/-- A space of any kind (Unicode's White_Space), and the characters the
font draws as an empty cell (both Hangul fillers, five private-use
points): each draws as blank. The inkless check (platforms/headless/
Inkless) finds every inkless glyph of the font here or invisible. -/
def isBlank (c : UInt32) : Bool :=
  c == 32 || Text.inRange c 9 13 || c == 0x85 || c == 0xA0 || c == 0x1680 ||
  Text.inRange c 0x2000 0x200A || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000 ||
  c == 0x3164 || c == 0xFFA0 || c == 0xE16E || c == 0xE1A0 || c == 0xE900 || c == 0xEC71 || c == 0xED30

/-- What a name looks like: its words, without the characters drawn as
nothing (`Text.isInvisible`), split at spaces of any kind and joined by
one space. Two users whose names look alike by it are namesakes, and
both are marked (Kinds.Profile.namesake). -/
def look (s : String) : List UInt32 :=
  [32].intercalate ((((s.toList.map (·.val)).filter (!Text.isInvisible ·)).splitOnP isBlank).filter (!·.isEmpty))

def nameLook (s : String) : ByteArray := (String.mk ((look s).map fun c => Char.ofNat c.toNat)).toUTF8

namespace Profile

/-- What its author writes and signs. -/
structure Body where
  name : ByteArray
  time : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 7 (fun x => (x.name, x.time, x.sig)) (fun (p : B × Nat × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 7 :: Codec.enc (x.name, x.time, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `profile`. -/
structure Fact where
  c : Id
  u : Id
  name : ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 6 (fun x => (x.c, x.u, x.name, x.time)) (fun (p : B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 6 :: Codec.enc (x.c, x.u, x.name, x.time) := rfl

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`profile.*`) -/
def byUser : Rel Fact := ⟨"profile", "byUser", fun f => some [f.c, f.u]⟩
@[simp] theorem byUser_args (f : Fact) : byUser.args f = (some [f.c, f.u]) := rfl
def all : Rel Fact := ⟨"profile", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl
/-- By how the name looks: a name's namesakes. -/
def byLook : Rel Fact := ⟨"profile", "byLook", fun f => some [f.c, nameLook ((String.fromUTF8? f.name).getD "?")]⟩
@[simp] theorem byLook_args (f : Fact) : byLook.args f = (some [f.c, nameLook ((String.fromUTF8? f.name).getD "?")]) := rfl

end Profile

end Community
