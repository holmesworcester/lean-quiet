/-
Character classes the renderer draws by, with no font: marks (no
advance) and characters drawn as nothing. Text draws by them, and a
profile's name is keyed by them (Community.nameLook), so what counts as
invisible is one definition.
-/
namespace Text

def inRange (c lo hi : UInt32) : Bool := lo ≤ c && c ≤ hi

/-- Marks: no advance, drawn on the glyph before. -/
def isMark (c : UInt32) : Bool :=
  inRange c 0x0300 0x036F || inRange c 0x0483 0x0489 || inRange c 0x0591 0x05BD ||
  c == 0x05BF || inRange c 0x05C1 0x05C2 || inRange c 0x05C4 0x05C5 || c == 0x05C7 ||
  inRange c 0x0610 0x061A || inRange c 0x064B 0x065F || c == 0x0670 ||
  inRange c 0x06D6 0x06DC || inRange c 0x06DF 0x06E4 || inRange c 0x06E7 0x06E8 ||
  inRange c 0x06EA 0x06ED || c == 0x0E31 || inRange c 0x0E34 0x0E3A || inRange c 0x0E47 0x0E4E ||
  inRange c 0x1AB0 0x1AFF || inRange c 0x1DC0 0x1DFF || inRange c 0x20D0 0x20FF ||
  inRange c 0xFE20 0xFE2F

/-- Drawn as nothing at all. -/
def isInvisible (c : UInt32) : Bool :=
  inRange c 0x200B 0x200F || inRange c 0x2060 0x2064 || inRange c 0xFE00 0xFE0F ||
  c == 0xFEFF || inRange c 0x1F3FB 0x1F3FF

end Text
