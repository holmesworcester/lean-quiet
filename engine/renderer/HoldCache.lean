/- One cached period of the existing message placeholder pixels. The frame
still expands row references to its current height. No font or IO inputs. -/
import engine.renderer.Hold

namespace Hold

/-- Every input read by messageLine; font cell and transient hover are absent. -/
structure MessageKey where
  bgRow : ByteArray
  width : Nat
  dpi : Nat
  theme : Theme.Value
  deriving DecidableEq

def MessageKey.ofState (s : St) : MessageKey := ⟨s.bgRow, s.W, s.dim.dpi, s.dim.theme⟩

def MessageKey.state (k : MessageKey) : St := ⟨k.bgRow, ⟨k.dpi, 0, k.theme, none⟩, k.width⟩

def MessageKey.rows (k : MessageKey) : Array ByteArray :=
  (Array.range (period k.state.dim)).map fun i => messageLine k.state i

/-- The invariant is erased at runtime. A caller cannot supply arbitrary pixels
for a matching key: every constructor must establish the exact generator result. -/
structure MessageTile where
  key : MessageKey
  rows : Array ByteArray
  exact : rows = key.rows

def MessageTile.make (key : MessageKey) : MessageTile := ⟨key, key.rows, rfl⟩

abbrev MessageCache := Option MessageTile

/-- One entry is enough: layout/density/theme changes replace it. -/
def MessageCache.prepare (cache : MessageCache) (s : St) : MessageTile :=
  let key := MessageKey.ofState s
  match cache with
  | some old => if old.key = key then old else MessageTile.make key
  | none => MessageTile.make key

def MessageTile.plane (tile : MessageTile) (height : Nat) : Array ByteArray :=
  let n := period tile.key.state.dim
  (Array.range (height + n)).map fun i => tile.rows[i % n]!

/-- Runtime entry point: return the exact original plane and the one-entry cache
for the following frame. Height changes reuse the same pixel period. -/
def cachedMessagePlane (cache : MessageCache) (s : St) (height : Nat) :
    Array ByteArray × MessageCache :=
  let tile := cache.prepare s
  (tile.plane height, some tile)

end Hold
