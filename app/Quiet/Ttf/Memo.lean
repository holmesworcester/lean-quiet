/-
The runtime memoization boundary beneath pure Paint. A private Source
gets a fresh identity at load, so keys distinguish font instances/sizes.
Source.bitmap is the single unsafe memoization seam. Its contract is exact
equality with Source.uncached, for every field and byte, independent of
cache state, call order and concurrent callers. The source/size are immutable.
Only lookup/put run under the mutex; parsing and raster work run outside it.
The miss path calls the ordinary raster and proved Cache.put. See NOTO.md
and the README seam: compiled memo/spec equivalence is tested, not proved.
-/
import Quiet.Ttf.Cache
import Std.Sync.Mutex

namespace Ttf.Memo

structure Source where
  private mk ::
  private uid : Nat
  private font : Thunk (Option Face)
  private size : Nat
  private cell : Nat
  deriving Inhabited

private structure State where
  cache : Cache.Store := Cache.empty
  hits : Nat := 0
  misses : Nat := 0
  peak : Nat := 0
  deriving Inhabited

private initialize shared : Std.Mutex State ← Std.Mutex.new {}
private initialize serial : Std.Mutex Nat ← Std.Mutex.new 1

/-- Parsing is pure and deferred until a glyph is actually painted. readHeader
checks tables/metrics; raster checks each requested outline, including cycles. -/
def source (bytes : ByteArray) (size cell : Nat) : BaseIO Source := do
  let uid ← serial.atomically do
    let n ← get
    set (n + 1)
    return n
  return ⟨uid, Thunk.mk fun _ => readHeader bytes, size, cell⟩

def Source.uncached (f : Source) (glyph : Nat) : Option Bitmap :=
  f.font.get >>= fun font => raster font glyph f.size f.cell

/-- Give the cache an exact-capacity coverage buffer, independent of the
raster builder's spare allocation capacity. -/
private def compact (b : Bitmap) : Bitmap := Id.run do
  let mut pixels := ByteArray.emptyWithCapacity b.pixels.size
  for v in b.pixels do pixels := pixels.push v
  return { b with pixels }

private def bitmapIO (f : Source) (glyph : Nat) : BaseIO (Option Bitmap) := do
  let key : Cache.Key := ⟨f.uid, glyph, f.size, f.cell⟩
  let found ← shared.atomically do
    let s ← get
    let found := Cache.get? s.cache key
    set { s with hits := s.hits + (if found.isSome then 1 else 0),
                 misses := s.misses + (if found.isNone then 1 else 0) }
    return found
  if found.isSome then return found
  let result := (f.uncached glyph).map compact
  if let some bitmap := result then
    shared.atomically do
      let s ← get
      let cache := Cache.put s.cache key bitmap
      set { s with cache, peak := max s.peak (Cache.bytes cache) }
  return result

private unsafe def bitmapImpl (f : Source) (glyph : Nat) : Option Bitmap :=
  unsafeBaseIO (bitmapIO f glyph)

@[implemented_by bitmapImpl] def Source.bitmap (f : Source) (glyph : Nat) : Option Bitmap :=
  f.uncached glyph

/-- Diagnostics do not retain a cache snapshot (and thus cannot retain
all the evicted pixels). -/
def stats : BaseIO (Nat × Nat × Nat × Nat × Nat) := shared.atomically do
  let s ← get
  return (s.hits, s.misses, Cache.bytes s.cache, s.peak, s.cache.index.size)

def clear : BaseIO Unit := shared.atomically (set ({} : State))

end Ttf.Memo
