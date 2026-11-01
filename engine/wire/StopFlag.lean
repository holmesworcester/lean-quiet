/- A one-way cross-thread cancellation token. Direct IO.Ref.set can be
lost to an overlapping IO.Ref.get in the pinned Lean runtime. A short mutex
critical section protects every access; no native IO or user callback runs
while the token's lock is held. -/
import Std.Sync.Mutex

namespace Engine.Sync

structure StopFlag where private mk ::
  private state : Std.Mutex Bool

def StopFlag.new : IO StopFlag := do
  return ⟨← Std.Mutex.new false⟩

/-- Read without replacing a concurrent stop request. -/
def StopFlag.get (flag : StopFlag) : IO Bool :=
  flag.state.atomically (getThe Bool)

/-- The only state change is false to true. Repeating a stop is harmless. -/
def StopFlag.request (flag : StopFlag) : IO Unit :=
  flag.state.atomically (set true)

end Engine.Sync
