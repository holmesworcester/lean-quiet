import app.Commands

/-! A nonempty two-query live cache. The snapshot is synthetic, and the
production cache laws say nothing here about native SQLite transactions. -/
namespace Vacuity.RendererLive
open Engine Data
attribute [local instance] LiveLaws.byteArray_lawful LiveLaws.listQ_lawful LiveLaws.q_lawful

def queryA : Q := .op (ByteArray.mk #[0x61])
def queryB : Q := .op (ByteArray.mk #[0x62])
def snapshot (q : Q) : Ans := if q == queryA then .bytes (some "hello".toUTF8) else .bytes none

def cacheA : Live := ({} : Live).store queryA (snapshot queryA)
def cache : Live := cacheA.store queryB (snapshot queryB)
private theorem agreesA : LiveLaws.Agrees cacheA snapshot :=
  LiveLaws.agrees_store (LiveLaws.agrees_empty snapshot) queryA

theorem empty : LiveLaws.Agrees {} snapshot := LiveLaws.agrees_empty snapshot

theorem store : LiveLaws.Agrees cache snapshot :=
  LiveLaws.agrees_store agreesA queryB

-- The two-entry cache answers queryB, and whatever it answers is the
-- moment's: no bytes (queryA's are "hello").
theorem cachedAnswer : cache.answer queryB = some (.bytes none) ∧
    ∀ a, cache.answer queryB = some a → a = .bytes none :=
  ⟨by simp [cache, cacheA, Live.store, Live.answer, snapshot, queryA, queryB],
   fun _ h => (LiveLaws.answer_agrees store h).trans (by simp [snapshot, queryA, queryB])⟩

-- A cache hit and a cache miss both produce the same synthetic moment.
theorem oneMoment :
    let r := (Live.readWith (m := _root_.Id) (fun q => pure (snapshot q)) queryA).run cache
    r.1 = snapshot queryA ∧ LiveLaws.Agrees r.2 snapshot :=
  LiveLaws.read_one_moment store queryA

theorem keep : LiveLaws.Agrees (cache.keep (fun q => q == queryA)) snapshot :=
  LiveLaws.agrees_keep store (fun q => q == queryA)

def dropped : Std.HashSet Q := Std.HashSet.ofList [queryB]
theorem unmount :
    LiveLaws.Agrees (cache.keep (fun q => !dropped.contains q)) snapshot ∧
    ∀ q, dropped.contains q = true → ∀ w, ¬ (cache.keep (fun q => !dropped.contains q)).subs.Has q w :=
  LiveLaws.agrees_unmount store dropped

def directCache : Live := { subs := ({} : Subs Q).add queryA (queryA.win (snapshot queryA)) }

private theorem watched : (directCache.keep (fun q => q == queryA)).subs.Has queryA (queryA.win (snapshot queryA)) := by
  exact (Subs.has_keep (I := directCache.subs) (fun q => q == queryA) queryA _).2
    ⟨(Subs.has_add (I := {}) queryA (queryA.win (snapshot queryA)) queryA _).2
      (Or.inr ⟨rfl, rfl⟩), by decide⟩

theorem watchedHeld : (fun q : Q => q == queryA) queryA = true :=
  LiveLaws.watched_held (fun q => q == queryA) watched

-- Holding an entry without its subscription fails agreement's index contract.
example : queryA != queryB := by decide

end Vacuity.RendererLive
