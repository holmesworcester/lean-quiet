/-
A message row's data is the view of the facts its ops hold, over the
running code (Kinds.Message.read, Kinds.Profile.read, Kinds.React.read),
read in a model: `Model`, where every list read answers as the engine's
`eval` of the store (the engine's laws, `eval_stable` and `view_stable`,
are what make the app's live cache answer the same).

- `profile_read`: a person's name is their newest Valid profile's, else
  "…" (and by Community.profile_authorized, only a device admitted into
  that user could have written it);
- `message_read`: a shown message is a Valid message fact of the store;
  its row's name is its author's (`profile_read`), its duplicate mark
  is the namesake read of its author (NamesakeLaws), its time is the time
  it claims, its text is its body opened with a content key this store
  holds, and its pills are `tally` of its reactions.

With Text's and Row's laws (the glyphs drawn are the text's, the name's
logical prefix, the clock of the time, a pill per emoji with distinct
reactors), that is message content from the store to the screen.
-/
import ops.community.message.View

namespace ViewLaws
open Engine Community Data Kinds

/-- The model: a list read is the engine's `eval` of a store. -/
abbrev Model := ReaderT (DB Fact) Id

instance : Reads Model where
  read q := fun db => match q with
    | .list q => .list (Engine.eval db q) []
    | .op _ => .bytes none

/-- A person's name, as the store holds it. -/
def nameIn (db : DB Fact) (c u : Id) : String :=
  match (Engine.eval db (profile.byUser.query [c, u] (limit := some 1))).rows.head? with
  | some (_, .profile _ _ n _) => Profile.bytesStr n
  | _ => "…"

/-- **A person's name is their newest profile's.** -/
theorem profile_read (db : DB Fact) (c u : Id) (deps : Array Q) :
    ((Profile.read (m := Model) c u deps).run db).1.name = nameIn db c u := by
  simp only [Profile.read, readList, nameIn, ReaderT.run, bind, ReaderT.bind, pure, ReaderT.pure, Reads.read]
  generalize (eval db (profile.byUser.query [c, u] (some 1))).rows.head? = r
  rcases r with _ | ⟨p, f⟩
  · rfl
  · cases f <;> rfl

theorem pure_none_ne {α : Type} (db : DB Fact) (x : α) :
    (ReaderT.pure none : Model (Option α)) db ≠ some x := by intro h; cases h

theorem id_bind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

/-- One fact, as the store holds it. -/
def factIn (db : DB Fact) (x : Id) : Option Fact :=
  (Engine.eval db { key := opKey x, limit := some 1 }).rows.head?.map (·.2)

/-- The first row of key.byId [kid], as the store holds it. -/
def keyIn (db : DB Fact) (kid : ByteArray) : Option Fact :=
  (Engine.eval db (key.byId.query [kid] (limit := some 1))).rows.head?.map (·.2)

/-- **A shown message is the store's.** If its row has data, the message
is a fact of the store; the row's name is its author's name, its time
the time it claims, and its text its body opened with a key the store
holds under the message's key id. -/
theorem message_read (db : DB Fact) (c me msg : Id) (d : Row.RowData) (deps : Array Q)
    (h : (Message.read (m := Model) c me msg).run db = some (d, deps)) :
    ∃ c' u dev kid sealed n tm, factIn db msg = some (.message c' u dev kid sealed n tm) ∧
      d.name = nameIn db c u ∧ d.time = tm ∧
      (∃ deps', d.namesake = ((Profile.namesake (m := Model) c u d.name deps').run db).1) ∧
      ∃ x y k, keyIn db kid = some (.key x y k) ∧
        (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr = some d.text := by
  simp only [Message.read, readFact, readList, ReaderT.run, bind, ReaderT.bind, pure, ReaderT.pure,
    Reads.read] at h
  generalize hf : Option.map (fun x => x.snd) (eval db { key := opKey msg, limit := some 1 }).rows.head? = fo at h
  rcases fo with _ | f
  · exact absurd h (pure_none_ne _ _)
  cases f
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i c' u dev kid sealed n tm
  simp only [ReaderT.bind, ReaderT.pure, id_bind] at h
  generalize hk : (eval db (key.byId.query [kid] (some 1))).rows.head? = kr at h
  rcases kr with _ | ⟨p, kf⟩
  · exact absurd h (pure_none_ne _ _)
  cases kf
  all_goals dsimp only at h
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i x y k
  generalize ht : Option.map Profile.bytesStr (openSealed cryptoSeal c kid sealed k) = tx at h
  rcases tx with _ | text
  · dsimp only at h; exact absurd h (pure_none_ne _ _)
  simp only [ReaderT.bind, ReaderT.pure, id_bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  refine ⟨c', u, dev, kid, sealed, n, tm, by simpa [factIn] using hf, profile_read db c u _, rfl,
    ⟨_, rfl⟩, x, y, k, by simp [keyIn, hk], ht⟩

/-- The running message component reads only its own fact and content
key. Its author is an identity for a child, never a profile subscription. -/
theorem message_own (db : DB Fact) (msg : Id) (d : Row.RowData) (deps : Array Q)
    (h : (Message.readOwn (m := Model) msg).run db = some (d, deps)) :
    ∃ c u dev kid sealed n tm,
      factIn db msg = some (.message c u dev kid sealed n tm) ∧
      d.author = u ∧ d.time = tm ∧
      deps = #[Q.get msg, .list (key.byId.query [kid] (limit := some 1))] ∧
      ∃ x y k, keyIn db kid = some (.key x y k) ∧
        (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr = some d.text := by
  simp only [Message.readOwn, readFact, readList, ReaderT.run, bind, ReaderT.bind,
    pure, ReaderT.pure, Reads.read] at h
  generalize hf : Option.map (fun x => x.snd)
    (eval db { key := opKey msg, limit := some 1 }).rows.head? = fo at h
  rcases fo with _ | f
  · exact absurd h (pure_none_ne _ _)
  cases f
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i c u dev kid sealed n tm
  simp only [ReaderT.bind, ReaderT.pure, id_bind] at h
  generalize hk : (eval db (key.byId.query [kid] (some 1))).rows.head? = kr at h
  rcases kr with _ | ⟨p, kf⟩
  · exact absurd h (pure_none_ne _ _)
  cases kf
  all_goals dsimp only at h
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i x y k
  generalize ht : Option.map Profile.bytesStr (openSealed cryptoSeal c kid sealed k) = tx at h
  rcases tx with _ | text
  · dsimp only at h; exact absurd h (pure_none_ne _ _)
  simp only [ReaderT.bind, ReaderT.pure, id_bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c, u, dev, kid, sealed, n, tm, by simpa [factIn] using hf,
    rfl, rfl, rfl, x, y, k, by simp [keyIn, hk], ht⟩

end ViewLaws
