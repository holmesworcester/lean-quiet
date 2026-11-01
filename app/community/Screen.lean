import app.Commands
import engine.renderer.Row
import app.community.Proofs
import app.community.channel.message.View
import app.community.channel.message.attachment.View
import app.community.channel.message.attachment.chunk.View
import app.community.channel.message.reaction.View
import app.community.key.View
import app.community.member.join.accept.View
import app.community.profile.View

namespace Kinds.Message
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- The message op alone. Child collections and op components own all
profile, attachment and reaction reads; this view never subscribes to them. -/
def readOwn (msg : Id) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message c u _ kid sealed _ tm clump) := f | return none
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  let some text := (match ks.rows.head? with
    | some (_, .key _ _ k) => (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr
    | _ => none) | return none
  return some ({ name := "…", avatar := none, text, time := tm, pics := [], tallies := [],
                 pending, selected := false, author := u, clump }, deps)
end Kinds.Message
namespace Kinds.File
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

def read (c msg : Id) (deps : Array Q) (withProgress : Bool := true) : m (Array Row.Pic × Array Q) := do
  let (as, _, deps) ← readList (attachment.byMessage.query [c, msg] (limit := some maxShown) (desc := false)) deps
  let mut deps := deps
  let mut out := #[]
  for ((_, att), f) in as.rows do
    let .attachment _ _ _ root len kid sealed := f | continue
    let (ks, _, d1) ← readList (key.byId.query [kid] (limit := some 1)) deps
    deps := d1
    let some k := ks.rows.head?.bind fun (_, g) => match g with | .key _ _ k => some k | _ => none
      | continue
    let some (info, fk, fn) := openInfo c kid sealed k | continue
    -- The parent's layout manifest needs immutable dimensions/preview,
    -- never the offscreen child's changing chunk/progress subscriptions.
    let (p, d2) ← if withProgress then pic c att root len info fk fn deps else
      pure ({
        hash := root, w := info.w, h := info.h, len, preview := info.preview,
        key := fk, nonce := fn, attachment := att : Row.Pic }, deps)
    deps := d2
    out := out.push p
  return (out, deps)
end Kinds.File
namespace Kinds.Message
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

def read (c me msg : Id) (attachmentProgress : Bool := true) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message _ u _ kid sealed _ tm clump) := f | return none
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  -- no key here yet, or a body it does not open: not shown (the list
  -- leaves such messages out; this is the row's own check)
  let some text := (match ks.rows.head? with
    | some (_, .key _ _ k) => (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr
    | _ => none) | return none
  let (who, deps) ← Profile.read c u deps
  let (twin, deps) ← Profile.namesake c u who.name deps
  let (pics, deps) ← File.read c msg deps attachmentProgress
  let (tallies, deps) ← React.read c msg me deps
  return some (⟨who.name, none, text, tm, pics.toList, tallies, pending, false, twin, u, clump, false, false, false⟩, deps)
end Kinds.Message
namespace ViewLaws
open _root_.Engine _root_.Community _root_.Data _root_.Kinds

/-- **A person's name is their newest profile's.** -/
theorem profile_read (db : DB Fact) (c u : Id) (deps : Array Q) :
    ((Profile.read (m := Model) c u deps).run db).1.name = nameIn db c u := by
  simp only [Profile.read, readList, nameIn, ReaderT.run, bind, ReaderT.bind, pure, ReaderT.pure, Reads.read]
  generalize (eval db (profile.byUser.query [c, u] (some 1))).rows.head? = r
  rcases r with _ | ⟨p, f⟩
  · rfl
  · cases f <;> rfl

/-- **A shown message is the store's.** If its row has data, the message
is a fact of the store; the row's name is its author's name, its time
the time it claims, and its text its body opened with a key the store
holds under the message's key id. -/
theorem message_read (db : DB Fact) (c me msg : Id) (d : Row.RowData) (deps : Array Q)
    (h : (Message.read (m := Model) c me msg).run db = some (d, deps)) :
    ∃ c' u dev kid sealed n tm clump, factIn db msg = some (.message c' u dev kid sealed n tm clump) ∧
      d.name = nameIn db c u ∧ d.time = tm ∧
      (∃ deps', d.namesake = ((Profile.namesake (m := Model) c u d.name deps').run db).1) ∧
      ∃ x y k, keyIn db kid = some (.key x y k) ∧
        (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr = some d.text := by
  simp only [Message.read, readFact, readList, ReaderT.run, bind, ReaderT.bind, pure, ReaderT.pure,
    Reads.read] at h
  generalize hf : Option.map (fun x => x.snd) (eval db { key := opKey msg, limit := some 1 }).rows.head? = fo at h
  rcases fo with _ | f
  · exact absurd h (pure_none_ne _ _)
  cases f <;> (try (rename_i x; cases x))
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i c' u dev kid sealed n tm clump
  simp only [ReaderT.bind, ReaderT.pure, id_bind] at h
  generalize hk : (eval db (key.byId.query [kid] (some 1))).rows.head? = kr at h
  rcases kr with _ | ⟨p, kf⟩
  · exact absurd h (pure_none_ne _ _)
  cases kf <;> (try (rename_i x; cases x))
  all_goals dsimp only at h
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i x y k
  generalize ht : Option.map Profile.bytesStr (openSealed cryptoSeal c kid sealed k) = tx at h
  rcases tx with _ | text
  · dsimp only at h; exact absurd h (pure_none_ne _ _)
  simp only [ReaderT.bind, ReaderT.pure, id_bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  refine ⟨c', u, dev, kid, sealed, n, tm, clump, by simpa [factIn] using hf, profile_read db c u _, rfl,
    ⟨_, rfl⟩, x, y, k, by simp [keyIn, hk], ht⟩

/-- The running message component reads only its own fact and content
key. Its author is an identity for a child, never a profile subscription. -/
theorem message_own (db : DB Fact) (msg : Id) (d : Row.RowData) (deps : Array Q)
    (h : (Message.readOwn (m := Model) msg).run db = some (d, deps)) :
    ∃ c u dev kid sealed n tm clump,
      factIn db msg = some (.message c u dev kid sealed n tm clump) ∧
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
  cases f <;> (try (rename_i x; cases x))
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i c u dev kid sealed n tm clump
  simp only [ReaderT.bind, ReaderT.pure, id_bind] at h
  generalize hk : (eval db (key.byId.query [kid] (some 1))).rows.head? = kr at h
  rcases kr with _ | ⟨p, kf⟩
  · exact absurd h (pure_none_ne _ _)
  cases kf <;> (try (rename_i x; cases x))
  all_goals dsimp only at h
  all_goals try (exact absurd h (pure_none_ne _ _))
  rename_i x y k
  generalize ht : Option.map Profile.bytesStr (openSealed cryptoSeal c kid sealed k) = tx at h
  rcases tx with _ | text
  · dsimp only at h; exact absurd h (pure_none_ne _ _)
  simp only [ReaderT.bind, ReaderT.pure, id_bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c, u, dev, kid, sealed, n, tm, clump, by simpa [factIn] using hf,
    rfl, rfl, rfl, x, y, k, by simp [keyIn, hk], ht⟩
end ViewLaws
namespace Kinds.Profile
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- The community's present members: users with a live device (the
engine's `live`: admitted, and none of the device's users removed), with
those devices' node keys. Laws (PeopleLaws): `present_iff`,
`present_not_removed`. -/
def present (c : Id) : View Fact (List (Id × List Key)) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (byUser ls)

/-- **The people list by window**: the first n present members of c (in
`present`'s order), found among c's newest m admissions, each with the
node keys of their live devices among those; and whether those m were
all of c's admissions (then the window is `present`'s first n:
PeopleLaws.presentW_complete). It reads one list of m rows and each
row's liveness, never every admission (PeopleLaws.presentW_lists). -/
def presentW (c : Id) (n m : Nat) : View Fact (List (Id × List Key) × Bool) := do
  let a ← admission.all.read [c] (limit := some m)
  let ls ← live c a.rows
  pure ((byUser ls).take n, decide (a.rows.length < m))

/-- **The header's count, capped**: the present members of c among its
newest m admissions, at most `cap`; and whether those were all of c's
admissions (then it is the count, capped: PeopleLaws.presentCount_complete). -/
def presentCount (c : Id) (cap m : Nat) : View Fact (Nat × Bool) := do
  let (us, all) ← presentW c cap m
  pure (us.length, all)

/-- The present members of c with their profiles, for the people list
and its count. A removed member is not among them (their messages keep
their names: Message reads the profile by author). -/
def members (c : Id) : m (Array (Id × List Key × Data) × Array Q) := do
  let (ps, deps) ← readView (present c) #[]
  let mut deps := deps
  let mut out : Array (Id × List Key × Data) := #[]
  for (u, ds) in ps do
    let (p, d) ← read c u deps
    deps := d
    out := out.push (u, ds, p)
  return (out, deps)
end Kinds.Profile
namespace ViewLaws
open _root_.Engine _root_.Community _root_.Data _root_.Kinds

theorem others_iff (db : DB Fact) (c u k : Id) : ∀ (rows : List (Pos × Fact)) (deps : Array Q),
    ((Profile.others (m := Model) c u k rows deps).run db).1 = true ↔
      ∃ p c' u' n tm, (p, Fact.profile c' u' n tm) ∈ rows ∧ u' ≠ u ∧ nameLook (nameIn db c u') = k
  | [], deps => by simp [Profile.others, ReaderT.run, pure, ReaderT.pure]
  | (p, f) :: t, deps => by
    have ih := others_iff db c u k t
    cases f
    case ofProfile x =>
      obtain ⟨c', u', n, tm⟩ := x
      by_cases hu : u' = u
      · simp only [Profile.others, hu, ite_true]
        rw [ih]
        constructor
        · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
          exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
        · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
          rcases List.mem_cons.1 hm with he | hm
          · simp only [Prod.mk.injEq, Fact.profile.injEq] at he
            obtain ⟨-, -, rfl, -, -⟩ := he
            exact absurd rfl hne
          · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩
      · have hr := profile_read db c u' deps
        simp only [Profile.others, hu, ite_false, ReaderT.run, bind, ReaderT.bind, pure] at hr ⊢
        by_cases hk : nameLook ((Profile.read (m := Model) c u' deps) db).1.name = k
        · simp only [hk, ite_true]
          refine iff_of_true rfl ⟨p, c', u', n, tm, List.mem_cons_self .., hu, hr ▸ hk⟩
        · simp only [hk, ite_false]
          have := ih ((Profile.read (m := Model) c u' deps) db).2
          simp only [ReaderT.run] at this
          rw [this]
          constructor
          · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
            exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
          · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
            rcases List.mem_cons.1 hm with he | hm
            · simp only [Prod.mk.injEq, Fact.profile.injEq] at he
              obtain ⟨-, -, rfl, -, -⟩ := he
              exact absurd (hr ▸ hl) hk
            · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩
    all_goals
      simp only [Profile.others]
      rw [ih]
      constructor
      · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
        exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
      · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩
variable {s : DB Fact} {C : Crypto}

/-- **A row is marked exactly when its name has a namesake.** At rest,
the running read marks user u of c (whose row shows `nameIn s c u`)
exactly when another user of c has a Valid profile and a newest name
that looks the same. -/
theorem namesake_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) (deps : Array Q) :
    ((Profile.namesake (m := Model) c u (nameIn s c u) deps).run s).1 = true ↔
      ∃ u', u' ≠ u ∧ (∃ y n tm, V C s.ops y (.profile c u' n tm)) ∧
        nameLook (nameIn s c u') = nameLook (nameIn s c u) := by
  simp only [Profile.namesake, readList, ReaderT.run, bind, ReaderT.bind, Reads.read, pure, ReaderT.pure]
  have := others_iff s c u (nameLook (nameIn s c u))
    (Engine.eval s (profile.byLook.query [c, nameLook (nameIn s c u)])).rows
  simp only [ReaderT.run] at this
  rw [this]
  constructor
  · rintro ⟨p, c', u', n, tm, hm, hne, hl⟩
    obtain ⟨hv, ha⟩ := row_filed (C := C) (by simp [rels]) h hq hm
    obtain ⟨_, _, _, hf, -⟩ := byLook_args.1 ha
    simp only [Fact.profile.injEq] at hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    exact ⟨u', hne, ⟨p.2, n, tm, hv⟩, hl⟩
  · rintro ⟨u', hne, ⟨y, n, tm, hv⟩, hl⟩
    obtain ⟨p, n', tm', hv', hn⟩ := newest h hq hv
    have hm := at_row (C := C) (r := profile.byLook) (as := [c, nameLook (nameIn s c u)]) (desc := true)
      (by simp [rels]) h hq hv' (byLook_args.2 ⟨u', n', tm', rfl, by rw [← hl, hn]; rfl⟩)
    exact ⟨_, c, u', n', tm', hm, hne, hl⟩

/-- **A message row is marked Duplicate exactly when its author has a
namesake.** At rest, a shown message's row carries the mark exactly when
another user of the community has a Valid profile whose newest name
looks as its author's does. -/
theorem row_marked (h : Inv (family C) s) (hq : s.queue = []) {c me msg : Id} {d : Row.RowData}
    {deps : Array Q} (hr : (Message.read (m := Model) c me msg).run s = some (d, deps)) :
    ∃ c' u dev kid sealed n tm clump, factIn s msg = some (.message c' u dev kid sealed n tm clump) ∧
      (d.namesake = true ↔ ∃ u', u' ≠ u ∧ (∃ y n tm, V C s.ops y (.profile c u' n tm)) ∧
        nameLook (nameIn s c u') = nameLook (nameIn s c u)) := by
  obtain ⟨c', u, dev, kid, sealed, n, tm, clump, hf, hn, -, ⟨deps', hd⟩, -⟩ := message_read s c me msg d deps hr
  refine ⟨c', u, dev, kid, sealed, n, tm, clump, hf, ?_⟩
  rw [hd, hn]
  exact namesake_iff h hq c u deps'
end ViewLaws
namespace Kinds.File
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- The attachment component's own view. Its live subscriptions end when
its last visible/prefetch owner leaves, independently of its message. -/
def readOne (c att : Id) (withProgress : Bool := true) : m (Option Row.Pic × Array Q) := do
  let (fact, _, deps) ← readFact att #[]
  let some (.attachment _ _ _ root len kid sealed) := fact | return (none, deps)
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  let some key := ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => some k | _ => none
    | return (none, deps)
  let some (info, fk, fn) := openInfo c kid sealed key | return (none, deps)
  if !withProgress then
    return (some { hash := root, w := info.w, h := info.h, len, preview := info.preview,
                   key := fk, nonce := fn, attachment := att }, deps)
  let (p, deps) ← pic c att root len info fk fn deps
  return (some p, deps)
end Kinds.File
namespace Kinds.Accepted
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- The entries, as described above. Each entry's device is taken from
an entry of `known` with the same seed if there is one (the entries the
caller read last time), so a step derives no device it already holds. -/
def read (known : Array Me := #[]) : m (Array Me × Array Q) := do
  let (acc, _, deps) ← readList (accepted.all.query []) #[]
  let (jn, _, deps) ← readList (joining.all.query []) deps
  let mut deps := deps
  let mut out := #[]
  let mut seen : List Id := []
  for (_, f) in acc.rows do
    let .accepted c _ := f | continue
    if seen.contains c then continue
    seen := c :: seen
    -- this device's entry in c: the engine's choice (Community.mine), the
    -- one the node answers and dials as, so the two cannot disagree
    let (pick, d0) ← readView (Community.mine c) deps
    deps := d0
    -- not held: the entry a cut device had, read only to hide and tell it
    let pick ← match pick with
      | some p => pure (some p)
      | none => do
        let (cut, d1) ← readView (Community.cutEntry c) deps
        deps := d1
        pure cut
    let some (pk, accId) := pick | continue
    let (sec, _, d1) ← readList (secret.byKey.query [pk] (limit := some 1)) deps
    let (adm, _, d2) ← readList (admission.byDevice.query [c, pk] (limit := some 1)) d1
    let (nm, _, d3) ← readList (named.current.query [c] (limit := some 1)) d2
    deps := d3
    let some (_, .secret _ seed) := sec.rows.head? | continue
    let name := match nm.rows.head? with
      | some (_, .named _ _ n _) => (String.fromUTF8? n).getD "?"
      | _ => "Waiting to join"
    let admId := (adm.rows.head?.map (·.1.2)).getD .empty
    let user := match adm.rows.head? with | some (_, .admission _ u _ _) => u | _ => .empty
    -- waiting: this device's live join of c (the one Stop waiting stops)
    let mut joiningOp := ByteArray.empty
    let mut dialing := ""
    if admId.isEmpty then
      for ((_, jid), g) in jn.rows do
        let .joining c' _ hs _ _ d _ := g | continue
        if c' != c || d != pk then continue
        let (ab, _, d4) ← readList (abandoned.byJoining.query [jid] (limit := some 0)) deps
        deps := d4
        if ab.total == 0 then
          joiningOp := jid
          dialing := (hs.head?.bind String.fromUTF8?).getD ""
    let (live, d6) ← readView (Community.deviceLive c pk) deps
    deps := d6
    let removed := !admId.isEmpty && !live
    let dv := deviceOf known seed
    out := out.push { acc := accId, dev := dv.1, seed, dev_ok := dv.2, c, adm := admId, user, name, joiningOp,
                      dialing, removed }
  let sorted := out.qsort fun a b => a.name < b.name || (a.name == b.name && Engine.bcmp a.acc b.acc == .lt)
  return (dedupe sorted, deps)

/-- **Reading with the devices already held is reading**: `read known`
is `read` for every `known`, so its entries are the same; it only
derives no device it is given. -/
theorem read_known (known : Array Me) : (read known : m (Array Me × Array Q)) = read := by
  unfold read
  simp only [deviceOf_eq known #[]]

end Kinds.Accepted

section

/-
The people list is the community's present members, over the running
code (Kinds.Profile.present, which the people list and its count read):

- `present_iff`: at rest, a user is listed exactly when one of their
  devices is live: admitted, and none of the users it is admitted into
  removed (by the engine's `mem_live_all`), so the user is not removed
  either (`present_not_removed`): a removed member is in neither the
  list nor the count;
- `present_nodup`: each user is listed once, so the count is the number
  of people, not of devices.
-/

namespace PeopleLaws
open Engine Community Kinds

theorem byUser_mem (ls : List (Id × Key × Key)) (u : Id) :
    u ∈ (Kinds.Profile.byUser ls).map (·.1) ↔ ∃ d e, (u, d, e) ∈ ls := by
  simp only [Kinds.Profile.byUser, List.map_map, Function.comp_def, List.map_id']
  rw [RowLaws.uniq_mem]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨u', d, e⟩, hm, rfl⟩; exact ⟨d, e, hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨(u, d, e), hm, rfl⟩

/-- **The people list is exactly the present members.** -/
theorem present_iff {C : Community.Crypto} {s : DB Fact} (h : Inv (family C) s) (hq : s.queue = [])
    (c u : Id) :
    u ∈ ((Profile.present c).eval s).map (·.1) ↔ ∃ d e, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure]
  rw [byUser_mem]
  constructor
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).1 hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).2 hm⟩

/-- **A removed member is not listed.** -/
theorem present_not_removed {C : Community.Crypto} {s : DB Fact} (h : Inv (family C) s)
    (hq : s.queue = []) {c u : Id} (hp : u ∈ ((Profile.present c).eval s).map (·.1)) :
    ¬ Removed C s.ops c u := by
  obtain ⟨d, e, ha, hl⟩ := (present_iff h hq c u).1 hp
  exact hl.2 u e ha

/-- **Each person is listed once.** -/
theorem present_nodup (s : DB Fact) (c : Id) : (((Profile.present c).eval s).map (·.1)).Nodup := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure, Kinds.Profile.byUser,
    List.map_map, Function.comp_def, List.map_id']
  exact RowLaws.uniq_nodup _

/-! ## The people list by window, and its capped count -/

theorem uniq_cons {α : Type} [DecidableEq α] (x : α) (t : List α) :
    React.uniq (x :: t) = x :: React.uniq (t.filter fun y => !decide (y = x)) := by
  rw [React.uniq]

/-- The distinct of a prefix are a prefix of the distinct. -/
theorem uniq_prefix {α : Type} [DecidableEq α] : ∀ (l1 l2 : List α), React.uniq l1 <+: React.uniq (l1 ++ l2)
  | [], _ => by rw [React.uniq]; exact List.nil_prefix
  | x :: t, l2 => by
    rw [List.cons_append, uniq_cons, uniq_cons, List.filter_append]
    have : (t.filter fun y => !decide (y = x)).length < (x :: t).length :=
      Nat.lt_succ_of_le (List.length_filter_le _ _)
    exact (List.prefix_cons_inj x).2 (uniq_prefix _ _)
termination_by l1 => l1.length

/-- Liveness is per row: the live admissions of two runs of rows are
each's, in order. -/
theorem live_append (s : DB Fact) (c : Id) : ∀ (l1 l2 : List (Pos × Fact)),
    (live c (l1 ++ l2)).eval s = (live c l1).eval s ++ (live c l2).eval s
  | [], l2 => by simp only [List.nil_append, live]; rfl
  | (p, f) :: t, l2 => by
    have ih := live_append s c t l2
    cases f
    case ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      simp only [List.cons_append, live]
      split
      · rw [View.eval_bind', View.eval_bind', View.eval_bind', View.eval_bind', ih]
        show (if _ then _ else _) = (if _ then _ else _) ++ _
        split <;> simp
      · exact ih
    all_goals simpa [live] using ih

/-- A list of at most m rows is the first m of the whole list. -/
theorem all_take (s : DB Fact) (c : Id) (m : Nat) :
    ((admission.all.read [c] (limit := some m)).eval s).rows = ((admission.all.read [c]).eval s).rows.take m := rfl

theorem byUser_users (ls : List (Id × Key × Key)) : (Kinds.Profile.byUser ls).map (·.1) = React.uniq (ls.map (·.1)) := by
  simp only [Kinds.Profile.byUser, List.map_map, Function.comp_def, List.map_id']

/-- **The window lists `present`'s first members, in its order**: its
users are a prefix of the people list's. -/
theorem presentW_prefix (s : DB Fact) (c : Id) (n m : Nat) :
    ((Profile.presentW c n m).eval s).1.map (·.1) <+: ((Profile.present c).eval s).map (·.1) := by
  simp only [Profile.presentW, Profile.present, View.eval_bind, View.eval_pure]
  rw [all_take, List.map_take, byUser_users, byUser_users]
  conv => rhs; rw [← List.take_append_drop m ((admission.all.read [c]).eval s).rows]
  rw [live_append, List.map_append]
  exact (List.take_prefix _ _).trans (uniq_prefix _ _)

/-- **With all of c's admissions read, the window is `present`'s first n**,
keys and all. -/
theorem presentW_complete (s : DB Fact) (c : Id) (n m : Nat) (h : ((Profile.presentW c n m).eval s).2 = true) :
    ((Profile.presentW c n m).eval s).1 = ((Profile.present c).eval s).take n := by
  simp only [Profile.presentW, Profile.present, View.eval_bind, View.eval_pure] at h ⊢
  rw [all_take] at h ⊢
  have hl : ((admission.all.read [c]).eval s).rows.length < m := by
    have := of_decide_eq_true h
    rw [List.length_take] at this
    omega
  rw [List.take_of_length_le (l := ((admission.all.read [c]).eval s).rows) (by omega)]

/-- **The header's count is the people count, capped**, when all of c's
admissions were read. -/
theorem presentCount_complete (s : DB Fact) (c : Id) (cap m : Nat)
    (h : ((Profile.presentCount c cap m).eval s).2 = true) :
    ((Profile.presentCount c cap m).eval s).1 = min cap ((Profile.present c).eval s).length := by
  simp only [Profile.presentCount, View.eval_bind, View.eval_pure] at h ⊢
  rw [presentW_complete s c cap m h, List.length_take]

/-! ### What a window costs, against the whole list -/

/-- Whether a row is an admission into c. -/
def admIn (c : Id) (r : Pos × Fact) : Bool :=
  match r.2 with
  | .admission c' .. => decide (c' = c)
  | _ => false

theorem unremoved_lists (s : DB Fact) (c : Id) : ∀ (l : List (Pos × Fact)),
    View.listsAt s (unremoved c l) ≤ l.length
  | [] => by simp [unremoved, View.listsAt]
  | (p, f) :: t => by
    have ih := unremoved_lists s c t
    cases f
    case ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      simp only [unremoved]
      split
      · simp only [View.listsAt, List.length_cons]
        split
        · omega
        · simp [View.listsAt]
      · simp only [List.length_cons]; omega
    all_goals simp only [unremoved, List.length_cons]; omega

theorem deviceLive_lists (s : DB Fact) (c : Id) (d : Key) :
    1 ≤ View.listsAt s (deviceLive c d) ∧
      View.listsAt s (deviceLive c d) ≤ 1 + ((admission.byDevice.read [c, d]).eval s).rows.length := by
  simp only [deviceLive]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.byDevice.read [c, d]) = 1 := rfl
  rw [e1]
  generalize ((admission.byDevice.read [c, d]).eval s).rows = rs
  have := unremoved_lists s c rs
  constructor
  · omega
  · by_cases h : rs.isEmpty = true
    · rw [if_pos h, View.listsAt_pure]; omega
    · rw [if_neg h]; omega

/-- **Liveness costs at most 1 + D lists a row**, when no device is
admitted more than D times. -/
theorem live_lists_le (s : DB Fact) (c : Id) (D : Nat)
    (hD : ∀ d, ((admission.byDevice.read [c, d]).eval s).rows.length ≤ D) :
    ∀ (l : List (Pos × Fact)), View.listsAt s (live c l) ≤ l.length * (1 + D)
  | [] => by simp [live, View.listsAt]
  | (p, f) :: t => by
    have ih := live_lists_le s c D hD t
    cases f
    case ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      simp only [live]
      split
      · rw [View.listsAt_bind, View.listsAt_bind]
        have := (deviceLive_lists s c d).2
        have := hD d
        simp only [View.listsAt, List.length_cons, Nat.succ_mul]
        omega
      · simp only [List.length_cons, Nat.succ_mul]; omega
    all_goals simp only [live, List.length_cons, Nat.succ_mul]; omega

/-- **And at least a list for each admission into c.** -/
theorem live_lists_ge (s : DB Fact) (c : Id) :
    ∀ (l : List (Pos × Fact)), (l.filter (admIn c)).length ≤ View.listsAt s (live c l)
  | [] => by simp [live, View.listsAt]
  | (p, f) :: t => by
    have ih := live_lists_ge s c t
    cases f
    case ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      by_cases hc : c' = c
      · have hf : List.filter (admIn c) ((p, Fact.admission c' u d e) :: t) =
            (p, Fact.admission c' u d e) :: List.filter (admIn c) t := by
          simp [List.filter_cons, admIn, hc]
        have hl : live c ((p, Fact.admission c' u d e) :: t) = ((deviceLive c d).bind fun ok =>
            (live c t).bind fun rest => View.pure (if ok = true then (u, d, e) :: rest else rest)) := by
          simp only [live, if_pos hc]
        rw [hf, hl, View.listsAt_bind, View.listsAt_bind, List.length_cons]
        have := (deviceLive_lists s c d).1
        omega
      · have hf : List.filter (admIn c) ((p, Fact.admission c' u d e) :: t) = List.filter (admIn c) t := by
          simp [List.filter_cons, admIn, hc]
        have hl : live c ((p, Fact.admission c' u d e) :: t) = live c t := by simp only [live, if_neg hc]
        rw [hf, hl]; exact ih
    all_goals simpa [live, List.filter_cons, admIn] using ih

/-- The lists of the people list's views: one list of admissions, and
each one's liveness. -/
theorem presentW_lists_eq (s : DB Fact) (c : Id) (n m : Nat) :
    View.listsAt s (Profile.presentW c n m) =
      1 + View.listsAt s (live c ((admission.all.read [c] (limit := some m)).eval s).rows) := by
  simp only [Profile.presentW]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.all.read [c] (limit := some m)) = 1 := rfl
  rw [e1, View.listsAt_bindOp, View.listsAt_pure, Nat.add_zero]

theorem present_lists_eq (s : DB Fact) (c : Id) :
    View.listsAt s (Profile.present c) = 1 + View.listsAt s (live c ((admission.all.read [c]).eval s).rows) := by
  simp only [Profile.present]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.all.read [c]) = 1 := rfl
  rw [e1, View.listsAt_bindOp, View.listsAt_pure, Nat.add_zero]

/-- **A window costs O(m) lists, whatever the community's size**: one
list of at most m admissions, and each one's liveness. -/
theorem presentW_lists (s : DB Fact) (c : Id) (n m D : Nat)
    (hD : ∀ d, ((admission.byDevice.read [c, d]).eval s).rows.length ≤ D) :
    View.listsAt s (Profile.presentW c n m) ≤ 1 + m * (1 + D) := by
  rw [presentW_lists_eq]
  have h1 := live_lists_le s c D hD ((admission.all.read [c] (limit := some m)).eval s).rows
  have h2 : ((admission.all.read [c] (limit := some m)).eval s).rows.length ≤ m := by
    rw [all_take, List.length_take]; omega
  have h3 := Nat.mul_le_mul_right (1 + D) h2
  omega

/-- The mutant: the whole list reads a list for every admission into c,
the community's size, on every re-read. -/
theorem present_scans (s : DB Fact) (c : Id) :
    1 + (((admission.all.read [c]).eval s).rows.filter (admIn c)).length ≤ View.listsAt s (Profile.present c) := by
  rw [present_lists_eq]
  have := live_lists_ge s c ((admission.all.read [c]).eval s).rows
  omega

end PeopleLaws

end

section

/-
The community switcher's laws, over the running code (Kinds.Accepted's
`dedupe` and `select`, which App's `switchToAcc` and `refreshComms` call):

- `dedupe_nodup`: no two entries share an acceptance (op id);
- `dedupe_one_per_community`: no two entries share a community;
- `select_tapped`: selecting the acceptance of the entry tapped gives
  exactly that entry, however many entries share its community or name.

Before, entries were told apart by community id, and a device that had
joined one community twice could not reach its second entry.
-/

namespace Switch
open Kinds.Accepted

theorem dedupeBy_fresh (key : Me → Engine.Id) : ∀ (ms : List Me) (seen : List Engine.Id) (m : Me),
    m ∈ dedupeBy key ms seen → key m ∉ seen
  | [], _, _, h => by simp [dedupeBy] at h
  | x :: t, seen, m, h => by
    unfold dedupeBy at h
    split at h
    · exact dedupeBy_fresh key t seen m h
    · rename_i hx
      rcases List.mem_cons.1 h with rfl | h
      · intro hm; exact hx (List.any_eq_true.2 ⟨_, hm, by simp⟩)
      · have := dedupeBy_fresh key t (key x :: seen) m h
        exact fun hm => this (List.mem_cons_of_mem _ hm)

theorem dedupeBy_nodup (key : Me → Engine.Id) : ∀ (ms : List Me) (seen : List Engine.Id),
    ((dedupeBy key ms seen).map key).Nodup
  | [], _ => by simp [dedupeBy]
  | x :: t, seen => by
    unfold dedupeBy
    split
    · exact dedupeBy_nodup key t seen
    · simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, dedupeBy_nodup key t (key x :: seen)⟩
      rintro ⟨m, hm, he⟩
      exact dedupeBy_fresh key t (key x :: seen) m hm (he ▸ List.mem_cons_self)

theorem dedupeBy_sublist (key : Me → Engine.Id) : ∀ (ms : List Me) (seen : List Engine.Id),
    (dedupeBy key ms seen).Sublist ms
  | [], _ => by simp [dedupeBy]
  | x :: t, seen => by
    unfold dedupeBy
    split
    · exact (dedupeBy_sublist key t seen).cons x
    · exact (dedupeBy_sublist key t (key x :: seen)).cons₂ x

/-- **No two entries share an acceptance.** -/
theorem dedupe_nodup (ms : Array Me) : ((dedupe ms).toList.map (·.acc)).Nodup := by
  simpa [dedupe] using dedupeBy_nodup (·.acc) (dedupeBy (·.c) ms.toList []) []

/-- **No two entries share a community**: a device holds a community at
most once, on screen too. -/
theorem dedupe_one_per_community (ms : Array Me) : ((dedupe ms).toList.map (·.c)).Nodup := by
  have h := dedupeBy_nodup (·.c) ms.toList []
  have hs := (dedupeBy_sublist (·.acc) (dedupeBy (·.c) ms.toList []) []).map (·.c)
  simpa [dedupe] using h.sublist hs

theorem find_nodup : ∀ (l : List Me) (i : Nat) (hi : i < l.length), (l.map (·.acc)).Nodup →
    l.find? (fun m => decide (m.acc = l[i].acc)) = some l[i]
  | [], _, hi, _ => by simp at hi
  | x :: t, 0, _, _ => by simp
  | x :: t, i + 1, hi, hn => by
    have hi' : i < t.length := by simp at hi; omega
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have hne : x.acc ≠ t[i].acc := fun he => hn.1 ⟨t[i], List.getElem_mem hi', he.symm⟩
    simp only [List.find?_cons, List.getElem_cons_succ, hne, decide_false]
    exact find_nodup t i hi' hn.2

/-- **A tap selects the entry tapped.** -/
theorem select_tapped (ms : Array Me) (hn : (ms.toList.map (·.acc)).Nodup) (i : Nat) (hi : i < ms.size) :
    select ms ms[i].acc = some ms[i] := by
  unfold select
  rw [← Array.find?_toList]
  have := find_nodup ms.toList i (by simpa using hi) hn
  simpa using this

/-- And on the entries the app holds (`Accepted.read` returns `dedupe`'s). -/
theorem select_tapped_dedupe (ms : Array Me) (i : Nat) (hi : i < (dedupe ms).size) :
    select (dedupe ms) (dedupe ms)[i].acc = some (dedupe ms)[i] :=
  select_tapped _ (dedupe_nodup ms) i hi

end Switch

end
