import app.Commands
import engine.renderer.Row
import engine.renderer.Brand
import app.community.Proofs
import app.community.channel.message.View
import app.community.channel.message.attachment.View
import app.community.channel.message.attachment.chunk.View
import app.community.channel.message.reaction.View
import app.community.key.View
import app.community.member.join.accept.View
import app.community.profile.View
import app.community.member.invite.request.Op
import app.community.channel.message.reaction.Op
import app.community.Family
import app.community.key.Op
import app.community.key.wrap.Op
import app.community.channel.message.Op
import app.community.member.remove.Commands
import app.community.member.remove.Op
import app.community.member.admin.Op
import app.community.member.join.joining.abandon.Op
import app.community.Commands
import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.receipt.Op
import app.community.profile.Op
import app.community.device.secret.Op
import app.community.name.Op
import app.community.member.join.accept.Op
import app.community.member.invite.request.approve.Op
import app.community.member.remove.Proofs
import app.community.channel.message.attachment.Op
import app.community.device.endpoint.Op
import app.community.member.invite.Op
import app.community.member.join.joining.Op
import app.community.Op
import engine.renderer.Page

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
    | some (_, .key _ _ k) => (openStored cryptoSeal c kid sealed k).map Profile.bytesStr
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
    let .attachment _ _ _ root len _ kid sealed := f | continue
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
    | some (_, .key _ _ k) => (openStored cryptoSeal c kid sealed k).map Profile.bytesStr
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
holds under the message's key id. Not covered: that the message is of
community `c`. The fact's community `c'` is not tied to `c`, and
`Message.read` does not check it, so a message of another community
would show with names read in `c`. Nothing that runs calls
`Message.read`. -/
theorem message_read (db : DB Fact) (c me msg : Id) (d : Row.RowData) (deps : Array Q)
    (h : (Message.read (m := Model) c me msg).run db = some (d, deps)) :
    ∃ c' u dev kid sealed n tm clump, factIn db msg = some (.message c' u dev kid sealed n tm clump) ∧
      d.name = nameIn db c u ∧ d.time = tm ∧
      (∃ deps', d.namesake = ((Profile.namesake (m := Model) c u d.name deps').run db).1) ∧
      ∃ x y k, keyIn db kid = some (.key x y k) ∧
        (openStored cryptoSeal c kid sealed k).map Profile.bytesStr = some d.text := by
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
  generalize ht : Option.map Profile.bytesStr (openStored cryptoSeal c kid sealed k) = tx at h
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
        (openStored cryptoSeal c kid sealed k).map Profile.bytesStr = some d.text := by
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
  generalize ht : Option.map Profile.bytesStr (openStored cryptoSeal c kid sealed k) = tx at h
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
  let some (.attachment _ _ _ root len _ kid sealed) := fact | return (none, deps)
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
    let mut linking := false
    if admId.isEmpty then
      for ((_, jid), g) in jn.rows do
        let .joining c' _ hs _ nm d _ := g | continue
        if c' != c || d != pk then continue
        let (ab, _, d4) ← readList (abandoned.byJoining.query [jid] (limit := some 0)) deps
        deps := d4
        if ab.total == 0 then
          joiningOp := jid
          dialing := (hs.head?.bind String.fromUTF8?).getD ""
          linking := nm.isEmpty
    -- removed: a removal of the user read, never a liveness not yet seen
    let (cut, d6) ← readView (Community.deviceCut c pk) deps
    deps := d6
    let removed := !admId.isEmpty && cut
    let dv := deviceOf known seed
    out := out.push { acc := accId, dev := dv.1, seed, dev_ok := dv.2, c, adm := admId, user, name, joiningOp,
                      dialing, linking, removed }
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

/-- Unremoved is false only at an admission into c whose user has a
removal. -/
theorem unremoved_false (s : DB Fact) (c : Id) : ∀ (l : List (Pos × Fact)),
    (unremoved c l).eval s = false →
      ∃ p u d e, (p, Fact.admission c u d e) ∈ l ∧ (Engine.eval s (removals c u)).total ≠ 0
  | [] => by simp [unremoved, View.eval]
  | (p, f) :: t => by
    intro h
    have ih := unremoved_false s c t
    cases f
    case ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      by_cases hc : c' = c
      · subst hc
        by_cases h0 : (Engine.eval s (removals c' u)).total = 0
        · simp only [unremoved, ↓reduceIte, View.eval, h0] at h
          obtain ⟨p', u', d', e', hm, hr⟩ := ih h
          exact ⟨p', u', d', e', List.mem_cons_of_mem _ hm, hr⟩
        · exact ⟨p, u, d, e, List.mem_cons_self .., h0⟩
      · simp only [unremoved, if_neg hc] at h
        obtain ⟨p', u', d', e', hm, hr⟩ := ih h
        exact ⟨p', u', d', e', List.mem_cons_of_mem _ hm, hr⟩
    all_goals
      simp only [unremoved] at h
      obtain ⟨p', u', d', e', hm, hr⟩ := ih h
      exact ⟨p', u', d', e', List.mem_cons_of_mem _ hm, hr⟩

/-- **A device is cut only by a removal read**: `deviceCut` holds only
when the store holds one of the device's admissions into c and a removal
of that admission's user. So the app tells a member "You've been
removed" (`Accepted.read`'s `removed`) only from a removal op: an
admission not yet read, or a stale read of one, never makes it. -/
theorem deviceCut_removal (s : DB Fact) (c : Id) (d : Key)
    (h : (deviceCut c d).eval s = true) :
    ∃ p u d' e, (p, Fact.admission c u d' e) ∈ ((admission.byDevice.read [c, d]).eval s).rows ∧
      (Engine.eval s (removals c u)).total ≠ 0 := by
  simp only [deviceCut] at h
  rw [View.eval_bind] at h
  generalize ((admission.byDevice.read [c, d]).eval s) = a at h ⊢
  by_cases he : a.rows.isEmpty = true
  · simp [he] at h
  · rw [if_neg he, View.eval_bind] at h
    have hf : (unremoved c a.rows).eval s = false := by
      cases hv : (unremoved c a.rows).eval s <;> simp_all
    exact unremoved_false s c a.rows hf

/-- An entry's removed mark as 59fa463 shipped it: its admission read
(`admitted`), and then, in a read of its own, its device not live. The
negative control of `deviceCut_removal`. -/
def removedShipped (admitted : Bool) (s : DB Fact) (c : Id) (d : Key) : Bool :=
  admitted && !(deviceLive c d).eval s

/-- **And it told of removals no one made**: the app reads an entry's
admission and then its device's standing as two reads, which need not see
the same store. When the second does not yet hold the admission the first
found, the shipped mark says removed (the member told "You've been
removed", the entry's composer, link and profile forgotten) with no
removal read, while `deviceCut` says not. Found by the pixel gate: a
switcher over sixteen new communities showed "You've been removed from
Community 16" in about one run in six under load. -/
theorem shipped_removed_without_removal (s : DB Fact) (c : Id) (d : Key)
    (h : ((admission.byDevice.read [c, d]).eval s).rows = []) :
    removedShipped true s c d = true ∧ (deviceCut c d).eval s = false := by
  simp only [removedShipped, deviceLive, deviceCut, View.eval_bind, h,
    List.isEmpty_nil, ↓reduceIte, View.eval_pure, Bool.not_false, Bool.and_self, and_self]

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

/-- **A window costs O(m·D) lists, whatever the community's size**: one
list of at most m admissions, and each one's liveness, given at most D
admissions per device (`hD`). D is a premise: nothing in the app caps a
device's admissions, so the bound is O(m) only where D is bounded. -/
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

namespace Pages
open Paint Text Font Row

/-! ### Get started (libquiet `GetStarted.svelte` in its `Stage`)

Measured from libquiet's own render: a full-window stage on the panel
colour, a 60 px bar with nothing in it, and a column 24rem wide with
16 px gutters. The column stacks the lockup (252 × 72.5), the 28/34
title, the `Rows` card (1 px Gray 10 edge, radius 16, 48 px rows on
Gray 06 dividers) and the 12/16 caption, on 24 px gaps (8 above the
caption). Phones and narrow windows top-anchor it under the bar; from
45rem it is centred in the window below the bar (`margin: auto`). -/

/-- Get started's column, in device pixels on the page (whose first row
is `px 56` below the stage's top): its left edge and width, the lockup's
top, and the column's top in quarter CSS pixels below the stage's top,
from which every other box is snapped. -/
structure Start where
  col : Nat
  colW : Nat
  logoY : Nat
  top4 : Nat
  deriving Repr, BEq, Inhabited

/-- The card's top edge, in quarter CSS pixels below the stage's top. -/
def Start.card4 (g : Start) : Nat := g.top4 + 714

/-- The column's height in quarter CSS pixels with `lines` caption lines:
24 + 72.5 + 24 + 34 + 24 + 148 + 8 + 16·lines + 32. -/
def startBody (lines : Nat) : Nat := 1466 + 64 * lines

/-- Where the column starts, in quarter CSS pixels below the stage's top:
under the 60 px bar, and centred in the rest from 45rem when it fits. -/
def startTop (wide : Bool) (stage4 lines : Nat) : Nat :=
  if wide && 240 + startBody lines ≤ stage4 then 240 + (stage4 - 240 - startBody lines) / 2 else 240

def startGeom (dm : Dim) (W stage lines : Nat) : Start :=
  let bodyW := min W (dm.px 384)
  let top4 := startTop (dm.px 720 ≤ W) (stage * 640 / max 1 dm.dpi) lines
  let y (a : Nat) := dm.q a - dm.px 56
  { col := (W - bodyW + 1) / 2 + dm.px 16, colW := bodyW - 2 * dm.px 16, logoY := y (top4 + 96), top4 }

/-- The cell top that puts `size` px Noto text on the baseline CSS gives a
`line` px line box at quarter-pixel `top4` below the page's top
(ascender 1.069, descender 0.293; the cell's baseline is 4/5 down it). -/
def textTop (dm : Dim) (top4 size line : Nat) : Nat :=
  let base := ((top4.toFloat / 4 + line.toFloat / 2 + 0.388 * size.toFloat) * dm.dpi.toFloat / 160).round
  (base.toUInt64.toNat) - dm.px size * 4 / 5

/-- One line with 0.4 px after each cluster (each placed glyph), starting
`start` 1/64 px in; spacing and start are added in 1/64 px before glyph
origins are rounded, as the browser spaces them. -/
def spaced (f : Font) (dm : Dim) (t : String) (start : Nat := 0) : Line :=
  let fine := Text.oneLine (Text.metricFont f) (Text.metricWidth 100000) t
  Text.pixelLine (fine.mapIdx fun i g => { g with x := g.x + start + (i * 256 * dm.dpi + 800) / 1600 })

/-- Words wrapped at `w` with 0.4 px letter-spacing, the first line
starting `start` 1/64 px in, as the caption is. -/
def spacedLines (f : Font) (dm : Dim) (w : Nat) (s : String) (start : Nat := 0) : Array Line := Id.run do
  let width (t : String) (first : Bool) : Nat := Paint.Line.width f (spaced f dm t (if first then start else 0))
  let mut out : Array String := #[]
  let mut cur := ""
  for word in s.splitOn " " do
    let next := if cur.isEmpty then word else cur ++ " " ++ word
    if cur.isEmpty || width next out.isEmpty ≤ w then cur := next
    else out := out.push cur; cur := word
  if !cur.isEmpty then out := out.push cur
  return out.mapIdx fun i t => spaced f dm (if i == 0 then " " ++ t else t) (if i == 0 then start else 0)

/-- The caption's mark, as its own span: Noto Color Emoji at 12 px draws
its 136 × 128 picture at 12/109 px a unit (14 px tall, 101 of them above
the baseline) and advances 2550/2048 em, then the 0.4 px spacing. -/
def markCell (dm : Dim) : Nat := (12 * 128 * dm.dpi + 109 * 80) / (109 * 160)
def markAscent (dm : Dim) : Nat := (12 * 101 * dm.dpi + 109 * 80) / (109 * 160)
def markAdvance64 (dm : Dim) : Nat := (12 * 2550 * 64 * dm.dpi + 2048 * 80) / (2048 * 160) + (256 * dm.dpi + 800) / 1600

def betaWarning : String := "Quiet is in beta and shouldn't be used for activities requiring security."

/-- Get started's rows: libquiet's three, each a glyph, a label and the
chevron. Link devices opens this device's side of linking: scan or paste
the other device's link (docs/LINKING.md). -/
def startRows {α : Type} (onJoin onCreate onDevices : α) : Array (String × String × α) :=
  #[("person-add", "Join a community", onJoin), ("plus", "Create a new community", onCreate),
    ("devices", "Link devices", onDevices)]

/-- Row i's box: 48 CSS px under the card's 1 px top edge, 49 a row
(each later row's 1 px Gray 06 divider is above its box), each edge
snapped on its own as the browser snaps it, so no rounding accumulates. -/
def startRow (dm : Dim) (g : Start) (i : Nat) : Box :=
  let top := g.card4 + 4 + 196 * i
  ⟨g.col + dm.px 1, dm.q top - dm.px 56, g.colW - 2 * dm.px 1, dm.q (top + 192) - dm.q top⟩

/-- A divider's rows: the pixel(s) above row i, from its own snapped edges. -/
def startDivider (dm : Dim) (g : Start) (i : Nat) : Nat × Nat :=
  (dm.q (g.card4 + 196 * i) - dm.px 56, dm.q (g.card4 + 196 * i + 4) - dm.px 56)

/-- Get started's geometry with its caption wrapped (the caption's line
count is the only text measure the boxes depend on). -/
def startOf (f : Font) (dm : Dim) (W stage : Nat) : Start × Array Line :=
  let small := f.atSize (dm.px 12)
  let caption := spacedLines small dm (startGeom dm W stage 0).colW betaWarning (markAdvance64 dm)
  (startGeom dm W stage caption.size, caption)

/-- What a tap on Get started does: row i's box, row i's action. The
painter draws every row in exactly this box (`getStarted_taps`). -/
def startTaps {α : Type} (dm : Dim) (g : Start) (rows : Array (String × String × α)) : Array (Box × α) :=
  rows.mapIdx fun i (_, _, act) => (startRow dm g i, act)

/-- Get started's pixels for geometry g and its wrapped caption. -/
def startPaint {α : Type} (f : Font) (dm : Dim) (W h : Nat) (g : Start) (caption : Array Line)
    (rows : Array (String × String × α)) : Bitmap := Id.run do
  let px := dm.px
  let color := Palette.color dm.theme
  let small := f.atSize (px 12)
  let mut b := Bitmap.blank W h (solid (color .panel) W)
  let lw := (252 * dm.dpi).toFloat / 160
  b := b.mask (Brand.lockup lw ((W.toFloat - lw) / 2) g.logoY.toFloat) (color .accentInk)
  let title := (f.atSize (px 28)).medium
  -- centred in 1/64 px, then rounded once (as the browser centres it)
  let fine := Text.oneLine (Text.metricFont title) (Text.metricWidth g.colW) "Let’s get started..."
  -- on the window's centre line, which is the column's, also at odd widths
  let inset := (W * 64 - min (W * 64) (Paint.Line.width (Text.metricFont title) fine)) / 2
  let tl := Text.pixelLine (fine.map fun c => { c with x := c.x + inset })
  b := b.line title tl 0 (textTop dm (g.top4 + 482) 28 34 - px 56) (color .fg) (exactInk := true)
  let (c0, c1) := (dm.q g.card4 - px 56, dm.q (g.card4 + 592) - px 56)
  let (i0, i1) := (dm.q (g.card4 + 4) - px 56, dm.q (g.card4 + 588) - px 56)
  b := b.round g.col c0 (g.col + g.colW) c1 (px 16) (color .line)
  b := b.round (g.col + px 1) i0 (g.col + g.colW - px 1) i1 (px 15) (color .panel)
  let label := f.atSize (px 16)
  for i in [0:rows.size] do
    let some (glyph, text, _) := rows[i]? | continue
    let r := startRow dm g i
    let (d0, d1) := startDivider dm g i
    if i > 0 then b := b.fill r.x d0 (r.x + r.w) d1 (color .selected)
    if dm.hot r.x r.y r.w r.h then
      -- `.rows .row:hover`: Gray 06 over the row and its divider, inside
      -- the card's rounded inner edge
      let top := if i == 0 then r.y else d0
      b := if i == 0 then (b.round r.x r.y (r.x + r.w) (r.y + 2 * px 15) (px 15) (color .selected)).fill r.x (r.y + px 15) (r.x + r.w) (r.y + r.h) (color .selected)
        else if i + 1 == rows.size then (b.fill r.x top (r.x + r.w) (r.y + r.h - px 15) (color .selected)).round r.x (r.y + r.h - 2 * px 15) (r.x + r.w) (r.y + r.h) (px 15) (color .selected)
        else b.fill r.x top (r.x + r.w) (r.y + r.h) (color .selected)
    b := b.icon f glyph (r.x + px 16) (r.y + px 12) (px 24) (color .fg)
    let l := Text.oneLineFine label (r.w - px 112) text
    let rowTop4 := (r.y + px 56) * 640 / max 1 dm.dpi
    b := b.line label l (r.x + px 56) (textTop dm (rowTop4 + 44) 16 26 - px 56) (color .fg) (exactInk := true)
    b := b.icon f "chevron" (r.x + r.w - px 40) (r.y + px 12) (px 24) (color .fg)
  for i in [0:caption.size] do
    let top := textTop dm (g.top4 + 1338 + 64 * i) 12 16 - px 56
    if i == 0 then
      let mark := f.atSize (markCell dm)
      match (f.emoji.emojify #[0x26A0, Emoji.vs16])[0]? with
      | some c => b := b.emoji mark c g.col (top + px 12 * 4 / 5 - markAscent dm)
      | none => pure ()
    b := b.line small caption[i]! g.col top (color .muted) (exactInk := true)
  return b

/-- Get started (libquiet `2811:2550`): the lockup, the title, the rows
and the beta caption, on the panel colour. `stage` is the window's
height below the status bar. -/
def getStarted {α : Type} [BEq α] [Inert α] (onJoin onCreate onDevices : α) (f : Font) (dm : Dim)
    (W h stage : Nat) : PageOf α :=
  let rows := startRows onJoin onCreate onDevices
  let (g, caption) := startOf f dm W stage
  ⟨startPaint f dm W h g caption rows, startTaps dm g rows⟩

/-- Create a community: a heading, the name field, Continue. -/
def create {α : Type} [BEq α] [Inert α] (onContinue onField : α) (f : Font) (dm : Dim) (W h : Nat) (name : String) (focused : Bool) : PageOf α := Id.run do
  let mut b := blank W h dm.theme
  let (b1, hh) := heading f dm b "Create a community" (dm.px 24)
  let fy := dm.px 24 + hh + dm.px 40
  let (b2, ft, fh) := field f dm b1 fy name "Community name" focused false onField
  let (b3, bt, _) := button f dm b2 "Continue" (fy + fh + dm.px 24) (!name.trimAscii.isEmpty) onContinue
  b := b3
  return ⟨b, #[ft, bt]⟩

/-- The home band (the header layer): the community's avatar and name,
with the caret that opens the switcher, and my avatar on the right. -/
def homeBand (f : Font) (dm : Dim) (W insetTop : Nat) (name id me : String) (ownId : String := "") : Bitmap := Id.run do
  let px := dm.px
  let font := f.atSize (px 16)
  let h := insetTop + px 64
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .accent) W)
  for (text, identity, x) in [(name, id, px 16), (me, ownId, W - px 44)] do
    b := b.round x (insetTop + px 18) (x + px 28) (insetTop + px 46) (px 3) (Palette.avatar identity)
    let l := oneLine font (px 28) (String.ofList [(text.toList.headD '?').toUpper])
    b := b.line font l (x + (px 28 - Paint.Line.width font l) / 2) (insetTop + px 23) 0xffffff
  let title := oneLine font (W - px 124) name
  b := b.line font title (px 52) (insetTop + px 23) 0xffffff
  b := b.icon f "caret" (px 58 + Paint.Line.width font title) (insetTop + px 27) (px 12) 0xffffff
  b := b.round (W - px 25) (insetTop + px 39) (W - px 11) (insetTop + px 53) (px 7) (Palette.color dm.theme .accent)
  b := b.round (W - px 23) (insetTop + px 41) (W - px 13) (insetTop + px 51) (px 5) 0xebb449
  b := b.round (W - px 21) (insetTop + px 43) (W - px 15) (insetTop + px 49) (px 3) (Palette.color dm.theme .accent)
  return b

/-- One geometry for the mobile list and its child visibility declarations. -/
def homePeopleTop (dm : Dim) (waiting channels : Nat) : Nat :=
  dm.px 16 + (if waiting > 0 then dm.px 44 + dm.px 24 else 0) +
    dm.px 36 + channels * dm.px 36 + dm.px 32 + dm.px 36

def home {α : Type} [BEq α] [Inert α] (onStub : String → α) (onRequests : α) (onOpenChannel onPerson : Nat → α) (f : Font) (dm : Dim) (W h : Nat) (waiting : Nat) (channels : Array String)
    (people : Array (String × Bool)) (ids : Array String := #[]) : PageOf α := Id.run do
  let px := dm.px
  let font := f.atSize (px 14)
  let ink := Palette.color dm.theme .fg
  let muted := if dm.theme == .dark then 0xa0a0a0 else 0x767676
  let mut b := Bitmap.blank W h (solid (Palette.color dm.theme .accent) W)
  b := b.round 0 0 W (h + px 16) (px 16) (Palette.color dm.theme .panel)
  let mut taps := #[]
  let mut y := px 16
  if waiting > 0 then
    if dm.hot 0 y W (px 44) then b := b.fill 0 y W (y + px 44) (Palette.color dm.theme .selected)
    b := b.icon f "icon-people" (px 16) (y + px 12) (px 20) muted
    b := b.line font (oneLine font (W - px 120) "Waiting to join") (px 48) (y + px 14) ink
    b := badge font dm b waiting (W - px 16) (y + px 10)
    taps := taps.push (⟨0, y, W, px 44⟩, onRequests)
    y := y + px 68
  b := b.line font (oneLine font W "Channels") (px 16) (y + px 10) ink
  b := b.icon f "add" (W - px 32) (y + px 10) (px 16) ink
  taps := taps.push (⟨W - px 48, y, px 44, px 36⟩, onStub "Create channel")
  y := y + px 36
  for i in [0:channels.size] do
    if dm.hot 0 y W (px 36) then b := b.fill 0 y W (y + px 36) (Palette.color dm.theme .selected)
    b := b.icon f "hash" (px 16) (y + px 12) (px 12) muted
    b := b.line font (oneLine font (W - px 48) channels[i]!) (px 32) (y + px 10) ink
    taps := taps.push (⟨0, y, W, px 36⟩, onOpenChannel i)
    y := y + px 36
  y := y + px 32
  b := b.line font (oneLine font W "Direct messages") (px 16) (y + px 10) ink
  b := b.icon f "add" (W - px 32) (y + px 10) (px 16) ink
  taps := taps.push (⟨W - px 48, y, px 44, px 36⟩, onStub "Direct message")
  y := homePeopleTop dm waiting channels.size
  for i in [0:people.size] do
    let (name, isMe) := people[i]!
    if y + px 40 > h then break
    if dm.hot 0 y W (px 40) then b := b.fill 0 y W (y + px 40) (Palette.color dm.theme .selected)
    b := b.round (px 16) (y + px 8) (px 40) (y + px 32) (px 3) (Palette.avatar (ids[i]?.getD name))
    let initial := oneLine font (px 24) (String.ofList [(name.toList.headD '?').toUpper])
    b := b.line font initial (px 16 + (px 24 - Paint.Line.width font initial) / 2) (y + px 12) 0xffffff
    let l := oneLine font (W - px 96) name
    b := b.line font l (px 48) (y + px 12) ink
    if isMe then b := b.line font (oneLine font W "(you)") (px 52 + Paint.Line.width font l) (y + px 12) muted
    taps := taps.push (⟨0, y, W, px 40⟩, onPerson i)
    y := y + px 40
  return ⟨b, taps⟩

/-- One community in the switcher. -/
structure Entry where
  name : String
  /-- Its id's first eight hex digits (what a pending join shows). -/
  id8 : String
  unread : Nat
  current : Bool
  waiting : Bool
  deriving Inhabited

/-- The switcher's rows: the current entry first, then the others in, then
the pending joins; each with its index in the entries. A row's tap selects
by that index, never by what the row shows (two entries may show the same
name and community). Laws: `switcherOrder_sound` (each row's index is the
entry it draws) and `switcherOrder_complete` (every entry has a row). -/
def switcherOrder (es : Array Entry) : List (Nat × Entry) :=
  let ix := (List.range es.size).filterMap fun i => es[i]?.map (i, ·)
  ix.filter (·.2.current) ++ ix.filter (fun p => !p.2.current && !p.2.waiting) ++
    ix.filter (fun p => !p.2.current && p.2.waiting)

theorem ix_sound (es : Array Entry) {p : Nat × Entry}
    (h : p ∈ (List.range es.size).filterMap fun i => es[i]?.map (i, ·)) : es[p.1]? = some p.2 := by
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at h
  obtain ⟨i, _, e, he, rfl⟩ := h
  exact he

/-- **A row's index is the entry it draws.** -/
theorem switcherOrder_sound (es : Array Entry) {p : Nat × Entry} (h : p ∈ switcherOrder es) :
    es[p.1]? = some p.2 := by
  unfold switcherOrder at h
  simp only [List.mem_append, List.mem_filter] at h
  rcases h with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact ix_sound es h

/-- **Every entry has a row.** -/
theorem switcherOrder_complete (es : Array Entry) (i : Nat) (hi : i < es.size) :
    ∃ p ∈ switcherOrder es, p.1 = i := by
  have hm : (i, es[i]) ∈ (List.range es.size).filterMap fun i => es[i]?.map (i, ·) := by
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
    exact ⟨i, hi, es[i], by simp, rfl⟩
  refine ⟨(i, es[i]), ?_, rfl⟩
  unfold switcherOrder
  simp only [List.mem_append, List.mem_filter]
  by_cases hc : es[i].current
  · exact Or.inl (Or.inl ⟨hm, by simp [hc]⟩)
  · by_cases hw : es[i].waiting
    · exact Or.inr ⟨hm, by simp [hc, hw]⟩
    · exact Or.inl (Or.inr ⟨hm, by simp [hc, hw]⟩)

/-- Quiet's mobile side sheet leaves a 56dp dismissal strip even on small phones. -/
def switcherWidth (dm : Dim) (W : Nat) : Nat := min (dm.px 320) (W - dm.px 56)

/-- Mobile title bar, including the sheet's rounded upper-right corner. -/
def switcherBar (f : Font) (dm : Dim) (W inset : Nat) : Bitmap := Id.run do
  let px := dm.px
  let pw := switcherWidth dm W
  let color := Palette.color dm.theme
  let mut b := Bitmap.blank W (inset + px 60) (solid (color .scrim) W)
  b := b.round 0 inset pw (inset + px 76) (px 16) (color .panel)
  b := b.fill 0 inset (px 16) b.h (color .panel)
  b := b.icon f "close" (px 14) (inset + px 16) (px 28) (color .fg)
  let title := (f.atSize (px 16)).medium
  let line := Text.oneLineFine title (pw - px 102) "Communities"
  b := b.line title line ((pw - px 2 - Paint.Line.width title line) / 2) (inset + px 23) (color .fg) (exactInk := true)
  return b.fill 0 (b.h - px 1) pw b.h (color .selected)

/-- The mobile body uses the same Quiet glyph atlas and identity palette as
its desktop sibling. Its 58dp rows and 36dp tiles follow the phone design;
all row actions retain the actual account index, including duplicate names. -/
def switcher {α : Type} [BEq α] [Inert α] (onSwitchTo : Nat → α) (onAddMembers : α) (onSettings : α) (onJoin : α) (onCreate : α) (onStub : String → α) (onBack : α) (f : Font) (dm : Dim) (W h : Nat) (es : Array Entry) (_asking : Nat) (canInvite : Bool) : PageOf α := Id.run do
  let px := dm.px
  let pw := switcherWidth dm W
  let color := Palette.color dm.theme
  let rows := switcherOrder es
  let height := max h (px (8 + rows.length * 58 + 16 + 3 * 58 + 8))
  let mut b := Bitmap.blank W height (solid (color .scrim) W)
  b := b.round 0 0 pw height (px 16) (color .panel)
  b := b.fill 0 0 pw (height - px 16) (color .panel)
  b := b.fill 0 0 (px 16) height (color .panel)
  let font := f.atSize (px 16)
  let mut taps := #[]
  let mut y := px 8
  for (idx, e) in rows do
    let ay := y + px 11
    if e.current then
      b := b.round (px 16) (ay - px 3) (px 58) (ay + px 39) (px 7)
        (if dm.theme == .dark then 0xdbbcf0 else 0x9c00ff)
      b := b.round (px 18) (ay - px 1) (px 56) (ay + px 37) (px 5) (color .panel)
    b := b.round (px 19) ay (px 55) (ay + px 36) (px 4) (Palette.avatar e.id8)
    let af := f.atSize (px (if e.waiting then 15 else 21))
    let initial := if e.waiting then String.ofList (e.id8.toList.take 2)
      else String.ofList [(e.name.trimAscii.toString.toList.headD '?').toUpper]
    let mark := Text.oneLineFine af (px 36) initial
    b := b.line af mark (px 19 + (px 36 - Paint.Line.width af mark) / 2) (ay + px 9) 0xffffff (exactInk := true)
    let right := if e.current then px 88 else px 16
    let label := if e.waiting then s!"<{String.ofList (e.id8.toList.take 8)}>" else e.name
    b := b.line font (Text.oneLineFine font (pw - px 70 - right) label) (px 70)
      (y + px (if e.waiting then 13 else 23)) (color (if e.waiting then .muted else .fg)) (exactInk := true)
    if e.waiting then
      let small := f.atSize (px 12)
      b := b.line small (Text.oneLineFine small (pw - px 86) "Waiting for a member to let you in.")
        (px 70) (y + px 33) (color .muted) (exactInk := true)
    else
      taps := taps.push (⟨px 8, y, pw - px 16 - (if e.current then px 80 else 0), px 58⟩, onSwitchTo idx)
      if e.current then
        for (rightEdge, icon, action) in [(88, "add-person", onAddMembers), (48, "gear", onSettings)] do
          let x := pw - px rightEdge
          b := b.icon f icon (x + px 8) (y + px 17) (px 24) (color .fg)
          if action != onAddMembers || canInvite then
            taps := taps.push (⟨x, y + px 7, px 40, px 44⟩, action)
    y := y + px 58
  y := y + px 16
  for (icon, label, action) in [("add-person", "Join a community", onJoin),
      ("add", "Create a community", onCreate),
      ("linked-devices", "Linked devices", onStub "Linked devices")] do
    b := b.round (px 19) (y + px 11) (px 55) (y + px 47) (px 4) (color .selected)
    b := b.icon f icon (px 29) (y + px 21) (px 16) (color .fg)
    b := b.line font (Text.oneLineFine font (pw - px 86) label) (px 70) (y + px 23) (color .fg) (exactInk := true)
    taps := taps.push (⟨px 8, y, pw - px 16, px 58⟩, action)
    y := y + px 58
  taps := taps.push (⟨pw, 0, W - pw, height⟩, onBack)
  return ⟨b, taps⟩

end Pages

/-! ## Notifications (libquiet's #844, Android first)

The policy, the per-process tracker and the native cards. Candidates are
committed, Valid, readable posts (the reader's `Kinds.Notify.read`, read
again only on an exact window notice); a post is news above this
device's `caughtUp` mark. Laws are over `Notify.step`, the function the
app runs each turn. -/

namespace Kinds.Notify
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- How many of a conversation's newest posts a turn considers. -/
def window : Nat := 16

/-- A candidate post, as a card needs it. -/
structure Row where
  id : Id
  author : Id
  device : ByteArray
  name : String
  text : String
  time : Nat
  photo : ByteArray := .empty
  deriving BEq, Inhabited

/-- What the reader hands the tracker for one community. -/
structure Snap where
  /-- The newest committed, Valid posts this device can read, newest first. -/
  rows : List Row := []
  mark : Option Nat := none
  read : List Id := []
  settings : Notice.Settings := {}
  deriving BEq, Inhabited

/-- c's newest `window` readable posts, as user u's device sees them,
with its mark and u's private state. Pending (outbox) rows are not
candidates: only what the store has judged Valid. -/
def read (c u : Id) : m (Snap × Array Q) := do
  let (a, deps) ← readView (Community.readable c (limit := some window)) #[]
  let mut deps := deps
  let mut rows : List Row := []
  for ((_, x), f) in a.rows do
    let .message _ author device kid sealed _ tm _ := f | continue
    let (g, pending, d) ← readFact x deps
    deps := d
    if pending || g.isNone then continue
    let (ks, _, d) ← readList (key.byId.query [kid] (limit := some 1)) deps
    deps := d
    let some text := (match ks.rows.head? with
      | some (_, .key _ _ k) => (openStored cryptoSeal c kid sealed k).map Profile.bytesStr
      | _ => none) | continue
    let (who, d) ← Profile.read c author deps
    deps := d
    let (pics, d) ← File.read c x deps false
    deps := d
    let photo := (pics[0]?.map (·.preview)).getD .empty
    let row : Row := { id := x, author := author, device := device, name := who.name, text := text, time := tm, photo := photo }
    rows := rows ++ [row]
  let (mark, d) ← readView (markOf c) deps
  let (st, d) ← readView (noticeState c u) d
  return ({ rows, mark, read := st.read, settings := st.settings }, d)
end Kinds.Notify

namespace Notify
open _root_.Engine _root_.Community

/-- What a post is, for the policy. The app has no direct messages,
mentions or threads yet, so the app passes the defaults (all false). -/
structure Subject where
  direct : Bool := false
  oneToOne : Bool := false
  mentioned : Bool := false
  reply : Bool := false
  manualFollow : Option Bool := none
  rootAuthor : Bool := false
  replied : Bool := false
  deriving BEq, Inhabited, Repr

/-- libquiet's policy (notify/policy.rs): the level is the
conversation's, then the community's, then All; Off silences all. A
top-level post notifies at All, or when it mentions the user or is a
direct message. A reply needs more than All: never when unfollowed; else
a mention, the replies setting (conversation, community; on by default
in one-to-one DMs), a followed thread, a one-to-one DM, the root's
author, or having replied. -/
def policy (s : Notice.Settings) (m : Subject) : Bool :=
  let level := (s.conversation.or s.community).getD .all
  if level == .off then false
  else if m.reply then
    if m.manualFollow == some false then false
    else m.mentioned || (s.replies.or s.communityReplies).getD m.oneToOne ||
      m.manualFollow == some true || m.oneToOne || m.rootAuthor || m.replied
  else level == .all || m.mentioned || m.direct

/-- The delivery gates around the policy, from the running store. -/
structure Facts where
  device : ByteArray := .empty
  authorDevice : ByteArray := .empty
  ownUser : Bool := false
  live : Bool := true
  news : Bool := true
  visible : Bool := false
  read : Bool := false
  subject : Subject := {}
  deriving Inhabited

/-- Whether a post alerts: not from this device or this user, this
device still a member, news (above the mark), not on screen, not read,
and the policy admits it. -/
def eligible (s : Notice.Settings) (f : Facts) : Bool :=
  decide (f.device ≠ f.authorDevice) && !f.ownUser && f.live && f.news &&
  !f.visible && !f.read && policy s f.subject

/-- The rule, stated propositionally. -/
def Rule (s : Notice.Settings) (f : Facts) : Prop :=
  f.device ≠ f.authorDevice ∧ f.ownUser = false ∧ f.live = true ∧ f.news = true ∧
  f.visible = false ∧ f.read = false ∧ policy s f.subject = true

/-- One message on a conversation's card. -/
structure Card where
  id : Id
  community : Id
  conversation : Id
  sender : Id
  name : String
  title : String
  body : String
  link : String
  time : Nat
  photo : ByteArray := .empty
  deriving BEq, Inhabited

inductive Effect where
  | post (card : Card)
  | withdraw (card : Card)
  deriving BEq, Inhabited

/-- The process's tracker: every post considered (alerted or not), and
the messages standing on cards, newest first. -/
structure State where
  seen : List Id := []
  active : List Card := []
  deriving Inhabited

/-- A post considered once: a repeat never alerts again, read or not. -/
def arrive (s : State) (settings : Notice.Settings) (f : Facts) (c : Card) : State × List Effect :=
  if Engine.has s.seen c.id then (s, [])
  else if eligible settings f then
    ({ seen := c.id :: s.seen, active := c :: s.active }, [.post c])
  else ({ s with seen := c.id :: s.seen }, [])

/-- Withdraw exactly the messages `gone` names; the rest stand, so a
read of older messages keeps newer unread ones on the card. -/
def reconcile (s : State) (gone : Card → Bool) : State × List Effect :=
  ({ s with active := s.active.filter (fun c => !gone c) },
    (s.active.filter gone).map Effect.withdraw)

/-- Collapse controls, bidi controls and whitespace to single spaces,
then keep `cap` visible characters (compose.rs's one_line). -/
def oneLine (text : String) (cap : Nat) : String := Id.run do
  let mut out := ""
  let mut kept := 0
  let mut space := false
  for c in text.toList do
    let n := c.toNat
    if isBlank c.val || n < 32 || (127 ≤ n && n ≤ 159) || Text.isInvisible c.val ||
        (0x202a ≤ n && n ≤ 0x202e) then
      space := !out.isEmpty
    else
      if kept == cap then return out ++ "…"
      if space then out := out ++ " "
      out := out.push c
      kept := kept + 1
      space := false
  return out

/-- One community, as a turn sees it. -/
structure Input where
  c : Id
  /-- The card's title: `#general (community)`. -/
  title : String
  /-- This device's signing key, and its user in c. -/
  device : ByteArray
  user : Id
  /-- This device still a member (admitted, not removed). -/
  live : Bool
  snap : Kinds.Notify.Snap

/-- A post's gates, from its community's input and the screen. -/
def facts (i : Input) (viewing : Option Id) (r : Kinds.Notify.Row) : Facts :=
  { device := i.device, authorDevice := r.device, ownUser := decide (r.author = i.user), live := i.live,
    news := (match i.snap.mark with | some m => decide (m ≤ r.time) | none => false),
    visible := decide (viewing = some i.c), read := Engine.has i.snap.read r.id }

def card (i : Input) (r : Kinds.Notify.Row) : Card :=
  { id := r.id, community := i.c, conversation := i.c, sender := r.author,
    name := oneLine (if r.name.isEmpty then "…" else r.name) 32, title := i.title,
    body := if r.text.isEmpty then (if r.photo.isEmpty then "Sent a message" else "Sent a photo")
      else oneLine r.text 140,
    link := (Target.uri ⟨i.c, i.c, r.id, []⟩), time := r.time, photo := r.photo }

/-- One post considered, its effects appended. -/
def arriveRow (viewing : Option Id) (i : Input) (acc : State × List Effect) (r : Kinds.Notify.Row) :
    State × List Effect :=
  let p := arrive acc.1 i.snap.settings (facts i viewing r) (card i r)
  (p.1, acc.2 ++ p.2)

/-- One community's new posts, oldest first. -/
def arriveAll (viewing : Option Id) (i : Input) (s : State) : State × List Effect :=
  i.snap.rows.reverse.foldl (arriveRow viewing i) (s, [])

/-- One community's turn, its effects appended. -/
def arriveIn (viewing : Option Id) (acc : State × List Effect) (i : Input) : State × List Effect :=
  let p := arriveAll viewing i acc.1
  (p.1, acc.2 ++ p.2)

/-- What leaves the cards: the conversation on screen, messages read
(here, or on the user's other devices), and every community this device
is no longer a member of or no longer holds. -/
def gone (present : List Id) (ins : List Input) (viewing : Option Id) (reads : List Id) (c : Card) : Bool :=
  decide (viewing = some c.community) || Engine.has reads c.id || !Engine.has present c.community ||
    ins.any (fun i => decide (i.c = c.community) && (!i.live || Engine.has i.snap.read c.id))

/-- **The turn**: every community's new posts considered, then the
cards reconciled. `present` is this device's communities, `viewing` the
conversation on screen (none in the background), `reads` the messages
read here this turn. -/
def step (s : State) (present : List Id) (viewing : Option Id) (reads : List Id) (ins : List Input) :
    State × List Effect :=
  let a := ins.foldl (arriveIn viewing) (s, [])
  let r := reconcile a.1 (gone present ins viewing reads)
  (r.1, a.2 ++ r.2)

/-- The marks to write: a community's first (now: the app reads a
community first when this device starts joining it, so posts written
before the join are history, and posts after it are news), or its newest
post considered, capped at now so a post claiming a future time cannot
silence later ones. -/
def marks (now : Nat) (ins : List Input) : List (Id × Nat) :=
  ins.filterMap fun i =>
    match i.snap.mark with
    | none => some (i.c, now)
    | some m =>
      if !i.live then none else
      let top := min now (i.snap.rows.foldl (fun t r => max t r.time) 0)
      if m < top then some (i.c, top) else none

/-! ### Laws, over the functions the app runs -/

theorem own_silent (s : Notice.Settings) (f : Facts) (h : f.device = f.authorDevice) :
    eligible s f = false := by simp [eligible, h]

theorem notifies_iff (s : Notice.Settings) (f : Facts) : eligible s f = true ↔ Rule s f := by
  simp [eligible, Rule, Bool.and_eq_true, and_assoc]

/-- An ordinary post from another device really does alert. -/
theorem can_alert : eligible {} { device := ⟨#[1]⟩, authorDevice := ⟨#[2]⟩ } = true := by decide

theorem once (s : State) (p : Notice.Settings) (f : Facts) (c : Card) :
    (arrive (arrive s p f c).1 p f c).2 = [] := by
  unfold arrive
  split
  · simp_all
  · split <;> simp [Engine.has]

theorem arrive_active (s : State) (p : Notice.Settings) (f : Facts) (c d : Card) (h : d ∈ s.active) :
    d ∈ (arrive s p f c).1.active := by
  unfold arrive; split
  · exact h
  · split
    · exact List.mem_cons_of_mem _ h
    · exact h

theorem arrive_post (s : State) (p : Notice.Settings) (f : Facts) (c d : Card)
    (h : Effect.post d ∈ (arrive s p f c).2) : d = c ∧ eligible p f = true := by
  unfold arrive at h; split at h
  · simp at h
  · split at h
    · simp at h; exact ⟨h, by assumption⟩
    · simp at h

theorem arriveAll_active (v : Option Id) (i : Input) (s : State) (d : Card) (h : d ∈ s.active) :
    d ∈ (arriveAll v i s).1.active := by
  unfold arriveAll
  suffices ∀ (rs : List Kinds.Notify.Row) (a : State × List Effect), d ∈ a.1.active →
      d ∈ (rs.foldl (arriveRow v i) a).1.active from this _ _ h
  intro rs
  induction rs with
  | nil => intro a h; exact h
  | cons r rs ih => intro a h; exact ih _ (arrive_active _ _ _ _ _ h)

/-- Every post a community's arrivals make is of an eligible post of it. -/
theorem arriveAll_post (v : Option Id) (i : Input) (s : State) (d : Card)
    (h : Effect.post d ∈ (arriveAll v i s).2) :
    ∃ r ∈ i.snap.rows, d = card i r ∧ eligible i.snap.settings (facts i v r) = true := by
  unfold arriveAll at h
  have gen : ∀ (rs : List Kinds.Notify.Row) (a : State × List Effect), (∀ r ∈ rs, r ∈ i.snap.rows) →
      Effect.post d ∈ (rs.foldl (arriveRow v i) a).2 →
      Effect.post d ∈ a.2 ∨ ∃ r ∈ i.snap.rows, d = card i r ∧ eligible i.snap.settings (facts i v r) = true := by
    intro rs
    induction rs with
    | nil => intro a _ h; exact Or.inl h
    | cons r rs ih =>
      intro a hrs h
      simp only [List.foldl_cons] at h
      rcases ih _ (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) h with h | h
      · simp only [arriveRow, List.mem_append] at h
        rcases h with h | h
        · exact Or.inl h
        · obtain ⟨rfl, he⟩ := arrive_post _ _ _ _ _ h
          exact Or.inr ⟨r, hrs r (List.mem_cons_self ..), rfl, he⟩
      · exact Or.inr h
  rcases gen _ (s, []) (fun r hr => List.mem_reverse.1 hr) h with h | h
  · simp at h
  · exact h

theorem step_fold_active (v : Option Id) (ins : List Input) (a : State × List Effect) (d : Card)
    (h : d ∈ a.1.active) : d ∈ (ins.foldl (arriveIn v) a).1.active := by
  induction ins generalizing a with
  | nil => exact h
  | cons i ins ih => exact ih _ (arriveAll_active v i a.1 d h)

theorem step_fold_post (v : Option Id) (ins : List Input) (a : State × List Effect) (d : Card)
    (h : Effect.post d ∈ (ins.foldl (arriveIn v) a).2) :
    Effect.post d ∈ a.2 ∨ ∃ i ∈ ins, ∃ r ∈ i.snap.rows, d = card i r ∧ eligible i.snap.settings (facts i v r) = true := by
  induction ins generalizing a with
  | nil => exact Or.inl h
  | cons i ins ih =>
    rcases ih _ h with h | ⟨j, hj, r, hr, rfl, he⟩
    · simp only [arriveIn, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · obtain ⟨r, hr, rfl, he⟩ := arriveAll_post v i a.1 d h
        exact Or.inr ⟨i, List.mem_cons_self .., r, hr, rfl, he⟩
    · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, r, hr, rfl, he⟩

/-- **The conversation on screen is quiet**: a turn posts no card of it,
and leaves none standing. -/
theorem step_quiet (s : State) (present : List Id) (c : Id) (reads : List Id) (ins : List Input) :
    (∀ d, Effect.post d ∈ (step s present (some c) reads ins).2 → d.community ≠ c) ∧
    (∀ d ∈ (step s present (some c) reads ins).1.active, d.community ≠ c) := by
  refine ⟨fun d h => ?_, fun d h => ?_⟩
  · simp only [step, reconcile, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨_, _, h⟩
    · rcases step_fold_post _ ins (s, []) d h with h | ⟨i, _, r, _, rfl, he⟩
      · simp at h
      · intro hc
        simp [card] at hc
        simp [eligible, facts, hc] at he
    · cases h
  · simp only [step, reconcile, List.mem_filter] at h
    intro hc
    simp [gone, hc] at h

/-- **Removal clears**: a community this device is no longer a member
of, or no longer holds, has no card standing after a turn. -/
theorem step_removed (s : State) (present : List Id) (v : Option Id) (reads : List Id) (ins : List Input)
    (d : Card) (hd : d ∈ (step s present v reads ins).1.active) :
    d.community ∈ present ∧ ∀ i ∈ ins, i.c = d.community → i.live = true := by
  simp only [step, reconcile, List.mem_filter] at hd
  have hg := hd.2
  simp only [gone, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at hg
  refine ⟨(Engine.has_iff _ _).1 (by simpa using hg.1.2), fun i hi hc => ?_⟩
  have := List.any_eq_false.1 hg.2 i hi
  simp [hc] at this
  cases h : i.live <;> simp_all

/-- **Reads clear**: a message read (here, or by the user's other
devices) has no card standing after a turn. -/
theorem step_read (s : State) (present : List Id) (v : Option Id) (reads : List Id) (ins : List Input)
    (d : Card) (hd : d ∈ (step s present v reads ins).1.active) : d.id ∉ reads := by
  simp only [step, reconcile, List.mem_filter] at hd
  have hg := hd.2
  simp only [gone, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at hg
  exact (Engine.has_false _ _).1 hg.1.1.2

/-- **A partial read keeps newer unread messages**: a message standing
before the turn stands after it unless the turn's `gone` names it. -/
theorem step_keeps (s : State) (present : List Id) (v : Option Id) (reads : List Id) (ins : List Input)
    (d : Card) (hd : d ∈ s.active) (hg : gone present ins v reads d = false) :
    d ∈ (step s present v reads ins).1.active := by
  simp only [step, reconcile, List.mem_filter]
  exact ⟨step_fold_active v ins (s, []) d hd, by simp [hg]⟩

/-- **Posts are exactly eligible**: every card a turn posts is of a
post in a snapshot that the rule admits. -/
theorem step_post (s : State) (present : List Id) (v : Option Id) (reads : List Id) (ins : List Input)
    (d : Card) (h : Effect.post d ∈ (step s present v reads ins).2) :
    ∃ i ∈ ins, ∃ r ∈ i.snap.rows, d = card i r ∧ Rule i.snap.settings (facts i v r) := by
  simp only [step, reconcile, List.mem_append, List.mem_map] at h
  rcases h with h | ⟨_, _, h⟩
  · rcases step_fold_post _ ins (s, []) d h with h | ⟨i, hi, r, hr, rfl, he⟩
    · simp at h
    · exact ⟨i, hi, r, hr, rfl, (notifies_iff _ _).1 he⟩
  · cases h

/-- **A mark never runs ahead of the clock**: a post claiming a future
time cannot silence later posts. -/
theorem marks_le (now : Nat) (ins : List Input) (p : Id × Nat) (h : p ∈ marks now ins) : p.2 ≤ now := by
  simp only [marks, List.mem_filterMap] at h
  obtain ⟨i, _, hi⟩ := h
  split at hi
  · cases hi; exact Nat.le_refl _
  · split at hi
    · cases hi
    · split at hi
      · cases hi; exact Nat.min_le_left _ _
      · cases hi

/-! ### The native seam: one card per conversation, as JSON -/

def jsonStr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c.toNat < 32 then
      let h := "0123456789abcdef".toList
      out := (out ++ "\\u00").push (h[c.toNat / 16]!) |>.push (h[c.toNat % 16]!)
    else out := out.push c
  return out ++ "\""

def jsonObj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jsonStr k ++ ":" ++ v) ++ "}"

def hexOf (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let h := "0123456789abcdef".toList
    [h[x.toNat / 16]!, h[x.toNat % 16]!])

/-- A placeholder avatar's colour (the app's identity palette) and its
initial. -/
def colorOf (id : ByteArray) : String :=
  let c := Palette.avatar ((hexOf id).take 8).toString
  "#" ++ (hexOf ⟨#[(c >>> 16).toUInt8, (c >>> 8).toUInt8, c.toUInt8]⟩)

def initialOf (name : String) (id : ByteArray) : String :=
  match name.toList.find? (fun c => !isBlank c.val && !Text.isInvisible c.val && c.toNat ≥ 32) with
  | some c => String.singleton c.toUpper
  | none => ((hexOf id).take 2).toString

/-- A card's inline photo: the attachment's preview, at most 128 px a
side, as base64 RGBA (Java paints it; nothing else is fetched). -/
def photoOf (bytes : ByteArray) : Nat × Nat × String :=
  match Image.decode bytes with
  | none => (0, 0, "")
  | some src =>
    let (w, h) := Image.fit src 128 128
    let bmp := Image.scaled src w h 0x222529
    let raw := bmp.rows.foldl (· ++ ·) .empty
    let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
    let out := Id.run do
      let mut out := ""
      for i in [0:(raw.size + 2) / 3] do
        let n := i * 3
        let a := raw[n]!.toNat
        let b := (raw[n + 1]?.getD 0).toNat
        let d := (raw[n + 2]?.getD 0).toNat
        out := out.push alphabet[a / 4]!
        out := out.push alphabet[(a % 4) * 16 + b / 16]!
        out := out.push (if n + 1 < raw.size then alphabet[(b % 16) * 4 + d / 64]! else '=')
        out := out.push (if n + 2 < raw.size then alphabet[d % 64]! else '=')
      return out
    (w, h, out)

def messageJson (c : Card) : String :=
  jsonObj [("id", jsonStr (hexOf c.id)), ("senderId", jsonStr (hexOf c.sender)),
    ("sender", jsonStr c.name), ("color", jsonStr (colorOf c.sender)),
    ("mark", jsonStr (initialOf c.name c.sender)), ("body", jsonStr c.body),
    ("time", toString (c.time * 60000))]

/-- The conversation's complete card (its standing messages: the count,
the latest five oldest first, the newest's photo and link), or its
cancellation when none stand. `alert` is whether a new post is in it. -/
def packet (active : List Card) (conversation : Id) (alert : Bool) : String :=
  let cards := active.filter fun a => decide (a.conversation = conversation)
  match cards.head? with
  | none => jsonObj [("action", jsonStr "cancel"), ("tag", jsonStr (hexOf conversation))]
  | some latest =>
    let (pw, ph, photo) := if latest.photo.isEmpty then (0, 0, "") else photoOf latest.photo
    jsonObj [("action", jsonStr "post"), ("tag", jsonStr (hexOf conversation)),
      ("group", jsonStr (hexOf latest.community)), ("title", jsonStr latest.title),
      ("link", jsonStr latest.link), ("color", jsonStr (colorOf latest.community)),
      ("mark", jsonStr (initialOf latest.title latest.community)),
      ("body", jsonStr latest.body), ("alert", if alert then "true" else "false"),
      ("count", toString cards.length), ("photoW", toString pw), ("photoH", toString ph),
      ("photo", jsonStr photo),
      ("messages", "[" ++ String.intercalate "," ((cards.take 5).reverse.map messageJson) ++ "]")]

/-- One packet per conversation a turn's effects touch: a post alerts;
a withdrawal re-renders what still stands, silently, or cancels. -/
def packets (active : List Card) (effects : List Effect) : List String := Id.run do
  let mut done : List Id := []
  let mut out := []
  for e in effects do
    let (c, alert) := match e with | .post c => (c, true) | .withdraw c => (c, false)
    if Engine.has done c.conversation then continue
    done := c.conversation :: done
    let alert := alert || effects.any fun e => match e with
      | .post d => decide (d.conversation = c.conversation) | _ => false
    out := out ++ [packet active c.conversation alert]
  return out

end Notify
