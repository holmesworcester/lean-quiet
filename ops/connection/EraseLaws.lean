/-
A closed session's keys are gone from the store (README, "A closed
session's keys cannot be recovered"; docs/CAUGHT.md, fs-erase).

**The statement, broadened.** A session's key material is its two
ephemeral secrets (each side holds its own: an `eph` op, drawn for the
request on the dialer's side and for the connection on the answerer's)
and its two transport keys (the `established` fact). In the store they
sit in two places: the `eph` op's bytes, and the verdicts (`status`) of
the `eph` and `established` ops, whose facts carry the secret and the
keys. No other table holds them: the index, the journal (`filings`) and
the counts hold relation keys, sort keys and ids, and a connection
fact's keys and sort key name only ids (`secret_unfiled`). So
`KeyRow s hs y`: row y of store s holds key material of one of the
handshakes `hs` names (an `eph` op citing one, as bytes or as a Valid
verdict; an `established` verdict naming one). `Forgets s hs`: no row
does.

Proven, over the running code:
- `purge_forgets`: the running purge (`purge`, which is `purgeS` on the
  model's tables, `run_purge`), then judging, leaves no key row of the
  handshakes it was given, whatever else the store holds. Any key row
  cites one of them, so the purge's walk reaches it, and it is local.
- `close_forgets`: so the close step every session end runs
  (`Node.endSession`, `close_purges`) with the family's `closing` leaves
  no key row of the connection or of the request it answers: neither
  side's ephemeral, nor the transport keys. `closing` names the
  connection even once it is gone (it named nothing before fs-erase),
  so a key row that cites a connection the store no longer holds cannot
  outlive the close either.
- `retired_complete`: every established session the store holds is
  kept open (`sessions`) or retired (`retired`), and `close_purges`
  ends every retired one. So no established session sits in the store
  with neither: every way a session stops being open ends it.
  `retired_open`: an open session is never retired.
- `forget_stays`: a later purge brings no key row back.

Caught (a negative control, `shipped_retired_misses`): `retired` as it
shipped (`retiredShipped`) read `allSessions`, which places a session
by its handshake's arrival record. A dialer that crashed between the
two writes of `onFrame` (the connection stored, its arrival record not)
established the session at its next write, and that session was
neither open nor retired: its keys and its ephemeral stayed in the store
for good, and `connectedTo` kept the dialer from dialing again.
tests/engine/ConnectionCheck.lean reproduces it on SQLite.

Assumed: the store model (`Model.run`, which since the purge bridge
covers the purge's reads and deletes too), and the README's trusted
item that a row SQLite deleted, with `secure_delete` on, then `VACUUM`
and the WAL truncated, leaves no recoverable byte (tests/engine/Purge.lean
reads the files raw). With both, a closed session's ephemerals are not
on this node's disk, which is `kk_forward_secret`'s premise. That last
step, from the store's bytes to the symbolic model's names, is read, not
proven.

What this does not say (README): an initiator holds its ephemeral while
its request waits for an answer, and a responder may have answered and
closed meanwhile (the answer lost); while the request waits, that
session's keys follow from the initiator's store and the static keys.
That needs the initiator to know of a session it never heard of, so it
is out of reach of any store law.
-/
import ops.connection.RemovalLaws
import engine.wire.CloseLaws

namespace Connection
open Engine Engine.Sync

/-! ## Where key material sits -/

/-- Row y of store s holds key material of one of the handshakes `hs`
names: an ephemeral drawn for one of them (an `eph` op citing it, or its
Valid fact), or the transport keys of a session one of them names (an
`established` fact). -/
def KeyRow (s : DB F) (hs : List Id) (y : Id) : Prop :=
  (∃ o, s.ops y = some o ∧ o.kind = 32 ∧ ∃ r ∈ o.reqs, r ∈ hs) ∨
  (∃ of pk sk, s.status y = some (.valid (.inr (.eph of pk sk))) ∧ of ∈ hs) ∨
  (∃ c c' p hh sk rk d, s.status y = some (.valid (.inr (.established c c' p hh sk rk d))) ∧ c ∈ hs)

/-- No row of s holds key material of the handshakes `hs`. -/
def Forgets (s : DB F) (hs : List Id) : Prop := ∀ y, ¬ KeyRow s hs y

/-- **No secret is filed.** The keys a connection fact is filed under,
and its sort key, name only ids: so the index, its counts and the
journal (`filings`), which copy them, hold no ephemeral and no
transport key. -/
theorem secret_unfiled (of pk sk c c' p hh sk' rk : B) (d : Bool) :
    keys (.eph of pk sk) = [eph.byOf.key [of]] ∧ sortOf (.eph of pk sk) = .empty ∧
    keys (.established c c' p hh sk' rk d) = [established.all.key [], established.byConn.key [c]] ∧
    sortOf (.established c c' p hh sk' rk d) = .empty := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> rfl

/-! ## A key fact is an op's own -/

theorem allValid_length {sts : List (Option (Verdict F))} {fs : List F} (h : allValid sts = some fs) :
    fs.length = sts.length := by
  induction sts generalizing fs with
  | nil => cases h; rfl
  | cons st t ih =>
    match st, h with
    | some (.valid f), h =>
      simp only [allValid] at h
      cases ht : allValid t with
      | none => rw [ht] at h; cases h
      | some fs' =>
        rw [ht] at h; cases h
        simp [ih ht]

/-- A Valid verdict of the node's is its validator's answer on the op's
requirements' facts. -/
theorem valid_op {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {y : Id} {g : Fact}
    (hy : s.status y = some (.valid (.inr g))) :
    ∃ o fs, s.ops y = some o ∧ fs.length = o.reqs.length ∧ validate K o fs = some g := by
  obtain ⟨n, hn⟩ := hi.sound y _ hy
  cases n with
  | zero => cases hn
  | succ n =>
    simp only [specAt] at hn
    cases ho : s.ops y with
    | none => rw [ho] at hn; cases hn
    | some o =>
      rw [ho] at hn
      simp only [judge] at hn
      split at hn
      · cases hn
      · split at hn
        · rename_i fs hfs
          refine ⟨o, fs, rfl, by rw [allValid_length hfs, List.length_map], ?_⟩
          split at hn
          · rename_i f hf
            simp only [Option.some.injEq, Verdict.valid.injEq] at hn
            subst hn
            simp only [node, Family.sum] at hf
            split at hf
            · change Option.map Sum.inr (validate K o fs) = _ at hf
              cases hv : validate K o fs with
              | none => rw [hv] at hf; cases hf
              | some g' =>
                rw [hv] at hf
                simp only [Option.map_some, Option.some.injEq, Sum.inr.injEq] at hf
                rw [hf]
            · cases hl : lefts fs with
              | none => rw [hl] at hf; cases hf
              | some xs =>
                rw [hl] at hf
                cases hv : (Community.family C).validate o xs with
                | none => simp [hv] at hf
                | some g' => simp [hv] at hf
          · cases hn
        · cases hn

theorem eph_check {K : Keys} {o : Op} {sk : B} {fs : List F} {g : Fact} (h : Eph.check K o sk fs = some g) :
    ∃ x, fs = [x] ∧ ∃ pk sk', g = .eph (o.reqs.headD .empty) pk sk' := by
  unfold Eph.check at h
  split at h
  · split at h
    · cases h; exact ⟨_, rfl, _, _, rfl⟩
    · cases h
  · cases h

theorem established_check {K : Keys} {o : Op} {fs : List F} {g : Fact} (h : Established.check K o fs = some g) :
    fs.length = 4 ∧ ∃ c p hh sk rk d, g = .established (o.reqs.headD .empty) c p hh sk rk d := by
  unfold Established.check at h
  split at h
  · refine ⟨rfl, ?_⟩
    split at h
    · cases h
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨st, re, p1⟩, -, ⟨c, a, os⟩, -, ⟨sr, m2'⟩, -, h⟩ := h
        split at h
        · cases h
        · cases h; exact ⟨_, _, _, _, _, _, rfl⟩
      · split at h
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨st, p1⟩, -, ⟨c, a, os⟩, -, ⟨si, x⟩, -, h⟩ := h
          cases h; exact ⟨_, _, _, _, _, _, rfl⟩
        · cases h
  · cases h

/-- **An ephemeral's fact names the op it cites, and is an `eph` op's.** -/
theorem validate_eph {K : Keys} {o : Op} {fs : List F} {of pk sk : B}
    (h : validate K o fs = some (.eph of pk sk)) :
    o.kind = 32 ∧ fs.length = 1 ∧ of = o.reqs.headD .empty := by
  unfold validate at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hk
      cases b with
      | eph sk' =>
        obtain ⟨x, rfl, pk', sk'', hg⟩ := eph_check h
        cases hg
        exact ⟨hk.symm, rfl, rfl⟩
      | request => simp only [check, Request.check] at h; split at h <;> (try split at h) <;> cases h
      | opened =>
        simp only [check, Opened.check] at h
        split at h
        · split at h
          · cases h
          · split at h
            · split at h <;> cases h
            · cases h
        · cases h
      | connection => simp only [check, Reply.check] at h; split at h <;> (try split at h) <;> cases h
      | established =>
        obtain ⟨-, _, _, _, _, _, _, hg⟩ := established_check h
        cases hg
      | send => simp only [check, Send.check] at h; split at h <;> (try split at h) <;> cases h
      | recv => simp only [check, Recv.check] at h; split at h <;> cases h
      | given => simp only [check, Given.check] at h; split at h <;> cases h
    · cases h
  · cases h

/-- **A session's keys are its `established` op's**, which cites the
connection they name. -/
theorem validate_established {K : Keys} {o : Op} {fs : List F} {c c' p hh sk rk : B} {d : Bool}
    (h : validate K o fs = some (.established c c' p hh sk rk d)) :
    o.kind = 36 ∧ fs.length = 4 ∧ c = o.reqs.headD .empty := by
  unfold validate at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hk
      cases b with
      | established =>
        obtain ⟨h4, _, _, _, _, _, _, hg⟩ := established_check h
        cases hg
        exact ⟨hk.symm, h4, rfl⟩
      | eph sk' =>
        obtain ⟨x, rfl, pk', sk'', hg⟩ := eph_check h
        cases hg
      | request => simp only [check, Request.check] at h; split at h <;> (try split at h) <;> cases h
      | opened =>
        simp only [check, Opened.check] at h
        split at h
        · split at h
          · cases h
          · split at h
            · split at h <;> cases h
            · cases h
        · cases h
      | connection => simp only [check, Reply.check] at h; split at h <;> (try split at h) <;> cases h
      | send => simp only [check, Send.check] at h; split at h <;> (try split at h) <;> cases h
      | recv => simp only [check, Recv.check] at h; split at h <;> cases h
      | given => simp only [check, Given.check] at h; split at h <;> cases h
    · cases h
  · cases h

theorem headD_mem {l : List Id} (h : l ≠ []) : l.headD .empty ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self ..

/-- Connection ops of kinds 32–39 other than the two handshake messages
are local: in the node's family their room is none. -/
theorem room_local {C : Community.Crypto} {K : Keys} {o : Op} (hk : o.kind = 32 ∨ o.kind = 36) :
    (node C K).room o = none := by
  have ho : owns o.kind = true := by rcases hk with hk | hk <;> rw [hk] <;> rfl
  have hs : ¬ (o.kind = 33 ∨ o.kind = 35) := by rcases hk with hk | hk <;> rw [hk] <;> decide
  simp only [Family.room, node, Family.sum, family, ho, ite_true, scopeOf, hs, ite_false]

/-- Every key row is a stored local op that cites one of `hs`. -/
theorem keyRow_op {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {hs : List Id} {y : Id}
    (h : KeyRow s hs y) :
    ∃ o, s.ops y = some o ∧ (node C K).room o = none ∧ ∃ r ∈ o.reqs, r ∈ hs := by
  rcases h with ⟨o, ho, hk, r, hr, hrs⟩ | ⟨of, pk, sk, hy, hof⟩ | ⟨c, c', p, hh, sk, rk, d, hy, hc⟩
  · exact ⟨o, ho, room_local (.inl hk), r, hr, hrs⟩
  · obtain ⟨o, fs, ho, hl, hv⟩ := valid_op hi hy
    obtain ⟨hk, h1, rfl⟩ := validate_eph hv
    have hne : o.reqs ≠ [] := by intro he; rw [he] at hl; rw [hl] at h1; cases h1
    exact ⟨o, ho, room_local (.inl hk), _, headD_mem hne, hof⟩
  · obtain ⟨o, fs, ho, hl, hv⟩ := valid_op hi hy
    obtain ⟨hk, h4, rfl⟩ := validate_established hv
    have hne : o.reqs ≠ [] := by intro he; rw [he] at hl; rw [hl] at h4; cases h4
    exact ⟨o, ho, room_local (.inr hk), _, headD_mem hne, hc⟩

/-! ## The purge forgets -/

theorem inv_drainS {fam : Family F} {s : DB F} (h : Inv fam s) : ∀ n, Inv fam (drainS fam n s)
  | 0 => h
  | n + 1 => by
    unfold drainS
    split
    · exact inv_step h
    · exact inv_drainS (inv_step h) n

/-- No stored conn or local op cites one of `hs`: what a purge of `hs`
leaves, and more than the key rows (the `opened`, the couriers, the
arrival records, the notices given). -/
def Uncited (s : DB F) (fam : Family F) (hs : List Id) : Prop :=
  ∀ y o, s.ops y = some o → fam.room o = none → ∀ r ∈ o.reqs, r ∉ hs

/-- With the tables' invariant, a store where nothing local cites `hs`
holds no key row of them. -/
theorem forgets_of_uncited {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s)
    {hs : List Id} (hu : Uncited s (node C K) hs) : Forgets s hs := by
  intro y hy
  obtain ⟨o, ho, hl, r, hr, hrs⟩ := keyRow_op hi hy
  exact hu y o ho hl r hr hrs

/-- The running purge of `hs` (`purgeS`, which the running `purge` is:
`run_purge`), then any judging, leaves no conn or local op that cites
one of `hs`: the purge's walk reaches every op that cites one. -/
theorem purge_uncited {fam : Family F} {s : DB F} (hi : Inv fam s) (hs : List Id) (n : Nat) :
    Uncited (drainS fam n (purgeS fam hs s)) fam hs := by
  intro y o ho hl r hr hrs
  rw [drainS_ops] at ho
  have hnot : y ∉ purgeSet fam s hs := fun hm => by rw [purgeS_ops_mem s hs hm] at ho; cases ho
  rw [purgeS_ops_not s hs hnot] at ho
  have hst : y ∈ s.stored := (hi.stored y).2 (by rw [ho]; rfl)
  have hc : y ∈ closeUp s hs := closeUp_closed s hs hst ho hr (closeUp_sub s hs hrs)
  exact hnot (mem_purgeSet_iff.2 ⟨hc, o, ho, hl⟩)

/-- **What a purge leaves uncited stays so** through any later purge: a
purge deletes, and judging writes no op. -/
theorem uncited_stays {fam : Family F} {s : DB F} {hs : List Id} (hu : Uncited s fam hs)
    (ids : List Id) (n : Nat) : Uncited (drainS fam n (purgeS fam ids s)) fam hs := by
  intro y o ho hl r hr hrs
  rw [drainS_ops] at ho
  have hnot : y ∉ purgeSet fam s ids := fun hm => by rw [purgeS_ops_mem s ids hm] at ho; cases ho
  rw [purgeS_ops_not s ids hnot] at ho
  exact hu y o ho hl r hr hrs

/-- **The running purge forgets the handshakes it is given.** After the
purge of `hs` and any judging, no row holds an ephemeral drawn for one
of `hs`, nor the keys of a session one of them names. -/
theorem purge_forgets {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) (hs : List Id)
    (n : Nat) : Forgets (drainS (node C K) n (purgeS (node C K) hs s)) hs :=
  forgets_of_uncited (inv_drainS (purge_inv hi hs) n) (purge_uncited hi hs n)

/-- **Forgotten stays forgotten**: once nothing local cites `hs`, no
later purge brings a key row of them back. -/
theorem forget_stays {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {hs : List Id}
    (hu : Uncited s (node C K) hs) (ids : List Id) (n : Nat) :
    Forgets (drainS (node C K) n (purgeS (node C K) ids s)) hs :=
  forgets_of_uncited (inv_drainS (purge_inv hi ids) n) (uncited_stays hu ids n)

/-! ## The close step forgets -/

/-- What `closing` names, on held data: the connection, and the
requirements of the connection op if the store holds it (the request
it answers). -/
theorem closing_apply (cid : Id) (h : Held F) :
    (closing cid : HeldM F (List Id)) h = (cid :: ((h.db.ops cid).map (·.reqs)).getD [], h) := by
  unfold closing
  simp only [HeldM.bind_apply, HeldM.getOp_apply]
  cases h.db.ops cid <;> rfl

/-- **A closed session's keys are gone from its node's store.** The
close step every session end runs (`Node.endSession`: a drop on
silence, a lost socket, a retirement, a session that left
`established`; `close_purges`), with the family's `closing`, from any
state that keeps the tables' invariant: afterwards no stored conn or
local op cites the connection or the request it answers (`Uncited`),
so no row holds this side's ephemeral for the session (drawn for the
request on the dialer's side, for the connection on the answerer's),
in its bytes or its verdict, nor the session's transport keys
(`Forgets`). -/
theorem close_forgets {C : Community.Crypto} {K : Keys} (x : Sync F (HeldM F)) (hf : x.fam = node C K)
    (hc : x.hooks.closing = closing) (h : Held F) (hi : Inv x.fam h.db) (cid : Id) :
    let hs := cid :: ((h.db.ops cid).map (·.reqs)).getD []
    let h' := ((Node.endSession x cid : HeldM F Effects) h).2
    Uncited h'.db x.fam hs ∧ Forgets h'.db hs := by
  intro hs h'
  have he : h' = ((Turn.purge x.fam hs true : HeldM F Unit) h).2 := by
    show ((Node.endSession x cid : HeldM F Effects) h).2 = _
    rw [endSession_purges, HeldM.bind_apply, hc, closing_apply]
    rfl
  rw [he, purge_apply]
  simp only [hf] at hi ⊢
  exact ⟨purge_uncited hi hs _, purge_forgets hi hs _⟩

/-! ## Every session not kept open is retired -/

/-- **Every established session is kept open or retired** (`retired`):
an established fact the store lists names a session `sessions` lists,
or one `retired` names, which the node then closes and purges
(`close_purges`, `close_forgets`). -/
theorem retired_complete (s : DB F) {y cid c p hh sk rk : B} {d : Bool}
    (hy : (y, Fact.established cid c p hh sk rk d) ∈ ((rows established.all [] : Model F _).run s).1) :
    (∃ e ∈ ((sessions : Model F _).run s).1, e.1 = cid) ∨ cid ∈ ((retired : Model F _).run s).1 := by
  simp only [sessions, retired, Model.run_bind, Model.run_pure, openSessions_state]
  by_cases ho : ((openSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1.any
      (fun e => decide (e.1 = cid)) = true
  · left
    obtain ⟨e, he, hd⟩ := List.any_eq_true.1 ho
    exact ⟨_, List.mem_map_of_mem he, of_decide_eq_true hd⟩
  · right
    rw [List.mem_filterMap]
    exact ⟨_, hy, by simp only [ho, Bool.false_eq_true, ite_false]⟩

/-- **No open session is retired.** -/
theorem retired_open (s : DB F) {cid : B} (hr : cid ∈ ((retired : Model F _).run s).1) :
    ∀ e ∈ ((sessions : Model F _).run s).1, e.1 ≠ cid := by
  simp only [sessions, retired, Model.run_bind, Model.run_pure, openSessions_state, List.mem_map,
    List.mem_filterMap] at hr ⊢
  rintro _ ⟨e, he, rfl⟩ hec
  obtain ⟨⟨_, f⟩, -, hf⟩ := hr
  cases f
  case established c c' p hh sk rk d =>
    simp only at hf
    split at hf
    · cases hf
    · rename_i hn
      simp only [Option.some.injEq] at hf
      subst hf
      exact hn (List.any_eq_true.2 ⟨e, he, decide_eq_true hec⟩)
  all_goals cases hf

/-- **Caught: `retired` as shipped left a session with neither.** With
an established fact for cid on the dialer's side and no arrival record
of the connection (a crash between `onFrame`'s two writes), the shipped
`retiredShipped` does not name cid, and `sessions` does not list it: the
node never closes it, so its keys and its ephemeral stay in the store.
`retired_complete` is false of it. -/
theorem shipped_retired_misses (s : DB F) {y cid c p hh sk rk : B}
    (hr : ((rows established.all [] : Model F _).run s).1 = [(y, .established cid c p hh sk rk true)])
    (ha : ((rows recv.byOp [cid] : Model F _).run s).1 = []) :
    (y, Fact.established cid c p hh sk rk true) ∈ ((rows established.all [] : Model F _).run s).1 ∧
      ¬ ((∃ e ∈ ((sessions : Model F _).run s).1, e.1 = cid) ∨
        cid ∈ ((retiredShipped : Model F _).run s).1) := by
  have hs2 : ((rows established.all [] : Model F _).run s).2 = s := by rw [run_rows]
  have hall : ((allSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1 = [] := by
    simp only [allSessions, Model.run_bind, Model.run_pure]
    rw [hr, hs2]
    simp only [sessionsOf, sessionOf, ite_true, Model.run_bind, Model.run_pure, arrival]
    rw [ha]
    rfl
  have hopen : ((openSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1 = [] := by
    simp only [openSessions, Model.run_bind, Model.run_pure]
    rw [allSessions_state, hall]
    rfl
  refine ⟨by rw [hr]; exact List.mem_singleton_self _, ?_⟩
  rintro (⟨e, he, -⟩ | hm)
  · simp only [sessions, Model.run_bind, Model.run_pure, hopen, List.map_nil, List.not_mem_nil] at he
  · simp only [retiredShipped, Model.run_bind, Model.run_pure, allSessions_state, hall,
      List.filterMap_nil, List.not_mem_nil] at hm

end Connection
