import app.Proofs
import tests.vacuity.ProductionBootstrap

/- Synthetic Alice/Bob identities and messages; native signatures, Noise,
AEAD and the complete production Node handlers. Not captured user data. -/
namespace Vacuity.StorageEffects
open Engine Engine.Sync Community Connection.Execution Vacuity.ProductionBootstrap

def finished (s : Scenario) := trace setup initial s.completed

theorem source_reachable (s : Scenario) :
    ((finished s).b.memory.held).Reachable Connection.Execution.family :=
  (empty_trace_store setup (entropy "alice") (entropy "bob") s.completed .b).1

theorem source_invariant (s : Scenario) : Inv Connection.Execution.family (finished s).b.memory.held.db := by
  obtain ⟨_, hr, _⟩ := source_reachable s
  exact reach_inv hr

theorem source_settled (s : Scenario) : (finished s).b.memory.held.db.queue = [] :=
  (empty_trace_store setup (entropy "alice") (entropy "bob") s.completed .b).2

/-- Checks the native membership and shared scope before applying the full
handler theorem. Reachability and initial settling come from the exact
production event prefix, not from native assumptions. -/
def eventCertificate (s : Scenario) (input : Node.Input) :=
  let p := (finished s).b
  if ho : p.memory.held.db.ops s.message.id = some s.message then
    if hs : (Connection.Execution.family.room s.message).isSome then
      some (PLift.up (And.intro
        (production_step_retains setup .b p.node input (finished s).now p.memory ho hs)
        (And.intro
          (production_step_reachable setup .b p.node input (finished s).now p.memory (source_reachable s))
          (production_step_settled setup .b p.node input (finished s).now p.memory
            (source_reachable s) (source_settled s)))))
    else none
  else none

/-- The fresh post must actually be absent and shared before applying the
full write-handler theorem; reachability supplies its store invariant. -/
def freshWriteCertificate (p : Peer) (o : Op) (now : Nat)
    (hi : Inv Connection.Execution.family p.memory.held.db) :=
  if hn : p.memory.held.db.ops o.id = none then
    if hs : (Connection.Execution.family.room o).isSome then
      some (PLift.up (production_write_receives setup .b p.node p.memory
        [o] now hi (o := o) (List.mem_singleton_self _) hs
        (by intro q hq _; exact List.mem_singleton.mp hq)
        (by intro q hq; rw [hn] at hq; cases hq)))
    else none
  else none

def writeCertificate (s : Scenario) :=
  freshWriteCertificate (finished s).b s.recoveryMessage (finished s).now (source_invariant s)

theorem source_history (s : Scenario) : (finished s).b.memory.held.LogAgrees :=
  (empty_trace_history setup (entropy "alice") (entropy "bob") s.completed .b).2

/-- Existing-row bounds are checked natively. The history invariant itself
comes from the actual arbitrary-prefix theorem, not a checked replacement DB. -/
def historyCertificateFor (p : Peer) (input : Node.Input) (now seq : Nat)
    (hr : p.memory.held.Reachable Connection.Execution.family) (ha : p.memory.held.LogAgrees) :=
  if hb : 0 < seq ∧ seq ≤ (Catalog.shared Connection.Execution.family p.memory.held).length then
    some (PLift.up (And.intro
      ((production_step_history setup .b p.node input now p.memory).catalog_read hr ha hb.1 hb.2)
      ((production_step_history setup .b p.node input now p.memory).ceiling_mono hr ha)))
  else none

def historyCertificate (s : Scenario) (input : Node.Input) (seq : Nat) :=
  historyCertificateFor (finished s).b input (finished s).now seq (source_reachable s) (source_history s)

theorem runInterval (w : World) (r : Run setup w) (o : Op)
    (ho : w.b.memory.held.db.ops o.id = some o) (hs : (Connection.Execution.family.room o).isSome)
    (hr : w.b.memory.held.Reachable Connection.Execution.family) (ha : w.b.memory.held.LogAgrees) :
    ((r.state 9).peer .b).memory.held.db.ops o.id = some o ∧
      ((r.state 9).peer .b).memory.held.Reachable Connection.Execution.family ∧
      ((r.state 9).peer .b).memory.held.LogAgrees ∧
      ∃ tail, Catalog.shared Connection.Execution.family ((r.state 9).peer .b).memory.held =
        Catalog.shared Connection.Execution.family w.b.memory.held ++ tail := by
  have hzero : ((r.state 0).peer .b).memory.held = w.b.memory.held := by rw [r.zero]; rfl
  have retained := r.shared_retained .b (n := 0) (k := 9) (i := o.id) (o := o) (by decide)
    (hzero.symm ▸ ho) hs
  have history := r.history .b (n := 0) (k := 9) (by decide)
  rw [hzero] at history
  exact ⟨retained, history hr ha⟩

/-- A populated production world is extended by the actual infinite
scheduler. The interval is nonzero and includes both ticks and deliveries. -/
def runCertificateFor (w : World) (o : Op)
    (hr : w.b.memory.held.Reachable Connection.Execution.family) (ha : w.b.memory.held.LogAgrees) :=
  if ho : w.b.memory.held.db.ops o.id = some o then
    if hs : (Connection.Execution.family.room o).isSome then
      some (PLift.up (runInterval w (fairRun setup w) o ho hs hr ha))
    else none
  else none

def runCertificate (s : Scenario) :=
  runCertificateFor (finished s) s.message (source_reachable s) (source_history s)

/-! The community laws in every production trace. After the bootstrap,
Alice's actual remover intent removes Bob's user; each certificate takes
the trace's store from `trace_good`, never from a checked replacement. -/

def storeAfter (acts : List Action) (side : Connection.Execution.Side) : DB Connection.F :=
  ((trace setup initial acts).peer side).memory.held.db

def removal (s : Scenario) : List Op :=
  (view (finished s) .a (removeMember c s.request.id alice)).ops

def removedActions (s : Scenario) : List Action := s.completed ++ [.write .a (removal s)]

/-- Every Valid admission of node key e in c is of user u, checked over the
stored rows; `Inv` rules out a verdict on an unstored id. -/
def ownedBy (st : DB Connection.F) (e : Community.Key) (u x : Id) : Bool :=
  match st.status x with
  | some (.valid (.inl (.admission c' u' _ e'))) => decide ((c' = c ∧ e' = e) → u' = u)
  | _ => true

theorem owned {st : DB Connection.F} (hi : Inv Connection.Execution.family st)
    {e : Community.Key} {u : Id} (hb : st.stored.all (ownedBy st e u) = true)
    {x u' : Id} {d : Community.Key} (hx : st.status x = some (.valid (.inl (.admission c u' d e)))) :
    u' = u := by
  obtain ⟨o, _, ho, _⟩ := spec_valid_inv (hi.sound x _ hx)
  have hs : x ∈ st.stored := (hi.stored x).2 (by rw [ho]; rfl)
  have hh := (List.all_eq_true.1 hb) x hs
  simp only [ownedBy, hx] at hh
  exact of_decide_eq_true hh (by simp)

/-- The op's own verdict at the peer is a Valid removal of user u from c. -/
def removedIn (st : DB Connection.F) (o : Op) (u : Id) :
    Option (PLift (∃ x r, st.status x = some (.valid (.inl (.removal c u r))))) :=
  match hst : st.status o.id with
  | some (.valid (.inl (.removal c' u' r))) =>
    if h : c' = c ∧ u' = u then some (PLift.up ⟨o.id, r, by rw [hst, h.1, h.2]⟩) else none
  | _ => none

/-- An admitted member is allowed: Alice's trust rule takes Bob's node,
and the trace law names the admitted live device under it. -/
def admittedCertificateFor (acts : List Action) :=
  if h : ((allowPeer c keyB).liftL : View Connection.F Bool).eval (storeAfter acts .a) = true then
    some (PLift.up ((connect_iff_trace setup (entropy "alice") (entropy "bob") acts .a c keyB).1 h))
  else none

/-- x's verdict at the peer is a Valid admission of Bob's device and node
key, for user u. -/
def admits (st : DB Connection.F) (u x : Id) : Bool :=
  match st.status x with
  | some (.valid (.inl (.admission c' u' d e))) => decide (c' = c ∧ u' = u ∧ d = bob.pk ∧ e = keyB)
  | _ => false

theorem admits_status {st : DB Connection.F} {u x : Id} (h : admits st u x = true) :
    st.status x = some (.valid (.inl (.admission c u bob.pk keyB))) := by
  unfold admits at h
  split at h
  next _ _ _ _ hx => obtain ⟨rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h; exact hx
  next => cases h

/-- Bob's admission is a stored Valid verdict at Alice, so `Admitted`. -/
def admissionCertificateFor (acts : List Action) (u : Id) :=
  if h : (storeAfter acts .a).stored.any (admits (storeAfter acts .a) u) = true then
    some (PLift.up ((admitted_trace setup (entropy "alice") (entropy "bob") acts .a).2
      (let ⟨x, _, hx⟩ := List.any_eq_true.1 h; ⟨x, admits_status hx⟩)))
  else none

/-- A removal stored and the removed key refused: Alice holds a Valid
removal of u, every admission of Bob's node key is u's, and the trace law
refuses that key. Withholding the removal must reject it. -/
def removalCertificateFor (acts : List Action) (o : Op) (u : Id) :=
  match removedIn (storeAfter acts .a) o u with
  | none => none
  | some ⟨hr⟩ =>
    if hb : (storeAfter acts .a).stored.all (ownedBy (storeAfter acts .a) keyB u) = true then
      some (PLift.up (removal_cuts_off_trace setup (entropy "alice") (entropy "bob") acts .a
        ((removed_trace setup (entropy "alice") (entropy "bob") acts .a).2 hr)
        fun u' d had => by
          obtain ⟨x, hx⟩ := (admitted_trace setup (entropy "alice") (entropy "bob") acts .a).1 had
          rw [owned (trace_good setup (entropy "alice") (entropy "bob") acts .a).1 hb hx] at had
          exact ⟨keyB, had⟩))
    else none

/-- The same premises, as every admission of Bob's node key being cut. -/
def refuseCertificateFor (acts : List Action) (o : Op) (u : Id) :=
  match removedIn (storeAfter acts .a) o u with
  | none => none
  | some ⟨hr⟩ =>
    if hb : (storeAfter acts .a).stored.all (ownedBy (storeAfter acts .a) keyB u) = true then
      some (PLift.up (refuse_nonmember_trace setup (entropy "alice") (entropy "bob") acts .a c keyB
        fun u' d had => by
          obtain ⟨x, hx⟩ := (admitted_trace setup (entropy "alice") (entropy "bob") acts .a).1 had
          have hu := owned (trace_good setup (entropy "alice") (entropy "bob") acts .a).1 hb hx
          subst hu
          exact ⟨u', keyB, had, (removed_trace setup (entropy "alice") (entropy "bob") acts .a).2 hr⟩))
    else none

def syncs (rs : List Engine.Sync.Room) : Bool :=
  rs.any fun | .sync r => decide (r = c) | _ => false

def peersAt (acts : List Action) (cid : Id) : List Community.Key :=
  Connection.peersOf (Engine.eval (storeAfter acts .a) (Connection.established.byConn.query [cid]))

/-- A run from `empty`: the given actions, then idling. -/
def walk (acts : List Action) : Nat → World
  | 0 => initial
  | n + 1 => step setup (walk acts n) (acts.getD n .idle)

def prefixRun (acts : List Action) : Run setup initial :=
  ⟨walk acts, fun n => acts.getD n .idle, rfl, fun _ => rfl⟩

/-- `Run.good` on a run through the bootstrap and the removal; its state
there is that trace (`Run.state_trace`), which the runner checks holds the
Valid removal. -/
def runGoodCertificate (s : Scenario) :=
  let acts := removedActions s
  some (PLift.up (And.intro (Run.good (prefixRun acts) acts.length .a)
    ((prefixRun acts).state_trace acts.length)))

def isValid (s : Memory) (o : Op) : Bool :=
  match s.held.db.status o.id with
  | some (.valid (.inl (.message ..))) => true
  | _ => false

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  let some scene := scenario | t.ok "native production scenario constructs" false; t.finish "storage-effects"
  let w := finished scene
  let p := w.b
  let some (cid, _) := p.node.conns.head? |
    t.ok "fixture has a production session" false; t.finish "storage-effects"
  let sealed := (Connection.sealFor Connection.sodium cid
    (Codec.encode [scene.recoveryMessage.bytes]) : M (Option ByteArray)) w.a.memory
  let some sealedBytes := sealed.1 |
    t.ok "actual sender hook seals new message" false; t.finish "storage-effects"
  let frameInput := Node.Input.frame (setup.addr .a) (tagged sealedTag sealedBytes)
  let written := p.node.step (setup.sync .b) (.write [scene.recoveryMessage]) w.now p.memory
  let framed := p.node.step (setup.sync .b) frameInput w.now p.memory
  let ticked := p.node.step (setup.sync .b) .tick w.now p.memory
  let closed := p.node.step (setup.sync .b) (.close (setup.addr .a)) w.now p.memory
  let malformed := p.node.step (setup.sync .b) (.frame (setup.addr .a) (tagged sealedTag "bad".toUTF8)) w.now p.memory
  t.ok "fixture starts with valid shared message and no replacement post"
    (isValid p.memory scene.message && (p.memory.held.db.ops scene.recoveryMessage.id).isNone)
  t.ok "sender sealing advances actual entropy cursor"
    (sealed.2.cursor == w.a.memory.cursor + 1)
  for (label, input) in [("write", Node.Input.write [scene.recoveryMessage]),
      ("frame", frameInput), ("tick", .tick), ("close", .close (setup.addr .a))] do
    t.ok s!"{label}: native premises apply full handler retention and settling"
      (eventCertificate scene input).isSome
  let catalog := Catalog.held Connection.Execution.family
  let oldRows := Catalog.shared Connection.Execution.family p.memory.held
  let seq := oldRows.idxOf scene.message + 1
  t.ok "nonempty catalog position contains the retained signed message"
    ((catalog.read seq p.memory.held).1 == some scene.message.id)
  for (label, input) in [("write", Node.Input.write [scene.recoveryMessage]),
      ("frame", frameInput), ("tick", .tick), ("close", .close (setup.addr .a))] do
    t.ok s!"{label}: complete handler preserves captured catalog position"
      (historyCertificate scene input seq).isSome
  t.ok "catalog position zero and beyond captured ceiling reject witness"
    (!(historyCertificate scene .tick 0).isSome &&
      !(historyCertificate scene .tick (oldRows.length + 1)).isSome)
  t.ok "actual append and session purge keep original message position"
    ([written.2, framed.2, ticked.2, closed.2].all fun memory =>
      (catalog.read seq memory.held).1 == some scene.message.id)
  t.ok "nonempty nine-step production continuation applies retention and history laws"
    ((runCertificate scene).isSome &&
      ((fairRun setup w).state 9).b.memory.held.db.ops scene.message.id == some scene.message)
  t.ok "absent message rejects infinite-run retention premises"
    (!(runCertificateFor w scene.recoveryMessage (source_reachable scene) (source_history scene)).isSome)
  t.ok "actual tick visits catalog and emits a bounded retry frame"
    (((Connection.retryKey cid : M _) p.memory).1.any (fun peer => (ticked.2.retries peer).isSome) &&
      ticked.1.2.serve > 0)
  t.ok "fresh write premises certify bytes committed by the complete handler"
    (writeCertificate scene).isSome
  t.ok "existing-byte control rejects fresh-write premise"
    (!(writeCertificate { scene with recoveryMessage := scene.message }).isSome)
  t.ok "actual write stores and validates new shared message"
    (written.2.held.db.ops scene.recoveryMessage.id == some scene.recoveryMessage &&
      isValid written.2 scene.recoveryMessage)
  t.ok "actual sealed frame stores and validates new shared message"
    (framed.2.held.db.ops scene.recoveryMessage.id == some scene.recoveryMessage &&
      isValid framed.2 scene.recoveryMessage)
  t.ok "all full handlers retain old shared bytes and finish validation"
    ([written.2, framed.2, ticked.2, closed.2, malformed.2].all fun s =>
      s.held.db.ops scene.message.id == some scene.message && s.held.db.queue.isEmpty)
  t.ok "close actually purges session secrets and connection operations"
    (!closed.1.2.purged.isEmpty && (closed.2.held.db.ops cid).isNone && closed.1.1.conns.isEmpty)
  t.ok "close keeps shared message valid while local connection disappears"
    (isValid closed.2 scene.message)
  let directlyPurged := (Turn.purge Connection.Execution.family [scene.message.id] true : M Unit) p.memory
  t.ok "even explicitly naming a shared message in purge retains and revalidates it"
    (directlyPurged.2.held.db.ops scene.message.id == some scene.message &&
      isValid directlyPurged.2 scene.message && directlyPurged.2.held.db.queue.isEmpty)
  t.ok "malformed frame cannot insert the absent new message"
    ((malformed.2.held.db.ops scene.recoveryMessage.id).isNone)
  let absentScene := { scene with message := scene.recoveryMessage }
  t.ok "unheld-operation premise rejects the retention certificate"
    (!(eventCertificate absentScene .tick).isSome)
  -- The community laws in every production trace.
  let bobUser := scene.request.id
  let some rm := (removal scene).head? |
    t.ok "Alice's remover intent writes a removal of Bob" false; t.finish "storage-effects"
  t.ok "remover intent writes one removal" ((removal scene).length == 1)
  let acts := removedActions scene
  let some (acid, _) := w.a.node.conns.head? |
    t.ok "Alice holds a production session" false; t.finish "storage-effects"
  t.ok "admitted member: the trace law takes Bob's node at Alice"
    (admittedCertificateFor scene.completed).isSome
  t.ok "admitted member: Bob's admission is a Valid verdict at Alice"
    (admissionCertificateFor scene.completed bobUser).isSome
  t.ok "before removal: the session names Bob's node and carries c's sync"
    ((peersAt scene.completed acid).contains keyB &&
      syncs ((Connection.roomsV acid).eval (storeAfter scene.completed .a)))
  t.ok "removal stored: Alice holds a Valid removal of Bob's user"
    (removedIn (storeAfter acts .a) rm bobUser).isSome
  t.ok "removal stored: the trace law refuses Bob's node"
    (removalCertificateFor acts rm bobUser).isSome
  t.ok "removal stored: so does the cut-admissions form"
    (refuseCertificateFor acts rm bobUser).isSome
  t.ok "removal stored: Alice's trust rule natively refuses Bob's node"
    (!(view (trace setup initial acts) .a (allowPeer c keyB)))
  t.ok "removal stored: Bob's admission is still Valid, so the ownership premise is not vacuous"
    (admissionCertificateFor acts bobUser).isSome
  -- Observed, not a law here: the write's own entry point closes Alice's
  -- session with Bob, so no reachable two-peer state keeps a session
  -- naming a removed peer.
  t.ok "removal stored: the same write closed Alice's session with Bob"
    ((trace setup initial acts).a.node.conns.isEmpty && (peersAt acts acid).isEmpty)
  t.ok "a run from empty through the removal: Run.good applies, and its state holds the removal"
    ((runGoodCertificate scene).isSome &&
      decide ((walk acts acts.length).a.memory.held.db.ops rm.id = some rm))
  t.ok "removal withheld: removal and refusal certificates reject"
    (!(removalCertificateFor scene.completed rm bobUser).isSome &&
      !(refuseCertificateFor scene.completed rm bobUser).isSome)
  t.ok "removal withheld: Alice's trust rule still takes Bob's node"
    (view w .a (allowPeer c keyB))
  t.ok "wrong user: a removal of Alice's own user is not held"
    (!(removalCertificateFor acts rm c).isSome)
  t.finish "full production node storage effects"

end Vacuity.StorageEffects
