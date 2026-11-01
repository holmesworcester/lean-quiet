import tests.endpoints.Harness
import app.Proofs

open Engine Community Connection EndpointNetwork

namespace EndpointChecks

def require (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"ok: {name}" else throw (IO.userError s!"FAIL: {name}")

def ad (detected observed : List ByteArray) (time expires : Nat) (signer : Device := dev "A") : Op :=
  let reqs := [c, c]
  let b : Community.Body := .addresses detected observed time expires .empty
  Community.mkOp reqs (.addresses detected observed time expires (Community.sig signer.sk reqs b))

def accepted (o : Op) : Bool :=
  (Community.validate ed25519 o [.admission c c (dev "A").pk (key "A"),
    .admission c c (dev "A").pk (key "A")]).isSome

/-- These checks construct proof terms after evaluating the exact hypotheses,
so a success cannot come from an uninhabited implication. -/
def memory (ops : List Op) : Execution.Memory :=
  { held := ((Engine.Sync.Turn.turn fam ops : Engine.Sync.HeldM F Unit) {}).2,
    entropy := fun n => Engine.sha256 s!"endpoint-progress/{n}".toUTF8 }

def readyWitness (s : Execution.Memory) (invite pub found : List ByteArray)
    (now : Nat) (old : Option (Nat × Nat)) (addr : ByteArray) :=
  if h : (Discovery.retryState (key "A")).eval s.held.db = old ∧
      Discovery.canTry now old = true ∧
      (Discovery.advertised c (key "A") now).eval s.held.db = pub ∧
      (Discovery.discovered (key "A") now).eval s.held.db = found ∧
      Hints.pick (Discovery.candidates invite pub found) (Discovery.nextAttempt old) = some addr then
    some (PLift.up (DiscoveryProgress.plan_ready s c (key "A") invite pub found now old addr
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2))
  else none

def backoffWitness (s : Execution.Memory) (invite : List ByteArray) (now last tries : Nat) :=
  if h : (Discovery.retryState (key "A")).eval s.held.db = some (last, tries) ∧
      Discovery.canTry now (some (last, tries)) = false then
    some (PLift.up (DiscoveryProgress.plan_backoff s c (key "A") invite now _ h.1 h.2))
  else none

def laterWitness (s : Execution.Memory) (pub : List ByteArray) (addr : ByteArray) :=
  if h : (Discovery.retryState (key "A")).eval s.held.db = some (1000, 0) ∧
      1000 + 60000 ≤ 61000 ∧
      (Discovery.advertised c (key "A") 61000).eval s.held.db = pub ∧
      (Discovery.discovered (key "A") 61000).eval s.held.db = [] ∧
      Hints.pick (Discovery.candidates [] pub []) (Discovery.nextAttempt (some (1000, 0))) = some addr then
    some (PLift.up (DiscoveryProgress.plan_after_backoff s c (key "A") [] pub [] 1000 0 61000 addr
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2))
  else none

def publicationWitness (ds os : List ByteArray) :=
  let o := ad ds os 1000 2000
  let sig := Community.sig (dev "A").sk [c, c] (.addresses ds os 1000 2000 .empty)
  if h : Community.check ed25519 o (.addresses ds os 1000 2000 sig)
      [.admission c c (dev "A").pk (key "A"), .admission c c (dev "A").pk (key "A")] =
      some (.addresses c (key "A") ds os 1000 2000) then
    some (PLift.up (DiscoveryLaws.publication_auth ed25519 o c c (dev "A").pk (key "A") c c (dev "A").pk
      (key "A") ds os 1000 2000 sig _ h))
  else none

theorem memory_reachable (ops : List Op) : (memory ops).held.Reachable Execution.family := by
  have h : Engine.Sync.Moves Execution.family {} (memory ops).held := .single (.turn ops {})
  exact h.store_reachable (Engine.Sync.held_empty_reachable Execution.family)

set_option maxRecDepth 4000 in
def storageCertificate (listen : ByteArray) (wall mono now : Nat) (cfg : Engine.Sync.Config)
    (input : Engine.Sync.Node.Input) (s : Execution.Memory)
    (hr : s.held.Reachable Execution.family) (n : Engine.Sync.Node) (o : Op) : Bool :=
  if ho : s.held.db.ops o.id = some o then
    if hs : (Execution.family.room o).isSome then
      if hq : s.held.db.queue = [] then
        let _moves := DiscoveryStorage.step_moves listen wall mono cfg n input now s
        let _retained := DiscoveryStorage.step_retains listen wall mono cfg n input now s ho hs
        let _settled := DiscoveryStorage.step_settled listen wall mono cfg n input now s hr hq
        true
      else false
    else false
  else false

def adapterWitness (listen : ByteArray) :=
  some (PLift.up (DiscoveryStorage.readOnly fam sodium listen 1000 1000 {}),
    PLift.up (DiscoveryStorage.setup_readOnly listen 1000 1000 {}))

/-- Evaluate distinctness, then apply every arbitration law to those same IDs. -/
def arbitrationWitness (a b peer : ByteArray) :=
  if h : a ≠ b then
    some (PLift.up (Winner.choose_comm a b),
      PLift.up (Winner.choose_stable a b),
      PLift.up (Winner.exactly_one a b h),
      PLift.up (DiscoveryLaws.kept_pair a b peer .empty .empty true false 1 99),
      PLift.up (DiscoveryLaws.both_choose_same a b peer peer .empty .empty .empty .empty 1 99 2 0),
      PLift.up (DiscoveryLaws.single_survivor a b peer .empty .empty 1 99 h),
      PLift.up (DiscoveryLaws.no_flapping a b peer .empty))
  else none

/-- Concrete successful premises and applications for the bounded policy laws. -/
def policyWitness (lan tail : ByteArray) :=
  let xs := [lan, tail]
  if h : 1 < (xs.take Hints.dialCap).length ∧
      Hints.fresh 1000 900 1100 = true ∧ 1000 + 60000 ≤ 61000 then
    some (PLift.up (DiscoveryLaws.candidate_cap xs xs xs),
      PLift.up (DiscoveryLaws.retry_eventually_due 1000 200 61000 h.2.2),
      PLift.up (DiscoveryLaws.candidate_visited xs 1 h.1),
      PLift.up (Hints.bounded_cap xs),
      PLift.up (Hints.delay_bounded 200),
      PLift.up (Hints.fresh_expires 1000 900 1100 h.2.1))
  else none

/-! ## Discovery bounds: concrete premises -/

instance bytesLawfulBEq : LawfulBEq ByteArray where
  rfl := by intro a; change (a.data == a.data) = true; simp
  eq_of_beq := by intro a b h; change (a.data == b.data) = true at h; exact ByteArray.ext (by simpa using h)

/-- Keys as numbers, for the scan core. -/
def natLt (a b : Nat) : Bool := decide (a < b)

theorem natLt_strict : Engine.Cursor.Strict natLt where
  irrefl a := by simp [natLt]
  trans h1 h2 := by simp only [natLt, decide_eq_true_eq] at *; omega
  total a b h := by simp only [natLt, decide_eq_true_eq]; omega

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

/-- A scan under an adaptive adversary: before each of steps 1–5 it files two
rows just past the cursor, ahead of the target 500. -/
def adv : Nat → List Nat × Option Nat
  | 0 => ([100, 200, 300, 400, 500], none)
  | k + 1 =>
    let R := (adv k).1
    let c' := Engine.Cursor.next natLt id R 2 (adv k).2
    let base := c'.getD 0
    ((if k < 5 then insertSorted (base + 1) (insertSorted (base + 2) R) else R), c')

def advR (k : Nat) : List Nat := (adv k).1
def advC (k : Nat) : Option Nat := (adv k).2
theorem adv_c (k : Nat) : advC (k + 1) = Engine.Cursor.next natLt id (advR k) 2 (advC k) := rfl

/-- The step when the adversarial scan first visits 500. -/
def advVisit : Option Nat :=
  (List.range 40).find? fun k => (Engine.Cursor.page natLt id (advR k) 2 (advC k)).contains 500

def cursorWitness :=
  if h : (∀ k, k ≤ (advR 5).length + 1 → Engine.Cursor.Sorted natLt id (advR k)) ∧
      (∀ k, k ≤ (advR 5).length + 1 → ∀ x ∈ advR k, id x ∈ advR 5) ∧
      (∀ k, k ≤ (advR 5).length + 1 → ∃ x ∈ advR k, id x = 500) then
    some (PLift.up (Engine.Cursor.visits natLt_strict 2 (by decide) (advR 5) advR advC h.1 h.2.1 adv_c h.2.2))
  else none

def distWitness :=
  let R := [10, 20, 30, 40, 50]
  if h : Engine.Cursor.Sorted natLt id R ∧ (∀ x ∈ R, id x ∈ R) ∧ 50 ∈ R ∧
      50 ∉ Engine.Cursor.page natLt id R 2 none then
    some (PLift.up (Engine.Cursor.dist_step natLt_strict R R 2 (by decide) h.1 h.2.1 h.2.2.1 none h.2.2.2))
  else none

/-- The members list a real store files, scanned from no cursor. -/
def membersRows (s : Execution.Memory) := DiscoveryBounds.rowsOf s.held.db Community.discoveryMembers

def scanC (s : Execution.Memory) : Nat → Option Engine.Pos
  | 0 => none
  | k + 1 => ((Discovery.page Community.discoveryMembers (scanC s k) : Execution.M _) s).1.2

theorem ownSorted (ops : List Op) :
    Engine.Cursor.Sorted DiscoveryBounds.ltPos (·.1) (membersRows (memory ops)) := by
  obtain ⟨_, hr, _⟩ := memory_reachable ops
  exact DiscoveryBounds.rows_strict (Engine.reach_inv hr) _

def scanWitness (s : Execution.Memory) (p : Engine.Pos) :=
  let U := (membersRows s).map fun (x : Engine.Pos × F) => x.1
  if h : (∀ k, k ≤ U.length + 1 → Engine.Cursor.Sorted DiscoveryBounds.ltPos (fun (x : Engine.Pos × F) => x.1) (membersRows s)) ∧
      (∀ k, k ≤ U.length + 1 → ∀ x ∈ membersRows s, x.2.isLeft = true) ∧
      (∀ k, k ≤ U.length + 1 → ∀ x ∈ membersRows s, x.1 ∈ U) ∧
      (∀ k, k ≤ U.length + 1 → p ∈ (membersRows s).map fun (x : Engine.Pos × F) => x.1) then
    some (PLift.up (DiscoveryBounds.scan_visits Community.discoveryMembers (fun _ => s) (scanC s) U
      h.1 h.2.1 h.2.2.1 (fun _ => rfl) h.2.2.2))
  else none

def pageWitness (s : Execution.Memory) :=
  PLift.up (DiscoveryBounds.page_run Community.discoveryMembers none s)

def staleSoundWitness (me : List ByteArray) (db : Engine.DB F) (x : Id) :=
  if h : x ∈ (Discovery.staleV me).eval db then
    some (PLift.up (DiscoveryBounds.stale_sound me db h))
  else none

def staleCompleteWitness (me : List ByteArray) (db : Engine.DB F) :=
  PLift.up (DiscoveryBounds.stale_complete me db)

def staleGoneWitness (me : List ByteArray) (db : Engine.DB F) (x : Id) (p : ByteArray) :=
  match ho : db.ops x with
  | some o =>
    if h : (p ∈ me ++ DiscoveryBounds.visitedIn db ∧
        x ∈ DiscoveryBounds.older Community.retry.byPeer [p] Discovery.staleCap db) ∧
        Execution.family.room o = none then
      some (PLift.up (DiscoveryBounds.stale_gone Execution.family me db ((Discovery.staleV me).eval db)
        (fun _ hx => hx) (Or.inr ⟨p, h.1.1, Or.inl h.1.2⟩) ho h.2))
    else none
  | none => none

def gapWitness (old new : ByteArray) :=
  if h : Discovery.due 70000 [new] [] (some (.addresses c (key "A") [old] [] 1000 2000)) = true then
    some (PLift.up (DiscoveryBounds.publish_gap 70000 [new] [] c (key "A") [old] [] 1000 2000 h))
  else none

def refreshWitness (lan : ByteArray) :=
  if h : Discovery.due (1000 + Discovery.refresh) [lan] [] (some (.addresses c (key "A") [lan] [] 1000 2000)) = true then
    some (PLift.up (DiscoveryBounds.publish_refresh (1000 + Discovery.refresh) [lan] [] c (key "A") 1000 2000 h))
  else none

/-- Visits 10 s apart, from a retry clock at attempt 3, 1 s in. -/
def visitT (i : Nat) : Nat := 1000 + 10000 * i
def visitSt : Nat → Option (Nat × Nat)
  | 0 => some (1000, 3)
  | i + 1 => DiscoveryBounds.visitStep (visitT i) (visitSt i)
theorem visitT_step (i : Nat) : visitT i + 10000 ≤ visitT (i + 1) := by simp only [visitT]; omega
theorem visit_past : DiscoveryBounds.Past visitT visitSt 0 := by
  intro t a h; simp only [visitSt, Option.some.injEq, Prod.mk.injEq] at h; simp only [visitT]; omega

def attemptsWitness (L : List ByteArray) :=
  if h : 2 < (L.take Hints.dialCap).length then
    some (PLift.up (DiscoveryBounds.attempts_reach L h 7))
  else none

def withinWitness :=
  PLift.up (DiscoveryBounds.attempt_within visitT visitSt 10000 (by decide) (fun _ => rfl) visitT_step 0 visit_past)

def reachWitness (L : List ByteArray) :=
  if h : 2 < (L.take Hints.dialCap).length ∧
      DiscoveryBounds.nextNo (visitSt 0) + (L.take Hints.dialCap).length < 2^63 then
    some (PLift.up (DiscoveryBounds.reaches L h.1 visitT visitSt 10000 (by decide) (fun _ => rfl)
      visitT_step visit_past h.2))
  else none

/-- A suite whose Diffie-Hellman never fails: a request can always be built. -/
def totalKeys : Keys := { sodium with suite := { Noise.suite with dh := fun a b => some (Engine.sha256 (a ++ b)) } }

def attemptWitness (s : Execution.Memory) (addr : ByteArray) (retry : Op) :=
  PLift.up (DiscoveryBounds.attempt_sends totalKeys addr (key "A") (nk "A") c (key "B") addr retry s
    (fun e => by simp [Connection.Request.op, Noise.write1, totalKeys]))

def memberWitness (s : Execution.Memory) (addr : ByteArray) :=
  if h : ((key "B") == (key "A")) = false ∧
      ((Community.allowPeer c (key "B")).liftL : View F Bool).eval s.held.db = true ∧
      ((Community.allowPeer c (key "A")).liftL : View F Bool).eval s.held.db = true ∧
      ((connectedTo (key "B") : Execution.M Bool) s).1 = false ∧
      (Discovery.retryState (key "B")).eval s.held.db = none ∧
      Discovery.canTry 1000 none = true ∧
      (Discovery.advertised c (key "B") 1000).eval s.held.db = [] ∧
      (Discovery.discovered (key "B") 1000).eval s.held.db = [addr] ∧
      Hints.pick (Discovery.candidates [] [] [addr]) (Discovery.nextAttempt none) = some addr then
    some (PLift.up (DiscoveryBounds.member_attempts sodium addr (key "A") (nk "A") 1000 (adm "B") c (adm "B")
      (dev "B").pk (key "B") s addr _ h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (DiscoveryProgress.plan_ready s c (key "B") [] [] [addr] 1000 none addr
        h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2)))
  else none

def main : IO Unit := do
  let lan := "192.168.4.35:47100".toUTF8
  let tail := "100.67.2.56:47100".toUTF8
  let a := ByteArray.mk #[1]
  let b := ByteArray.mk #[2]
  let peer := ByteArray.mk #[9]
  require "distinct simultaneous attempts have the same stable single winner"
    (a != b && kept [(b,peer,true,.empty,1),(a,peer,false,.empty,99)] == [a] &&
      kept [(a,peer,true,.empty,2),(b,peer,false,.empty,0)] == [a] &&
      Winner.choose (Winner.choose a b) b == a)
  require "arbitration premises and theorem applications" (arbitrationWitness a b peer).isSome
  require "bounded policy premises and theorem applications" (policyWitness lan tail).isSome
  let good := ad [lan] [tail] 1000 2000
  require "actual Ed25519 endpoint-op acceptance witness" (accepted good)
  require "publication proof premises hold on a real signature" (publicationWitness [lan] [tail]).isSome
  require "invite planner law has an inhabited running-state premise"
    (readyWitness (memory shared) [lan] [] [] 1000 none lan).isSome
  require "endpoint-op planner law has an inhabited running-state premise"
    (readyWitness (memory (shared ++ [good])) [] [lan, tail] [] 1000 none lan).isSome
  let localFound := Community.mkOp [] (.discovered (key "A") [tail] 1000 1000)
  require "DNS-SD observation planner law has an inhabited running-state premise"
    (readyWitness (memory (shared ++ [localFound])) [] [] [tail] 1000 none tail).isSome
  let retry := Community.mkOp [] (.retry (key "A") 1000 0)
  let retryMemory := memory (shared ++ [retry, ad [lan, tail] [] 60000 70000])
  require "backoff proof premises hold before the deadline" (backoffWitness retryMemory [lan] 1001 1000 0).isSome
  require "bounded waiting proves the next address is planned" (laterWitness retryMemory [lan, tail] tail).isSome
  require "another member cannot author A's endpoint op" (!accepted (ad [lan] [] 1000 2000 (dev "B")))
  require "nine addresses are rejected at validation" (!accepted (ad (List.replicate 9 lan) [] 1000 2000))
  require "lifetime beyond a day is rejected" (!accepted (ad [lan] [] 1000 (1000 + Hints.maxAge + 1)))
  require "a lifetime of a day is accepted" (accepted (ad [lan] [] 1000 (1000 + Hints.maxAge)))
  require "zero lifetime is rejected" (!accepted (ad [lan] [] 1000 1000))
  require "multicast destinations are rejected" (!accepted (ad ["224.0.0.251:5353".toUTF8] [] 1000 2000))
  require "zero TCP port is rejected" (!accepted (ad ["100.67.2.56:0".toUTF8] [] 1000 2000))
  require "expiry is strict" (!Hints.fresh 2000 1000 2000)
  require "future publication is not dialable" (!Hints.fresh 900 1000 2000)
  require "updated endpoint data does not reset retry clock"
    (!Discovery.canTry 1200 (some (1000, 5)))
  require "backoff releases by 60 seconds" (Discovery.canTry 61000 (some (1000, 500)))
  let hints := Link.hints [("docker0", [172,17,0,1], false), ("br-test", [192,168,80,1], false),
    ("wlan0", [192,168,4,35], false), ("tailscale0", [100,67,2,56], false)]
  require "invites carry LAN and tailnet, excluding Docker bridges" (hints == [lan, tail])
  let many := Link.hints ((List.range 10 |>.map fun i => ("wlan0", [192,168,4,i+1], false)) ++
    [("tailscale0", [100,67,2,56], false)])
  require "LAN aliases cannot crowd tailnet out of invite or publication caps"
    (many.length == 8 && many.head? == some "192.168.4.1:47100".toUTF8 && (many.take 4).contains tail)
  require "repeated interface addresses coalesce" ((Link.hints [("wlan0", [192,168,4,35], false),
    ("wlan1", [192,168,4,35], false)]).length == 1)
  let req := Community.issue c c (dev "A") (key "A") (seed "invite") hints
  require "multi-address invite roundtrips through the actual link parser"
    (Community.Invite.parse req.2.text == some req.2)
  let selfDiscovery := Community.mkOp [] (.discovered (key "A") [lan] 1000 100000)
  let reportReqs := [c, adm "B"]
  let reportBody : Community.Body := .sighting (key "A") tail 1000 .empty
  let report := Community.mkOp reportReqs (.sighting (key "A") tail 1000 (Community.sig (dev "B").sk reportReqs reportBody))
  let ownOps := shared ++ [Community.endpoint (nk "A"), secret (seed "A"),
    accept c (dev "A").pk, selfDiscovery, report]
  let ownMemory := memory ownOps
  require "discovery Node tick has inhabited storage-preservation premises"
    (storageCertificate lan 1000 1000 1000 {} .tick ownMemory (memory_reachable ownOps) (Engine.Sync.Node.boot fam [] 0) rootOp)
  require "both discovery adapter certificates are exercised" (adapterWitness lan).isSome
  let node := Engine.Sync.Node.boot fam [] 0
  let result := (node.step (DiscoveryStorage.setup lan 1000 1000 {}) .tick 1000) ownMemory
  require "storage witness tick actually stores discovery actions" (result.2.held.log.length > ownMemory.held.log.length)
  require "discovery tick retains shared root and finishes validation"
    (result.2.held.db.ops c == some rootOp && result.2.held.db.queue.isEmpty)
  let publications := (Discovery.publish c c (dev "A").pk (key "A") 1000 : Execution.M (List Op)) ownMemory |>.1
  require "owner republishes detected and authenticated observed hints"
    (publications.any fun o => match (Codec.decode o.body : Option Community.Body) with
      | some (.addresses ds os _ _ _) => ds == [lan] && os == [tail]
      | _ => false)
  let emptyMemory := memory (shared ++ [Community.endpoint (nk "A"), secret (seed "A"), accept c (dev "A").pk])
  require "startup does not publish an empty ad before interface detection"
    ((Discovery.publish c c (dev "A").pk (key "A") 1000 : Execution.M (List Op)) emptyMemory).1.isEmpty
  let db ← Db.openAt ":memory:"
  (Engine.receive fam (shared ++ [good, ad [] [] 2001 2100]) : SqlM F Unit).run db
  let current ← ((Discovery.advertised c (key "A") 2200).run : SqlM F _).run db
  require "an expired latest op never resurrects older addresses" current.isEmpty
  let svc := DiscoveryNet.service (key "A") 47100 [Std.Net.IPv4Addr.ofParts 100 67 2 56]
  let query := Mdns.unicastQuery DiscoveryNet.serviceType
  let some (reply, unicast) := Mdns.response [svc] query 5353 | throw (IO.userError "no DNS-SD reply")
  require "routed DNS-SD asks for and receives unicast" unicast
  let found := Mdns.found DiscoveryNet.serviceType reply
  require "same DNS-SD result maps to a bounded endpoint op" ((found.head?.bind (DiscoveryNet.foundOp · 1000)).isSome)
  require "malformed key cannot become a discovery op" ((DiscoveryNet.foundOp { inst := "bad", host := "bad", port := 1, txt := ["key=00"], addrs := [], ttl := 120 } 1000).isNone)
  -- Discovery bounds: each law applied to concrete premises.
  require "an adaptive adversary filing rows just ahead of the cursor still lets the scan reach its target"
    (cursorWitness.isSome && (advVisit.any fun k => k ≤ (advR 5).length + 1) && (advR 5).length == 15)
  require "a scan step that misses the target moves the cursor strictly closer" distWitness.isSome
  let _ := pageWitness ownMemory
  let some (root, _) := (membersRows ownMemory).head? | throw (IO.userError "no member rows")
  require "the dialer's real member scan visits every member within |U| + 2 steps"
    ((scanWitness ownMemory root).isSome && ((membersRows ownMemory).map (·.1)).all fun p => (scanWitness ownMemory p).isSome)
  let _ := ownSorted ownOps
  let retryOld := Community.mkOp [] (.retry (key "B") 1000 0)
  let retryNew := Community.mkOp [] (.retry (key "B") 2000 1)
  let scanOld := Community.mkOp [] (.scan (Codec.encode ((none : Option Engine.Pos), (none : Option Engine.Pos))) [] 1500)
  let scanNew := Community.mkOp [] (.scan (Codec.encode ((none : Option Engine.Pos), (none : Option Engine.Pos))) [key "B"] 2000)
  let staleMemory := memory (ownOps ++ [retryOld, retryNew, scanOld, scanNew])
  let named := (Discovery.staleV [key "A"]).eval staleMemory.held.db
  require "stale names the older retry clock and scan position, never the newest"
    (named.contains retryOld.id && named.contains scanOld.id && !named.contains retryNew.id && !named.contains scanNew.id)
  require "stale_sound applies to a named op" (staleSoundWitness [key "A"] staleMemory.held.db retryOld.id).isSome
  let _ := staleCompleteWitness [key "A"] staleMemory.held.db
  require "stale_gone applies: the older retry clock is a stored local op" (staleGoneWitness [key "A"] staleMemory.held.db retryOld.id (key "B")).isSome
  let after := ((Engine.Sync.Turn.purge fam named false : Engine.Sync.HeldM F Unit) staleMemory.held).2
  require "after the step's purge one retry clock and one scan position remain"
    ((after.db.ops retryOld.id).isNone && (after.db.ops scanOld.id).isNone &&
      (after.db.ops retryNew.id).isSome && (after.db.ops scanNew.id).isSome)
  require "changed hints after the gap are due" (gapWitness lan tail).isSome
  require "unchanged hints are due at half their life" (refreshWitness lan).isSome
  require "unchanged hints are not reissued before then"
    (!Discovery.due (1000 + Discovery.refresh - 1) [lan] [] (some (.addresses c (key "A") [lan] [] 1000 2000)))
  require "every retained address is attempted within |L| attempts" (attemptsWitness [lan, tail, "10.0.0.9:1".toUTF8]).isSome
  let _ := withinWitness
  require "a reachable third address is attempted within the reach bound" (reachWitness [lan, tail, "10.0.0.9:1".toUTF8]).isSome
  let heardB := memory (ownOps ++ [Community.mkOp [] (.discovered (key "B") [lan] 1000 100000)])
  require "a ready member visit runs the attempt, from a real store with B heard on the LAN"
    (memberWitness heardB lan).isSome
  let attemptOps := ((Discovery.attempt sodium lan (key "A") (nk "A") c (key "B") lan retryOld : Execution.M (List Op)) heardB).1
  require "the attempt holds the retry clock and a courier to the planned address"
    (attemptOps.contains retryOld && attemptOps.any fun o =>
      match (Codec.decode o.body : Option Connection.Body) with
      | some (.send a) => a == lan
      | _ => false)
  let _ := attemptWitness heardB lan retryOld
  IO.println "PASS endpoint validation, source selection, expiry and DNS-SD checks"

end EndpointChecks

def main : IO Unit := EndpointChecks.main
