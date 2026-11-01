import tests.endpoints.Harness
import ops.connection.DiscoveryStorage
import ops.connection.DiscoveryProgress

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
      Endpoint.pick (Discovery.candidates invite pub found) (Discovery.nextAttempt old) = some addr then
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
      Endpoint.pick (Discovery.candidates [] pub []) (Discovery.nextAttempt (some (1000, 0))) = some addr then
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
  if h : 1 < (xs.take Endpoint.dialCap).length ∧
      Endpoint.fresh 1000 900 1100 = true ∧ 1000 + 60000 ≤ 61000 then
    some (PLift.up (DiscoveryLaws.candidate_cap xs xs xs),
      PLift.up (DiscoveryLaws.retry_eventually_due 1000 200 61000 h.2.2),
      PLift.up (DiscoveryLaws.candidate_visited xs 1 h.1),
      PLift.up (Endpoint.bounded_cap xs),
      PLift.up (Endpoint.delay_bounded 200),
      PLift.up (Endpoint.fresh_expires 1000 900 1100 h.2.1))
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
  require "lifetime beyond five minutes is rejected" (!accepted (ad [lan] [] 1000 301001))
  require "zero lifetime is rejected" (!accepted (ad [lan] [] 1000 1000))
  require "multicast destinations are rejected" (!accepted (ad ["224.0.0.251:5353".toUTF8] [] 1000 2000))
  require "zero TCP port is rejected" (!accepted (ad ["100.67.2.56:0".toUTF8] [] 1000 2000))
  require "expiry is strict" (!Endpoint.fresh 2000 1000 2000)
  require "future publication is not dialable" (!Endpoint.fresh 900 1000 2000)
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
  IO.println "PASS endpoint validation, source selection, expiry and DNS-SD checks"

end EndpointChecks

def main : IO Unit := EndpointChecks.main
