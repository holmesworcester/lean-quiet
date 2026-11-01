/- Actual TCP/Noise/SQLite sessions discovered in separate OS processes.
Fixed public fixture identities are exclusively for tests. -/
import ops.connection.DiscoveryNet
import tests.engine.Lib

namespace EndpointNetwork
open Engine Engine.Sync Community Connection

def fam : Family F := node ed25519 sodium
def seed (name : String) := sha256 s!"endpoint-test/device/{name}".toUTF8
def nk (name : String) := sha256 s!"endpoint-test/node/{name}".toUTF8
def dev (name : String) := Device.ofSeed (seed name)
def key (name : String) := cryptoSeal.pub (nk name)
def rootOp := root (dev "A") (key "A")
def c := rootOp.id

def shared : List Op :=
  let bearer := Device.named "endpoint-test/invite"
  let inv := invite c c (dev "A") bearer.pk false 1
  let req := Community.request c inv.id (dev "B") (key "B") bearer.sk
  let approval := approve c req.id c (dev "A")
  [rootOp, inv, req, approval, admit c req.id [approval.id]]

def adm (name : String) : Id := if name == "A" then c else shared.getLast!.id

def marker (name : String) : Op := profile c (adm name) (dev name) s!"hello from {name}".toUTF8 1

def look {α} (path : String) (q : SqlM F α) : IO α := do q.run (← Db.openAt path)

def main (args : List String) : IO UInt32 := do
  let name := args[0]?.getD "A"
  let path := args[1]?.getD "out/endpoints/A.db"
  let port := (args[2]?.getD "49101").toNat!
  let mode := args[3]?.getD "lan"
  let address := args[4]?.getD s!"127.0.0.1:{port}"
  let duration := (args[5]?.getD "45").toNat!
  let remote := args[6]?.getD ""
  let other := if name == "A" then "B" else "A"
  let db ← Db.openAt path
  let wall ← DiscoveryNet.wallNow
  let mono ← IO.monoMsNow
  let h := Discovery.hooks fam sodium address.toUTF8 wall mono
  let x : Sync F (SqlM F) := { fam, cfg := { every := 500, askTime := 2000 }, hooks := h }
  let localOps := [Community.endpoint (nk name), secret (seed name), accept c (dev name).pk]
  let ops := if mode == "invite" && name == "B" then
      let req := shared[2]!
      localOps ++ [req, Community.mkOp [] (.joining c (key "A")
        ["127.0.0.1:1".toUTF8, remote.toUTF8] req.id "Bob".toUTF8 (dev "B").pk 0)]
    else shared ++ localOps
  discard <| ((Node.boot fam [] 0).onWrite x ops mono).run db
  let r ← Runner.start x db 0 port.toUInt16 (cfg := { tickMs := 100, stopMs := 500 })
  try
    if mode == "lan" || mode == "tailnet" then
      let seeds := (remote.splitOn ",").filterMap Std.Net.IPv4Addr.ofString
      DiscoveryNet.start r path seeds
    if mode == "op" then
      let hs := [remote.toUTF8]
      let reqs := [c, adm other]
      let body : Community.Body := .addresses hs [] wall (wall + Endpoint.maxAge) .empty
      r.write [Community.mkOp reqs (.addresses hs [] wall (wall + Endpoint.maxAge)
        (Community.sig (dev other).sk reqs body))]
    if mode == "simultaneous" then
      -- Both OS processes wait for the same externally written barrier.
      let barrier := args[7]?.getD "out/endpoints/go"
      while !(← System.FilePath.pathExists barrier) do IO.sleep 10
      let e := sha256 s!"endpoint-test/simultaneous/{name}".toUTF8
      let some req := Request.op sodium (nk name) (key other) e (hello c address.toUTF8 [])
        | throw (IO.userError "request construction failed")
      r.write [req, Eph.op e req.id, Send.op remote.toUTF8 req]
    r.write [marker name]
    IO.println s!"READY {name} {r.port} {mode}"
    (← IO.getStdout).flush
    let deadline := (← IO.monoMsNow) + duration * 1000
    let mut previous : List Id := []
    let mut stable := 0
    let mut success := false
    while (← IO.monoMsNow) < deadline do
      let ids := (← look path (sessions : SqlM F _)).map (·.1)
      let received ← look path (Store.getStatus (marker other).id : SqlM F _)
      let valid := match received with | some (.valid _) => true | _ => false
      if ids.length == 1 && valid then
        if previous == ids then stable := stable + 1 else stable := 0
        if stable ≥ 30 then
          IO.println s!"PASS {name} single stable session {DiscoveryNet.hex ids.head!}; peer marker received"
          (← IO.getStdout).flush
          success := true
          break
      previous := ids
      IO.sleep 100
    if !success then
      let all ← look path (allSessions : SqlM F _)
      IO.eprintln s!"FAIL {name}: {all.length} sessions, no stable authenticated marker exchange"
    -- Keep the successful side available long enough for its peer's check.
    if success then IO.sleep 5000
    IO.println "stopping TCP runner"
    (← IO.getStdout).flush
    r.stop
    IO.println "TCP runner stopped"
    (← IO.getStdout).flush
    return if success then 0 else 1
  catch e =>
    IO.eprintln s!"FAIL {name}: {e}"
    r.stop
    return 1

end EndpointNetwork

