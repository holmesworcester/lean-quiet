/-
A command-line peer for the end-to-end tests (and for trying it by hand):

    mdns_demo announce <instance> <type> <port> <seconds>
    mdns_demo browse <type> <seconds>

`announce` sends the service's records every second and answers questions
about it; `browse` asks every second and prints each service it finds
once: `found <instance> <host> <port> <txt,...> <addresses>`.
-/
import Mdns
open Mdns Std.Async

def showAddr (a : List UInt8) : String := ".".intercalate (a.map (toString ·.toNat))

def every (s : Std.Async.UDP.Socket) (m : Msg) (deadline : Nat) : IO Unit := do
  while (← IO.monoMsNow) < deadline do
    (Net.send s m).block
    IO.sleep 1000

def main (args : List String) : IO UInt32 := do
  let s ← Net.open
  match args with
  | ["announce", inst, type, port, secs] =>
    let host := (← IO.Process.run { cmd := "hostname" }).trimAscii.toString
    let me : Service := { inst, type, host := s!"{host}-lean", port := port.toNat!.toUInt16,
                          txt := ["impl=lean-mdns"], addrs := ← Net.localAddrs }
    let deadline := (← IO.monoMsNow) + secs.toNat! * 1000
    let _ ← IO.asTask (every s (announce me) deadline)
    (Net.loop s [me] [] (fun _ => pure ()) (stop := do pure ((← IO.monoMsNow) ≥ deadline))).block
    (Net.send s (goodbye me)).block
    pure 0
  | ["browse", type, secs] =>
    let deadline := (← IO.monoMsNow) + secs.toNat! * 1000
    let seen ← IO.mkRef ([] : List String)
    let _ ← IO.asTask (every s (query type) deadline)
    (Net.loop s [] [type] (stop := do pure ((← IO.monoMsNow) ≥ deadline)) fun f => do
      if f.ttl != 0 && !(← seen.get).contains f.inst then
        seen.modify (f.inst :: ·)
        IO.println s!"found {f.inst} {f.host} {f.port} {",".intercalate f.txt} {" ".intercalate (f.addrs.map showAddr)}"
        (← IO.getStdout).flush).block
    pure 0
  | _ =>
    IO.eprintln "usage: mdns_demo announce <instance> <type> <port> <seconds> | browse <type> <seconds>"
    pure 2
