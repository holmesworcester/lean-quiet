/-
The codec and service logic on real and hostile packets.

* Fixtures: packets captured on a LAN (tests/fixtures: avahi announcing
  and probing a "_leanchat._udp" service, eero routers' answers, a Sonos
  speaker) all decode, re-encode to a message that decodes the same (the
  laws, run on the compiled code), and say what they said on the wire.
* Hostile packets: pointer loops, pointers to themselves and forward,
  labels of 64+ bytes, names over 255 bytes built from pointer chains,
  every truncation of every fixture: all `none`, none of them hang.
* Mutation fuzzing of the fixtures (deterministic, 200k packets): decode
  never fails to return, and what it accepts round-trips and is in bounds.
* Services: an announce decodes and is found by a browser; a query for the
  type is answered with the service's records, a query for another type
  is not.
-/
import engine.wire.mdns.Mdns
open Mdns

initialize fails : IO.Ref Nat ← IO.mkRef 0

def check (what : String) (ok : Bool) : IO Unit := do
  if !ok then
    IO.eprintln s!"FAIL {what}"
    fails.modify (· + 1)

def bytes (xs : List Nat) : ByteArray := ⟨(xs.map (·.toUInt8)).toArray⟩

def header (q an : Nat) (flags : Nat := 0) : List Nat :=
  [0, 0, flags / 256, flags % 256, 0, q, 0, an, 0, 0, 0, 0]

def labelBytes (s : String) : List Nat := s.utf8ByteSize :: s.toUTF8.toList.map (·.toNat)

def nameOk (n : Name) : Bool := n.all (fun l => 0 < l.length && l.length < 64) && n.wireLen ≤ 255

def recOk (r : Record) : Bool := nameOk r.name &&
  match r.data with
  | .a a => a.length == 4
  | .aaaa a => a.length == 16
  | .ptr n | .srv _ _ _ n => nameOk n
  | .txt ss => ss.all (·.length < 256)
  | .other t _ => !known t

def msgOk (m : Msg) : Bool :=
  m.questions.all (nameOk ·.name) && (m.answers ++ m.authority ++ m.additional).all recOk

def fixtures : IO (List (String × ByteArray)) := do
  let dir : System.FilePath := "tests/fixtures"
  let es ← dir.readDir
  let es := es.qsort (·.fileName < ·.fileName)
  es.toList.mapM fun e => do pure (e.fileName, ← IO.FS.readBinFile e.path)

def roundtrips (p : ByteArray) : Bool :=
  match decode p with
  | some m => decode (encode m) == some m && msgOk m
  | none => true

def main : IO UInt32 := do
  -- Fixtures
  let fx ← fixtures
  check "fixtures present" (fx.length ≥ 20)
  for (f, p) in fx do
    match decode p with
    | none => check s!"{f} decodes" false
    | some m =>
      check s!"{f} round-trips" (decode (encode m) == some m)
      check s!"{f} in bounds" (msgOk m)
  -- What the avahi announcement said.
  let p ← IO.FS.readBinFile "tests/fixtures/avahi-171.bin"
  match decode p with
  | none => check "avahi-171 decodes" false
  | some m =>
    match found "_leanchat._udp" m with
    | [f] =>
      check "avahi: instance" (f.inst == "Lean fixture")
      check "avahi: host" (f.host == "desktop")
      check "avahi: port" (f.port == 7777)
      check "avahi: txt" (f.txt == ["proto=lean", "v=1"])
      check "avahi: address" (f.addrs == [[172, 21, 0, 1]])
    | fs => check s!"avahi-171: one service, got {fs.length}" false
    check "avahi: a query is not answered by a browser with no services" (react [] m == none)

  -- Hostile packets
  let q1 := header 1 0
  let hostile : List (String × List Nat) := [
    ("pointer to itself", q1 ++ [0xC0, 12, 0, 12, 0, 1]),
    ("pointer forward", q1 ++ [0xC0, 14, 0, 12, 0, 1, 1, 97, 0]),
    ("two pointers in a loop", header 2 0 ++ [1, 97, 0xC0, 19, 0, 12, 0, 1] ++ [0xC0, 12, 0, 12, 0, 1]),
    ("label of 64 bytes", q1 ++ [64] ++ List.replicate 64 97 ++ [0, 0, 12, 0, 1]),
    ("reserved label kind 0x40", q1 ++ [0x40, 0, 0, 12, 0, 1]),
    ("pointer past the end", q1 ++ [0xC0]),
    ("count larger than the packet", header 5 0 ++ [1, 97, 0, 0, 12, 0, 1]),
    ("A record with 5 bytes", header 0 1 0x8400 ++ [1, 97, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 5, 1, 2, 3, 4, 5]),
    ("rdlength past the end", header 0 1 0x8400 ++ [1, 97, 0, 0, 16, 0, 1, 0, 0, 0, 1, 0, 9, 1, 97]),
    ("TXT string past its rdata", header 0 1 0x8400 ++ [1, 97, 0, 0, 16, 0, 1, 0, 0, 0, 1, 0, 2, 5, 97, 97, 97]),
    ("PTR name shorter than rdlength", header 0 1 0x8400 ++ [1, 97, 0, 0, 12, 0, 1, 0, 0, 0, 1, 0, 4, 1, 98, 0, 0]),
    ("trailing byte", q1 ++ [1, 97, 0, 0, 12, 0, 1, 0])
  ]
  for (what, xs) in hostile do
    check s!"hostile: {what}" (decode (bytes xs) == none)
  -- Names from a chain of pointers: question k is a 63-byte label in front
  -- of a pointer to question k-1's name, so its name is k labels, 64k + 1
  -- wire bytes. Three fit in 255; four do not.
  let lab := 63 :: List.replicate 63 120
  let mut qs : Array (List Nat) := #[lab ++ [0, 0, 12, 0, 1]]
  let mut off := 12
  for _ in [0:4] do
    qs := qs.push (lab ++ [0xC0, off, 0, 12, 0, 1])
    off := off + qs[qs.size - 2]!.length
  let chain (k : Nat) := bytes (header k 0 ++ (qs.toList.take k).flatten)
  check "a 3-label pointer chain (193 bytes) decodes" (decode (chain 3)).isSome
  check "hostile: a 4-label pointer chain (257 bytes) is refused" (decode (chain 4) == none)
  check "hostile: a 5-label pointer chain (321 bytes) is refused" (decode (chain 5) == none)
  -- Every truncation of every fixture.
  for (f, p) in fx do
    for n in [0:p.size] do
      if (decode (p.extract 0 n)).isSome then check s!"{f} cut to {n} bytes is refused" false

  -- Mutation fuzzing: flip, set or drop bytes of fixtures.
  let mut seed : UInt64 := 0x9E3779B97F4A7C15
  let mut accepted := 0
  for k in [0:200000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let (_, p) := fx[(seed >>> 33).toNat % fx.length]!
    let mut d := p.data
    for _ in [0:1 + (seed >>> 20).toNat % 4] do
      seed := seed * 6364136223846793005 + 1442695040888963407
      let i := (seed >>> 33).toNat % d.size
      let v := ((seed >>> 13).toNat % 256).toUInt8
      d := match (seed >>> 8).toNat % 3 with
        | 0 => d.set! i v
        | 1 => d.set! i (d[i]! ^^^ ((1 : UInt8) <<< ((seed >>> 5).toNat % 8).toUInt8))
        | _ => d.eraseIdx! i
    let q : ByteArray := ⟨d⟩
    if (decode q).isSome then accepted := accepted + 1
    if !roundtrips q then check s!"fuzz case {k} round-trips" false
  check "fuzz: some mutants still decode" (accepted > 1000)
  IO.println s!"fuzz: 200000 mutants, {accepted} accepted, all round-trip"

  -- Services
  let me : Service := { inst := "Holmes's Pixel", type := "_leanquiet._udp", host := "holmes-pixel",
                        port := 7001, txt := ["v=1"], addrs := [[192, 168, 4, 77]] }
  let a := announce me
  check "announce round-trips" (decode (encode a) == some a)
  check "announce is found" (found "_leanquiet._udp" a ==
    [{ inst := "Holmes's Pixel", host := "holmes-pixel", port := 7001, txt := ["v=1"],
       addrs := [[192, 168, 4, 77]], ttl := 120 }])
  check "goodbye has ttl 0" ((found "_leanquiet._udp" (goodbye me)).map (·.ttl) == [0])
  check "another type is not found" (found "_other._udp" a == [])
  let q := query "_leanquiet._udp"
  check "query round-trips" (decode (encode q) == some q)
  match react [me] q with
  | none => check "query is answered" false
  | some r => check "query is answered with the service" (found "_leanquiet._udp" r == found "_leanquiet._udp" a)
  check "a query for another type is not answered" (react [me] (query "_other._tcp") == none)
  check "an answer is not answered" (react [me] a == none)
  -- Our own query, as captured on the LAN, is byte for byte our encoder's.
  let lq ← IO.FS.readBinFile "tests/fixtures/lean-query.bin"
  check "query bytes match the capture" ((encode (query "_services._dns-sd._udp")).data == lq.data)

  let n ← fails.get
  if n == 0 then IO.println "mdns_check: all passed" else IO.eprintln s!"mdns_check: {n} failed"
  pure (if n == 0 then 0 else 1)
