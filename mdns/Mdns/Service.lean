/-
DNS-SD over mDNS as plain functions on messages: what a service announces,
what a browser asks, what it learns from an answer, and how a responder
answers a question. No sockets here (Mdns.Net has them), so every step can
be run and tested on its own.

A service is found by its type ("_leanquiet._udp"). Its instance name is
one label (it may hold dots and spaces: "Holmes's Pixel"); its host is a
`.local` name with the addresses it answers on.
-/
import Mdns.Wire

namespace Mdns

def label (s : String) : Label := s.toUTF8.toList

/-- "_leanquiet._udp" → its labels, then "local". -/
def dotted (s : String) : Name := (s.splitOn ".").map label ++ [label "local"]

def labelText (l : Label) : String := (String.fromUTF8? ⟨l.toArray⟩).getD ""

/-- A name as text, without the trailing "local". -/
def Name.text (n : Name) : String := ".".intercalate ((n.take (n.length - 1)).map labelText)

-- Class IN, and IN with mDNS's cache-flush bit (the record is the only one
-- of its name and type, RFC 6762 §10.2).
def clsIN : UInt16 := 1
def clsFlush : UInt16 := 0x8001

/-- Flags of an authoritative response. -/
def flagsAnswer : UInt16 := 0x8400

def Msg.isResponse (m : Msg) : Bool := m.flags &&& 0x8000 != 0

structure Service where
  /-- One label: "Holmes's Pixel". -/
  inst : String
  /-- "_leanquiet._udp" -/
  type : String
  /-- "holmes-pixel", announced as holmes-pixel.local -/
  host : String
  port : UInt16
  txt : List String := []
  /-- 4 bytes for IPv4, 16 for IPv6. -/
  addrs : List (List UInt8) := []
  deriving Repr, DecidableEq, Inhabited

def Service.typeName (s : Service) : Name := dotted s.type
def Service.instName (s : Service) : Name := label s.inst :: dotted s.type
def Service.hostName (s : Service) : Name := dotted s.host

def addrData (a : List UInt8) : RData := if a.length = 4 then .a a else .aaaa a

/-- Everything a service announces: who it is (PTR), where (SRV, A/AAAA)
and its key=value strings (TXT). TTL 0 says goodbye. -/
def Service.records (s : Service) (ttl : UInt32 := 120) : List Record :=
  [ { name := s.typeName, cls := clsIN, ttl, data := .ptr s.instName },
    { name := s.instName, cls := clsFlush, ttl, data := .srv 0 0 s.port s.hostName },
    { name := s.instName, cls := clsFlush, ttl, data := .txt (s.txt.map label) } ]
  ++ s.addrs.map fun a => { name := s.hostName, cls := clsFlush, ttl, data := addrData a }

def announce (s : Service) : Msg := { flags := flagsAnswer, answers := s.records }
def goodbye (s : Service) : Msg := { flags := flagsAnswer, answers := s.records 0 }

/-- The question a browser sends: who offers this type? -/
def query (type : String) : Msg :=
  { questions := [{ name := dotted type, type := tPTR, cls := clsIN }] }

-- Browsing
-- --------

/-- A service seen in an answer. -/
structure Found where
  inst : String
  host : String
  port : UInt16
  txt : List String
  addrs : List (List UInt8)
  /-- 0: the service said goodbye. -/
  ttl : UInt32
  deriving Repr, DecidableEq, Inhabited

/-- The services of `type` an answer tells about. An SRV, TXT or address
record the answer leaves out leaves its field empty (port 0). -/
def found (type : String) (m : Msg) : List Found :=
  if !m.isResponse then [] else
  let rs := m.answers ++ m.additional
  rs.filterMap fun r =>
    match r.data with
    | .ptr inst =>
      if r.name == dotted type then
        let srv := rs.findSome? fun x =>
          match x.data with
          | .srv _ _ port host => if x.name == inst then some (port, host) else none
          | _ => none
        let txt := rs.findSome? fun x =>
          match x.data with
          | .txt ss => if x.name == inst then some ss else none
          | _ => none
        let host : Name := (srv.map (·.2)).getD []
        let addrs := rs.filterMap fun x =>
          match x.data with
          | .a a | .aaaa a => if x.name == host && !host.isEmpty then some a else none
          | _ => none
        some { inst := (inst.head?.map labelText).getD "", host := Name.text host,
               port := (srv.map (·.1)).getD 0, txt := (txt.getD []).map labelText,
               addrs, ttl := r.ttl }
      else none
    | _ => none

-- Responding
-- ----------

def wants (q : Question) (t : UInt16) : Bool := q.type == t || q.type == tANY

/-- A responder's records that answer one question. -/
def answers (s : Service) (q : Question) : List Record :=
  s.records.filter fun r =>
    r.name == q.name && wants q r.data.type

/-- The answer to a query, from the services we offer; `none` when none of
them is asked about (or the message is itself an answer). A service found
by its type also sends its SRV, TXT and address records, as additional
records, so a browser needs no second round (RFC 6763 §12.1). -/
def react (self : List Service) (m : Msg) : Option Msg :=
  if m.isResponse then none else
  let an := (self.flatMap fun s => m.questions.flatMap (answers s)).eraseDups
  let ad := self.flatMap fun s =>
    if an.any (fun r => r.data == .ptr s.instName) then s.records.filter (!an.contains ·) else []
  if an.isEmpty then none else some { flags := flagsAnswer, answers := an, additional := ad.eraseDups }

end Mdns
