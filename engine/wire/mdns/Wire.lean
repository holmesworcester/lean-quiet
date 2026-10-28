/-
DNS messages as mDNS (RFC 6762) and DNS-SD (RFC 6763) use them, and their
encoding (RFC 1035 §4).

Everything here is plain data. A name is its labels, a label its bytes; the
record kinds a service browser needs (A, AAAA, PTR, SRV, TXT) are decoded,
any other kind keeps its rdata as raw bytes. Numbers are big-endian on the
wire. `Valid` is what a message must satisfy to have an encoding at all;
`Mdns.Laws` proves the decoder returns exactly the valid messages.

The encoder never compresses names: mDNS packets here are small, and an
uncompressed name has one encoding. The decoder accepts compression, since
other responders use it.
-/
namespace Mdns

abbrev Label := List UInt8
abbrev Name := List Label

/-- Bytes a name takes on the wire, uncompressed: a length byte and the
bytes for each label, then the root's zero. -/
def Name.wireLen (n : Name) : Nat := (n.map (·.length + 1)).sum + 1

def Name.Valid (n : Name) : Prop :=
  (∀ l ∈ n, 0 < l.length ∧ l.length < 64) ∧ n.wireLen ≤ 255

/-- Record types with decoded rdata. -/
def tA : UInt16 := 1
def tPTR : UInt16 := 12
def tTXT : UInt16 := 16
def tAAAA : UInt16 := 28
def tSRV : UInt16 := 33
def tANY : UInt16 := 255

def known (t : UInt16) : Bool :=
  t == tA || t == tPTR || t == tTXT || t == tAAAA || t == tSRV

inductive RData where
  | a (addr : List UInt8)
  | aaaa (addr : List UInt8)
  | ptr (target : Name)
  | srv (prio weight port : UInt16) (target : Name)
  | txt (strings : List (List UInt8))
  /-- Any other type: rdata as it was on the wire (a name inside it, as in
  NSEC, may still hold a compression pointer into its packet). -/
  | other (type : UInt16) (bytes : List UInt8)
  deriving Repr, DecidableEq, Inhabited

def RData.type : RData → UInt16
  | .a _ => tA
  | .aaaa _ => tAAAA
  | .ptr _ => tPTR
  | .srv .. => tSRV
  | .txt _ => tTXT
  | .other t _ => t

structure Question where
  name : Name
  type : UInt16
  /-- Class; mDNS puts the unicast-response flag in its top bit. -/
  cls : UInt16
  deriving Repr, DecidableEq, Inhabited

structure Record where
  name : Name
  /-- Class; mDNS puts the cache-flush flag in its top bit. -/
  cls : UInt16
  ttl : UInt32
  data : RData
  deriving Repr, DecidableEq, Inhabited

structure Msg where
  id : UInt16 := 0
  flags : UInt16 := 0
  questions : List Question := []
  answers : List Record := []
  authority : List Record := []
  additional : List Record := []
  deriving Repr, DecidableEq, Inhabited

-- Encoding
-- --------

def be16 (v : Nat) : List UInt8 := [(v / 256).toUInt8, v.toUInt8]
def be32 (v : Nat) : List UInt8 := be16 (v / 65536) ++ be16 (v % 65536)

def encLabel (l : Label) : List UInt8 := l.length.toUInt8 :: l
def encName (n : Name) : List UInt8 := (n.map encLabel).flatten ++ [0]

/-- TXT rdata: each string after its length byte. -/
def encTxt (ss : List (List UInt8)) : List UInt8 := (ss.map encLabel).flatten

def encRData : RData → List UInt8
  | .a b | .aaaa b | .other _ b => b
  | .ptr n => encName n
  | .srv p w port n => be16 p.toNat ++ be16 w.toNat ++ be16 port.toNat ++ encName n
  | .txt ss => encTxt ss

def encQuestion (q : Question) : List UInt8 :=
  encName q.name ++ be16 q.type.toNat ++ be16 q.cls.toNat

def encRecord (r : Record) : List UInt8 :=
  let d := encRData r.data
  encName r.name ++ be16 r.data.type.toNat ++ be16 r.cls.toNat ++ be32 r.ttl.toNat
    ++ be16 d.length ++ d

def encMsg (m : Msg) : List UInt8 :=
  be16 m.id.toNat ++ be16 m.flags.toNat ++ be16 m.questions.length
    ++ be16 m.answers.length ++ be16 m.authority.length ++ be16 m.additional.length
    ++ (m.questions.map encQuestion).flatten ++ (m.answers.map encRecord).flatten
    ++ (m.authority.map encRecord).flatten ++ (m.additional.map encRecord).flatten

def encode (m : Msg) : ByteArray := ⟨(encMsg m).toArray⟩

-- Validity
-- --------

def RData.Valid : RData → Prop
  | .a b => b.length = 4
  | .aaaa b => b.length = 16
  | .ptr n => n.Valid
  | .srv _ _ _ n => n.Valid
  | .txt ss => ∀ s ∈ ss, s.length < 256
  | .other t _ => known t = false

def Record.Valid (r : Record) : Prop :=
  r.name.Valid ∧ r.data.Valid ∧ (encRData r.data).length < 65536

def Question.Valid (q : Question) : Prop := q.name.Valid

def Msg.Valid (m : Msg) : Prop :=
  (∀ q ∈ m.questions, q.Valid) ∧ (∀ r ∈ m.answers, r.Valid)
    ∧ (∀ r ∈ m.authority, r.Valid) ∧ (∀ r ∈ m.additional, r.Valid)
    ∧ m.questions.length < 65536 ∧ m.answers.length < 65536
    ∧ m.authority.length < 65536 ∧ m.additional.length < 65536

end Mdns
