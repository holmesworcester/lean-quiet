/-
Sync's three wire op kinds, carried as ops like everything else (one
codec, one strict decode, `Op.id_decode`), and never stored:

- `sync.rbsr`: one room's claims for one round (`reqs = [room]`, body
  the round and the claims); with no room it is the hello, which only
  says the sender's window floor.
- `sync.have`: ids the sender holds (`reqs`) in one room (body): a peer
  wants those it lacks in that room. This is also the stream: a newly
  stored op is offered so.
- `sync.want`: ids the sender asks for (`reqs`), answered with the ops'
  bytes.

Data ops travel as their own bytes.
-/
import ops.sync.Round

namespace Engine.Sync
open Codec

/-- The wire kinds: `sync.rbsr`, `sync.have`, `sync.want`. -/
def kRbsr : UInt8 := 240
def kHave : UInt8 := 241
def kWant : UInt8 := 242

def isWire (k : UInt8) : Bool := k == kRbsr || k == kHave || k == kWant

instance {α} [Codec α] : Codec (Option α) where
  enc | none => [0]
      | some a => 1 :: enc a
  dec | 0 :: rest => some (none, rest)
      | 1 :: rest => (dec rest).map fun p => (some p.1, p.2)
      | _ => none
  round o rest := by
    cases o with
    | none => rfl
    | some a => simp [round]
  encInto buf
    | none => buf.push 0
    | some a => encInto (buf.push 1) a
  encInto_eq buf o := by cases o <;> simp [encInto_tag]
  decFrom b i := match b[i]? with
    | some 0 => some (none, i + 1)
    | some 1 => decFromAs some b (i + 1)
    | _ => none
  decFrom_at o h := by
    cases o with
    | none => simp [h.tag]
    | some a => simp only [h.tag]; exact decFromAs_tag _ h

instance : Codec Key where
  enc k := enc (k.t, k.n)
  dec bs := (dec bs : Option ((Nat × Nat) × List UInt8)).map fun p => (⟨p.1.1, p.1.2⟩, p.2)
  round k rest := by simp [round]
  encInto buf k := encInto buf (k.t, k.n)
  encInto_eq buf k := encInto_eq buf (k.t, k.n)
  decFrom := decFromAs fun (p : Nat × Nat) => (⟨p.1, p.2⟩ : Key)
  decFrom_at k h := decFromAs_at _ h

instance : Codec Range where
  enc r := enc (r.lo, r.hi)
  dec bs := (dec bs : Option ((Key × Option Key) × List UInt8)).map fun p => (⟨p.1.1, p.1.2⟩, p.2)
  round r rest := by simp [round]
  encInto buf r := encInto buf (r.lo, r.hi)
  encInto_eq buf r := encInto_eq buf (r.lo, r.hi)
  decFrom := decFromAs fun (p : Key × Option Key) => (⟨p.1, p.2⟩ : Range)
  decFrom_at r h := decFromAs_at _ h

instance : Codec Claim where
  enc | .fp r n l => 0 :: enc (r, n, l)
      | .ids r xs => 1 :: enc (r, xs)
  dec | 0 :: rest => (dec rest : Option ((Range × Nat × ByteArray) × List UInt8)).map
          fun p => (.fp p.1.1 p.1.2.1 p.1.2.2, p.2)
      | 1 :: rest => (dec rest : Option ((Range × List ByteArray) × List UInt8)).map
          fun p => (.ids p.1.1 p.1.2, p.2)
      | _ => none
  round c rest := by
    cases c <;> simp [round]
  encInto buf
    | .fp r n l => encInto (buf.push 0) (r, n, l)
    | .ids r xs => encInto (buf.push 1) (r, xs)
  encInto_eq buf c := by cases c <;> simp [encInto_tag]
  decFrom b i := match b[i]? with
    | some 0 => decFromAs (fun (p : Range × Nat × ByteArray) => Claim.fp p.1 p.2.1 p.2.2) b (i + 1)
    | some 1 => decFromAs (fun (p : Range × List ByteArray) => Claim.ids p.1 p.2) b (i + 1)
    | _ => none
  decFrom_at c h := by
    cases c <;> (simp only [h.tag]; exact decFromAs_tag _ h)

/-- What a wire op says. -/
inductive Msg where
  | hello (floor : Nat)
  | rbsr (room : Id) (round : Nat) (claims : List Claim)
  | hold (room : Id) (ids : List Id)
  | want (ids : List Id)
  deriving Inhabited

def Msg.op : Msg → Op
  | .hello f => Op.make kRbsr [] (encode (0, f, ([] : List Claim)))
  | .rbsr c k cs => Op.make kRbsr [c] (encode (k, 0, cs))
  | .hold r ids => Op.make kHave ids (encode r)
  | .want ids => Op.make kWant ids .empty

/-- A wire op's message; none for a data op or a malformed wire op. -/
def Msg.ofOp (o : Op) : Option Msg :=
  if o.kind == kRbsr then
    match (decode o.body : Option (Nat × Nat × List Claim)), o.reqs with
    | some (_, f, []), [] => some (.hello f)
    | some (k, _, cs), [c] => some (.rbsr c k cs)
    | _, _ => none
  else if o.kind == kHave then (decode o.body : Option Id).map (.hold · o.reqs)
  else if o.kind == kWant then (if o.body.size == 0 then some (.want o.reqs) else none)
  else none

end Engine.Sync
