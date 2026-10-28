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
import Engine.Sync.Round

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

instance : Codec Key where
  enc k := enc (k.t, k.n)
  dec bs := (dec bs : Option ((Nat × Nat) × List UInt8)).map fun p => (⟨p.1.1, p.1.2⟩, p.2)
  round k rest := by simp [round]

instance : Codec Range where
  enc r := enc (r.lo, r.hi)
  dec bs := (dec bs : Option ((Key × Option Key) × List UInt8)).map fun p => (⟨p.1.1, p.1.2⟩, p.2)
  round r rest := by simp [round]

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
