/-
Real crypto and op composition. Ed25519 and SHA-256 come from
libsodium through native/glue.c; an op's id is the SHA-256 of its
canonical bytes. The laws hold for any `Crypto`, this one included.
-/
import Community.Facts

namespace Community
open Engine Codec

@[extern "le_sha256"] opaque sha256 (b : @& ByteArray) : ByteArray
@[extern "le_ed25519_keypair"] opaque edKeypair (seed : @& ByteArray) : ByteArray
@[extern "le_ed25519_sign"] opaque edSign (sk msg : @& ByteArray) : ByteArray
@[extern "le_ed25519_verify"] opaque edVerify (pk msg sig : @& ByteArray) : Bool

def ed25519 : Crypto := ⟨fun pk m s => edVerify pk m s⟩

/-- A device: its signing key pair and its encryption key. -/
structure Device where
  pk : Key
  sk : ByteArray
  enc : Key
  deriving Inhabited

/-- A device from a 32-byte seed (tests derive seeds from names). -/
def Device.ofSeed (seed : ByteArray) : Device :=
  let kp := edKeypair seed
  ⟨kp.extract 0 32, kp.extract 32 96, sha256 ("enc".toUTF8 ++ seed)⟩

def Device.named (name : String) : Device := Device.ofSeed (sha256 name.toUTF8)

def Body.tag : Body → UInt8
  | .root .. => 0 | .invite .. => 1 | .request .. => 12 | .grant .. => 3
  | .remove .. => 4 | .post .. => 5 | .wrap .. => 6
  | .profile .. => 7 | .blob .. => 8 | .react .. => 9
  | .approve .. => 10 | .admit => 11

/-- The op with these requirements and body, named by its bytes' hash. -/
def mkOp (reqs : List Id) (b : Body) : Op :=
  let body := encode b
  { id := sha256 (encode (b.tag, reqs, body)), kind := b.tag, reqs, body }

/-- What a signer signs for an op with these requirements and body. -/
def toSign (reqs : List Id) (b : Body) : ByteArray :=
  signed { id := .empty, kind := 0, reqs, body := .empty } b

def sig (sk : ByteArray) (reqs : List Id) (b : Body) : ByteArray := edSign sk (toSign reqs b)

theorem signed_eq (o : Op) (b : Body) : signed o b = toSign o.reqs b := rfl

def root (d : Device) : Op :=
  mkOp [] (.root d.pk d.enc (sig d.sk [] (.root d.pk d.enc .empty)))

/-- An invitation; a link invitation needs one approval, a member
invitation `threshold` (none by default). -/
def invite (c issuerAdm : Id) (by_ : Device) (bearer : Key) (link : Bool)
    (threshold : Nat := if link then 1 else 0) : Op :=
  let reqs := [c, issuerAdm]
  mkOp reqs (.invite bearer link threshold (sig by_.sk reqs (.invite bearer link threshold .empty)))

def request (c inv : Id) (d : Device) (bearerSk : ByteArray) : Op :=
  let reqs := [c, inv]
  let u : Body := .request d.pk d.enc .empty .empty
  mkOp reqs (.request d.pk d.enc (sig d.sk reqs u) (sig bearerSk reqs u))

/-- by_'s approval of request req, signed as its admission adm. -/
def approve (c req adm : Id) (by_ : Device) : Op :=
  let reqs := [c, req, adm]
  mkOp reqs (.approve (sig by_.sk reqs (.approve .empty)))

/-- The admission of request req by these approvals. -/
def admit (c req : Id) (approvals : List Id := []) : Op := mkOp (c :: req :: approvals) .admit

def grant (c granterAdm auth targetAdm : Id) (by_ : Device) : Op :=
  let reqs := [c, granterAdm, auth, targetAdm]
  mkOp reqs (.grant (sig by_.sk reqs (.grant .empty)))

def remove (c removerAdm auth targetAdm : Id) (by_ : Device) : Op :=
  let reqs := [c, removerAdm, auth, targetAdm]
  mkOp reqs (.remove (sig by_.sk reqs (.remove .empty)))

def post (c adm : Id) (by_ : Device) (ckey text : ByteArray) (time : Nat := 0)
    (atts : List Id := []) : Op :=
  let reqs := [c, adm] ++ atts
  mkOp reqs (.post ckey text time (sig by_.sk reqs (.post ckey text time .empty)))

def profile (c adm : Id) (by_ : Device) (name : ByteArray) (time : Nat) (avatar : List Id) : Op :=
  let reqs := [c, adm] ++ avatar
  mkOp reqs (.profile name time (sig by_.sk reqs (.profile name time .empty)))

/-- An image's blob op, named by the bytes' hash; the bytes go in the
blob store beside it. -/
def blob (c : Id) (bytes : ByteArray) (w h : Nat) : Op := mkOp [c] (.blob (sha256 bytes) w h)

def react (c adm target : Id) (by_ : Device) (emoji : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm, target]
  mkOp reqs (.react emoji time (sig by_.sk reqs (.react emoji time .empty)))

def wrap (c : Id) (ckey recipient box : ByteArray) : Op := mkOp [c] (.wrap ckey recipient box)

end Community
