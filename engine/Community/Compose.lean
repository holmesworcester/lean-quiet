/-
Real crypto and op composition. Ed25519 and SHA-256 come from
libsodium through native/glue.c; an op's id is the SHA-256 of its
bytes (`Engine.Op.make`). The laws hold for any `Crypto`, this one
included.
-/
import Community.Facts

namespace Community
open Engine Codec

export Engine (sha256)
@[extern "le_ed25519_keypair"] opaque edKeypair (seed : @& ByteArray) : ByteArray
@[extern "le_ed25519_sign"] opaque edSign (sk msg : @& ByteArray) : ByteArray
@[extern "le_ed25519_verify"] opaque edVerify (pk msg sig : @& ByteArray) : Bool

def ed25519 : Crypto := ⟨fun pk m s => edVerify pk m s, fun seed => (edKeypair seed).extract 0 32⟩

/-- A device: its Ed25519 signing key pair, and its X25519 encryption
key (the conversion of the signing key), which content keys are wrapped
to. -/
structure Device where
  pk : Key
  sk : ByteArray
  enc : Key
  deriving Inhabited

/-- A device from a 32-byte seed (tests derive seeds from names). -/
def Device.ofSeed (seed : ByteArray) : Device :=
  let kp := edKeypair seed
  ⟨kp.extract 0 32, kp.extract 32 96, Crypto.staticPubOf (kp.extract 0 32)⟩

/-- A device's X25519 secret: what opens keys wrapped to it. -/
def Device.encSecret (d : Device) : ByteArray := Crypto.staticOf d.sk

def Device.named (name : String) : Device := Device.ofSeed (sha256 name.toUTF8)

/-- The op with these requirements and body, named by its bytes' hash. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.tag reqs (encode b)

/-- What a signer signs for an op with these requirements and body. -/
def toSign (reqs : List Id) (b : Body) : ByteArray :=
  encode ("quiet/attest/v1".toUTF8, reqs, b.unsigned)

def sig (sk : ByteArray) (reqs : List Id) (b : Body) : ByteArray := edSign sk (toSign reqs b)

theorem signed_eq (o : Op) (b : Body) : signed o b = toSign o.reqs b := rfl

def root (d : Device) : Op :=
  mkOp [] (.root d.pk d.enc (sig d.sk [] (.root d.pk d.enc .empty)))

/-- An invitation needing `threshold` approvals (one by default; a link
invitation needs exactly one). -/
def invite (c issuerAdm : Id) (by_ : Device) (bearer : Key) (link : Bool)
    (threshold : Nat := 1) : Op :=
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

def post (c adm : Id) (by_ : Device) (ckey text : ByteArray) (time : Nat := 0) : Op :=
  let reqs := [c, adm]
  mkOp reqs (.post ckey text time (sig by_.sk reqs (.post ckey text time .empty)))

def profile (c adm : Id) (by_ : Device) (name : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm]
  mkOp reqs (.profile name time (sig by_.sk reqs (.profile name time .empty)))

def react (c adm target : Id) (by_ : Device) (emoji : ByteArray) (time : Nat) : Op :=
  let reqs := [c, adm, target]
  mkOp reqs (.react emoji time (sig by_.sk reqs (.react emoji time .empty)))

def wrap (c : Id) (ckey recipient box : ByteArray) : Op := mkOp [c] (.wrap ckey recipient box)

/-! ## Content keys and sealed bodies (`Community.Keys`) -/

/-- This device's copy of c's content key k (local). -/
def contentKey (c k : ByteArray) : Op := mkOp [] (.key c k)

/-- Content key k of c wrapped to the device whose X25519 key is `to`,
with a fresh ephemeral secret `esk`. -/
def wrapKey (c : Id) (k esk to : ByteArray) : Op :=
  let kid := kidOf cryptoSeal k
  wrap c kid to (box cryptoSeal esk to kid k)

/-- A post whose text is sealed under content key k with a fresh
24-byte nonce n: its sealed bytes are the nonce, then the ciphertext. -/
def sealedPost (c adm : Id) (by_ : Device) (k n text : ByteArray) (time : Nat := 0) : Op :=
  let kid := kidOf cryptoSeal k
  post c adm by_ kid (n ++ sealBody cryptoSeal k n c kid text) time

/-! ## Attachments -/

/-- What a file's attachment says of it, sealed under the content key. -/
structure FileMeta where
  name : ByteArray
  kind : ByteArray
  w : Nat
  h : Nat
  preview : ByteArray
  deriving Inhabited, BEq

/-- A file to attach, with the fresh random bytes it needs: its own key
(32), the nonce it is sealed with (24), and the nonce its sealed info
is sealed with (24). -/
structure NewFile where
  info : FileMeta
  bytes : ByteArray
  key : ByteArray
  nonce : ByteArray
  metaNonce : ByteArray

/-- What the file's own seal is bound to. -/
def fileAd : ByteArray := "quiet/file/v1".toUTF8

/-- The file sealed under its own key: what the Merkle tree is over. -/
def fileCipher (f : NewFile) : ByteArray := cryptoSeal.enc f.key f.nonce fileAd f.bytes

/-- An attachment of file f to message `msg` of c, by `by_` (admitted
as `adm`), its meta sealed under content key k; and the file's chunks. -/
def attach (c adm msg : Id) (by_ : Device) (k : ByteArray) (f : NewFile) : Op × List Op :=
  let ct := fileCipher f
  let root := Merkle.fileRoot sha256 ct
  let kid := kidOf cryptoSeal k
  let m := encode (f.info.name, f.info.kind, f.info.w, f.info.h, f.info.preview, f.key, f.nonce)
  let sealed := f.metaNonce ++ sealBody cryptoSeal k f.metaNonce c kid m
  let reqs := [c, adm, msg]
  let a := mkOp reqs (.attach root ct.size kid sealed (sig by_.sk reqs (.attach root ct.size kid sealed .empty)))
  let chunks := (List.range (Merkle.nChunks ct.size)).map fun i =>
    mkOp [c] (.chunk root ct.size i ((Merkle.slices ct).getD i .empty) (Merkle.proof sha256 ct i))
  (a, chunks)

/-- An attachment's info and the file's key and nonce, opened with the
content key. -/
def openInfo (c kid sealed k : ByteArray) : Option (FileMeta × ByteArray × ByteArray) :=
  (openSealed cryptoSeal c kid sealed k).bind fun m =>
    (decode m : Option (ByteArray × ByteArray × Nat × Nat × ByteArray × ByteArray × ByteArray)).map
      fun (n, kd, w, h, p, fk, fn) => (⟨n, kd, w, h, p⟩, fk, fn)

/-- A file from its chunks' slices, in order, opened with its key. -/
def openFile (slices : List ByteArray) (fileKey fileNonce : ByteArray) : Option ByteArray :=
  cryptoSeal.dec fileKey fileNonce fileAd (Merkle.assemble slices)

/-- This device's secret seed (local). -/
def secret (seed : ByteArray) : Op := mkOp [] (.secret (Device.ofSeed seed).pk seed)

/-- This device is in community c (local). -/
def accept (c : Id) (device : Key) : Op := mkOp [] (.accept c device)

/-- Name community c: an admin's register entry, superseding `prev` (the
names it saw), its counter one past theirs. `auth` shows the admin. -/
def setName (c adm auth : Id) (prev : List Id) (n : Nat) (by_ : Device) (name : ByteArray) : Op :=
  let reqs := [c, adm, auth] ++ prev
  mkOp reqs (.name n name (sig by_.sk reqs (.name n name .empty)))

end Community
