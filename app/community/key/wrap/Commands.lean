import app.community.Family

namespace Community
open Engine Codec

/-- A wrap of c by device d (admitted as `myAdm`) to the node admission
`toAdm` names, holding `bx`, signed by d. -/
def wrap (c myAdm toAdm : Id) (d : Device) (bx : ByteArray) : Op :=
  let reqs := [c, myAdm, toAdm]
  mkOp reqs (.wrap bx (sig d.sk reqs (.wrap bx .empty)))

/-- Content key k of c wrapped by device d (admitted as `myAdm`) to the
node whose X25519 key is `to`, as admission `toAdm` names it, with a
fresh ephemeral secret `esk`. -/
def wrapKey (c myAdm toAdm : Id) (d : Device) (k esk : Key32) (to : ByteArray) : Op :=
  wrap c myAdm toAdm d (box cryptoSeal esk to (kidOf cryptoSeal k) k)

end Community
