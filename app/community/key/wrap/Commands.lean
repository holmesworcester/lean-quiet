import app.community.Family

/-!
`community.key.wrap`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

def wrap (c : Id) (ckey recipient box : ByteArray) : Op := mkOp [c] (.wrap ckey recipient box)

/-- Content key k of c wrapped to the device whose X25519 key is `to`,
with a fresh ephemeral secret `esk`. -/
def wrapKey (c : Id) (k esk to : ByteArray) : Op :=
  let kid := kidOf cryptoSeal k
  wrap c kid to (box cryptoSeal esk to kid k)

end Community
