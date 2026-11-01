import engine.wire.Node
import app.community.Family

/-!
`community.member.invite.request`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- Device d's request to join through invitation inv, from the node with
key `key`: d signs both keys, and so does the bearer key. -/
def request (c inv : Id) (d : Device) (key : Key) (bearerSk : ByteArray) : Op :=
  let reqs := [c, inv]
  let u : Body := .request d.pk key .empty .empty
  mkOp reqs (.request d.pk key (sig d.sk reqs u) (sig bearerSk reqs u))

/-- The joiner's request, composed from the link: device d asks to join
through the link's invitation, signed by d and by the bearer key. -/
def Invite.request (i : Invite) (d : Device) (key : Key) : Op :=
  Community.request i.community i.invitation d key i.bearer.sk

end Community
