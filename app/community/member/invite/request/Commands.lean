import engine.wire.Node
import app.community.Family

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

/-- Whether this device's user `me` is asked about a request: a member's
request, by any member; a device link's, only by its issuer's user, who
alone may approve it (`link_approved_by_issuer`). -/
def asks (me : Id) : Fact → Bool
  | .request _ u _ _ l => !l || decide (u = me)
  | _ => false

end Community
