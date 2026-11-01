/- DNS-SD queries on routed networks: RFC 6762 §5.5, direct unicast to
port 5353. QU requests a unicast answer. No multicast forwarding or iroh. -/
import engine.wire.mdns.Net

namespace Mdns

def unicastQuery (type : String) : Msg :=
  { (query type) with questions := (query type).questions.map fun q => { q with cls := clsFlush } }

/-- Legacy queries from ephemeral ports need their id and question echoed.
QU queries from 5353 also receive a unicast answer. -/
def response (self : List Service) (m : Msg) (sourcePort : UInt16) : Option (Msg × Bool) := do
  let r ← react self m
  let legacy := sourcePort != Net.port
  return ({ r with id := m.id, questions := if legacy then m.questions else [] },
    legacy || m.questions.any (fun q => q.cls &&& 0x8000 != 0))

end Mdns
