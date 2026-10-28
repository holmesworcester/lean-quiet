/-
How a node connects, as functions from what it holds and what arrives to
what it then holds and sends. After poc-17's op-as-wire model over TCP
(a hello sealed to the dialed key, an answer that proves the responder
holds it, then sync over the session) and libquiet's join gate, with
these rules:

- **One trust rule, both ends.** A node opens a session for community c
  with the node whose key is p only if it trusts p: a live device of c is
  admitted under p by the node's own ops (`Allowed`, what `allowPeer`
  answers at rest; see `Net.Bridge`), or, while the node is not yet let
  in itself, p is the key its invite link names and its ops say nothing
  about p yet.
  The responder applies the rule to the initiator, and the initiator to
  the responder. `allowPeer` itself has no exception: the link clause
  is the joiner's only, it ends at the joiner's admission, and it never
  outlives what the ops say about p.
- **A request is delivered, not connected.** A hello may carry one op,
  an introduction, read only if it is a Valid request of c. The
  responder stores it and answers only if it now trusts the sender, so
  a request alone opens nothing and earns no reply. The joiner re-sends
  the same hello every tick until approval lets the answer through.
- **Bootstrap facts are local.** What a node accepts (`accepted`, from
  founding or pasting a link), its link (the dial key and the request,
  presented until admitted) and its sessions are node-local, never ops,
  and nothing on the wire can create them. Ops of other communities
  are dropped, and only a session's community's ops are read from it.

Sync is abstracted as "send the session's community's ops"; reconciling
by fingerprints instead of whole sets is its own protocol.

The cryptography of the handshake (the hello is sealed to the dialed
node's key; the answer proves possession of that key) is abstracted: a
hello is read only by its addressee, and an answer is taken only from
the node the node dialed. A node is named by its own key (its
`endpoint`), which the roots and requests of the devices it holds name
as their `enc`: the transport authenticates the node key, and the
admissions tie it to devices (docs/REMOVAL.md).
-/
import ops.community.Community

namespace Net
open Engine Community

/-- The engine's op table over the ops a node holds: each id to its op. -/
def table (L : List Op) : Id → Option Op := fun x => L.find? fun o => decide (o.id = x)

section
variable (C : Crypto)

/-- A live device of c is admitted under node key p, by these ops: what
`allowPeer` answers once they are processed (`Net.Bridge`). -/
def Allowed (L : List Op) (c : Id) (p : Key) : Prop :=
  ∃ u d, Admitted C (table L) c u d p ∧ Live C (table L) c d

/-- These ops say something about node key p: a device was admitted
under it (into a user removed or not). -/
def Known (L : List Op) (c : Id) (p : Key) : Prop := ∃ u d, Admitted C (table L) c u d p

end

/-- A pasted invite link, kept until this node is admitted: the
community, the inviter's node key (whom to dial, and the one node
trusted before any ops arrive), and the request composed once at paste
(libquiet's pending join). -/
structure Link where
  c : Id
  dial : Key
  req : Op
  deriving DecidableEq

/-- A node: its key, the ops it holds, the communities it accepted, its
pending link, and its open sessions (community, peer key). -/
structure Node where
  me : Key
  ops : List Op
  accepted : List Id
  links : List Link
  sessions : List (Id × Key)

/-- What travels: a hello (poc-17's conn.request, sealed to dst) with an
optional introduction; an answer (conn.connection); and ops pushed over a
session. -/
inductive Msg where
  | hello (c : Id) (src dst : Key) (intro : Option Op)
  | answer (c : Id) (src dst : Key)
  | push (c : Id) (src dst : Key) (ops : List Op)
  deriving DecidableEq

def Msg.dst : Msg → Key
  | .hello _ _ d _ => d
  | .answer _ _ d => d
  | .push _ _ d _ => d

/-- An op of community c: its root, or an op whose slot 0 is c. -/
def ofC (c : Id) (o : Op) : Bool :=
  decide (o.reqs.head? = some c) || (o.reqs.isEmpty && decide (o.id = c))

/-- Store an op unless one with its id is held. -/
def add1 (L : List Op) (o : Op) : List Op :=
  if L.any fun p => decide (p.id = o.id) then L else L ++ [o]

def add (L : List Op) (os : List Op) : List Op := os.foldl add1 L

def ins (l : List (Id × Key)) (s : Id × Key) : List (Id × Key) :=
  if l.any fun t => decide (t = s) then l else l ++ [s]

section
open Classical
variable (C : Crypto)

/-- The node key p this node is told to dial for c by its link. -/
def Node.Anchored (n : Node) (c : Id) (p : Key) : Prop := ∃ l ∈ n.links, l.c = c ∧ l.dial = p

/-- **The trust rule.** -/
def Trusts (n : Node) (c : Id) (p : Key) : Prop :=
  c ∈ n.accepted ∧
    (Allowed C n.ops c p ∨
      (n.Anchored c p ∧ ¬ Known C n.ops c p ∧ ¬ Allowed C n.ops c n.me))

/-- The one op read from a peer not trusted: a Valid request of c. -/
def IntroOk (n : Node) (c : Id) (q : Op) : Prop :=
  ofC c q = true ∧ ∃ u d e l t, V C (table (add1 n.ops q)) q.id (.request c u d e l t)

/-- A hello from i for c: store its introduction if it is a Valid
request; answer, and open the session, only if i is trusted. -/
noncomputable def onHello (n : Node) (c : Id) (i : Key) (intro : Option Op) : Node × List Msg :=
  if c ∈ n.accepted then
    let n1 := match intro with
      | some q => if IntroOk C n c q then { n with ops := add1 n.ops q } else n
      | none => n
    if Trusts C n1 c i then ({ n1 with sessions := ins n1.sessions (c, i) }, [.answer c n.me i])
    else (n1, [])
  else (n, [])

/-- An answer from r for c: open the session if this node dialed r for c
and trusts it. -/
noncomputable def onAnswer (n : Node) (c : Id) (r : Key) : Node :=
  if n.Anchored c r ∧ Trusts C n c r then { n with sessions := ins n.sessions (c, r) } else n

/-- Ops from p for c: stored only over an open session with a peer still
trusted, and only c's. -/
noncomputable def onPush (n : Node) (c : Id) (p : Key) (os : List Op) : Node :=
  if (c, p) ∈ n.sessions ∧ Trusts C n c p then { n with ops := add n.ops (os.filter (ofC c)) }
  else n

/-- The links a tick keeps: those of communities this node is not yet
admitted to. -/
noncomputable def keptLinks (n : Node) : List Link :=
  n.links.filter fun l => !decide (Allowed C n.ops l.c n.me)

/-- A node after a tick's bookkeeping: links of communities it is now
admitted to forgotten, sessions with peers no longer trusted closed. -/
noncomputable def ticked (n : Node) : Node :=
  let n1 := { n with links := keptLinks C n }
  { n1 with sessions := n1.sessions.filter fun s => decide (Trusts C n1 s.1 s.2) }

/-- What a tick sends: each pending link's hello, with its request, until
its session opens; each session's community's ops. -/
def sends (n : Node) : List Msg :=
  (n.links.filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map
    (fun l => Msg.hello l.c n.me l.dial (some l.req)) ++
  n.sessions.map fun s => Msg.push s.1 n.me s.2 (n.ops.filter (ofC s.1))

/-- A tick. -/
noncomputable def tick (n : Node) : Node × List Msg := (ticked C n, sends (ticked C n))

/-- A node's reaction to a message addressed to it. -/
noncomputable def recv (n : Node) : Msg → Node × List Msg
  | .hello c i _ q => onHello C n c i q
  | .answer c r _ => (onAnswer C n c r, [])
  | .push c p _ os => (onPush C n c p os, [])

end

end Net
