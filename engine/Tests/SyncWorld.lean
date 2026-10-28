/-
Two nodes syncing a real community (Ed25519) in the pure world the
stream law is proven over (`Engine.Sync.World`): held stores, plain
sealing, fixed rooms, and the frames in flight as data.

- round: a node with the whole history and an empty one connect; once
  every frame is delivered, the empty one holds all of it;
- full: each holds part of it; frames are delivered in a random
  interleaving of the two directions, with ticks between; both end with
  all of it;
- stream: after the round, the premises of `stream_delivers` hold of
  the live world for a new op, and the run goes as the law says. The
  write sends exactly the offer frame, the offer is answered with
  exactly the want frame, the answer's first frame begins with the op,
  and after it the peer holds the op, with no new round;
- every session: with two sessions between the nodes, a write is
  offered on each (`stream_offered`);
- rooms (negative control): a peer whose rooms on the session leave the
  community out gets none of it, streamed or not.
-/
import Tests.Lib

open Engine Engine.Sync Community Tests

def C := ed25519
def fam := family C

/-- A community: members admitted through invitations, requests,
approvals and admissions, then timed posts by them. -/
def history (tag : String) (members posts : Nat) : List Op × Id := Id.run do
  let f := Device.named s!"{tag}-founder"
  let r := root f
  let c := r.id
  let mut ops : Array Op := #[r]
  let mut adms : Array (Id × Device) := #[(c, f)]
  for j in [0:members] do
    let b := Device.named s!"{tag}-bearer-{j}"
    let d := Device.named s!"{tag}-member-{j}"
    let inv := invite c c f b.pk false
    let req := request c inv.id d b.sk
    let ok := approve c req.id c f
    let adm := admit c req.id [ok.id]
    ops := ops ++ #[inv, req, ok, adm]
    adms := adms.push (adm.id, d)
  for i in [0:posts] do
    let (a, d) := adms[i % adms.size]!
    ops := ops.push (post c a d "k".toUTF8 s!"{tag} post {i}".toUTF8 (1000 + 100 * i))
  return (ops.toList, c)

/-- A node whose store holds these ops (one write turn of them). -/
def peerOf (S : Setup Fact) (ops : List Op) (addr : String) : Peer Fact :=
  let h := ((Turn.turn S.fam (intake S.fam true ops) : HeldM Fact Unit).run {}).2
  { node := Node.boot S.fam h.log 0, held := h, addr := addr.toUTF8 }

def holds (p : Peer Fact) (x : Id) : Bool := (p.held.db.ops x).isSome

/-- Which node a frame is addressed to. -/
def dstOf (w : World Fact) (f : Frame) : Who := if f.dst == w.b.addr then .b else .a

/-- Deliver frame i in flight. -/
def deliverAt (S : Setup Fact) (w : World Fact) (i : Nat) (t : Nat) : World Fact :=
  let f := w.net[i]!
  w.deliver S (dstOf w f) (w.net.take i) (w.net.drop (i + 1)) f t

/-- Deliver frames until none is in flight (at most `fuel`): the oldest
first, or, with a generator, the oldest to a random one of the nodes
that has one waiting. -/
def drain (S : Setup Fact) (w : World Fact) (g : Option Rng) (fuel : Nat) : World Fact × Option Rng :=
  Id.run do
    let mut w := w
    let mut g := g
    for _ in [0:fuel] do
      if w.net.isEmpty then break
      let mut i := 0
      if let some r := g then
        let (k, r') := r.below 2
        g := some r'
        let want : Who := if k == 0 then .a else .b
        i := (w.net.findIdx? fun f => dstOf w f == want).getD 0
      w := deliverAt S w i (w.now + 1)
    return (w, g)

/-- Whether frame f, on session cid, carries an offer naming x. -/
def offers (f : Frame) (cid : Id) (x : Id) : Bool :=
  match (Codec.decode (f.bytes.extract 1 f.bytes.size) : Option (Id × ByteArray)) with
  | some (c, b) => c == cid && match (Codec.decode b : Option (List ByteArray)) with
    | some ps => ps.any fun p => match (Op.decode p).bind Msg.ofOp with
      | some (.hold l) => l.contains x
      | _ => false
    | none => false
  | none => false

def round (w : World Fact) (s : Who) (cid : Id) : Nat :=
  ((w.peer s).node.conn? cid).map (·.round) |>.getD 0

def main : IO UInt32 := do
  let t ← Checks.new
  let (h, c) := history "acme" 4 30
  IO.println s!"history: {h.length} ops"
  let S : Setup Fact := { fam, rooms := fun _ _ => [c] }
  let cid := sha256 "conn".toUTF8

  -- Round: a holds everything, b nothing.
  let w : World Fact := { a := peerOf S h "a", b := peerOf S [] "b" }
  let w := (w.connect S .a cid true 0).connect S .b cid false 0
  t.ok "round: b starts with none of it" (h.all fun o => !holds w.b o.id)
  let (w, _) := drain S w none 100000
  IO.println s!"round: b holds {w.b.held.db.stored.length} ops, settled {(w.b.node.conn? cid).map (·.settled.length)}"
  t.ok "round: b holds the whole history" (h.all fun o => holds w.b o.id)
  t.ok "round: nothing left in flight" w.net.isEmpty

  -- Full: each holds part; a random interleaving, ticks between.
  let mut g := Rng.mk 7
  let mut sa : List Op := []
  let mut sb : List Op := []
  for o in h do
    let (k, g') := g.below 3
    g := g'
    if k != 1 then sa := sa ++ [o]
    if k != 0 then sb := sb ++ [o]
  let mut wf : World Fact := { a := peerOf S sa "a", b := peerOf S sb "b" }
  wf := (wf.connect S .a cid true 0).connect S .b cid false 0
  let mut r : Option Rng := some (Rng.mk 11)
  for k in [0:5] do
    let (w', r') := drain S wf r 100000
    wf := w'
    r := r'
    let now := wf.now + 1000 * (k + 1)
    wf := (wf.tick S .a now).tick S .b now
  let (wd, _) := drain S wf r 100000
  IO.println s!"full: a held {sa.length}, b {sb.length}; now {wd.a.held.db.stored.length} and {wd.b.held.db.stored.length}"
  t.ok "full: a holds the whole history" (h.all fun o => holds wd.a o.id)
  t.ok "full: b holds the whole history" (h.all fun o => holds wd.b o.id)

  -- Stream: after the round, a new op at a.
  let late := post c c (Device.named "acme-founder") "k".toUTF8 "late news".toUTF8 99999
  let rounds := round w .a cid
  let ready := match w.a.node.conns, w.b.node.conns with
    | [(ca, ka)], [(cb, kb)] =>
      ca == cid && cb == cid && !ka.known.contains late.id && !ka.offered.contains late.id &&
        !kb.asked.contains late.id
    | _, _ => false
  t.ok "stream: the law's premises hold of the live world" (ready && w.a.node.managed.isEmpty &&
    w.b.node.managed.isEmpty && w.a.node.addr? cid == some w.b.addr && !holds w.a late.id &&
    !holds w.b late.id && fam.room late == some c && !isWire late.kind)
  let f1 : Frame := ⟨w.b.addr, plainFrame cid [(Msg.hold [late.id]).op.bytes]⟩
  let f2 : Frame := ⟨w.a.addr, plainFrame cid [(Msg.want [late.id]).op.bytes]⟩
  let w1 := w.write S .a [late] (w.now + 1)
  t.ok "stream: the write sends exactly the offer" (w1.net.map (·.bytes) == [f1.bytes] &&
    w1.net.map (·.dst) == [f1.dst])
  let w2 := w1.deliver S .b [] [] f1 (w1.now + 1)
  t.ok "stream: the offer is answered with exactly the want" (w2.net.map (·.bytes) == [f2.bytes] &&
    w2.net.map (·.dst) == [f2.dst])
  let w3 := w2.deliver S .a [] [] f2 (w2.now + 1)
  let first := match w3.net with
    | f :: _ => f.dst == w.b.addr && (do
        let (x, b) ← (Codec.decode (f.bytes.extract 1 f.bytes.size) : Option (Id × ByteArray))
        let ps ← (Codec.decode b : Option (List ByteArray))
        pure (x == cid && ps.head? == some late.bytes)) == some true
    | [] => false
  t.ok "stream: the answer's first frame begins with the op" first
  let w4 := w3.deliver S .b [] w3.net.tail w3.net.head! (w3.now + 1)
  t.ok "stream: the peer holds the op" (holds w4.b late.id)
  t.ok "stream: without another round" (round w4 .a cid == rounds)

  -- Every session: a holds a second session to b; a write is offered on
  -- both (`stream_offered`).
  let cid2 := sha256 "conn2".toUTF8
  let w5 := (w4.connect S .a cid2 true (w4.now + 1)).connect S .b cid2 false (w4.now + 1)
  let (w5, _) := drain S w5 none 100000
  let later := post c c (Device.named "acme-founder") "k".toUTF8 "later news".toUTF8 100000
  let w6 := w5.write S .a [later] (w5.now + 1)
  t.ok "stream: two sessions, each up" (w5.a.node.conns.length == 2 && w5.b.node.conns.length == 2)
  t.ok "stream: a write is offered on each session" ([cid, cid2].all fun x =>
    w6.net.any fun f => f.dst == w.b.addr && offers f x later.id)
  t.ok "stream: and on no session that is not open" (!w6.net.any fun f =>
    offers f (sha256 "conn3".toUTF8) later.id)

  -- Negative control: b's rooms on the session leave c out, so the
  -- stream's room premise fails; nothing of c reaches b.
  let Sx : Setup Fact := { fam, rooms := fun s _ => if s == .b then [] else [c] }
  let wx : World Fact := { a := peerOf Sx h "a", b := peerOf Sx [] "b" }
  let wx := (wx.connect Sx .a cid true 0).connect Sx .b cid false 0
  let (wx, _) := drain Sx wx none 100000
  let (wx, _) := drain Sx (wx.write Sx .a [late] (wx.now + 1)) none 100000
  t.ok "rooms: a peer without the room gets none of it, streamed or not"
    (!holds wx.b late.id && h.all fun o => !holds wx.b o.id)

  t.finish "syncworld"
