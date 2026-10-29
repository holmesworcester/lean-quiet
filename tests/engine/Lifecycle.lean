/-
A community's lifecycle as ops, intents and lists only, on two SQLite
nodes with real Ed25519: A founds "Acme" and invites; B pastes the link
and joins; ops move between the nodes through sync's filed/want path and
`intake`; A approves; A renames; B ends up admitted, with A's ops and
the new name. Everything a screen would show (communities, who is
waiting, names) is read as lists; nothing is kept beside the ops. A
peer's local ops never land, and a secret whose seed is not its key's
is refused.
-/
import tests.engine.Lib
import tests.engine.Stream

open Engine Community Tests

def C := ed25519
def fam := family C

def fresh (dir name : String) : IO Db := do
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/" ++ name ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  Db.openAt (dir ++ "/" ++ name)

def rows (db : Db) (q : ListQ) : IO (List (Pos × Fact)) := do
  return (← (Lists.list q : SqlM Fact (Answer Fact)).run db).rows

/-- Ops held by db that a peer may be sent. -/
def sendable (db : Db) : IO (List Op) := streamOps fam db

/-- The channel's order, on A and B once both are admitted to c and
hold its content key kA: a counter every device shares, the time
breaking ties, then the id; past the counter cap, each device's own
receipts. A node writes a receipt for every op it takes
(`Connection.onArrival`, each job's receipts reading the store as it was
before them); `arrive` does the same here. -/
def channelOrder (t : Checks) (a b : Db) (c : Id) (kA seedA seedB : ByteArray) : IO Unit := do
  let dA := Device.ofSeed seedA
  let dB := Device.ofSeed seedB
  let kid := kidOf cryptoSeal kA
  let mine (db : Db) (w : Write) : IO Unit := (receive fam (intake fam true w.ops)).run db
  let fromPeer (db : Db) (ops : List Op) : IO Unit := (receive fam (intake fam false ops)).run db
  let sendOn (db : Db) (v : View Fact Write) : IO Write := (v.run : SqlM Fact Write).run db
  let rd (db : Db) : IO (Answer Fact) := ((readable c (some 50)).run : SqlM Fact (Answer Fact)).run db
  let receipts (db : Db) (ops : List Op) : IO (List Op) := do
    let mut out := []
    for o in ops do out := out ++ (← ((receiptFor o).run : SqlM Fact (List Op)).run db)
    return out
  let arrive (db : Db) (ops : List Op) : IO Unit := do
    fromPeer db ops
    mine db ⟨← receipts db ops⟩
  let sync : IO Unit := do
    arrive a (← sendable b)
    arrive b (← sendable a)
  let order (db : Db) : IO (List Id) := return (← rd db).rows.map (·.1.2)
  let counterOf (o : Op) : Nat := match (Codec.decode o.body : Option Body) with
    | some (.post _ _ n _ _) => n | _ => 0
  let nonceOf (tag : String) : ByteArray := (sha256 tag.toUTF8).extract 0 24
  let admOf (db : Db) (d : Device) : IO Id := do
    return ((← rows db (admission.byDevice.query [c, d.pk] (limit := some 1))).headD default).1.2
  let admA ← admOf a dA
  let admB ← admOf b dB
  let mins := 29350000  -- minutes since the Unix epoch, late October 2026
  sync
  t.ok "before writing, A and B list the same messages" ((← order a) == (← order b))
  -- Concurrent sends hold the same messages, so they claim the same
  -- counter; the earlier time sorts first.
  let wA1 ← sendOn a (send c admA dA kA (nonceOf "A1") "A1".toUTF8 (mins + 500))
  let wB1 ← sendOn b (send c admB dB kA (nonceOf "B1") "B1".toUTF8 (mins + 400))
  let pA1 := wA1.ops.headD default
  let pB1 := wB1.ops.headD default
  t.ok "concurrent sends claim the same counter, one past the highest held"
    (counterOf pA1 == counterOf pB1 && counterOf pA1 ≥ 2 && wA1.ops.length == 1)
  mine a wA1
  mine b wB1
  sync
  t.ok "equal counters: the earlier time first, on both devices"
    ((← order a).take 2 == [pA1.id, pB1.id] && (← order b).take 2 == [pA1.id, pB1.id])
  -- Equal counter and time: the id decides.
  let wA2 ← sendOn a (send c admA dA kA (nonceOf "A2") "A2".toUTF8 (mins + 600))
  let wB2 ← sendOn b (send c admB dB kA (nonceOf "B2") "B2".toUTF8 (mins + 600))
  let pA2 := wA2.ops.headD default
  let pB2 := wB2.ops.headD default
  mine a wA2
  mine b wB2
  sync
  let (lo, hi) := if bcmp pA2.id pB2.id == .lt then (pA2, pB2) else (pB2, pA2)
  t.ok "equal counter and time: the larger id is newer, on both devices"
    (counterOf pA2 == counterOf pB2 && (← order a).take 2 == [hi.id, lo.id] && (← order b).take 2 == [hi.id, lo.id])
  -- Time is for display: a clock far behind still sorts last-written last.
  let wA3 ← sendOn a (send c admA dA kA (nonceOf "A3") "A3".toUTF8 5)
  let pA3 := wA3.ops.headD default
  mine a wA3
  sync
  t.ok "a send with a clock far behind still sorts after everything its device held, on both"
    (counterOf pA3 == counterOf hi + 1 && (← order a).head? == some pA3.id && (← order b).head? == some pA3.id)
  -- A member claims a huge counter (written raw, not by `send`).
  let huge := sealedPost c admB dB kA (nonceOf "huge") "MAX".toUTF8 (2 ^ 200) (mins + 700)
  mine b ⟨[huge]⟩
  mine b ⟨← receipts b [huge]⟩
  sync
  t.ok "a message claiming a huge counter is Valid on A"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) huge.id).run a) matches some (.valid _))
  t.ok "A holds one receipt of it, its first in c"
    ((← rows a (received.byMsg.query [huge.id])).map (·.2) == [.received c kid huge.id 1])
  t.ok "it is listed after every message below the cap, on both"
    ((← order a).take 2 == [huge.id, pA3.id] && (← order b).take 2 == [huge.id, pA3.id])
  -- Past the cap: every send claims the cap and carries its receipt,
  -- and each device lists in its own arrival order.
  let wA4 ← sendOn a (send c admA dA kA (nonceOf "A4") "A4".toUTF8 (mins + 800))
  let wB4 ← sendOn b (send c admB dB kA (nonceOf "B4") "B4".toUTF8 (mins + 800))
  let pA4 := wA4.ops.headD default
  let pB4 := wB4.ops.headD default
  t.ok "past the cap, a send claims the cap and writes its receipt, one past the newest"
    (counterOf pA4 == countCap && wA4.ops.map (·.id) == [pA4.id, (receipt pA4.id 2).id])
  mine a wA4
  mine b wB4
  t.ok "each device lists its own saturated message newest at once"
    ((← order a).head? == some pA4.id && (← order b).head? == some pB4.id)
  sync
  t.ok "past the cap, each device lists in its own arrival order (the two disagree)"
    ((← order a).take 3 == [pB4.id, pA4.id, huge.id] && (← order b).take 3 == [pA4.id, pB4.id, huge.id])
  let oa ← order a
  let ob ← order b
  t.ok "and every message is listed once, the same set on both"
    (oa.length == ob.length && oa.all ob.contains && oa.eraseDups.length == oa.length)
  t.ok "receipts never leave a device" ((← sendable a).all fun o => o.kind != 24)
  t.ok "a message already received gets no second receipt" ((← receipts a [pB4, huge, pA4]).isEmpty)
  let lowRcpt := receipt pA3.id 9
  mine a ⟨[lowRcpt]⟩
  t.ok "a receipt of a message below the cap is refused"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) lowRcpt.id).run a) == some .invalid)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/lifecycle"
  IO.FS.createDirAll dir
  let t ← Checks.new
  let a ← fresh dir "a.db"
  let b ← fresh dir "b.db"
  let seedA := sha256 "device A".toUTF8
  let seedB := sha256 "device B".toUTF8
  let dA := Device.ofSeed seedA
  let dB := Device.ofSeed seedB
  -- each node's own key: the first found or join writes it
  let nkA := sha256 "node A".toUTF8
  let nkB := sha256 "node B".toUTF8
  let nkC := sha256 "node C".toUTF8
  let keyA := cryptoSeal.pub nkA
  let keyB := cryptoSeal.pub nkB
  let keyC := cryptoSeal.pub nkC
  let mine (db : Db) (w : Write) : IO Unit := (receive fam (intake fam true w.ops)).run db
  let fromPeer (db : Db) (ops : List Op) : IO Unit := (receive fam (intake fam false ops)).run db
  let sendOn (db : Db) (v : View Fact Write) : IO Write := (v.run : SqlM Fact Write).run db

  -- A founds Acme as Ann: the secret, the root, the acceptance, the
  -- name, A's profile, and the community's content key, wrapped to A.
  let kA := sha256 "Acme's content key".toUTF8
  let w ← ((found seedA "Acme".toUTF8 "Ann".toUTF8 1 kA (sha256 "esk 1".toUTF8) nkA).run :
    SqlM Fact Write).run a
  t.ok "founding on a node with no key writes its key first" (w.ops.head? == some (endpoint nkA))
  mine a w
  let c := (root dA keyA).id
  let kid := kidOf cryptoSeal kA
  t.ok "A holds the content key" ((← rows a (key.byId.query [kid])).any fun (_, f) => f == .key c kid kA)
  t.ok "and its wrap to A's node key is stored"
    ((← rows a (wrap.byRecipient.query [c, keyA])).length == 1)
  t.ok "A's node key is a real X25519 key, held as a local op with its secret"
    (keyA.size == 32 && (← rows a (endpoint.all.query [])).any fun (_, f) => f == .endpoint keyA nkA)
  t.ok "the root names A's device and A's node key"
    ((← rows a (admission.byKey.query [c, keyA])).any fun (_, f) => f == .admission c c dA.pk keyA)
  -- A posts: the text is sealed; the op and its fact hold only ciphertext.
  let nonce := (sha256 "nonce 1".toUTF8).extract 0 24
  let wpost ← sendOn a (send c c dA kA nonce "hello from Ann".toUTF8 3 [])
  mine a wpost
  let msgs ← rows a (message.all.query [c])
  let sealed := msgs.findSome? fun (_, f) => match f with
    | .message _ _ _ k s _ _ => if k == kid then some s else none
    | _ => none
  t.ok "A's post is Valid, under the key's id" sealed.isSome
  let ct := sealed.getD .empty
  let plain := "hello from Ann".toUTF8
  t.ok "its stored body is not the plaintext"
    (ct.size == 24 + plain.size + 16 && ct.extract 24 (24 + plain.size) != plain)
  t.ok "A opens it with the key" (openSealed cryptoSeal c kid ct kA == some "hello from Ann".toUTF8)
  t.ok "another key does not open it"
    ((openSealed cryptoSeal c kid ct (sha256 "other".toUTF8)).isNone)
  let annOn (db : Db) : IO Bool := do
    return (← rows db (profile.byUser.query [c, c])).any fun (_, f) => match f with
      | .profile _ _ nm _ => nm == "Ann".toUTF8 | _ => false
  t.ok "A's profile names it Ann (the founder is user c)" (← annOn a)
  let wa ← ((introduce c dA 2).run : SqlM Fact Write).run a
  t.ok "the founder has a profile, so introducing writes nothing" wa.ops.isEmpty
  t.ok "A is in its community" ((← rows a (accepted.all.query [])).any fun (_, f) => f == .accepted c dA.pk)
  t.ok "A's secret is held, and derives to its key"
    ((← rows a (secret.byKey.query [dA.pk])).any fun (_, f) => f == .secret dA.pk seedA)
  let name ← rows a (named.current.query [c] (limit := some 1))
  t.ok "the community is named Acme" (name.map (·.2) == [.named c c "Acme".toUTF8 1])

  -- A invites; the link is text.
  let some (wi, link) ← ((inviteTo c c dA (sha256 "bearer".toUTF8) ["10.0.0.5:7001".toUTF8]).run :
    SqlM Fact _).run a | t.ok "A invites" false; return 1
  t.ok "the link names A's node key" (link.inviter == keyA)
  mine a wi

  -- B pastes the link and joins: just ops on B.
  let some i := Invite.parse link.text | t.ok "the link parses" false; return 1
  let wj ← ((join i seedB "Bea".toUTF8 nkB).run : SqlM Fact Write).run b
  t.ok "a first join on a new node writes the node's key, the secret, the request, the acceptance and the joining"
    (wj.ops.length == 5 && wj.ops.head? == some (endpoint nkB))
  mine b wj
  let again ← ((join i seedB "Bea".toUTF8 nkB).run : SqlM Fact Write).run b
  t.ok "joining a community already held writes nothing" again.ops.isEmpty
  let other ← ((join i (sha256 "device B2".toUTF8) "Bea2".toUTF8 nkB).run : SqlM Fact Write).run b
  t.ok "not even as another device" other.ops.isEmpty
  t.ok "B is in c as dB" ((← ((Community.mine c).run : SqlM Fact _).run b).map (·.1) == some dB.pk)
  let req := i.request dB keyB
  t.ok "B lists the community" ((← rows b (accepted.all.query [])).any fun (_, f) => f == .accepted c dB.pk)
  t.ok "B lists its pending join"
    ((← rows b (joining.all.query [])).any fun (_, f) => f == .joining c keyA i.hints req.id "Bea".toUTF8 dB.pk 0)
  let wn ← ((introduce c dB 5).run : SqlM Fact Write).run b
  t.ok "before admission, introducing writes nothing" wn.ops.isEmpty
  t.ok "B is not admitted yet" (!(← ((allowPeer c keyB).run : SqlM Fact Bool).run b))

  -- B's join reaches A through sync: only the request lands.
  fromPeer a (← sendable b)
  let held ← (dumpOps (F := Fact)).run a
  t.ok "A holds B's request" (held.any (·.id == req.id))
  t.ok "none of B's local ops land on A" (!held.any fun o => wj.ops.any fun l => l.id == o.id && l.id != req.id)
  t.ok "A sees the request pending" ((← rows a (request.all.query [c])).length == 1)

  -- A approves: its approval completes the tally, so it admits B.
  let wa ← ((approveReq c req.id c dA (sha256 "esk 2".toUTF8)).run : SqlM Fact Write).run a
  t.ok "approving composes the approval, the admission and the key's wrap to B"
    (wa.ops.length == 3)
  mine a wa
  t.ok "A now lets B's node in" (← ((allowPeer c keyB).run : SqlM Fact Bool).run a)

  -- A renames: one past the current name.
  let wr ← ((rename c c c dA "Acme Corp".toUTF8).run : SqlM Fact Write).run a
  mine a wr
  let name2 ← rows a (named.current.query [c] (limit := some 1))
  t.ok "the current name is the new one" (name2.map (·.2) == [.named c c "Acme Corp".toUTF8 2])

  -- A's ops reach B through sync.
  fromPeer b (← sendable a)
  t.ok "B is admitted, by its own ops" (← ((allowPeer c keyB).run : SqlM Fact Bool).run b)
  t.ok "B lets A in" (← ((allowPeer c keyA).run : SqlM Fact Bool).run b)
  let name3 ← rows b (named.current.query [c] (limit := some 1))
  t.ok "B shows the new name" (name3.map (·.2) == [.named c c "Acme Corp".toUTF8 2])
  t.ok "A's secret never reached B" ((← rows b (secret.byKey.query [dA.pk])).isEmpty)
  t.ok "B shows A as Ann" (← annOn b)
  -- B opens the key wrapped to it, and with it A's post.
  t.ok "before unwrapping, B holds no key" ((← rows b (key.byId.query [kid])).isEmpty)
  let rd (db : Db) : IO (Answer Fact) := ((readable c (some 50)).run : SqlM Fact (Answer Fact)).run db
  let before ← rd b
  t.ok "B's readable messages: none yet, so the message sealed under the key on its way is hidden"
    (before.rows.isEmpty && before.total == 0)
  let wu ← ((unwrap c).run : SqlM Fact Write).run b
  t.ok "B unwraps one key, A's" (wu.ops.length == 1)
  mine b wu
  let kB := (← rows b (key.byId.query [kid])).findSome? fun (_, f) => match f with
    | .key _ _ k => some k | _ => none
  t.ok "B now holds Acme's content key" (kB == some kA)
  let after ← rd b
  t.ok "now B's readable messages list A's post, and only it"
    (after.rows.length == 1 && after.total == 1 &&
      after.rows.all fun (_, f) => match f with | .message _ _ _ k _ _ _ => k == kid | _ => false)
  t.ok "A reads the same one message" ((← rd a).rows.length == 1)
  -- A message under a key nobody here holds stays hidden.
  let kX := sha256 "a key never wrapped".toUTF8
  mine a (← sendOn a (send c c dA kX ((sha256 "nonce X".toUTF8).extract 0 24) "unreadable".toUTF8 4))
  t.ok "A stores the message under the unheld key" ((← rows a (message.all.query [c])).length == 2)
  t.ok "but A's readable messages still hold only the one under its key" ((← rd a).rows.length == 1)
  let ctB := (← rows b (message.all.query [c])).findSome? fun (_, f) => match f with
    | .message _ _ _ _ s _ _ => some s | _ => none
  t.ok "B opens A's post" ((ctB.bind fun s => kB.bind fun k => openSealed cryptoSeal c kid s k)
    == some "hello from Ann".toUTF8)
  let wu2 ← ((unwrap c).run : SqlM Fact Write).run b
  t.ok "unwrapping again writes nothing" wu2.ops.isEmpty
  -- Two acceptances of c on B (a join that raced): B is in c as its
  -- admitted device, whichever acceptance id is less.
  let seedB2 := sha256 "device B twin".toUTF8
  let w2 := joinOps i seedB2 "Bea twin".toUTF8 keyB
  mine b w2
  t.ok "with a raced second acceptance, B is still in c as its admitted device"
    ((← ((Community.mine c).run : SqlM Fact _).run b).map (·.1) == some dB.pk)
  t.ok "A's content key travelled only wrapped: B holds it as its own local op"
    ((← rows b (key.byCommunity.query [c])).length == 1)

  -- A attaches a file to a post: an attachment (a child of the post)
  -- and the file's chunks, all ops.
  let plainFile := ByteArray.mk ((List.range 200000).map fun i => (i * 7 + i / 300).toUInt8).toArray
  let info : FileMeta := ⟨"photo.qoi".toUTF8, "image/qoi".toUTF8, 640, 480, "tiny preview".toUTF8⟩
  let nf : NewFile := ⟨info, plainFile, sha256 "file key".toUTF8, (sha256 "file nonce".toUTF8).extract 0 24,
    (sha256 "info nonce".toUTF8).extract 0 24⟩
  let wf ← sendOn a (send c c dA kA ((sha256 "nonce 2".toUTF8).extract 0 24) "a photo".toUTF8 7 [nf])
  let nc := Merkle.nChunks (fileCipher nf).size
  t.ok "the send writes the post, the attachment and the chunks" (wf.ops.length == 2 + nc && nc == 4)
  mine a wf
  let postId := (wf.ops.headD default).id
  t.ok "on A, the post lists its attachment"
    ((← rows a (attachment.byMessage.query [c, postId])).length == 1)
  fromPeer b (← sendable a)
  let atts ← rows b (attachment.byMessage.query [c, postId])
  t.ok "on B, the post lists its attachment" (atts.length == 1)
  match atts.head? with
  | some (_, .attachment _ _ _ root len akid sealedInfo) =>
    let cs ← rows b (chunk.byAttachment.query [c, (wf.ops.getD 1 default).id] (desc := false))
    t.ok "B holds every chunk: progress is a count" (cs.length == Merkle.nChunks len)
    let mut slicesB : List ByteArray := []
    for ((_, x), _) in cs do
      match ← ((Store.getOp x : SqlM Fact _).run b) with
      | some o => match (Codec.decode o.body : Option Body) with
        | some (.chunk _ _ _ sl _) => slicesB := slicesB ++ [sl]
        | _ => pure ()
      | none => pure ()
    match openInfo c akid sealedInfo kA with
    | some (i2, fk, fn) =>
      t.ok "B opens the attachment's info with the content key" (i2 == info)
      t.ok "B assembles the chunks and opens the file" (openFile slicesB fk fn == some plainFile)
    | none => t.ok "B opens the attachment's info" false
    t.ok "the info does not open with another key"
      ((openInfo c akid sealedInfo (sha256 "other".toUTF8)).isNone)
  | _ => t.ok "the attachment's fact" false
  -- Chunks are their attachment's: on a node without it they wait, and
  -- they are Valid once it arrives; a tampered one is Invalid.
  let solo ← fresh dir "solo.db"
  let postOp := wf.ops.headD default
  let attOp := wf.ops.getD 1 default
  let att := attOp.id
  let chunkOps := wf.ops.drop 2
  t.ok "every chunk cites its community and its attachment, and nothing else"
    (chunkOps.all fun o => o.reqs == [c, att])
  fromPeer solo ([root dA keyA] ++ chunkOps)
  let soloChunks ← rows solo (message.all.query [c])
  t.ok "a node without the post holds no message" soloChunks.isEmpty
  let countValid (db : Db) (os : List Op) : IO Nat := do
    let mut n := 0
    for o in os do
      if let some (.valid _) ← ((Store.getStatus o.id : SqlM Fact _).run db) then n := n + 1
    return n
  t.ok "without their attachment, no chunk is Valid: they wait" ((← countValid solo chunkOps) == 0)
  fromPeer solo [postOp, attOp]
  t.ok "with it, every chunk is Valid" ((← countValid solo chunkOps) == nc)
  -- The same file attached to a second post: its own attachment, its
  -- own chunks, none shared with the first.
  let wf2 ← sendOn a (send c c dA kA ((sha256 "nonce 3".toUTF8).extract 0 24) "the photo again".toUTF8 8 [nf])
  let chunks2 := wf2.ops.drop 2
  t.ok "the same file sent twice shares no chunk op"
    (chunks2.length == nc && chunks2.all fun o => !(chunkOps.any (·.id == o.id)))
  match (chunkOps.headD default |>.body |> fun b => (Codec.decode b : Option Body)) with
  | some (.chunk r l i sl p) =>
    let bad := mkOp [c, att] (.chunk r l i (sl.set! 5 (sl.get! 5 ^^^ 1)) p)
    let short := mkOp [c, att] (.chunk r l i sl p.tail)
    let wrongIndex := mkOp [c, att] (.chunk r l (i + 1) sl p)
    let wrongLen := mkOp [c, att] (.chunk r (l + 1) i sl p)
    -- another post's attachment, with another file: this chunk is not its
    let nf3 : NewFile := { nf with bytes := "other bytes".toUTF8, key := sha256 "file key 3".toUTF8 }
    let wf3 ← sendOn a (send c c dA kA ((sha256 "nonce 4".toUTF8).extract 0 24) "other".toUTF8 9 [nf3])
    let att3 := (wf3.ops.getD 1 default).id
    let foreign := mkOp [c, att3] (.chunk r l i sl p)
    fromPeer solo ([wf3.ops.headD default, wf3.ops.getD 1 default] ++ [bad, short, wrongIndex, wrongLen, foreign])
    let st (o : Op) : IO Bool := do
      return match ← ((Store.getStatus o.id : SqlM Fact _).run solo) with | some .invalid => true | _ => false
    t.ok "a tampered chunk is Invalid" (← st bad)
    t.ok "a chunk with a short path is Invalid" (← st short)
    t.ok "a chunk under the wrong index is Invalid" (← st wrongIndex)
    t.ok "a chunk with a length not its attachment's is Invalid" (← st wrongLen)
    t.ok "a chunk cited under another file's attachment is Invalid" (← st foreign)
    let st (o : Op) : IO Bool := do
      return match ← ((Store.getStatus o.id : SqlM Fact _).run solo) with | some .invalid => true | _ => false
    t.ok "a tampered chunk is Invalid" (← st bad)
    t.ok "a chunk with a short path is Invalid" (← st short)
    t.ok "a chunk under the wrong index is Invalid" (← st wrongIndex)
    -- Progress is one count of one list, chunk by chunk; a chunk sent
    -- twice, or re-sent under another op type, is not counted again.
    let pr (db : Db) (len : Nat) : IO (Nat × Nat) :=
      ((progress c att len).run : SqlM Fact (Nat × Nat)).run db
    let dl ← fresh dir "download.db"
    fromPeer dl [root dA keyA, postOp, attOp]
    t.ok "before any chunk, progress is 0 of the chunk count" ((← pr dl l) == (0, nc))
    let mut steps := true
    let mut k := 0
    for o in chunkOps do
      fromPeer dl [o]
      k := k + 1
      fromPeer dl [o]
      let retyped := Op.make 99 o.reqs o.body
      fromPeer dl [retyped]
      steps := steps && (← pr dl l) == (k, nc) && (← ((Store.getStatus retyped.id : SqlM Fact _).run dl)) == some .invalid
    t.ok "each chunk adds one; again, or under another op type (Invalid), adds none" steps
    t.ok "every chunk here: progress is full" ((← pr dl l) == (nc, nc))
    fromPeer dl ([wf2.ops.headD default, wf2.ops.getD 1 default] ++ chunks2.take 2)
    t.ok "the second send's chunks count toward its own attachment only"
      ((← pr dl l) == (nc, nc) &&
        (← ((progress c (wf2.ops.getD 1 default).id l).run : SqlM Fact (Nat × Nat)).run dl) == (2, nc))
  | _ => t.ok "a chunk op" false
  -- A post re-sent under another op type is another op with the same
  -- fact: Invalid, so the message is not shown twice.
  let msgsBefore := (← rows b (message.all.query [c])).length
  let retypedPost := Op.make 42 (wf.ops.headD default).reqs (wf.ops.headD default).body
  fromPeer b [retypedPost]
  t.ok "a post re-sent under another op type is Invalid"
    ((← ((Store.getStatus retypedPost.id : SqlM Fact _).run b)) == some .invalid)
  t.ok "and the message is not listed twice" ((← rows b (message.all.query [c])).length == msgsBefore)

  -- Admitted, B introduces itself by the name it joined with, once.
  let wp ← ((introduce c dB 5).run : SqlM Fact Write).run b
  t.ok "admitted, introducing writes one profile" (wp.ops.length == 1)
  mine b wp
  let reqA2 := (wj.ops.filter fun o => o.id == req.id).length
  let u := req.id
  t.ok "B's profile names it Bea"
    ((← rows b (profile.byUser.query [c, u])).any fun (_, f) => match f with
      | .profile _ _ nm _ => nm == "Bea".toUTF8 | _ => false)
  let wp2 ← ((introduce c dB 6).run : SqlM Fact Write).run b
  t.ok "with a profile, introducing writes nothing" (wp2.ops.isEmpty && reqA2 == 1)

  -- C joins and stops waiting: still listed, no longer waiting; the
  -- request stays with A, and A's approval still admits C.
  let seedC := sha256 "device C".toUTF8
  let dC := Device.ofSeed seedC
  let cdb ← fresh dir "c.db"
  let some (wi2, link2) ← ((inviteTo c c dA (sha256 "bearer 2".toUTF8) []).run : SqlM Fact _).run a
    | t.ok "A invites again" false; return 1
  mine a wi2
  let wc ← ((join link2 seedC "Cy".toUTF8 nkC).run : SqlM Fact Write).run cdb
  mine cdb wc
  let reqC := link2.request dC keyC
  let jC := (wc.ops.getLast!).id
  mine cdb (stopWaiting jC)
  let waiting ← do
    let js ← rows cdb (joining.all.query [])
    js.filterMapM fun ((_, jid), f) => match f with
      | .joining _ _ _ r _ _ _ => do
        let ab ← (Lists.list (abandoned.byJoining.query [jid] (limit := some 0)) : SqlM Fact (Answer Fact)).run cdb
        pure (if ab.total == 0 then some r else none)
      | _ => pure none
  t.ok "after stopping, C waits on nothing" waiting.isEmpty
  t.ok "and C holds no entry for c" ((← ((Community.mine c).run : SqlM Fact _).run cdb).isNone)
  -- Joining again resumes the stopped join: the same request, a new joining.
  let wr ← ((join link2 seedC "Cy".toUTF8 nkC).run : SqlM Fact Write).run cdb
  t.ok "re-joining after stopping writes one joining op" (wr.ops.length == 1)
  let resumed := match wr.ops.head? with
    | some o => match (Codec.decode o.body : Option Body) with
      | some (.joining _ _ _ r _ d n) => r == reqC.id && d == dC.pk && n == 1
      | _ => false
    | none => false
  t.ok "for the same request, the same device, one epoch on" resumed
  mine cdb wr
  t.ok "C holds c again" ((← ((Community.mine c).run : SqlM Fact _).run cdb).map (·.1) == some dC.pk)
  -- and stops again, so the rest of this scenario is unchanged
  mine cdb (stopWaiting (wr.ops.headD default).id)
  t.ok "C still lists the community" ((← rows cdb (accepted.all.query [])).any fun (_, f) => f == .accepted c dC.pk)
  fromPeer a (← sendable cdb)
  t.ok "C's request reached A; its abandon did not"
    ((← (dumpOps (F := Fact)).run a).any (·.id == reqC.id) &&
      !((← (dumpOps (F := Fact)).run a).any fun o => o.id == (stopWaiting jC).ops.head!.id))
  mine a (← ((approveReq c reqC.id c dA).run : SqlM Fact Write).run a)
  fromPeer cdb (← sendable a)
  t.ok "an approval after stopping still admits C" (← ((allowPeer c keyC).run : SqlM Fact Bool).run cdb)

  channelOrder t a b c kA seedA seedB

  -- A secret whose seed is not its key's is refused.
  let bad := mkOp [] (.secret dB.pk seedA)
  mine a ⟨[bad]⟩
  t.ok "a secret with another key's seed is refused"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) bad.id).run a) == some .invalid)
  -- A name by a non-admin is refused.
  let byB := setName c wa.ops.getLast!.id wa.ops.getLast!.id [] 9 dB "B's name".toUTF8
  fromPeer a [byB]
  t.ok "a name by a non-admin is refused"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) byB.id).run a) == some .invalid)
  -- The remover flow: only an admin removes, never itself, and once.
  let rmBy (db : Db) (target : Id) (d : Device) : IO Write :=
    ((removeMember c target d).run : SqlM Fact Write).run db
  t.ok "a non-admin's removal writes nothing" ((← rmBy b c dB).ops.isEmpty)
  t.ok "an admin removing itself writes nothing" ((← rmBy a c dA).ops.isEmpty)
  t.ok "B is let in before" (← ((allowPeer c keyB).run : SqlM Fact Bool).run a)
  let wrm ← rmBy a u dA
  t.ok "the founder removing B writes one removal" (wrm.ops.length == 1)
  mine a wrm
  t.ok "the removal is Valid"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) (wrm.ops.headD default).id).run a) matches some (.valid _))
  t.ok "B is listed as removed, by A"
    ((← rows a (removal.byUser.query [c, u])).any fun (_, f) => f == .removal c u c)
  t.ok "and no longer let in" !(← ((allowPeer c keyB).run : SqlM Fact Bool).run a)
  t.ok "removing B again writes nothing" ((← rmBy a u dA).ops.isEmpty)

  -- E4: a removed entry is not held, and the node rejoins as a new
  -- device. C (admitted after stopping and resuming its join) is removed.
  let liveOn (db : Db) (d : Key) : IO Bool := ((deviceLive c d).run : SqlM Fact Bool).run db
  let uC := reqC.id
  t.ok "C holds c, as its admitted device"
    ((← ((Community.mine c).run : SqlM Fact _).run cdb).map (·.1) == some dC.pk && (← liveOn cdb dC.pk))
  let wrmC ← rmBy a uC dA
  mine a wrmC
  t.ok "A removes C, and refuses C's node" (wrmC.ops.length == 1 && !(← ((allowPeer c keyC).run : SqlM Fact Bool).run a))
  fromPeer cdb (← sendable a)
  t.ok "C holds its removal" ((← rows cdb (removal.byUser.query [c, uC])).any fun (_, f) => f == .removal c uC c)
  t.ok "C's device is cut on C" (!(← liveOn cdb dC.pk))
  t.ok "so C holds c no more: its cut entry is not held"
    ((← ((Community.mine c).run : SqlM Fact _).run cdb).isNone)
  t.ok "a join with the cut device's seed writes nothing"
    ((← ((join link2 seedC "Cy".toUTF8 nkC).run : SqlM Fact Write).run cdb).ops.isEmpty)
  let some (wi3, link3) ← ((inviteTo c c dA (sha256 "bearer 3".toUTF8) []).run : SqlM Fact _).run a
    | t.ok "A invites C again" false; return 1
  mine a wi3
  let seedC3 := sha256 "device C, rejoined".toUTF8
  let dC3 := Device.ofSeed seedC3
  let wj3 ← ((join link3 seedC3 "Cy".toUTF8 (sha256 "unused".toUTF8)).run : SqlM Fact Write).run cdb
  t.ok "rejoining writes a fresh join for the new device, from C's node key"
    (wj3.ops.map (·.id) == (joinOps link3 seedC3 "Cy".toUTF8 keyC).ops.map (·.id))
  let req3 := link3.request dC3 keyC
  t.ok "its request is the new device's, not the cut one's" (dC3.pk != dC.pk && wj3.ops.any (·.id == req3.id))
  mine cdb wj3
  t.ok "C holds c again, as its new device, waiting"
    ((← ((Community.mine c).run : SqlM Fact _).run cdb).map (·.1) == some dC3.pk)
  fromPeer a (← sendable cdb)
  t.ok "C's node is still refused before the new device is approved"
    (!(← ((allowPeer c keyC).run : SqlM Fact Bool).run a))
  let wa3 ← ((approveReq c req3.id c dA).run : SqlM Fact Write).run a
  mine a wa3
  t.ok "once approved, A lets C's node in again: the cut device does not block it"
    (← ((allowPeer c keyC).run : SqlM Fact Bool).run a)
  fromPeer cdb (← sendable a)
  t.ok "C is in c as its new device, admitted"
    ((← ((Community.mine c).run : SqlM Fact _).run cdb).map (·.1) == some dC3.pk && (← liveOn cdb dC3.pk))
  let adm3 ← rows cdb (admission.byDevice.query [c, dC3.pk])
  t.ok "the new device is a new user, never the removed one"
    (adm3.any fun (_, f) => match f with | .admission _ u3 _ k => u3 != uC && k == keyC | _ => false)
  t.ok "the old user stays removed and its device stays cut, on both nodes"
    (!(← liveOn a dC.pk) && !(← liveOn cdb dC.pk) &&
      (← rows a (removal.byUser.query [c, uC])).length == 1)
  t.finish "lifecycle"
