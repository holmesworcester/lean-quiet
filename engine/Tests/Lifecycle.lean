/-
A community's lifecycle as ops, intents and lists only, on two SQLite
nodes with real Ed25519: A founds "Acme" and invites; B pastes the link
and joins; ops move between the nodes only through sync's `offer` and
`intake`; A approves; A renames; B ends up admitted, with A's ops and
the new name. Everything a screen would show (communities, who is
waiting, names) is read as lists; nothing is kept beside the ops. A
peer's local ops never land, and a secret whose seed is not its key's
is refused.
-/
import Tests.Lib

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
def sendable (db : Db) : IO (List Op) := do
  let all ← (dumpOps (F := Fact)).run db
  (offer fam (all.map (·.id)) : SqlM Fact (List Op)).run db

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
  let mine (db : Db) (w : Write) : IO Unit := (receive fam (intake fam true w.ops)).run db
  let fromPeer (db : Db) (ops : List Op) : IO Unit := (receive fam (intake fam false ops)).run db

  -- A founds Acme as Ann: the secret, the root, the acceptance, the
  -- name, A's profile, and the community's content key, wrapped to A.
  let kA := sha256 "Acme's content key".toUTF8
  let w := found seedA "Acme".toUTF8 "Ann".toUTF8 1 kA (sha256 "esk 1".toUTF8)
  mine a w
  let c := (root dA).id
  let kid := kidOf cryptoSeal kA
  t.ok "A holds the content key" ((← rows a (key.byId.query [kid])).any fun (_, f) => f == .key c kid kA)
  t.ok "and its wrap to A's device is stored"
    ((← rows a (wrap.byRecipient.query [c, dA.enc])).length == 1)
  t.ok "A's device key is a real X25519 key" (dA.enc.size == 32 && cryptoSeal.pub dA.encSecret == dA.enc)
  -- A posts: the text is sealed; the op and its fact hold only ciphertext.
  let nonce := (sha256 "nonce 1".toUTF8).extract 0 24
  let wpost := send c c seedA kA nonce "hello from Ann".toUTF8 3 []
  mine a wpost
  let msgs ← rows a (message.all.query [c])
  let sealed := msgs.findSome? fun (_, f) => match f with
    | .message _ _ _ k s _ => if k == kid then some s else none
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
  let wa ← ((introduce c seedA 2).run : SqlM Fact Write).run a
  t.ok "the founder has a profile, so introducing writes nothing" wa.ops.isEmpty
  t.ok "A is in its community" ((← rows a (accepted.all.query [])).any fun (_, f) => f == .accepted c dA.pk)
  t.ok "A's secret is held, and derives to its key"
    ((← rows a (secret.byKey.query [dA.pk])).any fun (_, f) => f == .secret dA.pk seedA)
  let name ← rows a (named.current.query [c] (limit := some 1))
  t.ok "the community is named Acme" (name.map (·.2) == [.named c c "Acme".toUTF8 1])

  -- A invites; the link is text.
  let (wi, link) := inviteTo c c seedA (sha256 "bearer".toUTF8) ["10.0.0.5:7001".toUTF8]
  mine a wi

  -- B pastes the link and joins: just ops on B.
  let some i := Invite.parse link.text | t.ok "the link parses" false; return 1
  let wj ← ((join i seedB "Bea".toUTF8).run : SqlM Fact Write).run b
  t.ok "a first join writes the secret, the request, the acceptance and the joining" (wj.ops.length == 4)
  mine b wj
  let again ← ((join i seedB "Bea".toUTF8).run : SqlM Fact Write).run b
  t.ok "joining a community already held writes nothing" again.ops.isEmpty
  let other ← ((join i (sha256 "device B2".toUTF8) "Bea2".toUTF8).run : SqlM Fact Write).run b
  t.ok "not even as another device" other.ops.isEmpty
  t.ok "B is in c as dB" ((← ((Community.mine c).run : SqlM Fact _).run b).map (·.1) == some dB.pk)
  let req := i.request dB
  t.ok "B lists the community" ((← rows b (accepted.all.query [])).any fun (_, f) => f == .accepted c dB.pk)
  t.ok "B lists its pending join"
    ((← rows b (joining.all.query [])).any fun (_, f) => f == .joining c dA.pk i.hints req.id "Bea".toUTF8 dB.pk 0)
  let wn ← ((introduce c seedB 5).run : SqlM Fact Write).run b
  t.ok "before admission, introducing writes nothing" wn.ops.isEmpty
  t.ok "B is not admitted yet" (!(← ((allowPeer c dB.pk).run : SqlM Fact Bool).run b))

  -- B's join reaches A through sync: only the request lands.
  fromPeer a (← sendable b)
  let held ← (dumpOps (F := Fact)).run a
  t.ok "A holds B's request" (held.any (·.id == req.id))
  t.ok "none of B's local ops land on A" (!held.any fun o => wj.ops.any fun l => l.id == o.id && l.id != req.id)
  t.ok "A sees the request pending" ((← rows a (request.all.query [c])).length == 1)

  -- A approves: its approval completes the tally, so it admits B.
  let wa ← ((approveReq c req.id c seedA (sha256 "esk 2".toUTF8)).run : SqlM Fact Write).run a
  t.ok "approving composes the approval, the admission and the key's wrap to B"
    (wa.ops.length == 3)
  mine a wa
  t.ok "A now lets B in" (← ((allowPeer c dB.pk).run : SqlM Fact Bool).run a)

  -- A renames: one past the current name.
  let wr ← ((rename c c c seedA "Acme Corp".toUTF8).run : SqlM Fact Write).run a
  mine a wr
  let name2 ← rows a (named.current.query [c] (limit := some 1))
  t.ok "the current name is the new one" (name2.map (·.2) == [.named c c "Acme Corp".toUTF8 2])

  -- A's ops reach B through sync.
  fromPeer b (← sendable a)
  t.ok "B is admitted, by its own ops" (← ((allowPeer c dB.pk).run : SqlM Fact Bool).run b)
  t.ok "B lets A in" (← ((allowPeer c dA.pk).run : SqlM Fact Bool).run b)
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
  let wu ← ((unwrap c seedB).run : SqlM Fact Write).run b
  t.ok "B unwraps one key, A's" (wu.ops.length == 1)
  mine b wu
  let kB := (← rows b (key.byId.query [kid])).findSome? fun (_, f) => match f with
    | .key _ _ k => some k | _ => none
  t.ok "B now holds Acme's content key" (kB == some kA)
  let after ← rd b
  t.ok "now B's readable messages list A's post, and only it"
    (after.rows.length == 1 && after.total == 1 &&
      after.rows.all fun (_, f) => match f with | .message _ _ _ k _ _ => k == kid | _ => false)
  t.ok "A reads the same one message" ((← rd a).rows.length == 1)
  -- A message under a key nobody here holds stays hidden.
  let kX := sha256 "a key never wrapped".toUTF8
  mine a (send c c seedA kX ((sha256 "nonce X".toUTF8).extract 0 24) "unreadable".toUTF8 4)
  t.ok "A stores the message under the unheld key" ((← rows a (message.all.query [c])).length == 2)
  t.ok "but A's readable messages still hold only the one under its key" ((← rd a).rows.length == 1)
  let ctB := (← rows b (message.all.query [c])).findSome? fun (_, f) => match f with
    | .message _ _ _ _ s _ => some s | _ => none
  t.ok "B opens A's post" ((ctB.bind fun s => kB.bind fun k => openSealed cryptoSeal c kid s k)
    == some "hello from Ann".toUTF8)
  let wu2 ← ((unwrap c seedB).run : SqlM Fact Write).run b
  t.ok "unwrapping again writes nothing" wu2.ops.isEmpty
  -- Two acceptances of c on B (a join that raced): B is in c as its
  -- admitted device, whichever acceptance id is less.
  let seedB2 := sha256 "device B twin".toUTF8
  let w2 := joinOps i seedB2 "Bea twin".toUTF8
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
  let wf := send c c seedA kA ((sha256 "nonce 2".toUTF8).extract 0 24) "a photo".toUTF8 7 [nf]
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
    let cs ← rows b (chunk.byFile.query [c, root, Codec.encode len] (desc := false))
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
  -- Chunks authenticate themselves: Valid on a node with no attachment,
  -- and a tampered one is Invalid.
  let solo ← fresh dir "solo.db"
  let chunkOps := wf.ops.drop 2
  fromPeer solo ([root dA] ++ chunkOps)
  let soloChunks ← rows solo (message.all.query [c])
  t.ok "a node without the post holds no message" soloChunks.isEmpty
  let mut validChunks := 0
  for o in chunkOps do
    if let some (.valid _) ← ((Store.getStatus o.id : SqlM Fact _).run solo) then validChunks := validChunks + 1
  t.ok "every chunk is Valid there, before its attachment" (validChunks == nc)
  match (chunkOps.headD default |>.body |> fun b => (Codec.decode b : Option Body)) with
  | some (.chunk r l i sl p) =>
    let bad := mkOp [c] (.chunk r l i (sl.set! 5 (sl.get! 5 ^^^ 1)) p)
    let short := mkOp [c] (.chunk r l i sl p.tail)
    let wrongIndex := mkOp [c] (.chunk r l (i + 1) sl p)
    fromPeer solo [bad, short, wrongIndex]
    let st (o : Op) : IO Bool := do
      return match ← ((Store.getStatus o.id : SqlM Fact _).run solo) with | some .invalid => true | _ => false
    t.ok "a tampered chunk is Invalid" (← st bad)
    t.ok "a chunk with a short path is Invalid" (← st short)
    t.ok "a chunk under the wrong index is Invalid" (← st wrongIndex)
    -- Progress is one count of one list, chunk by chunk; a chunk sent
    -- twice, or re-sent under another op type, is not counted again.
    let pr (db : Db) (len : Nat) : IO (Nat × Nat) :=
      ((progress c r len).run : SqlM Fact (Nat × Nat)).run db
    let dl ← fresh dir "download.db"
    fromPeer dl [root dA]
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
    t.ok "a length the attachment does not commit counts no chunk" ((← pr dl (l + 1)).1 == 0)
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
  let wp ← ((introduce c seedB 5).run : SqlM Fact Write).run b
  t.ok "admitted, introducing writes one profile" (wp.ops.length == 1)
  mine b wp
  let reqA2 := (wj.ops.filter fun o => o.id == req.id).length
  let u := req.id
  t.ok "B's profile names it Bea"
    ((← rows b (profile.byUser.query [c, u])).any fun (_, f) => match f with
      | .profile _ _ nm _ => nm == "Bea".toUTF8 | _ => false)
  let wp2 ← ((introduce c seedB 6).run : SqlM Fact Write).run b
  t.ok "with a profile, introducing writes nothing" (wp2.ops.isEmpty && reqA2 == 1)

  -- C joins and stops waiting: still listed, no longer waiting; the
  -- request stays with A, and A's approval still admits C.
  let seedC := sha256 "device C".toUTF8
  let dC := Device.ofSeed seedC
  let cdb ← fresh dir "c.db"
  let (wi2, link2) := inviteTo c c seedA (sha256 "bearer 2".toUTF8) []
  mine a wi2
  let wc ← ((join link2 seedC "Cy".toUTF8).run : SqlM Fact Write).run cdb
  mine cdb wc
  let reqC := link2.request dC
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
  let wr ← ((join link2 seedC "Cy".toUTF8).run : SqlM Fact Write).run cdb
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
  mine a (← ((approveReq c reqC.id c seedA).run : SqlM Fact Write).run a)
  fromPeer cdb (← sendable a)
  t.ok "an approval after stopping still admits C" (← ((allowPeer c dC.pk).run : SqlM Fact Bool).run cdb)

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
  t.finish "lifecycle"
