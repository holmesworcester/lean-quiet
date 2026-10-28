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
  -- name, A's profile.
  let w := found seedA "Acme".toUTF8 "Ann".toUTF8 1
  mine a w
  let c := (root dA).id
  let annOn (db : Db) : IO Bool := do
    return (← rows db (profile.byUser.query [c, c])).any fun (_, f) => match f with
      | .profile _ _ nm _ _ => nm == "Ann".toUTF8 | _ => false
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
  let wj := join i seedB "Bea".toUTF8
  mine b wj
  let req := i.request dB
  t.ok "B lists the community" ((← rows b (accepted.all.query [])).any fun (_, f) => f == .accepted c dB.pk)
  t.ok "B lists its pending join"
    ((← rows b (joining.all.query [])).any fun (_, f) => f == .joining c dA.pk i.hints req.id "Bea".toUTF8)
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
  let wa ← ((approveReq c req.id c seedA).run : SqlM Fact Write).run a
  t.ok "approving composes the approval and the admission" (wa.ops.length == 2)
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

  -- Admitted, B introduces itself by the name it joined with, once.
  let wp ← ((introduce c seedB 5).run : SqlM Fact Write).run b
  t.ok "admitted, introducing writes one profile" (wp.ops.length == 1)
  mine b wp
  let reqA2 := (wj.ops.filter fun o => o.id == req.id).length
  let u := req.id
  t.ok "B's profile names it Bea"
    ((← rows b (profile.byUser.query [c, u])).any fun (_, f) => match f with
      | .profile _ _ nm _ _ => nm == "Bea".toUTF8 | _ => false)
  let wp2 ← ((introduce c seedB 6).run : SqlM Fact Write).run b
  t.ok "with a profile, introducing writes nothing" (wp2.ops.isEmpty && reqA2 == 1)

  -- C joins and stops waiting: still listed, no longer waiting; the
  -- request stays with A, and A's approval still admits C.
  let seedC := sha256 "device C".toUTF8
  let dC := Device.ofSeed seedC
  let cdb ← fresh dir "c.db"
  let (wi2, link2) := inviteTo c c seedA (sha256 "bearer 2".toUTF8) []
  mine a wi2
  let wc := join link2 seedC "Cy".toUTF8
  mine cdb wc
  let reqC := link2.request dC
  let jC := (wc.ops.getLast!).id
  mine cdb (stopWaiting jC)
  let waiting ← do
    let js ← rows cdb (joining.all.query [])
    js.filterMapM fun (_, f) => match f with
      | .joining _ _ _ r _ => do
        let ab ← (Lists.list (abandoned.byRequest.query [r] (limit := some 0)) : SqlM Fact (Answer Fact)).run cdb
        pure (if ab.total == 0 then some r else none)
      | _ => pure none
  t.ok "after stopping, C waits on nothing" waiting.isEmpty
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
  mine a ⟨[bad], []⟩
  t.ok "a secret with another key's seed is refused"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) bad.id).run a) == some .invalid)
  -- A name by a non-admin is refused.
  let byB := setName c wa.ops.getLast!.id wa.ops.getLast!.id [] 9 dB "B's name".toUTF8
  fromPeer a [byB]
  t.ok "a name by a non-admin is refused"
    ((← (Store.getStatus (F := Fact) (m := SqlM Fact) byB.id).run a) == some .invalid)
  t.finish "lifecycle"
