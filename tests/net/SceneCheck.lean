/-
The scene the laws are about, run on the real engine: the five ops
composed with real Ed25519 and SHA-256, received into SQLite in every
subset and in shuffled orders, and the running `allowPeer` and verdicts
checked against what the laws use (Net.Scene): the founder's node key
is let in exactly when the root is held, the joiner's exactly when all
five are,
and the request, approval and admission are Valid exactly when what
they cite is held. This also checks the scene's assumptions (`Good`)
for real keys: distinct ids, distinct devices and node keys, and
signatures that verify (else the ops would be Invalid).
-/
import ops.connection.bootstrap.Net
import tests.engine.Lib

open Engine Community Net Tests

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/scene"
  IO.FS.createDirAll dir
  let t ← Checks.new
  let x : Scene := ⟨Device.named "founder", Device.named "joiner", cryptoSeal.pub (sha256 "founder's node".toUTF8),
    cryptoSeal.pub (sha256 "joiner's node".toUTF8), sha256 "bearer seed".toUTF8⟩
  t.ok "the scene's link parses back from its text" (Invite.parse x.inviteLink.text == some x.inviteLink)
  let fam := family ed25519
  t.ok "the five ops have distinct ids" ((x.S.map (·.id)).eraseDups.length == 5)
  t.ok "founder and joiner are different devices" (x.A.pk.data != x.B.pk.data)
  t.ok "on different nodes" (x.kA.data != x.kB.data)
  let mut g := Rng.mk 17
  let mut n := 0
  for mask in [0:32] do
    let L := (List.range 5).filterMap fun k => if mask &&& (1 <<< k) != 0 then x.S[k]? else none
    let has (o : Op) := L.any fun p => p.id == o.id
    for round in [0:2] do
      let (order, g') := if round == 0 then (L.reverse, g) else g.shuffle L
      g := g'
      let path := s!"{dir}/m{mask}-{round}.db"
      for suffix in ["", "-wal", "-shm"] do
        if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
      let db ← Db.openAt path
      (receive fam order).run db
      let allowA ← ((allowPeer x.c x.kA).run : SqlM Fact Bool).run db
      let allowB ← ((allowPeer x.c x.kB).run : SqlM Fact Bool).run db
      let valid (o : Op) : IO Bool := do
        let a ← (Lists.list { key := opKey o.id, limit := some 1 } : SqlM Fact (Answer Fact)).run db
        return !a.rows.isEmpty
      let tag := s!"subset {mask} order {round}"
      t.ok s!"{tag}: founder let in iff the root is held" (allowA == has x.r)
      t.ok s!"{tag}: joiner let in iff all five are held" (allowB == x.S.all has)
      t.ok s!"{tag}: request valid iff it and its root and invitation are held"
        ((← valid x.req) == (has x.r && has x.inv && has x.req))
      t.ok s!"{tag}: approval valid iff it and what it cites are held"
        ((← valid x.appr) == (has x.r && has x.inv && has x.req && has x.appr))
      t.ok s!"{tag}: admission valid iff all five are held" ((← valid x.adm) == x.S.all has)
      t.ok s!"{tag}: nobody else is let in" (!(← ((allowPeer x.c x.K.pk).run : SqlM Fact Bool).run db) &&
        !(← ((allowPeer x.c x.A.pk).run : SqlM Fact Bool).run db))
      let dial ← ((members x.c).run : SqlM Fact (List Key)).run db
      t.ok s!"{tag}: dials exactly the admitted devices"
        (dial.length == [has x.r, x.S.all has].count true &&
          (dial.contains x.A.pk == has x.r) && (dial.contains x.B.pk == x.S.all has))
      n := n + 1
  IO.println s!"scene: {n} databases"
  t.finish "scene_check"
