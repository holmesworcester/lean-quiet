/-
The trusted statements of the proposed headline laws, for Comparator
(Lean v4.35's `lake comparator`): the challenge. Nothing here is final:
the user decides which laws are headline laws (docs/HEADLINE.md).

Each theorem restates one law of the app, word for word, under the name
`Headline.<law>`, with `sorry` for its proof; the `-- law` line above it
names the law. tests/comparator/solution.py writes from this file:
Solution.lean (the same statements, each proved by its law), Check.lean
(each statement is its law's own, `#same_statement`) and comparator.json.
Run, on Lean v4.35:

  lake comparator --config tests/comparator/comparator.json

These modules are the `Comparator` library, never a default target, so
`lake build` and `lake check` never see the `sorry`s. tests/headline.sh
checks them on every toolchain, and runs Comparator from v4.35 on.

A reviewer reads this file, and each definition the statements name
(docs/HEADLINE.md lists them: the spec-only and assumed parts).
-/
import app.Proofs
import app.community.Family
import app.community.Proofs
import app.community.member.Proofs
import app.community.member.invite.Proofs
import app.community.member.remove.Proofs
import app.community.member.remove.View
import app.connection.Proofs
import app.community.Screen
import app.community.channel.message.Proofs
import engine.core.IngestCost
import engine.core.Termination
import engine.renderer.Cover
import engine.sync.ConnLaws
import engine.wire.NoiseSymbolic

namespace Headline

/-! ## Who can do what -/

section
open Engine Engine.Codec Community

-- law Community.no_impersonation
/-- **Nobody can post as you.** If no signature in the store is forged,
a valid message from user u's device d was signed, as this exact op, by
the holder of d's key, and that holder also signed the op that admitted
d into u. -/
theorem no_impersonation {C : Community.Crypto} {ops : Id → Option Op}
    {Signed : Community.Key → ByteArray → Prop} (hU : Unforgeable C ops Signed)
    {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) :
    ∃ o s, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t n tm s) ∧
      Signed d (signed o (.post k t n tm s)) ∧
      ∃ y e z oz bz, V C ops y (.admission c u d e) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  sorry

-- law Community.admission_needs_approval
/-- **Nobody joins without a member's approval.** Every admission is the
founder's, or cites a valid request for that device and one valid
approval of it, by an admitted device other than the requester's. -/
theorem admission_needs_approval {C : Community.Crypto} {ops : Id → Option Op}
    (hk : Keyed ops) {y c u : Id} {d e : Community.Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r x a l da ea ra, ops y = some o ∧ o.reqs = [c, r, x] ∧ V C ops r (.request c u d e l) ∧
      V C ops x (.approval c r a) ∧ V C ops ra (.admission c a da ea) ∧ da ≠ d ∧
      (l = true → a = u) := by
  sorry

-- law Community.removal_authorized
/-- **Only admins remove others.** A valid removal of user t by user u
is a self-removal, or u is an admin. -/
theorem removal_authorized {C : Community.Crypto} {ops : Id → Option Op} {x c t u : Id}
    (h : V C ops x (.removal c t u)) : t = u ∨ IsAdmin C ops c u := by
  sorry

-- law Community.removed_stays
/-- **A removal cannot be undone.** More ops never restore a removed user. -/
theorem removed_stays {C : Community.Crypto} {ops ops' : Id → Option Op}
    (he : Extends ops ops') {c u : Id} (h : Removed C ops c u) : Removed C ops' c u := by
  sorry

-- law Community.connect_iff
/-- **The node connects to exactly the live members.** At rest, the trust
rule, read from the node's tables, accepts node key e for community c
exactly when a live device is admitted under e. -/
theorem connect_iff {s : DB Community.Fact} {C : Community.Crypto} (h : Inv (family C) s)
    (hq : s.queue = []) (c : Id) (e : Community.Key) :
    (allowPeer c e).eval s = true ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  sorry

end

section
open Engine Engine.Sync

-- law Connection.removal_reaches_session
/-- **A removal reaches a live session.** Whatever the node runs, every
frame it sends on a session whose peer the trust rule now refuses
carries, of that community, only sync messages and the removal's
notice. -/
theorem removal_reaches_session [Fresh (HeldM Connection.F)]
    (hfr : Reads (Fresh.fresh : HeldM Connection.F ByteArray))
    (x : Sync Connection.F (HeldM Connection.F)) (K : Connection.Keys) (listen : Connection.B)
    (hx : x.hooks = Connection.hooks x.fam K listen)
    (hc : ∀ cat, x.catalog = some cat → Reads cat.ceiling ∧ ∀ i, Reads (cat.read i))
    (hs : ∀ store, x.retryStore = some store →
      (∀ peer, Reads (store.load peer)) ∧ (∀ peer cursor, Reads (store.save peer cursor)))
    {E : Engine.Sync.Node → HeldM Connection.F (Engine.Sync.Node × Effects)} (hE : Entry x E)
    (n : Engine.Sync.Node) (h : Held Connection.F) :
    Moves x.fam h ((E n).run h).2 ∧
      FramesBy x (fun h' cid o => ∀ c, Connection.MayGo x.fam h' cid c o) h ((E n).run h).2
        ((E n).run h).1.2 := by
  sorry

/-! ## What leaves the device -/

-- law Engine.Sync.recv_send
/-- **A session sends only what its peer may see:** sync messages, and
ops of the rooms the connection is let into. A local op (a secret) is in
no room, so it is never sent. -/
theorem recv_send {F : Type} (fam : Family F) (cfg : Config) (ix : Index) (c : Conn)
    (bytes : ByteArray) (now : Nat) (s : DB F) :
    ∀ o ∈ ((Conn.recv fam cfg ix c bytes now : Model F Step).run s).1.send, Sendable fam c o := by
  sorry

-- law Connection.sealed_auth
/-- **Authenticate before parsing.** A sealed frame that does not pass
its AEAD check, under the receive key of the session it names, leaves the
node and its store as they were, and sends nothing. -/
theorem sealed_auth (x : Sync Connection.F (HeldM Connection.F)) {K : Connection.Keys}
    (hx : x.hooks.openFrame = Connection.openFrame K)
    (n : Engine.Sync.Node) (addr f : Connection.B) (now : Nat) (h : Held Connection.F)
    (hbad : ∀ cid sk rk, Connection.Frame.cid f = some cid →
      ((Connection.sessionKeys cid : HeldM Connection.F _) h).1 = some (sk, rk) →
      K.fdec rk (f.extract 33 57) (Connection.Frame.ad cid) (f.extract 57 f.size) = none) :
    n.onFrame x addr (tagged sealedTag f) now h = ((n, {}), h) := by
  sorry

end

/-! ## Sessions (in the symbolic model of the cryptography) -/

section
open Connection.Noise Connection.Noise.Symbolic

-- law Connection.Noise.Symbolic.kk_secret
/-- **Session keys are secret.** An active attacker that knows every
name but a session's four secrets (both static keys, both ephemerals)
derives neither side's keys, whatever honest calls it makes. -/
theorem kk_secret {O : T → T → Prop} {sI sR e f : Nat} {pro pro' m1 m2 m1' m2' re p1 p2 q1 q2 : T}
    {st st' : Sym T} {si sr : Session T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (h2 : read2 sym st (.atom sI) (.atom e) m2 = some (si, p2))
    (h3 : read1 sym pro' (.atom sR) (.pub (.atom sI)) m1' = some (st', re, q1))
    (h4 : write2 sym st' (.atom f) (.pub (.atom sI)) re q2 = some (sr, m2')) :
    ¬ Derivable O (Exposed (secrets sI sR e f)) si.send.k ∧
      ¬ Derivable O (Exposed (secrets sI sR e f)) si.recv.k ∧
      ¬ Derivable O (Exposed (secrets sI sR e f)) sr.send.k ∧
      ¬ Derivable O (Exposed (secrets sI sR e f)) sr.recv.k := by
  sorry

-- law Connection.Noise.Symbolic.kk_authentic
/-- **The dialer authenticates the peer it dialed.** Unless that peer
answered this request, the dialer accepts no reply the attacker can
make. -/
theorem kk_authentic {S : Nat → Prop} {O : T → T → Prop} {K : T → Prop}
    (hK : ∀ t, K t → Clean S t)
    (hK2 : ∀ t, K t → ∀ {k n ad p}, Part (.aead k n ad p) t → Clean S k)
    {sI sR e : Nat} (hR : S sR) (hIe : S sI ∨ S e) {pro m1 m2 p1 : T} {st : Sym T}
    (no_answer : ∀ q m, O q m → ¬ Answers sR m1 q m)
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (hm2 : Derivable O K m2) :
    read2 sym st (.atom sI) (.atom e) m2 = none := by
  sorry

end

/-! ## Agreement -/

-- law Engine.same_ops_same_verdicts
/-- **Same ops, any order, same verdicts.** Two nodes that received the
same ops, in any order or batches, both finish judging, and then hold
the same verdict for every op. -/
theorem same_ops_same_verdicts {F : Type} {fam : Engine.Family F} {L M : List Engine.Op}
    {s t : Engine.DB F} (hs : Engine.Reach fam L s) (ht : Engine.Reach fam M t)
    (hd : Engine.Distinct (L ++ M)) (hsame : ∀ o, o ∈ L ↔ o ∈ M) :
    ∃ n m, (Engine.drainS fam n s).queue = [] ∧ (Engine.drainS fam m t).queue = [] ∧
      (Engine.drainS fam n s).status = (Engine.drainS fam m t).status := by
  sorry

section
open Engine Community

-- law Community.display_agrees
/-- **Every device shows a channel in the same order.** Two devices that
hold the same two messages of channel c list them in the same order,
unless both messages claim the counter's cap (2^63) or more. -/
theorem display_agrees {C : Community.Crypto} {ops ops' : Id → Option Op} {c x y : Id}
    {sx sy sx' sy' : ByteArray}
    (hx : ops x = ops' x) (hy : ops y = ops' y)
    (lx : Listed C ops c x sx) (ly : Listed C ops c y sy) (lx' : Listed C ops' c x sx')
    (ly' : Listed C ops' c y sy')
    (hsat : (∃ n tm, Posted ops x n tm ∧ n < countCap) ∨ ∃ n tm, Posted ops y n tm ∧ n < countCap) :
    Pos.cmp (sx, x) (sy, y) = Pos.cmp (sx', x) (sy', y) := by
  sorry

end

/-! ## What the user sees and does -/

-- law Cover.covered
/-- **Scrolling never shows a blank.** Every position in the content,
from the bottom padding up to the last loaded row, and above it while
older messages are still to load, shows a line of a message or a
placeholder. -/
theorem covered (pad bottom : Nat) (more : Bool) (rows : List (Nat × Option Nat)) (p : Nat)
    (lo : pad ≤ p) (hi : p < bottom + (rows.map (·.1)).sum ∨ more = true) :
    Cover.seen pad bottom more rows p ≠ .blank := by
  sorry

-- law NavLaws.back_open
/-- **Back goes back.** Back after opening a page restores the app's
state from before it, except for a few fields that belong to the page
that closed, an editor counter, and the record of the two navigation
steps. -/
theorem back_open (p : App.PageId) (s : App.St) (hp : p ≠ s.page) (hs : p ∉ s.backStack)
    (hw : p ≠ .switcher) :
    App.backSt (App.openSt p s) = { s with
      editorEpoch := s.editorEpoch + 1 + 1, field := "", refusal := none, pageKey := none,
      pageScrollStarted := false, ownSends := {}, presenting := none,
      eph := Data.placeIn (Data.placeIn s.eph (s.navGen + 1) p.code
          ((Nav.go p s.nav).stack.map App.PageId.code))
        (s.navGen + 1 + 1) s.page.code (s.backStack.map App.PageId.code),
      navGen := s.navGen + 1 + 1 } := by
  sorry

-- law Switch.select_tapped_dedupe
/-- **A tap on a community opens that community.** Selecting the
switcher entry at row i, by its account, gives back exactly that entry,
even when two communities share a name. -/
theorem select_tapped_dedupe (ms : Array Kinds.Accepted.Me) (i : Nat)
    (hi : i < (Kinds.Accepted.dedupe ms).size) :
    Kinds.Accepted.select (Kinds.Accepted.dedupe ms) (Kinds.Accepted.dedupe ms)[i].acc =
      some (Kinds.Accepted.dedupe ms)[i] := by
  sorry

/-! ## What it costs -/

-- law Community.approveReq_ops
/-- **Letting someone in costs at most three ops, whatever the community
holds:** the approval, the admission, and one wrap of the content key,
to the new member's node. -/
theorem approveReq_ops (c req myAdm : Engine.Id) (d : Community.Device) (esk : ByteArray) :
    Engine.View.Always (fun w : Community.Write => w.ops.length ≤ 3)
      (Community.approveReq c req myAdm d esk) := by
  sorry

-- law Engine.ingest_costs
/-- **Storing an op that arrives costs one read and at most two writes**,
whatever the store holds, on any store the app's code runs on. -/
theorem ingest_costs {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Engine.Store F m]
    (o : Engine.Op) :
    Engine.Costs { reads := 1, writes := 2, seeks := 3 } (Engine.ingest (F := F) (m := Engine.CostT m) o) := by
  sorry

/-! ## What the app tells the user -/

section
open Engine Community

-- law PeopleLaws.deviceCut_removal
/-- **"You've been removed" comes only from a removal.** When the app
marks this device cut from c, the store holds one of the device's
admissions into c and a removal of that admission's user. -/
theorem deviceCut_removal (s : DB Fact) (c : Id) (d : Key)
    (h : (deviceCut c d).eval s = true) :
    ∃ p u d' e, (p, Fact.admission c u d' e) ∈ ((admission.byDevice.read [c, d]).eval s).rows ∧
      (Engine.eval s (removals c u)).total ≠ 0 := by
  sorry

end

end Headline
