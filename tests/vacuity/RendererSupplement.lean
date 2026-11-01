import tests.vacuity.IdentityMessages
import ops.community.Screen
import ops.community.profile.View
import ops.community.member.invite.View
import engine.core.View

set_option linter.defProp false
namespace Vacuity.RendererSupplement
open Engine Community Data Tests Kinds Vacuity.Identity Vacuity.IdentityTrust

-- Nonempty interface list: loopback/public filtered, Wi-Fi ranked first.
def addresses : List (String × List Nat × Bool) :=
  [("eth0", [10, 0, 0, 4], false), ("wlan0", [192, 168, 1, 12], false),
   ("lo", [127, 0, 0, 1], true), ("public", [8, 8, 8, 8], false)]
def hints := Link.hints_fit addresses 47100
def qr := Link.qr_fits 41 256 (by decide +kernel)
example : Link.scale 41 256 = 5 := by decide +kernel
example : ¬ 41 + 8 ≤ (40 : Nat) := by decide +kernel

-- Actual inhabited signed DB from the identity message fixture.
def db := run Vacuity.IdentityMessages.scene
def nextOp := post c admission.id bob "content-key-1".toUTF8 "A pending later message".toUTF8 3 29880002
private theorem later : Later (family ed25519) db (ingestS nextOp db) :=
  .ingest nextOp (.refl db)
private theorem sameIndex (k : ByteArray) : (ingestS nextOp db).idx k = db.idx k := by
  unfold ingestS
  split <;> rfl

def stableList := eval_stable (runInv Vacuity.IdentityMessages.scene) later
  (q := message.byKey.query [c, Vacuity.IdentityMessages.kid]) (sameIndex _)
def stableView := view_stable (runInv Vacuity.IdentityMessages.scene) later
  (Profile.present c) (fun k _hk => sameIndex k)
def uniqueRows := matching_nodup (runInv Vacuity.IdentityMessages.scene)
  (message.byKey.query [c, Vacuity.IdentityMessages.kid])
def namedKeys := mem_keysOf rels_distinct (r := message.byKey) (by simp [rels])
  (as := [c, Vacuity.IdentityMessages.kid]) (f := Vacuity.IdentityMessages.fact1)

def filedRelation := if hq : db.queue = [] then
  some (PLift.up (filed_rel (fam := family ed25519) rfl rels_distinct
    (r := message.byKey) (by simp [rels]) (rels_short _ (by simp [rels]))
    (runInv Vacuity.IdentityMessages.scene) hq [c, Vacuity.IdentityMessages.kid]
    Vacuity.IdentityMessages.post1.id Vacuity.IdentityMessages.fact1))
  else none

-- Two real admitted identities choose visually identical profile labels.
def aliceLabel := profile c c alice "Bob".toUTF8 29880003
def twinScene := Vacuity.IdentityMessages.scene ++ [aliceLabel]
def twins := run twinScene

def namesake := if hq : twins.queue = [] then
  some (PLift.up (ViewLaws.namesake_iff (runInv twinScene) hq c requestB.id #[])) else none

def RowMarked (d : Row.RowData) : Prop :=
  ∃ c' u dev kid sealed n tm clump,
    ViewLaws.factIn twins Vacuity.IdentityMessages.post1.id = some (.message c' u dev kid sealed n tm clump) ∧
    (d.namesake = true ↔ ∃ u', u' ≠ u ∧
      (∃ y n tm, V ed25519 twins.ops y (.profile c u' n tm)) ∧
      nameLook (ViewLaws.nameIn twins c u') = nameLook (ViewLaws.nameIn twins c u))

def marked : Option (Σ d : Row.RowData, PLift (RowMarked d)) :=
  if hq : twins.queue = [] then
    match hr : (Message.read (m := ViewLaws.Model) c c Vacuity.IdentityMessages.post1.id).run twins with
    | none => none
    | some (d, deps) => some ⟨d, ⟨ViewLaws.row_marked (runInv twinScene) hq
        (c := c) (me := c) (msg := Vacuity.IdentityMessages.post1.id) (d := d) (deps := deps) hr⟩⟩
  else none

-- These bytes are all held by a node's own input job (including receipts).
def capPost := sealedPost c admission.id bob Vacuity.IdentityMessages.content
  Vacuity.IdentityMessages.nonce "Saturated post".toUTF8 countCap 29880004
def capReceipt := receipt capPost.id 5
def capNext := sealedPost c admission.id bob Vacuity.IdentityMessages.content
  Vacuity.IdentityMessages.nonce "Next saturated post".toUTF8 countCap 29880005
def orderScene := twinScene ++ [capPost, capReceipt]
def orderDB := run orderScene

def counterSmall : Fact → Bool
  | .received _ _ _ j _ => decide (j + 1 < 2 ^ 64)
  | _ => true

theorem receiptBounds (hq : orderDB.queue = [])
    (good : ((received.all.read [c]).eval orderDB).rows.all (fun p => counterSmall p.2) = true)
    (z : Id) (kid m : ByteArray) (j : Nat) (clump : Option Id)
    (hv : V ed25519 orderDB.ops z (.received c kid m j clump)) : j + 1 < 2 ^ 64 := by
  have hm := at_row (C := ed25519) (r := received.all) (by simp [rels])
    (runInv orderScene) hq (desc := true) hv (show received.all.args (.received c kid m j clump) = some [c] from rfl)
  have hgood := List.all_eq_true.1 good _ hm
  exact of_decide_eq_true hgood

def receiptOnce := do
  let ⟨hv⟩ ← certifyDB orderScene capReceipt
    (.received c Vacuity.IdentityMessages.kid capPost.id 5 none)
  if hq : orderDB.queue = [] then
    return PLift.up (receipt_once (runInv orderScene) hq (o := capPost) hv)
  else none

def arrival := if hq : orderDB.queue = [] then
  if good : ((received.all.read [c]).eval orderDB).rows.all (fun p => counterSmall p.2) = true then
    if hr : (receipt capNext.id 6) ∈ (receiptFor capNext).eval orderDB then
      some (PLift.up (arrival_order (runInv orderScene) hq capNext
        (by
          have hc : capNext.reqs.headD .empty = c := by rfl
          rw [hc]
          exact receiptBounds hq good) hr))
    else none
  else none
else none

def sendAfter := if hq : orderDB.queue = [] then
  if good : ((received.all.read [c]).eval orderDB).rows.all (fun p => counterSmall p.2) = true then
    some (PLift.up (send_after (runInv orderScene) hq c admission.id bob
      Vacuity.IdentityMessages.content Vacuity.IdentityMessages.nonce "A message after the cap".toUTF8
      29880006 [] (receiptBounds hq good)))
  else none
else none

def fedLoad : DB Fact := (intake (family ed25519) true orderScene).foldl (fun s o => ingestS o s) DB.empty

theorem fedDrain {M : List Op} {s : DB Fact} (h : Fed (family ed25519) M s) (n : Nat) :
    Fed (family ed25519) M (drainS (family ed25519) n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    unfold drainS; split
    · exact Fed.step h
    · exact ih (Fed.step h)

def fedDB := drainS (family ed25519) 400 fedLoad
private theorem fed : Fed (family ed25519) orderScene fedDB :=
  fedDrain (Fed.job true orderScene Fed.empty) 400

def localOrder :=
  if hv : specAt (family ed25519) fedDB.ops 8 capReceipt.id =
      some (.valid (.received c Vacuity.IdentityMessages.kid capPost.id 5 none)) then
    some (PLift.up (order_local fed (c := c) (x := capPost.id) (sk := recKey 5 capPost.id)
      (Or.inr ⟨capReceipt.id, Vacuity.IdentityMessages.kid, 5, none, ⟨8, hv⟩, rfl⟩)))
  else none

def displayAgreement := do
  let scene := Vacuity.IdentityMessages.scene
  let x := Vacuity.IdentityMessages.post1
  let y := Vacuity.IdentityMessages.post2
  let ⟨hxv⟩ ← certify scene x Vacuity.IdentityMessages.fact1
  let ⟨hyv⟩ ← certify scene y Vacuity.IdentityMessages.fact2
  let ⟨hxv'⟩ ← certify scene.reverse x Vacuity.IdentityMessages.fact1
  let ⟨hyv'⟩ ← certify scene.reverse y Vacuity.IdentityMessages.fact2
  if hx : table scene x.id = table scene.reverse x.id then
    if hy : table scene y.id = table scene.reverse y.id then
      return PLift.up (display_agrees hx hy
        (Or.inl ⟨_, _, _, _, 1, 29880000, none, hxv, by decide +kernel, rfl⟩)
        (Or.inl ⟨_, _, _, _, 2, 1, none, hyv, by decide +kernel, rfl⟩)
        (Or.inl ⟨_, _, _, _, 1, 29880000, none, hxv', by decide +kernel, rfl⟩)
        (Or.inl ⟨_, _, _, _, 2, 1, none, hyv', by decide +kernel, rfl⟩)
        (Or.inl ⟨1, 29880000, (by
          obtain ⟨o, sig, _, _, ho, hb, _⟩ := message_authorized hxv
          exact ⟨o, _, _, sig, ho, hb⟩), by decide +kernel⟩))
    else none
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  let actualHints := (Link.hints addresses 47100).map String.fromUTF8!
  t.ok "actual nonempty hints are private, Wi-Fi first, with loopback/public excluded"
    (actualHints == ["192.168.1.12:47100", "10.0.0.4:47100"])
  t.ok "actual message relation is filed" filedRelation.isSome
  t.ok "nonempty relation still has two actual sealed messages"
    ((matching db (message.byKey.query [c, Vacuity.IdentityMessages.kid])).length == 2)
  t.ok "a new unjudged op is actually queued"
    ((ingestS nextOp db).queue.contains nextOp.id && db.ops nextOp.id == none)
  t.ok "pending intake leaves the actual message query equal"
    (eval (ingestS nextOp db) (message.byKey.query [c, Vacuity.IdentityMessages.kid]) ==
      eval db (message.byKey.query [c, Vacuity.IdentityMessages.kid]))
  t.ok "nonempty same-label community satisfies namesake theorem premises" namesake.isSome
  t.ok "actual Bob message row is marked after Alice takes Bob's label"
    (marked.any fun v => v.1.namesake)
  t.ok "before the duplicate profile arrives, Bob has no namesake"
    (!(((Profile.namesake (m := ViewLaws.Model) c requestB.id "Bob" #[]).run db).1))
  t.ok "existing saturated post has exactly one receipt, so writes none" receiptOnce.isSome
  t.ok "new saturated post receives a strictly later receipt" arrival.isSome
  t.ok "send_after applies with a real existing receipt and bounded counter" sendAfter.isSome
  t.ok "receipt belongs to this device's own actual fed input job" localOrder.isSome
  t.ok "reversing real signed message storage preserves displayed order" displayAgreement.isSome
  t.ok "bound premise covers one actual nonempty receipt row"
    (((received.all.read [c]).eval orderDB).rows.length == 1)
  t.ok "arrival writes exactly the next counter" ((receiptFor capNext).eval orderDB == [receipt capNext.id 6])
  t.ok "duplicate receipt produces no additional op" ((receiptFor capPost).eval orderDB).isEmpty
  let result := (send c admission.id bob Vacuity.IdentityMessages.content Vacuity.IdentityMessages.nonce
    "A message after the cap".toUTF8 29880006 []).eval orderDB
  t.ok "send_after fixture exercises the saturated branch and adds a receipt"
    (result.ops.length == 2 && result.ops.any fun o => o.kind == 24)
  return ← t.finish "supplemental vacuity (signed receipts, duplicate names, lists and invites)"

end Vacuity.RendererSupplement
