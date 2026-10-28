/-
The bootstrap scene: founder A creates community c and invites B with a
member invitation that needs one approval; B pastes the link. The ops
are the real ones, composed by lean-engine's `Community.Compose` (op
ids are SHA-256, signatures Ed25519 through `edSign`), and judged by
the real validators. What is assumed is stated in `Good`: the
signature scheme verifies what the three key pairs sign, A and B are
different devices, and the five ops' ids are distinct (SHA-256 does not
collide on them).

Then: among any of these ops a node may hold, what is Valid, who is
admitted, and that nobody is removed. These are what the protocol's
decisions come down to in this scene.
-/
import ops.connection.bootstrap.System

namespace Net
open Engine Community Codec

structure Scene where
  /-- The founder's device; also its dial key. -/
  A : Device
  /-- The joiner's device. -/
  B : Device
  /-- The bearer seed the invitation's key pair derives from; it is in
  the link. -/
  secret : ByteArray

namespace Scene
variable (x : Scene)

def r : Op := root x.A
def c : Id := x.r.id
/-- The invitation and its link, as A's app issues them (Community.issue). -/
def issued : Op × Invite := issue x.c x.c x.A x.secret []
def inv : Op := x.issued.1
def inviteLink : Invite := x.issued.2
/-- The bearer key pair, from the link's seed. -/
def K : Device := x.inviteLink.bearer
/-- B's request, as B's app composes it from the link it parsed
(`parse_text`: the text parses back to `inviteLink`). -/
def req : Op := x.inviteLink.request x.B
def appr : Op := approve x.c x.req.id x.c x.A
def adm : Op := admit x.c x.req.id [x.appr.id]
def S : List Op := [x.r, x.inv, x.req, x.appr, x.adm]

/-- B's link: community, A's device to dial, B's request. -/
def link : Link := ⟨x.c, x.A.pk, x.req⟩

/-- A after founding and inviting; B after pasting the link. -/
def a0 : Node := ⟨x.A.pk, [x.r, x.inv], [x.c], [], []⟩
def b0 : Node := ⟨x.B.pk, [x.req], [x.c], [x.link], []⟩
def init : Sys := ⟨x.a0, x.b0, []⟩

/-- What A's user does on approving B's request, once A holds it: A signs
the approval and composes the admission. -/
def approval (n : Node) : Node :=
  if n.ops.any (fun o => decide (o = x.req)) then { n with ops := add n.ops [x.appr, x.adm] } else n

/-- The assumptions. -/
structure Good (C : Crypto) : Prop where
  sigA : ∀ m, C.verify x.A.pk m (edSign x.A.sk m) = true
  sigB : ∀ m, C.verify x.B.pk m (edSign x.B.sk m) = true
  sigK : ∀ m, C.verify x.K.pk m (edSign x.K.sk m) = true
  AB : x.A.pk ≠ x.B.pk
  distinct : Distinct x.S

end Scene

/-! ## The op table -/

theorem table_some {L : List Op} {i : Id} {o : Op} (h : table L i = some o) : o ∈ L ∧ o.id = i := by
  unfold table at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  exact of_decide_eq_true this

theorem table_of {L : List Op} (hd : Distinct L) {o : Op} (h : o ∈ L) : table L o.id = some o := by
  unfold table
  cases hf : L.find? (fun p => decide (p.id = o.id)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf o h)
  | some o' =>
    have := table_some hf
    rw [hd o' this.1 o h this.2]

theorem table_keyed (L : List Op) : Keyed (table L) := fun _ _ h => (table_some h).2

theorem distinct_sub {L M : List Op} (hd : Distinct M) (h : ∀ o ∈ L, o ∈ M) : Distinct L :=
  fun a ha b hb => hd a (h a ha) b (h b hb)

namespace Scene
variable {x : Scene} {C : Crypto}

theorem body_mk (reqs : List Id) (b : Body) : (decode (mkOp reqs b).body : Option Body) = some b :=
  decode_encode b

theorem c_eq : x.c = x.r.id := rfl

section
variable {L : List Op} (g : x.Good C) (hL : ∀ o ∈ L, o ∈ x.S)
include g hL

theorem hd : Distinct L := distinct_sub g.distinct hL

theorem v_root (h : x.r ∈ L) : V C (table L) x.c (.admission x.c x.c x.A.pk x.A.enc) := by
  refine spec_valid_of (table_of (hd g hL) h) (fs := []) .nil ?_
  show validate C x.r [] = _
  unfold validate
  rw [show x.r = root x.A from rfl, root, body_mk]
  simp only [Body.tag, Op.make_kind, ↓reduceIte, check]
  rw [if_pos]
  · rfl
  · exact g.sigA _

theorem v_inv (h1 : x.r ∈ L) (h2 : x.inv ∈ L) :
    V C (table L) x.inv.id (.invitation x.c x.c x.K.pk false 1) := by
  refine spec_valid_of (table_of (hd g hL) h2)
    (fs := [.admission x.c x.c x.A.pk x.A.enc, .admission x.c x.c x.A.pk x.A.enc]) ?_ ?_
  · exact .cons (v_root g hL h1) (.cons (v_root g hL h1) .nil)
  · show validate C x.inv _ = _
    unfold validate
    rw [show x.inv = invite x.c x.c x.A x.K.pk false 1 from rfl, invite, body_mk]
    simp only [mkOp, Body.tag, Op.make_kind, ↓reduceIte, check]
    rw [if_pos]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | decide | exact g.sigA _ | simp

theorem v_req (h1 : x.r ∈ L) (h2 : x.inv ∈ L) (h3 : x.req ∈ L) :
    V C (table L) x.req.id (.request x.c x.req.id x.B.pk x.B.enc false 1) := by
  have := request_valid (C := C) (table_keyed L) (table_of (hd g hL) h3)
    (body_mk _ _) rfl rfl (v_root g hL h1) (v_inv g hL h1 h2) (g.sigB _) (g.sigK _)
  have e : x.inviteLink.community = x.c := rfl
  simpa [e] using this

theorem v_appr (h1 : x.r ∈ L) (h2 : x.inv ∈ L) (h3 : x.req ∈ L) (h4 : x.appr ∈ L) :
    V C (table L) x.appr.id (.approval x.c x.req.id x.c) :=
  approve_valid (table_of (hd g hL) h4) (body_mk _ _) rfl rfl (v_root g hL h1)
    (v_req g hL h1 h2 h3) (v_root g hL h1) (fun h => absurd h (by simp)) g.AB (g.sigA _)

theorem v_adm (h : ∀ o ∈ x.S, o ∈ L) :
    V C (table L) x.adm.id (.admission x.c x.req.id x.B.pk x.B.enc) := by
  have h1 := h x.r (by simp [S]); have h2 := h x.inv (by simp [S])
  have h3 := h x.req (by simp [S]); have h4 := h x.appr (by simp [S])
  have h5 := h x.adm (by simp [S])
  exact admit_admits (us := [x.c]) (table_of (hd g hL) h5) (body_mk _ _) rfl rfl (v_root g hL h1)
    (v_req g hL h1 h2 h3) (.cons (v_appr g hL h1 h2 h3 h4) .nil) (by simp) rfl

omit g in
/-- The op stored under an id among these is that one of the scene's. -/
theorem table_S {i : Id} {o : Op} (h : table L i = some o) : o ∈ x.S ∧ o ∈ L ∧ o.id = i :=
  ⟨hL o (table_some h).1, table_some h⟩

/-- **Who is admitted among these ops**: A, by the root; B, by the admit. -/
theorem admitted_inv {c' u : Id} {d e : Key} (h : Admitted C (table L) c' u d e) :
    (d = x.A.pk ∧ x.r ∈ L) ∨ (d = x.B.pk ∧ x.adm ∈ L) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv hy
  obtain ⟨hS, hoL, _⟩ := table_S hL hx
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · rw [show x.r = root x.A from rfl, root, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩
    · cases hb; exact Or.inl ⟨rfl, hoL⟩
    · cases hb
  · rw [show x.inv = invite x.c x.c x.A x.K.pk false 1 from rfl, invite, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ <;> cases hb
  · rw [show x.req = request x.c x.inv.id x.B x.K.sk from rfl, request, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ <;> cases hb
  · rw [show x.appr = approve x.c x.req.id x.c x.A from rfl, approve, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ <;> cases hb
  · rcases check_admission hv with ⟨s, hb', _⟩ | ⟨d0, e0, l, t, aps, _, rfl, _⟩
    · rw [show x.adm = admit x.c x.req.id [x.appr.id] from rfl, admit, body_mk] at hb
      rw [hb'] at hb; cases hb
    · obtain ⟨_, ri, _, hreq, _, hri, _⟩ := all2_cons2 hr
      have hri' : ri = x.req.id := by
        have : x.adm.reqs = x.c :: x.req.id :: [x.appr.id] := rfl
        rw [this] at hreq; simp at hreq; exact hreq.2.1.symm
      subst hri'
      obtain ⟨o', b', fs', hx', hb', _, hv'⟩ := valid_inv hri
      obtain ⟨hS', ho'L, hid'⟩ := table_S hL hx'
      have : o' = x.req := g.distinct o' hS' x.req (by simp [S]) hid'
      subst this
      rw [show x.req = request x.c x.inv.id x.B x.K.sk from rfl, request, body_mk] at hb'
      cases hb'
      obtain ⟨_, _, _, _, _, _, hb'', _⟩ := check_request hv'
      cases hb''
      exact Or.inr ⟨rfl, hoL⟩

omit g in
/-- **Nobody is removed** among these ops: none is a removal. -/
theorem not_removed {c' u : Id} : ¬ Removed C (table L) c' u := by
  rintro ⟨y, rr, hy⟩
  obtain ⟨o, b, fs, hx, hb, _, hv⟩ := valid_inv hy
  obtain ⟨hS, _, _⟩ := table_S hL hx
  obtain ⟨s, _, _, _, _, _, _, _, hb', _⟩ := check_removal hv
  subst hb'
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · rw [show x.r = root x.A from rfl, root, body_mk] at hb; cases hb
  · rw [show x.inv = invite x.c x.c x.A x.K.pk false 1 from rfl, invite, body_mk] at hb; cases hb
  · rw [show x.req = request x.c x.inv.id x.B x.K.sk from rfl, request, body_mk] at hb; cases hb
  · rw [show x.appr = approve x.c x.req.id x.c x.A from rfl, approve, body_mk] at hb; cases hb
  · rw [show x.adm = admit x.c x.req.id [x.appr.id] from rfl, admit, body_mk] at hb; cases hb

/-- A is known, and allowed, exactly when the root is held. -/
theorem knownA : Known C L x.c x.A.pk ↔ x.r ∈ L := by
  constructor
  · rintro ⟨u, e, h⟩
    rcases admitted_inv g hL h with ⟨_, h⟩ | ⟨hAB, _⟩
    · exact h
    · exact absurd hAB g.AB
  · intro h; exact ⟨_, _, _, v_root g hL h⟩

theorem allowedA : Allowed C L x.c x.A.pk ↔ x.r ∈ L := by
  constructor
  · rintro ⟨u, e, h, _⟩; exact (knownA g hL).1 ⟨u, e, h⟩
  · intro h; exact ⟨_, _, ⟨_, v_root g hL h⟩, not_removed hL⟩

/-- B is known exactly when its admission is held. -/
theorem knownB : Known C L x.c x.B.pk → x.adm ∈ L := by
  rintro ⟨u, e, h⟩
  rcases admitted_inv g hL h with ⟨hAB, _⟩ | ⟨_, h⟩
  · exact absurd hAB.symm g.AB
  · exact h

/-- B is allowed exactly when its admission is held (with what it cites). -/
theorem allowedB (hall : x.adm ∈ L → ∀ o ∈ x.S, o ∈ L) :
    Allowed C L x.c x.B.pk ↔ x.adm ∈ L := by
  constructor
  · rintro ⟨u, e, h, _⟩; exact knownB g hL ⟨u, e, h⟩
  · intro h; exact ⟨_, _, ⟨_, v_adm g hL (hall h)⟩, not_removed hL⟩

end

end Scene

end Net
