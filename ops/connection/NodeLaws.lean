/-
The Community laws in the running node.

The node's one family is Community and Connection composed
(`Connection.node`), so its store holds both families' ops. Its
Community part (`community`, `Engine.DB.proj`) is a store of the
Community family alone: the Community ops it holds, with Community's
own verdicts over them. The trust rule, members and recipients read
only Community relations (`reads_allowPeer`, `reads_members`,
`reads_recipients`), none of which shares a name with a Connection
relation (`rels_apart`). So at rest:

- `sum_project_node`: the Community part keeps Community's invariant,
  holds exactly the node's Community ops, and is Valid exactly where
  the node is; every Community view that reads only Community relations
  answers, lifted, as it does on the Community part (`Engine.sum_project`).
- `connect_iff_node`, `refuse_nonmember_node`, `removal_cuts_off_node`,
  `members_iff_node`, `recipients_iff_node`: Community.Connect's laws
  (over node keys and live devices, as removal states them), read from
  the node's own tables. Admitted and Removed among its
  Community ops are its own Valid verdicts (`admitted_node`,
  `removed_node`).
- `rooms_cut_node`: a node let into c carries no sync room of c on a
  connection to a peer whose devices' users were removed (`rooms_cut`,
  with the removal itself in place of the refusal).
- `node_settles`: the premises hold. Every state the running engine
  reaches keeps `Inv`, and judging brings it to rest.
-/
import ops.connection.RoomLaws
import engine.core.Project

namespace Community
open Engine

/-! ## Community's views read only Community relations -/

theorem reads_unremoved (c : Id) (rows : List (Pos × Fact)) : (unremoved c rows).Reads (RelKey rels) := by
  induction rows with
  | nil => exact .pure _
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | admission c' u d e =>
      show View.Reads _ (if c' = c then _ else _)
      split
      · exact .list ⟨removal.byUser, by simp [rels], [c, u], rfl⟩ fun a => by
          show View.Reads _ (if a.total = 0 then _ else _)
          split
          · exact ih
          · exact .pure _
      · exact ih
    | _ => exact ih

theorem reads_deviceLive (c : Id) (d : Key) : (deviceLive c d).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.byDevice, by simp [rels], [c, d], rfl⟩).bind fun a => by
    show View.Reads _ (if a.rows.isEmpty then _ else _)
    split
    · exact .pure _
    · exact reads_unremoved c a.rows

theorem reads_live (c : Id) (rows : List (Pos × Fact)) : (live c rows).Reads (RelKey rels) := by
  induction rows with
  | nil => exact .pure _
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | admission c' u d e =>
      show View.Reads _ (if c' = c then _ else _)
      split
      · exact (reads_deviceLive c d).bind fun _ => ih.bind fun _ => .pure _
      · exact ih
    | _ => exact ih

theorem reads_allowPeer (c : Id) (e : Key) : (allowPeer c e).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.byKey, by simp [rels], [c, e], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _

theorem reads_members (c : Id) : (members c).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.all, by simp [rels], [c], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _

theorem reads_recipients (c : Id) : (recipients c).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.all, by simp [rels], [c], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _

end Community

namespace Connection
open Engine

/-! ## The Community part -/

/-- The node's Community part: the Community ops its store holds, with
Community's own verdicts over them (`Engine.DB.proj`). -/
noncomputable abbrev community (C : Community.Crypto) (s : DB F) : DB Community.Fact :=
  s.proj (Community.family C) owns

/-- No Community relation shares its names with a Connection relation. -/
theorem rels_apart : ∀ r ∈ Community.rels, ∀ r' ∈ rels, ¬ (r'.kind = r.kind ∧ r'.name = r.name) := by
  decide

/-! ## The projection -/

variable {C : Community.Crypto} {K : Keys} {s : DB F}

/-- **`sum_project` for the running node.** At rest, the node's
Community part keeps Community's invariant and is at rest. It holds
exactly the node's Community ops (kinds Connection does not own), and an
op is Valid there with a Community fact exactly when it is in the node.
Every Community view reading only Community relations answers, lifted to
the node's store, as it does on the Community part. -/
theorem sum_project_node (h : Inv (node C K) s) (hq : s.queue = []) :
    Inv (Community.family C) (community C s) ∧ (community C s).queue = [] ∧
      (∀ x o, (community C s).ops x = some o ↔ s.ops x = some o ∧ owns o.kind = false) ∧
      (∀ x f, Community.V C (community C s).ops x f ↔ s.status x = some (.valid (.inl f))) ∧
      ∀ {α : Type} (v : View Community.Fact α), v.Reads (RelKey Community.rels) →
        (v.liftL : View F α).eval s = v.eval (community C s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sum_project (b := family K) h hq
  exact ⟨h1, h2, h3, h4, fun v hv =>
    h5 v (hv.mono fun _ => leftKey_rels h rfl Community.rels_short rels_apart)⟩

theorem community_inv (h : Inv (node C K) s) (hq : s.queue = []) :
    Inv (Community.family C) (community C s) :=
  (sum_project_node h hq).1

theorem view_node (h : Inv (node C K) s) (hq : s.queue = []) {α : Type}
    {v : View Community.Fact α} (hv : v.Reads (RelKey Community.rels)) :
    (v.liftL : View F α).eval s = v.eval (community C s) :=
  (sum_project_node h hq).2.2.2.2 v hv

/-! ## The Community laws, in the node -/

open Community (Admitted Removed)

/-- Admitted among the node's Community ops: by a Valid admission in the
node's own verdicts. -/
theorem admitted_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id} {d e : Community.Key} :
    Admitted C (community C s).ops c u d e ↔ ∃ x, s.status x = some (.valid (.inl (.admission c u d e))) :=
  exists_congr fun x => (sum_project_node h hq).2.2.2.1 x _

/-- Removed among the node's Community ops: by a Valid removal in the
node's own verdicts. -/
theorem removed_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id} :
    Removed C (community C s).ops c u ↔ ∃ x r, s.status x = some (.valid (.inl (.removal c u r))) :=
  exists_congr fun x => exists_congr fun _ => (sum_project_node h hq).2.2.2.1 x _

/-- **Which nodes the node lets in.** At rest, the node's `allowPeer`
accepts node key e for c exactly when a device admitted under e is live
(admitted, into no removed user) among the Community ops it holds. -/
theorem connect_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key) :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = true ↔
      ∃ u d, Admitted C (community C s).ops c u d e ∧ Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.connect_iff (community_inv h hq) hq c e

/-- **The node lets in no node whose devices are all cut.** -/
theorem refuse_nonmember_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key)
    (hd : ∀ u d, Admitted C (community C s).ops c u d e → Community.Cut C (community C s).ops c d) :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = false := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.refuse_nonmember (community_inv h hq) hq c e hd

/-- **A removal, once the node holds it, cuts the removed user's
devices' node out of its trust rule.** -/
theorem removal_cuts_off_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id}
    {e : Community.Key} (hr : Removed C (community C s).ops c u)
    (only : ∀ u' d, Admitted C (community C s).ops c u' d e → ∃ e', Admitted C (community C s).ops c u d e') :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = false := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.removal_cuts_off (community_inv h hq) hq hr only

/-- **Whom the node dials:** the live devices. -/
theorem members_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (d : Community.Key) :
    d ∈ ((Community.members c).liftL : View F (List Community.Key)).eval s ↔
      Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_members c)]
  exact Community.members_iff (community_inv h hq) hq c d

/-- **Who the node seals a content key to:** the node keys of live
devices. -/
theorem recipients_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key) :
    e ∈ ((Community.recipients c).liftL : View F (List Community.Key)).eval s ↔
      ∃ u d, Admitted C (community C s).ops c u d e ∧ Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_recipients c)]
  exact Community.recipients_iff (community_inv h hq) hq c e

/-- **A removal ends a live session's sync, in the running node.** At
rest, if this node is let into c (a device admitted under its key is
live), and each peer connection cid's established facts name in c has
only devices admitted into a removed user u, then cid carries no sync
room of c: no step of it sends an op of c or takes one (`recv_send`,
`recv_take`). -/
theorem rooms_cut_node (h : Inv (node C K) s) (hq : s.queue = []) {cid c : Id}
    (hme : ∀ me, (meV c).eval s = some me →
      ∃ u d, Admitted C (community C s).ops c u d me ∧ Community.Live C (community C s).ops c d)
    (hpeer : ∀ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])),
      ∃ u, Removed C (community C s).ops c u ∧
        ∀ u' d, Admitted C (community C s).ops c u' d peer → ∃ e', Admitted C (community C s).ops c u d e') :
    Engine.Sync.Room.sync c ∉ (roomsV cid).eval s :=
  rooms_cut s (fun me hm => (connect_iff_node h hq c me).2 (hme me hm)) fun peer hp =>
    let ⟨_, hr, only⟩ := hpeer peer hp
    removal_cuts_off_node h hq hr only

/-! ## The premises hold -/

/-- **Every state the running node reaches settles where these laws
apply:** it keeps `Inv` (`reach_inv`), and judging empties its queue
(`drain_terminates`). -/
theorem node_settles {L : List Op} (hd : Distinct L) (hr : Reach (node C K) L s) :
    ∃ n, Inv (node C K) (drainS (node C K) n s) ∧ (drainS (node C K) n s).queue = [] :=
  let ⟨n, hn⟩ := drain_terminates hd s hr
  ⟨n, reach_inv (reach_drain hr n), hn⟩

end Connection
