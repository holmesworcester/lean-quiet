/-
What a connection gives as a notice (docs/REMOVAL.md), stated of
`Conn`'s code run on the model store. A notice is (room r, op x): x and
its requirement closure in r, given once and never taken.

Statements (`_stmt`), proven in phase 2:

- `closure_stmt`: the notice walk (`closureOps`) returns only stored ops
  of room r in x's requirement closure, and, when that closure has at
  most `fuel` ids, every one of them that is stored.
- `notice_sent_stmt`: a connection carrying a notice it has not given
  gives it on its next `filed` step (and on a `tick` that does not drop
  it): every op of x's closure in r that the peer is not known to hold
  goes out, and x is reported settled and recorded given.
- `notice_send_stmt`: everything `filed` and `tick` send is a sync wire
  op or an op of a notice not given before: so a step sends no data op
  but a notice's. (This replaces `filed_send` and `tick_send`, which
  said "wire ops only".)
- `notice_once_stmt`: once a connection has given all its notices,
  `filed` and `tick` send wire ops only again: a notice is given once
  per connection. `recv` never gives one (`recv_send` stands).
-/
import Engine.Sync.ConnLaws
import Engine.Sync.Locality

namespace Engine.Sync

section
variable {F : Type} (fam : Family F)

/-- y is x, or required (recursively) by an op of room r that x reaches:
x's requirement closure in r. An op of another room is not followed. -/
inductive ReachIn (ops : Id → Option Op) (r x : Id) : Id → Prop
  | refl : ReachIn ops r x x
  | step {y : Id} {o : Op} {z : Id} : ReachIn ops r x y → ops y = some o → fam.room o = some r →
      z ∈ o.reqs → ReachIn ops r x z

/-- x's closure in r has at most n ids. -/
def ClosureWithin (ops : Id → Option Op) (r x : Id) (n : Nat) : Prop :=
  ∃ L : List Id, L.length ≤ n ∧ ∀ y, ReachIn fam ops r x y → y ∈ L

end

/-- **The notice walk.** `closureOps r fuel [x] []`, run on the model at
s, returns stored ops of room r in x's closure; and every one of them
when the closure fits the fuel. -/
def closure_stmt : Prop :=
  ∀ {F : Type} (fam : Family F) (s : DB F) (r x : Id) (fuel : Nat),
    let ops := ((closureOps fam r fuel [x] [] : Model F (List Op)).run s).1
    (∀ o ∈ ops, s.ops o.id = some o ∧ fam.room o = some r ∧ ReachIn fam s.ops r x o.id) ∧
    (ClosureWithin fam s.ops r x fuel →
      ∀ y o, ReachIn fam s.ops r x y → s.ops y = some o → fam.room o = some r → o ∈ ops)

/-- What giving notice (r, x) in a step means: every stored op of x's
closure in r the peer is not known to hold goes out, x is reported
settled, and the connection records it given. -/
def Gives {F : Type} (fam : Family F) (s : DB F) (c : Conn) (r x : Id) (st : Step) : Prop :=
  Status.settled x ∈ st.status ∧ has st.conn.settled x = true ∧
    ∀ y o, ReachIn fam s.ops r x y → s.ops y = some o → fam.room o = some r →
      c.known.contains y = false → o ∈ st.send

/-- **E1, the notice is given (`notice_sent`).** A connection carrying
notice (r, x) it has not given gives it on its next `filed` step (which
the node runs on every connection right after storing ops, so right
after it decides a removal), and on a `tick` that does not drop it;
given that x's closure fits `cfg.walk`. -/
def notice_sent_stmt : Prop :=
  ∀ {F : Type} (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (c : Conn)
    (ids : List Id) (now : Nat) (r x : Id),
    (r, x) ∈ c.notices → has c.settled x = false → ClosureWithin fam s.ops r x cfg.walk →
    Gives fam s c r x ((c.filed fam cfg ids : Model F Step).run s).1 ∧
    (¬ (c.waiting = true ∧ c.heard + cfg.patience < now) →
      Gives fam s c r x ((c.tick fam cfg ix now : Model F Step).run s).1)

/-- **A step gives nothing but notices (`notice_send`).** Everything
`filed` and `tick` send is a sync wire op, or a stored op of room r in
x's closure for a notice (r, x) the connection carried and had not
given. -/
def notice_send_stmt : Prop :=
  ∀ {F : Type} (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (c : Conn)
    (ids : List Id) (now : Nat),
    ∀ st ∈ [((c.filed fam cfg ids : Model F Step).run s).1,
        ((c.tick fam cfg ix now : Model F Step).run s).1],
      (∀ o ∈ st.send, isWire o.kind = true ∨
        ∃ r x, (r, x) ∈ c.notices ∧ has c.settled x = false ∧ s.ops o.id = some o ∧
          fam.room o = some r ∧ ReachIn fam s.ops r x o.id) ∧
      st.take = []

/-- **Once (`notice_once`).** A connection that has given every notice
it carries sends only sync wire ops on `filed` and `tick`, as before
notices: a notice is given once per connection. -/
def notice_once_stmt : Prop :=
  ∀ {F : Type} (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (c : Conn)
    (ids : List Id) (now : Nat),
    (∀ p ∈ c.notices, has c.settled p.2 = true) →
    (∀ o ∈ ((c.filed fam cfg ids : Model F Step).run s).1.send, isWire o.kind = true) ∧
    (∀ o ∈ ((c.tick fam cfg ix now : Model F Step).run s).1.send, isWire o.kind = true)

end Engine.Sync
