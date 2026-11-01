import ops.connection.Progress
import ops.connection.Execution

/- The positive answer law with the production interpreter's advancing
entropy tape. This does not rely on FreshPure or repeat a secret whenever
the database is unchanged. Native entropy remains an external input. -/
namespace Connection.ProgressTape
open Engine Engine.Sync Codec Execution

theorem run_bind (a : M α) (f : α → M β) (s : Memory) :
    (a >>= f) s = f (a s).1 (a s).2 := rfl

theorem run_count (r : Rel Fact) (args : List B) (s : Memory) :
    (count r args : M Nat) s = ((Engine.eval s.held.db (r.query args (limit := some 0))).total, s) := rfl

theorem run_get (id : Id) (s : Memory) :
    (Store.getOp id : M (Option Op)) s = (s.held.db.ops id, s) := rfl

theorem run_view (v : View F α) (s : Memory) :
    (v.run : M α) s = (v.eval s.held.db, s) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval s.held.db q)

theorem run_arrivedFrom (id : Id) (s : Memory) :
    (arrivedFrom id : M (Option B)) s =
      (((arrivedFrom id : Model F (Option B)).run s.held.db).1, s) := rfl

theorem run_fresh (s : Memory) :
    (Fresh.fresh : M B) s = (s.entropy s.cursor, { s with cursor := s.cursor + 1 }) := rfl

/-- The actual answer handler consumes exactly its next entropy input and
constructs the answer from that value. All earlier and later tape values
are arbitrary. Store readiness is checked before that draw. -/
theorem answer_ready (K : Keys) (s : Memory) (eps : List (B × B × Id))
    (r c frm to frm' m1 sk epOp addr : B) (ro co : Op)
    (hcount : (Engine.eval s.held.db (connection.byRequest.query [r] (limit := some 0))).total = 0)
    (hro : s.held.db.ops r = some ro)
    (hb : (decode ro.body : Option Body) = some (.request to frm' m1))
    (hep : eps.find? (fun p => decide (p.1 = to)) = some (to, sk, epOp))
    (ht : ((trusts c to frm).liftL : View F Bool).eval s.held.db = true)
    (ha : ((arrivedFrom r : Model F (Option B)).run s.held.db).1 = some addr)
    (hc : Reply.op K r sk frm m1 (s.entropy s.cursor) = some co) :
    (answerOne K eps r c frm : M (List Op)) s =
      ([co, Eph.op (s.entropy s.cursor) co.id,
        Established.op co.id r (Eph.op (s.entropy s.cursor) co.id).id epOp,
        Send.op addr co], { s with cursor := s.cursor + 1 }) := by
  simp only [answerOne, run_bind, run_count, hcount, ne_eq, not_true_eq_false, ↓reduceIte,
    run_get, hro, hb, hep, run_view, ht, Bool.not_true, Bool.false_eq_true,
    run_arrivedFrom, ha]
  simp only [run_fresh, hc]
  rfl

end Connection.ProgressTape
