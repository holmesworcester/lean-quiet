import app.Screen
import engine.sync.Ephemeral
import app.community.channel.message.draft.Commands
import app.community.channel.message.draft.View

/-
Draft's laws over the running app (DRAFT01). Leaving a conversation
writes its draft into the app's ephemeral log (`Data.draftIn`), and the
log's newest draft for that entry is exactly that one
(`draftIn_newest`); an empty composer leaves none (`draftIn_empty`). So
coming back to the entry brings its text back (`stash_use`).
-/

namespace Community
namespace Draft
open Engine Engine.Sync Codec

/-- Of Community's relations, only `draft.byAcc` is a draft list. -/
theorem draft_rels : Community.rels.filter (fun r => r.kind == "draft") = [draft.byAcc] := by rfl

theorem rel_draft {r : Rel Community.Fact} (hr : r ∈ Community.rels) (hk : r.kind = "draft") :
    r = draft.byAcc := by
  have : r ∈ Community.rels.filter (fun r => r.kind == "draft") := List.mem_filter.2 ⟨hr, by simp [hk]⟩
  rw [draft_rels] at this
  exact List.mem_singleton.1 this

/-- **A community fact filed under entry acc's draft list is acc's draft.** -/
theorem key_draft {cf : Community.Fact} {acc : Id} (hk : (query acc).key ∈ Community.keys cf) :
    ∃ d, cf = .ofDraft d ∧ d.acc = acc := by
  rw [Community.keys, keysOf, List.mem_filterMap] at hk
  obtain ⟨r, hr, he⟩ := hk
  cases ha : r.args cf with
  | none => rw [ha] at he; cases he
  | some as =>
    rw [ha] at he
    have he' : r.key as = (query acc).key := Option.some.inj he
    obtain ⟨hkind, -, has⟩ := Rel.key_eq_iff.1 he'
    have hrd := rel_draft hr hkind
    subst hrd
    cases cf with
    | ofDraft d =>
      simp [draft.byAcc, Draft.byAcc] at ha
      subst ha
      exact ⟨d, rfl, by simpa using has⟩
    | _ => simp [draft.byAcc] at ha

theorem apart_connection : ∀ r ∈ Connection.rels, r.kind ≠ "draft" := by decide
theorem apart_settings : ∀ r ∈ Settings.rels, r.kind ≠ "draft" := by decide
theorem apart_nav : ∀ r ∈ Nav.rels, r.kind ≠ "draft" := by decide

theorem not_relKey {G : Type} {rels : List (Rel G)} (hr : ∀ r ∈ rels, r.kind ≠ "draft") (f : G) (acc : Id) :
    (query acc).key ∉ keysOf rels f := by
  intro hk
  rw [keysOf, List.mem_filterMap] at hk
  obtain ⟨r, hr', he⟩ := hk
  cases ha : r.args f with
  | none => rw [ha] at he; cases he
  | some as =>
    rw [ha] at he
    have he' : r.key as = Community.draft.byAcc.key [acc] := Option.some.inj he
    exact hr r hr' (Rel.key_names he').1

theorem key_ne_opKey (acc y : Id) : (query acc).key ≠ opKey y := Rel.key_ne_opKey _ (by decide) [acc] y

/-- **Entry acc's draft list holds only acc's drafts,** in a store of the
node's family. -/
theorem query_only {C : Crypto} {K : Connection.Keys} {s : DB Quiet.F} (h : Engine.Inv (Quiet.node C K) s)
    {acc x : Id} (hx : x ∈ s.idx (query acc).key) :
    ∃ d, s.status x = some (.valid (.inl (.inl (.ofDraft d)))) ∧ d.acc = acc := by
  obtain ⟨g, hg, hk⟩ := (h.idx _ x).1 hx
  rcases List.mem_cons.1 hk with e | e
  · exact absurd e (key_ne_opKey acc x)
  · rcases g with (cf | kf) | (sf | nf)
    · obtain ⟨d, rfl, hd⟩ := key_draft (cf := cf) e
      exact ⟨d, hg, hd⟩
    · exact absurd e (not_relKey apart_connection kf acc)
    · exact absurd e (not_relKey apart_settings sf acc)
    · exact absurd e (not_relKey apart_nav nf acc)

/-- A draft fact comes only from a draft body, with its fields. -/
theorem check_draft {C : Crypto} {o : Op} {b : Community.Body} {fs : List Community.Fact} {d : Fact}
    (h : Community.check C o b fs = some (.ofDraft d)) : ∃ b', b = .ofDraft b' ∧ Draft.check o b' = some d := by
  unfold Community.check at h
  split at h <;> (try (simp at h; done)) <;> first
    | (obtain ⟨f', hf, he⟩ := Option.map_eq_some_iff.1 h; cases he; exact ⟨_, rfl, hf⟩)
    | (obtain ⟨f', -, he⟩ := Option.map_eq_some_iff.1 h; cases he)

/-- **A draft fact in the node comes only from a draft op,** with its fields. -/
theorem node_draft {C : Crypto} {K : Connection.Keys} {o : Op} {fs : List Quiet.F} {d : Fact}
    (h : (Quiet.node C K).validate o fs = some (.inl (.inl (.ofDraft d)))) :
    Draft.of o = some ⟨d.acc, d.gen, d.text, d.pics⟩ := by
  unfold Quiet.node Family.sum at h
  by_cases ha : Quiet.app.owns o.kind = true
  · simp only [ha, ite_true] at h
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h; cases e
  · simp only [ha, Bool.false_eq_true, ite_false] at h
    obtain ⟨xs, -, hx⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.1 hx
    cases he
    unfold Connection.node Family.sum at hg
    by_cases hc : (Connection.family K).owns o.kind = true
    · simp only [hc, ite_true] at hg
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 hg; cases e
    · simp only [hc, Bool.false_eq_true, ite_false] at hg
      obtain ⟨ys, -, hy⟩ := Option.bind_eq_some_iff.1 hg
      obtain ⟨g', hg', he'⟩ := Option.map_eq_some_iff.1 hy
      cases he'
      simp only [Community.family, Community.validate] at hg'
      split at hg'
      · cases hg'
      · rename_i b hb
        split at hg'
        · obtain ⟨b', rfl, hc'⟩ := check_draft hg'
          simp only [Draft.check] at hc'
          split at hc'
          · cases hc'; simp [Draft.of, hb]
          · cases hc'
        · cases hg'

/-- An op is entry acc's draft, if it makes one. -/
theorem isFor_of {o : Op} {b : Body} (h : Draft.of o = some b) (acc : Id) (hb : b.acc = acc) :
    Draft.isFor acc o = true := by
  haveI := lawfulBEqByteArray
  simp [Draft.isFor, h, hb]

end Draft
end Community

namespace Data
open Engine Engine.Sync

/-- **A stashed draft is the log's newest for its entry.** Once the log is
rebuilt with entry acc's draft holding something (its ops' ids
distinct), the draft read from it for acc is exactly that one. -/
theorem draftIn_newest (h : Held SF) (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray)
    (hne : (text.isEmpty && pics.isEmpty) = false) (hd : Distinct (drafted h acc gen text pics)) :
    draftOf (draftIn h acc gen text pics) acc =
      some ((Community.Draft.write acc gen text pics).id, ⟨acc, gen, text, pics⟩) := by
  let op := Community.Draft.write acc gen text pics
  let L := drafted h acc gen text pics
  let H := Held.ofOps fam L
  let df : Community.Draft.Fact := ⟨acc, gen, text, pics⟩
  have hop : op ∈ L := by
    show op ∈ drafted h acc gen text pics
    unfold drafted; rw [hne]; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hv : fam.validate op [] = some (.inl (.inl (.ofDraft df))) := by
    have h1 := Quiet.node_left (C := C) (K := Connection.sodium) (o := op)
      (by show Quiet.appOwns 25 = false; decide) ([] : List Connection.F)
    have h2 := sum_left (Community.family C) (Connection.family Connection.sodium) op []
      (by show Connection.owns 25 = false; decide)
    simp only [List.map_nil] at h1 h2
    rw [show fam = Quiet.node C Connection.sodium from rfl, h1]
    show Option.map Sum.inl ((Connection.node C Connection.sodium).validate op []) = _
    rw [show Connection.node C Connection.sodium =
      Family.sum (Community.family C) (Connection.family Connection.sodium) from rfl, h2,
      Community.Draft.write_valid]
    rfl
  have hst : H.db.status op.id = some (.valid (.inl (.inl (.ofDraft df)))) := ofOps_valid fam hd hop rfl hv
  have hinv := ofOps_inv fam L
  have hin : Community.draft.byAcc ∈ Community.rels :=
    (List.mem_filter.1 (by rw [Community.Draft.draft_rels]; exact List.mem_singleton.2 rfl :
      Community.draft.byAcc ∈ Community.rels.filter (fun r => r.kind == "draft"))).1
  have hkey : (Community.Draft.query acc).key ∈ Community.keys (.ofDraft df) := by
    rw [Community.keys, keysOf, List.mem_filterMap]
    exact ⟨Community.draft.byAcc, hin, rfl⟩
  have hx : op.id ∈ H.db.idx (Community.Draft.query acc).key :=
    (hinv.idx _ op.id).2 ⟨_, hst, List.mem_cons_of_mem _ hkey⟩
  have hq : (Community.Draft.query acc) = { key := (Community.Draft.query acc).key, limit := some 1 } := rfl
  have hm : ((SortKey.sortOf (Sum.inl (Sum.inl (Community.Fact.ofDraft df)) : Quiet.F), op.id),
      (Sum.inl (Sum.inl (Community.Fact.ofDraft df)) : Quiet.F)) ∈ matching H.db (Community.Draft.query acc) := by
    rw [hq]; exact (mem_matching _ _).2 ⟨op.id, _, rfl, hx, hst⟩
  obtain ⟨t, ht, htm, -⟩ := top_max (q := Community.Draft.query acc) rfl rfl rfl
    (by show some 1 ≠ some 0; decide) hm
  rw [hq] at htm
  obtain ⟨y, g, rfl, hy, hg⟩ := (mem_matching _ _).1 htm
  obtain ⟨d, hgd, hda⟩ := Community.Draft.query_only hinv hy
  rw [hg] at hgd
  cases hgd
  obtain ⟨o, fs, ho, hid, hvo⟩ := ofOps_from fam hd hg
  have hof := Community.Draft.node_draft hvo
  have hoeq : o = op := by
    unfold drafted at ho
    rcases List.mem_append.1 ho with hr | hr
    · have := (List.mem_filter.1 hr).2
      rw [Community.Draft.isFor_of hof acc hda] at this; cases this
    · rw [hne] at hr; exact List.mem_singleton.1 hr
  subst hoeq
  rw [← hid, hst] at hg
  cases hg
  obtain ⟨rest, hrows⟩ : ∃ rest, (Engine.eval H.db (Community.Draft.query acc)).rows =
      ((SortKey.sortOf (Sum.inl (Sum.inl (Community.Fact.ofDraft df)) : Quiet.F), op.id),
        (Sum.inl (Sum.inl (Community.Fact.ofDraft df)) : Quiet.F)) :: rest := by
    cases hr : (Engine.eval H.db (Community.Draft.query acc)).rows with
    | nil => rw [hr, ← hid] at ht; cases ht
    | cons t rest => rw [hr, ← hid] at ht; cases ht; exact ⟨rest, rfl⟩
  show (((((Community.Draft.current acc).liftL.liftL : View SF _).run : HeldM SF _).run H).1) = _
  rw [run_eval]
  simp only [Community.Draft.current, View.read, bind, View.bind, View.liftL, View.eval, pure]
  rw [hrows]
  rfl

theorem mem_eval_matching {F : Type} [SortKey F] {s : DB F} {q : ListQ} {pf : Pos × F}
    (h : pf ∈ (Engine.eval s q).rows) : pf ∈ matching s q := by
  unfold Engine.eval at h
  simp only at h
  have h1 : pf ∈ (if q.desc then ((matching s q).filter fun p => q.inside p.1).reverse
      else (matching s q).filter fun p => q.inside p.1) := by
    unfold ListQ.cut at h; split at h
    · exact h
    · exact List.mem_of_mem_take h
  have h2 : pf ∈ (matching s q).filter fun p => q.inside p.1 := by
    split at h1
    · exact List.mem_reverse.1 h1
    · exact h1
  exact (List.mem_filter.1 h2).1

/-- **An empty composer leaves no draft**: once the log is rebuilt with
entry acc's composer empty, no draft is read for acc. -/
theorem draftIn_empty (h : Held SF) (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray)
    (he : (text.isEmpty && pics.isEmpty) = true) (hd : Distinct (drafted h acc gen text pics)) :
    draftOf (draftIn h acc gen text pics) acc = none := by
  let L := drafted h acc gen text pics
  let H := Held.ofOps fam L
  have hinv := ofOps_inv fam L
  show (((((Community.Draft.current acc).liftL.liftL : View SF _).run : HeldM SF _).run H).1) = _
  rw [run_eval]
  simp only [Community.Draft.current, View.read, bind, View.bind, View.liftL, View.eval, pure]
  cases hr : (Engine.eval H.db (Community.Draft.query acc)).rows with
  | nil => rfl
  | cons t rest =>
    exfalso
    have hq : (Community.Draft.query acc) = { key := (Community.Draft.query acc).key, limit := some 1 } := rfl
    have htm : t ∈ matching H.db (Community.Draft.query acc) :=
      mem_eval_matching (by rw [hr]; exact List.mem_cons_self ..)
    rw [hq] at htm
    obtain ⟨y, g, rfl, hy, hg⟩ := (mem_matching _ _).1 htm
    obtain ⟨d, hgd, hda⟩ := Community.Draft.query_only hinv hy
    rw [hg] at hgd
    cases hgd
    obtain ⟨o, fs, ho, -, hvo⟩ := ofOps_from fam hd hg
    have hof := Community.Draft.node_draft hvo
    unfold drafted at ho
    rw [he] at ho
    simp only [ite_true, List.append_nil] at ho
    have := (List.mem_filter.1 ho).2
    rw [Community.Draft.isFor_of hof acc hda] at this
    cases this

end Data

namespace App
open Engine Engine.Sync Data

/-- **Coming back to a conversation brings its text back** (DRAFT01).
Leaving entry acc with text in the composer, then returning to it, puts
that text back in the composer (its ops' ids distinct). -/
theorem stash_use (s : St) (hacc : s.me.acc.isEmpty = false)
    (hne : (s.text.toUTF8.isEmpty && (s.chips.toList.map (·.1)).isEmpty) = false)
    (hd : Distinct (drafted s.eph s.me.acc (s.draftGen + 1) s.text.toUTF8 (s.chips.toList.map (·.1)))) :
    (useDraft (stashDraft s)).text = s.text := by
  have hn := draftIn_newest s.eph s.me.acc (s.draftGen + 1) s.text.toUTF8 (s.chips.toList.map (·.1)) hne hd
  simp only [stashDraft, hacc, Bool.false_eq_true, ite_false, useDraft]
  rw [hn]
  simp only [String.fromUTF8!, String.toUTF8_eq_toByteArray, dite_eq_left s.text.isValidUTF8]
  rfl

end App
