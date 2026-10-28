/-
Line wrapping keeps the text and fits it, over the running code
(`Text.wrapL`, which `layout` calls for every paragraph):

- `wrap_keeps`: the lines, joined, are the paragraph with some spaces
  left out (a sublist of it with the same non-space characters): nothing
  but spaces is lost, nothing is added or reordered;
- `wrap_fits`: every line is at most the width, when every character is.
-/
import engine.renderer.Text

namespace Text

variable (f : Font.Font)

def ns (c : UInt32) : Bool := !isSpace c

theorem tokens_flatten : ∀ cs : List UInt32, (tokens f cs).flatten = cs
  | [] => by simp [tokens]
  | c :: t => by
    unfold tokens
    split
    · simp [tokens_flatten t]
    · split
      · have := splitW_append (fun d => adv f d == 0) t
        have h := splitW_len (fun d => adv f d == 0) t
        simp only [List.flatten_cons, List.cons_append]
        rw [tokens_flatten (splitW (fun d => adv f d == 0) t).2, this]
      · have := splitW_append (fun d => !isSpace d && !wide f d) t
        have h := splitW_len (fun d => !isSpace d && !wide f d) t
        simp only [List.flatten_cons, List.cons_append]
        rw [tokens_flatten (splitW (fun d => !isSpace d && !wide f d) t).2, this]
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-! ## trimEnd -/

theorem dropWhile_sp_filter : ∀ m : List UInt32, (m.dropWhile isSpace).filter ns = m.filter ns
  | [] => rfl
  | x :: t => by
    by_cases h : isSpace x
    · simp [List.dropWhile_cons, h, ns, dropWhile_sp_filter t]
    · simp [List.dropWhile_cons, h]

theorem trimEnd_filter (l : List UInt32) : (trimEnd l).filter ns = l.filter ns := by
  simp [trimEnd, List.filter_reverse, dropWhile_sp_filter]

theorem trimEnd_sublist (l : List UInt32) : (trimEnd l).Sublist l := by
  have := (List.dropWhile_sublist (p := isSpace) (l := l.reverse)).reverse
  simpa [trimEnd] using this

theorem lineW_append (a b : List UInt32) : lineW f (a ++ b) = lineW f a + lineW f b := by
  simp [lineW, List.sum_append]

theorem lineW_sublist : ∀ {a b : List UInt32}, a.Sublist b → lineW f a ≤ lineW f b
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons x h => by have := lineW_sublist h; simp [lineW] at *; omega
  | _, _, .cons_cons x h => by have := lineW_sublist h; simp [lineW] at *; omega

theorem trimEnd_le (l : List UInt32) : lineW f (trimEnd l) ≤ lineW f l :=
  lineW_sublist f (trimEnd_sublist l)

theorem dropWhile_spaces_append : ∀ (s m : List UInt32), (∀ x ∈ s, isSpace x = true) →
    (s ++ m).dropWhile isSpace = m.dropWhile isSpace
  | [], _, _ => rfl
  | x :: t, m, h => by
    simp only [List.cons_append, List.dropWhile_cons, h x List.mem_cons_self, if_true]
    exact dropWhile_spaces_append t m (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem trimEnd_spaces (cur s : List UInt32) (h : ∀ x ∈ s, isSpace x = true) :
    trimEnd (cur ++ s) = trimEnd cur := by
  simp only [trimEnd, List.reverse_append]
  rw [dropWhile_spaces_append s.reverse cur.reverse (by simpa using h)]

/-! ## Nothing but spaces is lost -/

/-- The text a wrap state holds: its lines, then the current line. -/
def held (lines : List (List UInt32)) (cur : List UInt32) : List UInt32 := lines.flatten ++ cur

theorem breakIn_keeps (width : Nat) : ∀ (tok : List UInt32) (lines : List (List UInt32)) (cur : List UInt32),
    let r := breakIn f width tok lines cur
    (held r.1 r.2).filter ns = (held lines cur ++ tok).filter ns ∧
    (held r.1 r.2).Sublist (held lines cur ++ tok)
  | [], lines, cur => by simp [breakIn]
  | c :: t, lines, cur => by
    unfold breakIn
    split
    · have ih := breakIn_keeps width t (lines ++ [trimEnd cur]) [c]
      refine ⟨?_, ?_⟩
      · rw [ih.1]; simp [held, List.filter_append, trimEnd_filter]
      · refine ih.2.trans ?_
        simp only [held, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.append_assoc, List.cons_append, List.nil_append]
        exact List.Sublist.append_left (List.Sublist.append (trimEnd_sublist cur) (List.Sublist.refl _)) _
    · have ih := breakIn_keeps width t lines (cur ++ [c])
      refine ⟨?_, ?_⟩
      · rw [ih.1]; simp [held, List.append_assoc]
      · exact ih.2.trans (by simp [held, List.append_assoc])

theorem fill_keeps (width : Nat) : ∀ (toks : List (List UInt32)) (lines : List (List UInt32)) (cur : List UInt32),
    (fill f width toks lines cur).flatten.filter ns = (held lines cur ++ toks.flatten).filter ns ∧
    (fill f width toks lines cur).flatten.Sublist (held lines cur ++ toks.flatten)
  | [], lines, cur => by
    simp only [fill, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, held]
    exact ⟨by simp [List.filter_append, trimEnd_filter], List.Sublist.append_left (trimEnd_sublist cur) _⟩
  | tok :: t, lines, cur => by
    unfold fill
    split
    · have ih := fill_keeps width t lines (cur ++ tok)
      exact ⟨by rw [ih.1]; simp [held, List.append_assoc], ih.2.trans (by simp [held, List.append_assoc])⟩
    · split
      · have ih := fill_keeps width t lines (cur ++ tok)
        exact ⟨by rw [ih.1]; simp [held, List.append_assoc], ih.2.trans (by simp [held, List.append_assoc])⟩
      · split
        · have ih := fill_keeps width t (lines ++ [trimEnd cur]) tok
          refine ⟨?_, ?_⟩
          · rw [ih.1]; simp [held, List.filter_append, trimEnd_filter, List.append_assoc]
          · refine ih.2.trans ?_
            simp only [held, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
              List.append_assoc]
            exact List.Sublist.append_left (List.Sublist.append (trimEnd_sublist cur) (List.Sublist.refl _)) _
        · have hb := breakIn_keeps f width tok lines cur
          have ih := fill_keeps width t (breakIn f width tok lines cur).1 (breakIn f width tok lines cur).2
          refine ⟨?_, ?_⟩
          · rw [ih.1, List.filter_append, hb.1]; simp [held, List.append_assoc, List.filter_append]
          · refine ih.2.trans ?_
            have := List.Sublist.append hb.2 (List.Sublist.refl t.flatten)
            simpa [held, List.append_assoc] using this

/-- **Wrapping loses nothing but spaces.** The lines, joined, are a
sublist of the paragraph with exactly its non-space characters. -/
theorem wrap_keeps (width : Nat) (cs : List UInt32) :
    (wrapL f width cs).flatten.filter ns = cs.filter ns ∧ (wrapL f width cs).flatten.Sublist cs := by
  have h := fill_keeps f width (tokens f cs) [] []
  simp only [held, List.flatten_nil, List.nil_append, tokens_flatten] at h
  exact h

/-! ## Every line fits -/

theorem breakIn_fits (width : Nat) : ∀ (tok : List UInt32) (lines : List (List UInt32)) (cur : List UInt32),
    (∀ c ∈ tok, adv f c ≤ width) → (∀ l ∈ lines, lineW f l ≤ width) → lineW f (trimEnd cur) ≤ width →
    let r := breakIn f width tok lines cur
    (∀ l ∈ r.1, lineW f l ≤ width) ∧ lineW f (trimEnd r.2) ≤ width
  | [], _, _, _, hl, hc => ⟨hl, hc⟩
  | c :: t, lines, cur, ha, hl, hc => by
    unfold breakIn
    have hc' : adv f c ≤ width := ha c List.mem_cons_self
    have ht : ∀ d ∈ t, adv f d ≤ width := fun d hd => ha d (List.mem_cons_of_mem _ hd)
    split
    · refine breakIn_fits width t _ [c] ht ?_ ?_
      · intro l hm
        rcases List.mem_append.1 hm with h | h
        · exact hl l h
        · simp at h; subst h; exact hc
      · have := trimEnd_le f [c]; simp [lineW] at this ⊢; omega
    · rename_i hn
      refine breakIn_fits width t lines (cur ++ [c]) ht hl ?_
      have h1 := trimEnd_le f (cur ++ [c])
      rw [lineW_append] at h1
      have hcw : lineW f [c] = adv f c := by simp [lineW]
      have key : lineW f cur + adv f c ≤ width ∨ cur = [] := by
        by_cases hgt : lineW f cur + adv f c > width
        · right
          cases hcur : cur with
          | nil => rfl
          | cons y ys => exfalso; apply hn; simp [hcur] at hgt ⊢; omega
        · left; omega
      rcases key with k | k
      · omega
      · subst k; simp [lineW] at h1 ⊢; omega

theorem fill_fits (width : Nat) : ∀ (toks : List (List UInt32)) (lines : List (List UInt32)) (cur : List UInt32),
    (∀ tok ∈ toks, ∀ c ∈ tok, adv f c ≤ width) → (∀ l ∈ lines, lineW f l ≤ width) → lineW f (trimEnd cur) ≤ width →
    ∀ l ∈ fill f width toks lines cur, lineW f l ≤ width
  | [], lines, cur, _, hl, hc => by
    intro l hm
    simp only [fill, List.mem_append, List.mem_singleton] at hm
    rcases hm with h | rfl
    · exact hl l h
    · exact hc
  | tok :: t, lines, cur, ha, hl, hc => by
    have ht : ∀ tok ∈ t, ∀ c ∈ tok, adv f c ≤ width := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have htok : ∀ c ∈ tok, adv f c ≤ width := ha tok List.mem_cons_self
    unfold fill
    split
    · rename_i hs
      refine fill_fits width t lines (cur ++ tok) ht hl ?_
      rw [trimEnd_spaces cur tok (by simpa [List.all_eq_true] using hs)]; exact hc
    · split
      · rename_i _ hw
        refine fill_fits width t lines (cur ++ tok) ht hl ?_
        have := trimEnd_le f (cur ++ tok); rw [lineW_append] at this; omega
      · split
        · rename_i _ _ hw
          refine fill_fits width t (lines ++ [trimEnd cur]) tok ht ?_ ?_
          · intro l hm
            rcases List.mem_append.1 hm with h | h
            · exact hl l h
            · simp at h; subst h; exact hc
          · have := trimEnd_le f tok; omega
        · have hb := breakIn_fits f width tok lines cur htok hl hc
          exact fill_fits width t _ _ ht hb.1 hb.2

/-- **Every line fits**, when every character does (one wider than the
line cannot fit anywhere). -/
theorem wrap_fits (width : Nat) (cs : List UInt32) (h : ∀ c ∈ cs, adv f c ≤ width) :
    ∀ l ∈ wrapL f width cs, lineW f l ≤ width := by
  refine fill_fits f width (tokens f cs) [] [] ?_ (by simp) (by simp [trimEnd, lineW])
  intro tok htok c hc
  exact h c (by rw [← tokens_flatten f cs]; exact List.mem_flatten.2 ⟨tok, htok, hc⟩)

end Text
