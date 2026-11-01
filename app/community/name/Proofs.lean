import app.community.Family

/-!
`community.name`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

theorem prevMax_shared {c : Id} : ∀ {fs : List Fact} {m}, prevMax c fs = some m →
    ∀ g ∈ fs, g.isLocal = false
  | [], _, _, g, hg => by cases hg
  | .named .. :: rest, m, h, g, hg => by
    simp only [prevMax] at h
    split at h
    · obtain ⟨k, hk, _⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hg with rfl | hg
      · rfl
      · exact prevMax_shared hk g hg
    · cases h
  | .admission .. :: _, _, h, _, _ | .invitation .. :: _, _, h, _, _ | .admin .. :: _, _, h, _, _
  | .removal .. :: _, _, h, _, _ | .message .. :: _, _, h, _, _ | .wrap .. :: _, _, h, _, _
  | .profile .. :: _, _, h, _, _ | .react .. :: _, _, h, _, _ | .request .. :: _, _, h, _, _
  | .attachment .. :: _, _, h, _, _ | .chunk .. :: _, _, h, _, _ | .secret .. :: _, _, h, _, _ | .accepted .. :: _, _, h, _, _
  | .joining .. :: _, _, h, _, _ | .approval .. :: _, _, h, _, _ | .abandoned .. :: _, _, h, _, _
  | .key .. :: _, _, h, _, _ => by simp [prevMax] at h

theorem counterOk_shared {c : Id} {n : Nat} {fs : List Fact} (h : counterOk c n fs = true) :
    ∀ g ∈ fs, g.isLocal = false := by
  unfold counterOk at h
  split at h
  · rename_i m hm; exact prevMax_shared hm
  · cases h

end Community
