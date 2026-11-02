import app.community.Family

namespace Community
open Engine Codec

theorem check_notice {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {r bx : ByteArray} {tm : Nat}
    (h : check C o b fs = some (.notice c u r bx tm)) :
    ∃ s d0 e0 d e, b = .notice r bx tm s ∧ fs = [.admission c c d0 e0, .admission c u d e] ∧
      o.reqs.head? = some c ∧ r.size = 32 ∧ bx.size ≤ Notice.maxBox ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a
  rcases b with ⟨r', bx', tm', s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c1, u', d, e⟩
  simp only [Notice.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofNotice.injEq, Notice.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h4, h5, h6⟩ := hc
    exact ⟨_, _, _, _, _, rfl, rfl, h1, h4, h5, h6⟩
  · simp at h
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **A user's private notification state is written only by that
user.** A Valid notice about user u of c (its reads and its settings,
sealed to one device) was signed, as this exact op, by a device
admitted into u: nobody marks another user's messages read or changes
another user's notifications. -/
theorem notice_signed {x c u : Id} {r bx : ByteArray} {tm : Nat}
    (h : V C ops x (.notice c u r bx tm)) :
    ∃ o s d e y, ops x = some o ∧ (decode o.body : Option Body) = some (.notice r bx tm s) ∧
      o.reqs = [c, y] ∧ V C ops y (.admission c u d e) ∧ r.size = 32 ∧
      C.verify d (signed o (.notice r bx tm s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, d, e, rfl, rfl, hh, hr32, _, hs⟩ := check_notice hv
  obtain ⟨a, y, hreq, _, hy⟩ := all2_two hr
  rw [hreq] at hh; simp at hh; subst hh
  exact ⟨o, s, d, e, y, hx, hb, hreq, hy, hr32, hs⟩

/-- **Notification state never leaves this device** (for now): a notice
is local, as is a caught-up mark, so no other member's node learns when
this user reads or changes a setting. With device linking, notices will
travel only between the user's own devices (docs/NOTIFICATIONS.md). -/
theorem notice_local (r bx : ByteArray) (tm : Nat) (s : ByteArray) (reqs : List Id) :
    (family C).shared (mkOp reqs (.notice r bx tm s)) = false := by
  rw [shared_mkOp]; rfl

theorem caughtUp_local (c : Id) (mark : Nat) :
    (family C).shared (mkOp [] (.caughtUp c mark)) = false := by
  rw [shared_mkOp]; rfl

end Community
