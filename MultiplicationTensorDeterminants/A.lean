import Mathlib

namespace DetRatioFour.Extension

/-- A length-d Frobenius cycle splits into gcd(d,m) equal cycles over degree m. -/
def powered (m : ℕ) (profile : List ℕ) : List ℕ :=
  profile.flatMap fun d => List.replicate (d.gcd m) (d / d.gcd m)

private theorem powered_without_splitting (m : ℕ) (a : List ℕ)
    (h : ∀ d ∈ a, d.gcd m = 1) : powered m a = a := by
  induction a with
  | nil => rfl
  | cons d a ih =>
    have hd := h d (List.mem_cons_self)
    have hrest : ∀ e ∈ a, e.gcd m = 1 := fun e he => h e (List.mem_cons_of_mem d he)
    simpa [powered, hd] using congrArg (d :: ·) (ih hrest)

/-- Distinct powered degrees imply that no original cycle split. -/
theorem distinct_powered_iff (m : ℕ) (a : List ℕ)
    (hpos : ∀ d ∈ a, 0 < d) :
    (powered m a).Nodup ↔ a.Nodup ∧ ∀ d ∈ a, d.gcd m = 1 := by
  constructor
  · intro h
    have hnd := (List.nodup_flatMap.mp h).1
    have hsplit (d : ℕ) (hd : d ∈ a) : d.gcd m = 1 := by
      have hle := List.nodup_replicate.mp (hnd d hd)
      have hgt := Nat.gcd_pos_of_pos_left m (hpos d hd)
      omega
    exact ⟨powered_without_splitting m a hsplit ▸ h, hsplit⟩
  · rintro ⟨h, hsplit⟩
    rwa [powered_without_splitting m a hsplit]

/-- A genuinely new ordinary agreement can only occur at a repeated powered degree. -/
theorem new_power_agreement_forces_repeat (m : ℕ) (a b : List ℕ)
    (ha : ∀ d ∈ a, 0 < d) (hb : ∀ d ∈ b, 0 < d)
    (hne : ¬ a.Perm b) (hpow : (powered m a).Perm (powered m b)) :
    ¬ (powered m a).Nodup := by
  intro h
  have h' := hpow.nodup_iff.mp h
  rw [powered_without_splitting m a ((distinct_powered_iff m a ha).mp h).2,
    powered_without_splitting m b ((distinct_powered_iff m b hb).mp h').2] at hpow
  exact hne hpow

section Matrices
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A trace isometry's determinant ratio squared is the discriminant ratio. -/
theorem discriminant_transforms {A B X : Matrix n n K}
    (h : X.transpose * B * X = A) : A.det = X.det ^ 2 * B.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  rw [← hd]
  ring

/-- When the trace determinants agree, an odd automorphism repairs the sign
of an allowed transporter. The closure hypothesis keeps composition inside the
intended family of transporters. -/
theorem repair_equal_discriminant (allowed : Matrix n n K → Prop)
    {A B X W : Matrix n n K} (hx : allowed X) (htrace : X.transpose * B * X = A)
    (hdisc : A.det = B.det) (hperfect : B.det ≠ 0)
    (hodd : W.det = -1) (hcompose : ∀ Y, allowed Y → allowed (W * Y)) :
    ∃ Y, allowed Y ∧ Y.det = 1 := by
  have hh := discriminant_transforms htrace
  have hs : X.det ^ 2 = 1 := by
    apply mul_right_cancel₀ hperfect
    simpa [← hdisc] using hh.symm
  rcases sq_eq_one_iff.mp hs with h | h
  · exact ⟨X, hx, h⟩
  · refine ⟨W * X, hcompose X hx, ?_⟩
    simp [Matrix.det_mul, hodd, h]

end Matrices
end DetRatioFour.Extension
