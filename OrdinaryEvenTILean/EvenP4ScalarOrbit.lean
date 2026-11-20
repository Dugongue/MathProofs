import EvenP4ScalarDensity
import EvenRecognizerScan

open scoped BigOperators

namespace EvenTI.Action

variable {K : Type*} [Field K] {d n : ℕ}

private theorem scalar_commute (a : (Matrix (Fin n) (Fin n) K)ˣ) (u : Kˣ) :
    scalar u * a = a * scalar u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalar_val, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

private theorem scalarAccepted_act {T : Tensor K d n} (g : Changes K d n)
    (h : scalarAccepted T) : scalarAccepted (act g T) := by
  have hInv : act g⁻¹ (act g T) = T := by
    rw [← act_mul, inv_mul_cancel, act_one]
  constructor
  · intro hz
    apply h.1
    calc
      T = act g⁻¹ (act g T) := hInv.symm
      _ = 0 := by rw [hz]; exact Matrix.mulVec_zero _
  · intro a ha
    let b := g⁻¹ * a * g
    have hb : act b T = T := by
      change act (g⁻¹ * a * g) T = T
      rw [act_mul, act_mul, ha, hInv]
    obtain ⟨u, hu⟩ := h.2 b hb
    have haeq : a = g * b * g⁻¹ := by simp [b, mul_assoc]
    refine ⟨u, ?_⟩
    rw [haeq, hu]
    funext i
    change (g i * scalar (u i)) * (g i)⁻¹ = scalar (u i)
    rw [← scalar_commute (g i) (u i), mul_assoc, mul_inv_cancel, mul_one]

/-- Source acceptance by the scalar condition is constant on tensor orbits. -/
theorem scalarAccepted_act_iff (T : Tensor K d n) (g : Changes K d n) :
    scalarAccepted (act g T) ↔ scalarAccepted T := by
  constructor
  · intro h
    have hh := scalarAccepted_act g⁻¹ h
    rwa [← act_mul, inv_mul_cancel, act_one] at hh
  · exact scalarAccepted_act g

variable [DecidableEq K] {q : ℕ}

/-- A covered and valid stabilizer scan recognizes the mathematical scalar gate. -/
theorem verifyScalarTrials_iff_scalarAccepted (hn : 2 ≤ n) (hd : 0 < d)
    (enum : Fin q ≃ Kˣ) (xs : List (StabilizerTrial K d n)) (T : Tensor K d n)
    (cover : ∀ a, act a T = T → ∃ p ∈ xs, ∃ u,
      u ∈ Subgroup.closure {z | z ∈ p.generators} ∧ a = p.representative * u)
    (validRepresentative : ∀ p ∈ xs, act p.representative T = T)
    (validGenerator : ∀ p ∈ xs, ∀ z ∈ p.generators, act z T = T) :
    verifyScalarTrials enum xs = true ↔ scalarAccepted T := by
  rw [verifyScalarTrials_iff enum xs T cover validRepresentative validGenerator]
  exact ⟨fun h => ⟨scalar_only_ne_zero hn hd h, h⟩, And.right⟩

#print axioms scalarAccepted_act_iff
#print axioms verifyScalarTrials_iff_scalarAccepted

end EvenTI.Action
