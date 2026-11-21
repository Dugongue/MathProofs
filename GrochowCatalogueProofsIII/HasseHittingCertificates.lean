import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace GrochowCatalogueThird

/-- The finite specialization step for the two-parameter Hasse hitting set.
    The additional polynomial records the poles in the first parameter. -/
theorem grid_point_avoiding_poles {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (P : Polynomial (Polynomial F)) (D : Polynomial F) (c : ℕ)
    (u : I → F) (t : J → F) (hu : Function.Injective u) (ht : Function.Injective t)
    (hc : P.coeff c ≠ 0) (hD : D ≠ 0)
    (hU : (P.coeff c).natDegree + D.natDegree < Fintype.card I)
    (hT : P.natDegree < Fintype.card J) :
    ∃ i j, D.eval (u i) ≠ 0 ∧ ((P.map (evalRingHom (u i))).eval (t j)) ≠ 0 := by
  classical
  have hprod : P.coeff c * D ≠ 0 := mul_ne_zero hc hD
  have hdeg : (P.coeff c * D).natDegree < Fintype.card I :=
    lt_of_le_of_lt natDegree_mul_le hU
  have hi : ∃ i, (P.coeff c * D).eval (u i) ≠ 0 := by
    by_contra! hall
    exact hprod (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hu hall hdeg)
  obtain ⟨i, hi⟩ := hi
  rw [eval_mul] at hi
  have hvalid : D.eval (u i) ≠ 0 := right_ne_zero_of_mul hi
  have hspec : P.map (evalRingHom (u i)) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial F => p.coeff c) hzero
    simp only [coeff_map, coeff_zero, coe_evalRingHom] at hcoeff
    exact (left_ne_zero_of_mul hi) hcoeff
  have hj : ∃ j, ((P.map (evalRingHom (u i))).eval (t j)) ≠ 0 := by
    by_contra! hall
    apply hspec
    exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht hall
      (lt_of_le_of_lt natDegree_map_le hT)
  obtain ⟨j, hj⟩ := hj
  exact ⟨i, j, hvalid, hj⟩

end GrochowCatalogueThird

#print axioms GrochowCatalogueThird.grid_point_avoiding_poles
