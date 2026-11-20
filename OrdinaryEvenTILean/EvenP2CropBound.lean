import EvenNextAnchorSpecialized

namespace Mathproof.EvenOrdinaryTISingular
open Matrix Module EvenTI.Action
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {l r n : ℕ}

theorem quotient_finrank_ge_for_higher_order
    (R : Submodule K (Coord (r + 1) n → K))
    (hr : 2 ≤ r) (hn : 3 ≤ n) (hc : finrank K R ≤ n) :
    n ^ 2 + n ^ 2 ≤ finrank K ((Coord (r + 1) n → K) ⧸ R) := by
  have hsum := R.finrank_quotient_add_finrank
  rw [Module.finrank_fintype_fun_eq_card, cut_side_card] at hsum
  have hn' : n ≤ n ^ 2 := by
    simpa only [one_mul, pow_two] using (Nat.mul_le_mul_right n (show 1 ≤ n by omega))
  have hp : n ^ 3 ≤ n ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : n ^ 2 * 3 ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn
  have hm' : n ^ 2 + n ^ 2 + n ^ 2 ≤ n ^ 3 := by
    calc
      _ = n ^ 2 * 3 := by ring
      _ ≤ _ := hm.trans_eq (by ring)
  omega

/-- For order at least six, the exact-kernel crop bound is exponentially
small uniformly in the order of the physical tensor. -/
theorem uniformFraction_physicalPairCrop_small
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A₀ : DenseKernelFiber R S) (hr : 2 ≤ r) (hn : 3 ≤ n)
    (hc : finrank K R ≤ n)
    (P : Matrix (Fin (retainedImageWidth S i ell)) (Fin (retainedImageWidth R j rho)) K → Prop) :
    |uniformFraction (DenseKernelFiber R S) (fun A => P (physicalPairCrop R S i j ell rho A.val)) -
      uniformFraction (Matrix (Fin (retainedImageWidth S i ell))
        (Fin (retainedImageWidth R j rho)) K) P| ≤
      ((Fintype.card K : ℝ) ^ (n ^ 2))⁻¹ := by
  apply (uniformFraction_physicalPairCrop R S i j ell rho A₀ P).trans
  let q := (Fintype.card K : ℝ)
  let b := retainedImageWidth R j rho
  let s := finrank K ((Coord (r + 1) n → K) ⧸ R)
  change (q ^ b - 1) / (q ^ s * (q - 1)) ≤ (q ^ (n ^ 2))⁻¹
  have hq : 2 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 2 ≤ Fintype.card K from Fintype.one_lt_card)
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hb : b ≤ n ^ 2 := retainedImageWidth_le_square R j rho
  have hs : n ^ 2 + n ^ 2 ≤ s := quotient_finrank_ge_for_higher_order R hr hn hc
  rw [← one_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hq0 _) (by linarith)) (pow_pos hq0 _)).2
  rw [one_mul]
  calc
    (q ^ b - 1) * q ^ (n ^ 2) ≤ q ^ (n ^ 2) * q ^ (n ^ 2) :=
      mul_le_mul_of_nonneg_right ((sub_le_self _ zero_le_one).trans
        (pow_le_pow_right₀ hq1 hb)) (pow_nonneg hq0.le _)
    _ = q ^ (n ^ 2 + n ^ 2) := (pow_add q _ _).symm
    _ ≤ q ^ s := pow_le_pow_right₀ hq1 hs
    _ ≤ q ^ s * (q - 1) := le_mul_of_one_le_right (pow_nonneg hq0.le _) (by linarith)

theorem corank_le_dimension_of_gate (c n : ℕ) (h : Fintype.card K ^ c ≤ n) :
    c ≤ n :=
  (Nat.lt_pow_self (show 1 < Fintype.card K from Fintype.one_lt_card)).le.trans h

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_physicalPairCrop_small
#print axioms Mathproof.EvenOrdinaryTISingular.corank_le_dimension_of_gate
