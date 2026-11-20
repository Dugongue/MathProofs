import EvenLiveSingularBlock

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical
open Mathproof.EvenOrdinaryTISingular Module

noncomputable section

private theorem fraction_nonneg {X : Type*} (E : X → Prop) :
    0 ≤ uniformFraction X E := by unfold uniformFraction; positivity

theorem fraction_condition_le_two {X : Type*} [Finite X] [Nonempty X]
    (G E : X → Prop) (hHalf : Nat.card X ≤ 2 * Nat.card {x : X // G x}) :
    uniformFraction {x : X // G x} (fun x => E x.val) ≤ 2 * uniformFraction X E := by
  let n := (Nat.card X : ℝ)
  let g := (Nat.card {x : X // G x} : ℝ)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Nat.card_pos
  have hH : n ≤ 2 * g := by dsimp [n, g]; exact_mod_cast hHalf
  have hg : 0 < g := by linarith
  let F (x : {x : {x : X // G x} // E x.val}) : {x : X // E x} := ⟨x.val.val, x.property⟩
  have hc : Nat.card {x : {x : X // G x} // E x.val} ≤ Nat.card {x : X // E x} :=
    Nat.card_le_card_of_injective F (fun _ _ h => Subtype.ext (Subtype.ext
      (congrArg (fun z : {x : X // E x} => z.val) h)))
  apply (div_le_iff₀ hg).mpr
  calc
    _ ≤ (Nat.card {x : X // E x} : ℝ) := by exact_mod_cast hc
    _ = uniformFraction X E * n := by
      change _ = (_ / n) * n
      rw [div_mul_cancel₀ _ hn.ne']
    _ ≤ uniformFraction X E * (2*g) :=
      mul_le_mul_of_nonneg_left hH (fraction_nonneg E)
    _ = _ := by ring

theorem half_independent_tuples {K V A : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Fintype V] [Fintype A]
    (hDim : Fintype.card A + 1 ≤ finrank K V) :
    Nat.card (A → V) ≤ 2 * Nat.card {x : A → V // LinearIndependent K x} := by
  let b := Fintype.card A
  let e := Fintype.equivFin A
  let p : (A → V) ≃ (Fin b → V) := Equiv.arrowCongr e (Equiv.refl V)
  have hInd (x : A → V) : LinearIndependent K x ↔ LinearIndependent K (p x) := by
    change LinearIndependent K x ↔ LinearIndependent K (x ∘ e.symm)
    exact ⟨fun h => h.comp e.symm e.symm.injective, fun h => by
      have hh := h.comp e e.injective
      simpa [Function.comp_def] using hh⟩
  let ep : {x : A → V // LinearIndependent K x} ≃ {x : Fin b → V // LinearIndependent K x} :=
    p.subtypeEquiv hInd
  rw [Nat.card_congr p, Nat.card_congr ep]
  let q := (Fintype.card K : ℝ)
  have hq : 2 ≤ q := by dsimp [q]; exact_mod_cast (Fintype.one_lt_card (α := K))
  have hBound := dependent_column_fraction_le (K := K) (V := V) b (by omega)
  change 1 - (Nat.card {x : Fin b → V // LinearIndependent K x} : ℝ) /
    (Fintype.card (Fin b → V) : ℝ) ≤
    (q^b - 1) / (q^(finrank K V) * (q - 1)) at hBound
  have hPower : q^(b+1) ≤ q ^ finrank K V :=
    pow_le_pow_right₀ (by linarith) hDim
  have hTwo : 2 * q^b ≤ q ^ finrank K V := by
    refine (mul_le_mul_of_nonneg_right hq (by positivity)).trans ?_
    rwa [← pow_succ']
  have hDen : 0 < q^(finrank K V) * (q - 1) := mul_pos
    (pow_pos (by linarith) _) (by linarith)
  have hfrac : (q^b - 1) / (q^(finrank K V) * (q - 1)) ≤ 1/2 := by
    apply (div_le_div_iff₀ hDen (by norm_num : (0:ℝ) < 2)).mpr
    rw [one_mul]
    exact (by linarith : (q^b - 1) * 2 ≤ q ^ finrank K V).trans
      (le_mul_of_one_le_right (by positivity) (by linarith))
  have hOne := hBound.trans hfrac
  have hRat : (1:ℝ)/2 ≤ (Nat.card {x : Fin b → V // LinearIndependent K x} : ℝ) /
      Fintype.card (Fin b → V) := by linarith
  have hc : (0:ℝ) < Fintype.card (Fin b → V) := by positivity
  have hcount := (le_div_iff₀ hc).mp hRat
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast (by linarith : (Fintype.card (Fin b → V) : ℝ) ≤
    2 * (Nat.card {x : Fin b → V // LinearIndependent K x} : ℝ))

/-- Conditioning both stages on independent rows costs at most four,
provided each stage retains at least half of its own uniform law. -/
theorem twice_conditioned_average_le_four {X : Type*} [Fintype X] [Nonempty X]
    {Y : X → Type*} [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]
    (P : X → Prop) [Fintype {x : X // P x}]
    (Q : ∀ x, Y x → Prop) (E : ∀ x, Y x → Prop)
    (hP : Nat.card X ≤ 2 * Nat.card {x : X // P x})
    (hQ : ∀ x : {x : X // P x}, Nat.card (Y x.val) ≤ 2 * Nat.card {y : Y x.val // Q x.val y}) :
    (∑ x : {x : X // P x}, uniformFraction {y : Y x.val // Q x.val y}
      (fun y => E x.val y.val)) / (Nat.card {x : X // P x} : ℝ) ≤
      4 * ((∑ x : X, uniformFraction (Y x) (E x)) / (Fintype.card X : ℝ)) := by
  let g : X → ℝ := fun x => uniformFraction (Y x) (E x)
  let e : {x : X // P x} ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  have hs : (∑ x : {x : X // P x}, g x.val) ≤ ∑ x : X, g x := by
    change (∑ x, g (e x)) ≤ ∑ x, g x
    rw [← Finset.sum_map Finset.univ e g]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => fraction_nonneg _)
  let n := (Nat.card X : ℝ)
  let p := (Nat.card {x : X // P x} : ℝ)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Nat.card_pos
  have hP' : n ≤ 2*p := by dsimp [n, p]; exact_mod_cast hP
  have hp : 0 < p := by linarith
  have hsum : 0 ≤ ∑ x, g x := Finset.sum_nonneg (fun _ _ => fraction_nonneg _)
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ x : {x : X // P x}, 2 * g x.val :=
      Finset.sum_le_sum (fun x _ => fraction_condition_le_two _ _ (hQ x))
    _ ≤ 2 * ∑ x, g x := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 2 * ((∑ x, g x) / n) * n := by
      rw [mul_assoc, div_mul_cancel₀ _ hn.ne']
    _ ≤ 2 * ((∑ x, g x) / n) * (2*p) :=
      mul_le_mul_of_nonneg_left hP' (mul_nonneg (by norm_num) (div_nonneg hsum hn.le))
    _ = _ := by
      have hnCard : n = (Fintype.card X : ℝ) := by simp [n, Nat.card_eq_fintype_card]
      rw [hnCard]
      change _ = 4 * ((∑ x, g x) / (Fintype.card X : ℝ)) * p
      ring

#print axioms half_independent_tuples
#print axioms twice_conditioned_average_le_four

end
end Mathproof.EvenTI.Reciprocal.Coverage
