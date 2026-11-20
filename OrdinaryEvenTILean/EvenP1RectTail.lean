import EvenP1RectExposure
import EvenP1RectCount
import EvenP1ProbKernel

namespace Mathproof.EvenTI.Reciprocal.Part1

open Matrix Module
open Mathproof.EvenOrdinaryTISingular (uniformFraction uniformFraction_equiv
  uniformFraction_linear_surjective)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)
open scoped Matrix BigOperators

private theorem uniformFraction_prod_eq_mean {A C : Type*} [Fintype A] [Fintype C]
    [Nonempty C] (P : A → C → Prop) :
    uniformFraction (A × C) (fun p => P p.1 p.2) =
      (∑ a, uniformFraction C (P a)) / (Fintype.card A : ℝ) := by
  let e : {x : A × C // P x.1 x.2} ≃ Σ a : A, {c : C // P a c} :=
    { toFun := fun x => ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
      invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      left_inv := by rintro ⟨⟨a,c⟩,h⟩; rfl
      right_inv := by rintro ⟨a,c,h⟩; rfl }
  classical
  unfold uniformFraction
  rw [Nat.card_congr e, Nat.card_sigma, Nat.card_prod,
    Nat.card_eq_fintype_card (α := A), Nat.cast_mul, Nat.cast_sum, ← Finset.sum_div]
  rw [div_div, mul_comm (Nat.card C : ℝ)]

private theorem uniformFraction_prod_fst {A C : Type*} [Fintype A] [Fintype C]
    [Nonempty C] (P : A → Prop) :
    uniformFraction (A × C) (fun p => P p.1) = uniformFraction A P := by
  let e : {x : A × C // P x.1} ≃ {a : A // P a} × C :=
    { toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
      invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
      left_inv := by rintro ⟨⟨a,c⟩,h⟩; rfl
      right_inv := by rintro ⟨⟨a,h⟩,c⟩; rfl }
  have h : (Nat.card C : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := C)).ne'
  unfold uniformFraction
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ h]

private theorem average_constant {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    (∑ _ : A, c) / (Fintype.card A : ℝ) = c := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀ _ hA]

variable {K I B L : Type*} [Field K] [Fintype K]
  [Fintype I] [DecidableEq I] [Fintype B] [Fintype L]

private theorem projectedRank_perturb (Z : Matrix I I K) (U : L → Matrix I B K)
    (u : I → K) (v : Module.Dual K (I → K)) (z : L → B → K)
    (hv : v u = 0) (hvZ : v (Z *ᵥ u) = 1) :
    projectedRank v Z (perturb U u z) =
      finrank K (Submodule.span K (Set.range fun j =>
        (rowSpan v U).mkQ (rowProjection v (Z * U j) + z j))) := by
  let C (S : Submodule K (B → K)) (ys : L → B → K) :=
    finrank K (Submodule.span K (Set.range fun j => S.mkQ (ys j)))
  change C (rowSpan v (perturb U u z)) (fun j => rowProjection v (Z * (perturb U u z) j))
    = C (rowSpan v U) (fun j => rowProjection v (Z * U j) + z j)
  rw [rowSpan_perturb U u v z hv]
  congr
  funext j
  exact projected_perturb Z U u v z hvZ j

private theorem uniformFraction_projectedRank_perturb_le (Z : Matrix I I K)
    (U : L → Matrix I B K) (u : I → K) (v : Module.Dual K (I → K))
    (hv : v u = 0) (hvZ : v (Z *ᵥ u) = 1)
    (r : Nat) (hrL : r ≤ Fintype.card L) (hrB : Fintype.card L + r ≤ Fintype.card B) :
    uniformFraction (L → B → K) (fun z => projectedRank v Z (perturb U u z) ≤ r) ≤
      (2 : ℝ)^Fintype.card L /
        (Fintype.card K : ℝ)^((Fintype.card L - r) * (Fintype.card B - Fintype.card L - r)) := by
  classical
  let S := rowSpan v U
  let f : (L → B → K) →ₗ[K] (L → ((B → K) ⧸ S)) :=
    LinearMap.pi (fun j : L => S.mkQ.comp (LinearMap.proj j))
  have hf : Function.Surjective f := by
    intro y
    choose z hz using (fun j => S.mkQ_surjective (y j))
    exact ⟨z, funext hz⟩
  let anchor : L → B → K := fun j => rowProjection v (Z * U j)
  let E : (L → B → K) ≃ (L → B → K) := Equiv.addLeft anchor
  let Q (ys : L → ((B → K) ⧸ S)) := finrank K (Submodule.span K (Set.range ys)) ≤ r
  have h₀ : (fun z => projectedRank v Z (perturb U u z) ≤ r) = fun z => Q (f (E z)) := by
    funext z
    rw [projectedRank_perturb Z U u v z hv hvZ]
    rfl
  haveI : Fintype ((B → K) ⧸ S) := Fintype.ofFinite _
  have hD := S.finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hD
  have hS : finrank K S ≤ Fintype.card L := by
    exact finrank_range_le_card (R := K) (fun j => rowProjection v (U j))
  have hD' : Fintype.card B - Fintype.card L ≤ finrank K ((B → K) ⧸ S) := by omega
  have hrD : r ≤ finrank K ((B → K) ⧸ S) := by omega
  rw [h₀, uniformFraction_equiv E (fun z => Q (f z)),
    uniformFraction_linear_surjective f hf Q]
  apply (uniformFraction_rank_le (K := K) (V := ((B → K) ⧸ S)) r hrL hrD).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply pow_le_pow_right₀ (by exact_mod_cast (Fintype.card_pos (α := K)))
  exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hD' r)

/-- For a nonscalar label, low rank of its actual quotient coefficient rows
has an exponentially small uniform fraction. -/
theorem uniformFraction_coefficientRank_le (Z : Matrix I I K)
    (hZ : ∀ a : K, Z ≠ a • 1)
    (r : Nat) (hrL : r ≤ Fintype.card L) (hrB : Fintype.card L + r ≤ Fintype.card B) :
    uniformFraction (L → Matrix I B K) (fun U => coefficientRank Z U ≤ r) ≤
      (2 : ℝ)^Fintype.card L /
        (Fintype.card K : ℝ)^((Fintype.card L - r) * (Fintype.card B - Fintype.card L - r)) := by
  classical
  obtain ⟨u, v, hv, hvZ⟩ := exists_escape_functional Z hZ
  let p : (L → Matrix I B K) → Prop := fun U => coefficientRank Z U ≤ r
  have hprod := uniformFraction_prod_fst (C := L → B → K) p
  rw [← hprod, ← uniformFraction_equiv (perturbEquiv u)
    (fun x : (L → Matrix I B K) × (L → B → K) => p x.1)]
  have hle : uniformFraction ((L → Matrix I B K) × (L → B → K))
       (fun x => p ((perturbEquiv u x).1)) ≤
      uniformFraction ((L → Matrix I B K) × (L → B → K))
        (fun x => projectedRank v Z (perturb x.1 u x.2) ≤ r) := by
    apply uniformFraction_le_of_imp
    intro x hx
    exact (projectedRank_le_coefficientRank v Z _).trans hx
  apply hle.trans
  rw [uniformFraction_prod_eq_mean (fun (U : L → Matrix I B K) (z : L → B → K) =>
    projectedRank v Z (perturb U u z) ≤ r)]
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun U _ => ?_)) (by positivity)).trans_eq
    (average_constant (A := L → Matrix I B K) _)
  exact uniformFraction_projectedRank_perturb_le Z U u v hv hvZ r hrL hrB

#print axioms uniformFraction_coefficientRank_le

end Mathproof.EvenTI.Reciprocal.Part1
