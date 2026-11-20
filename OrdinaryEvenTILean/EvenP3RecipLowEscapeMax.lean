import EvenP3RecipLowEscape
import EvenP3RecipLowQuotientScalar
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped Matrix BigOperators
open Matrix Module LinearMap Submodule
open Mathproof.Problem17PolarAssembly (matAnti)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private abbrev pairVectors {t : ℕ} (P : End K V) (u : Fin t → V) : Fin t ⊕ Fin t → V :=
  Sum.elim u (fun i => P (u i))

private def stepIndex {t : ℕ} :
    Fin (t+1) ⊕ Fin (t+1) → (Fin t ⊕ Fin t) ⊕ Fin 2 :=
  Sum.elim (Fin.lastCases (.inr 0) (fun i => .inl (.inl i)))
    (Fin.lastCases (.inr 1) (fun i => .inl (.inr i)))

private theorem stepIndex_injective (t : ℕ) : Function.Injective (@stepIndex t) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j <;>
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simpa [stepIndex, Fin.lastCases_last, Fin.lastCases_castSucc] using h

set_option backward.isDefEq.respectTransparency false in
private theorem extendEscape {t : ℕ} (P : End K V) (u : Fin t → V)
    (hi : LinearIndependent K (pairVectors P u)) (x : V)
    (h : LinearIndependent K (Submodule.Quotient.mk
      (p := Submodule.span K (Set.range (pairVectors P u))) ∘ ![x, P x])) :
    LinearIndependent K (pairVectors P (Fin.snoc u x)) := by
  let S := Submodule.span K (Set.range (pairVectors P u))
  let f : Fin t ⊕ Fin t → S := fun i => ⟨pairVectors P u i, Submodule.subset_span ⟨i,rfl⟩⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp S.subtype hi
  have he := (hf.sumElim_of_quotient ![x, P x] h).comp stepIndex (stepIndex_injective t)
  have hEq : pairVectors P (Fin.snoc u x) =
      Sum.elim (fun i => (f i).val) ![x,P x] ∘ stepIndex := by
    funext i
    rcases i with i | i <;> induction i using Fin.lastCases <;>
      simp [pairVectors, Function.comp_def, f, stepIndex]
  rw [hEq]
  exact he

variable [Module.Finite K V]

private theorem maximalEscape (P : End K V) :
    ∃ (t : ℕ) (u : Fin t → V),
      LinearIndependent K (pairVectors P u) ∧
      ∀ x : V, let S := Submodule.span K (Set.range (pairVectors P u))
        S.mkQ x ≠ 0 → S.mkQ (P x) ∈ K ∙ S.mkQ x := by
  classical
  let ExistsPair (t : ℕ) := ∃ u : Fin t → V, LinearIndependent K (pairVectors P u)
  have h0 : ExistsPair 0 := ⟨Fin.elim0, linearIndependent_empty_type⟩
  let t := Nat.findGreatest ExistsPair (finrank K V)
  obtain ⟨u, hu⟩ := Nat.findGreatest_spec (Nat.zero_le _) h0
  refine ⟨t, u, hu, ?_⟩
  intro x S hx
  by_contra hn
  have hpair : LinearIndependent K (Submodule.Quotient.mk (p := S) ∘ ![x, P x]) := by
    have hswap : LinearIndependent K ![S.mkQ (P x), S.mkQ x] :=
      linearIndependent_fin2.mpr ⟨hx, fun a ha =>
        hn (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
    have hswap' := hswap.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _)
    convert hswap' using 1
    funext i
    fin_cases i <;> rfl
  have hnext := extendEscape P u hu x hpair
  have hsize := hnext.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hsize
  have hle : t + 1 ≤ finrank K V := by omega
  have ht : t + 1 ≤ t := Nat.le_findGreatest hle ⟨Fin.snoc u x, hnext⟩
  omega

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem matrix_rank_of_independent_pairs (P : Matrix I I K) {t : ℕ}
    (u : Fin t → I → K) (h : LinearIndependent K (pairVectors (Matrix.toLinAlgEquiv' P) u)) :
    Fintype.card I * t ≤ finrank K (matAnti P).range := by
  let U : Matrix I (Fin t) K := fun i j => u j i
  have hmul (i : I) (j : Fin t) : (P * U) i j = ∑ k : I, P i k * u j k := rfl
  have hcomb (x : (Fin t → K) × (Fin t → K)) :
      (∑ j : Fin t ⊕ Fin t, Sum.elim x.1 x.2 j • pairVectors (Matrix.toLinAlgEquiv' P) u j) =
        U *ᵥ x.1 + (P * U) *ᵥ x.2 := by
    rw [Fintype.sum_sum_type]
    ext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, pairVectors, Sum.elim_inl, Sum.elim_inr, Matrix.toLinAlgEquiv'_apply,
      Matrix.toLin'_apply]
    simp only [hmul]
    simp only [U, mul_comm]
  have hi : Function.Injective (fun x : (Fin t → K) × (Fin t → K) =>
      U *ᵥ x.1 + (P * U) *ᵥ x.2) := by
    intro x y hxy
    have hh : (∑ j : Fin t ⊕ Fin t, Sum.elim (x.1-y.1) (x.2-y.2) j •
        pairVectors (Matrix.toLinAlgEquiv' P) u j) = 0 := by
      have he : (fun j : Fin t ⊕ Fin t => Sum.elim (x.1-y.1) (x.2-y.2) j) =
          fun j => Sum.elim x.1 x.2 j - Sum.elim y.1 y.2 j := by
        funext j
        cases j <;> rfl
      simp_rw [he, sub_smul, Finset.sum_sub_distrib, hcomb, hxy, sub_self]
    have hz := Fintype.linearIndependent_iff.mp h _ hh
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · exact sub_eq_zero.mp (hz (.inl j))
    · exact sub_eq_zero.mp (hz (.inr j))
  simpa only [Fintype.card_fin] using anticommutator_rank_ge_of_escape P U hi

/-- The low-rank labels lie within a low-rank matrix of the scalar line.
The proof finds a maximal collection of independent source-image pairs. -/
theorem exists_scalar_shift_rank_le (P : Matrix I I K) :
    ∃ (t : ℕ) (a : K),
      Fintype.card I * t ≤ finrank K (matAnti P).range ∧
      finrank K (Matrix.toLinAlgEquiv' (P - a • 1)).range ≤ 2*t+1 := by
  classical
  let E : Matrix I I K ≃ₐ[K] End K (I → K) := Matrix.toLinAlgEquiv'
  obtain ⟨t, u, hu, hm⟩ := maximalEscape (E P)
  let S := Submodule.span K (Set.range (pairVectors (E P) u))
  have hS : finrank K S = 2*t := by
    simpa [S, two_mul] using finrank_span_eq_card hu
  have hr := matrix_rank_of_independent_pairs P u hu
  by_cases hq : 1 < finrank K ((I → K) ⧸ S)
  · obtain ⟨a, ha⟩ := scalar_shift_range_le_of_no_escape (E P) S hq hm
    refine ⟨t, a, hr, ?_⟩
    have he : E (P - a • 1) = E P - a • LinearMap.id := by
      rw [map_sub, map_smul, map_one] <;> rfl
    change finrank K (E (P - a • 1)).range ≤ _
    rw [he]
    exact (Submodule.finrank_mono ha).trans (by omega)
  · refine ⟨t, 0, hr, ?_⟩
    have hdim := S.finrank_quotient_add_finrank
    exact (LinearMap.finrank_range_le (E (P - 0 • 1))).trans (by omega)

#print axioms exists_scalar_shift_rank_le

end Mathproof.EvenTI.Reciprocal.SquareLow
