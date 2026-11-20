import EvenNextRecipPolar
import EvenReciprocalRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal
open Mathproof.Problem17PolarAssembly (matAnti matAnti_apply matAnti_escape rank_comp_pairing)
open Mathproof.Problem17TracePairing

variable {K : Type*} [Field K]

theorem restrict_rank_loss {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (S : Submodule K V) :
    finrank K B.range ≤ finrank K (B.compl₁₂ S.subtype S.subtype).range +
      2 * finrank K (V ⧸ S) := by
  let s := LinearMap.lcomp K K S.subtype
  have hs : Function.Surjective s := fun f => LinearMap.exists_extend f
  have hk := s.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Subspace.dual_finrank_eq,
    Subspace.dual_finrank_eq] at hk
  have hq := S.finrank_quotient_add_finrank
  have hker : finrank K s.ker = finrank K (V ⧸ S) := by omega
  have hpre := precompose_rank_loss S.subtype B
  rw [Submodule.range_subtype] at hpre
  have hsub : finrank K V - finrank K S = finrank K (V ⧸ S) := by omega
  rw [hsub] at hpre
  have hpost := postcompose_rank_loss (LinearMap.comp B S.subtype) s
  have he : s.comp (LinearMap.comp B S.subtype) = B.compl₁₂ S.subtype S.subtype := rfl
  rw [he, hker] at hpost
  omega

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem finrank_comp_le_mid {A B C : Type*} [AddCommGroup A] [Module K A]
    [Module.Finite K A] [AddCommGroup B] [Module K B] [Module.Finite K B]
    [AddCommGroup C] [Module K C] (f : A →ₗ[K] B) (g : B →ₗ[K] C) :
    finrank K (g.comp f).range ≤ finrank K g.range := by
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

private theorem finrank_comp_le_start {A B C : Type*} [AddCommGroup A] [Module K A]
    [Module.Finite K A] [AddCommGroup B] [Module K B] [Module.Finite K B]
    [AddCommGroup C] [Module K C] (f : A →ₗ[K] B) (g : B →ₗ[K] C) :
    finrank K (g.comp f).range ≤ finrank K f.range := by
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem matAnti_finrank_ge (P : Matrix I I K) (hP : ∀ a : K, P ≠ a • (1 : Matrix I I K)) :
    Fintype.card I ≤ finrank K (matAnti P).range := by
  obtain ⟨a,b,_,h⟩ := matAnti_escape P hP
  have hle := (finrank_comp_le_start ((matAnti P).comp a) b).trans
    (finrank_comp_le_mid a (matAnti P))
  rw [h, LinearMap.range_id, finrank_top, Subspace.dual_finrank_eq, Module.finrank_pi] at hle
  exact hle

theorem trace_squarePolar_factor (P : Matrix I I K) :
    squarePolar LinearMap.id (tracePairing P) =
      LinearMap.comp ((tracePairing (K := K) (ι := I)).toDual
        tracePairing_nondegenerate).toLinearMap (matAnti P) := by
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro Y
  change (P * (X * Y + Y * X)).trace = ((P * X + X * P) * Y).trace
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add,
    ← Matrix.mul_assoc P X Y, Matrix.trace_mul_cycle' P Y X, ← Matrix.mul_assoc X P Y]

theorem nonscalar_label_finrank_ge (P : Matrix I I K)
    (hP : ∀ a : K, P ≠ a • (1 : Matrix I I K)) :
    Fintype.card I ≤ finrank K (squarePolar LinearMap.id (tracePairing P)).range := by
  rw [trace_squarePolar_factor, rank_comp_pairing]
  exact matAnti_finrank_ge P hP

/-- In odd characteristic the missing nonzero scalar labels also have full
single-block rank before restricting to the trace hyperplane. -/
theorem odd_label_finrank_ge [Nonempty I] (P : Matrix I I K)
    (hP : P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    Fintype.card I ≤ finrank K (squarePolar LinearMap.id (tracePairing P)).range := by
  by_cases hn : ∀ a : K, P ≠ a • (1 : Matrix I I K)
  · exact nonscalar_label_finrank_ge P hn
  · push Not at hn
    obtain ⟨a, ha⟩ := hn
    have ha0 : a ≠ 0 := by
      intro hz
      exact hP (by simp [ha, hz])
    have ha2 : a + a ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero h₂ ha0
    have hi : Function.Injective (matAnti P) := by
      intro X Y h
      have hf (X : Matrix I I K) : matAnti P X = (a + a) • X := by
        rw [matAnti_apply, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one, add_smul]
      rw [hf, hf] at h
      exact smul_right_injective _ ha2 h
    rw [trace_squarePolar_factor, rank_comp_pairing, LinearMap.finrank_range_of_inj hi,
      Module.finrank_matrix, Module.finrank_self, mul_one]
    exact Nat.le_mul_of_pos_right _ Fintype.card_pos

def traceKernel : Submodule K (Matrix I I K) := (Matrix.traceLinearMap (α := K) I K).ker

theorem traceKernel_codim [Nonempty I] :
    finrank K (Matrix I I K ⧸ (traceKernel (K := K) (I := I))) = 1 := by
  let tr := Matrix.traceLinearMap (α := K) I K
  have hr : tr.range = ⊤ := LinearMap.range_eq_top.mpr Matrix.trace_surjective
  change finrank K (Matrix I I K ⧸ tr.ker) = 1
  rw [tr.quotKerEquivRange.finrank_eq, hr, finrank_top, Module.finrank_self]

/-- Every nontrivial label on the trace-zero target has the needed
single-block polar rank lower bound. -/
theorem traceZero_label_rank [Nonempty I] (c : Module.Dual K (Matrix I I K))
    (hc : c.comp (traceKernel (K := K) (I := I)).subtype ≠ 0) :
    Fintype.card I - 2 ≤ finrank K (labelForm traceKernel c).range := by
  obtain ⟨P, hP⟩ := ((tracePairing (K := K) (ι := I)).toDual tracePairing_nondegenerate).surjective c
  change tracePairing P = c at hP
  have hns : ∀ a : K, P ≠ a • (1 : Matrix I I K) := by
    intro a ha
    apply hc
    rw [← hP, ha]
    apply LinearMap.ext
    intro x
    have hx : x.val.trace = 0 := x.property
    change ((a • (1 : Matrix I I K)) * x.val).trace = 0
    simp [Matrix.trace_smul, hx]
  have hfull := nonscalar_label_finrank_ge P hns
  have hres := restrict_rank_loss (squarePolar LinearMap.id c)
    (traceKernel (K := K) (I := I))
  rw [hP] at hfull
  rw [traceKernel_codim] at hres
  change Fintype.card I - 2 ≤
    finrank K ((squarePolar LinearMap.id c).compl₁₂ traceKernel.subtype traceKernel.subtype).range
  exact Nat.sub_le_iff_le_add.2 (hfull.trans (by simpa only [mul_one] using hres))

theorem traceZero_odd_label_rank [Nonempty I] (P : Matrix I I K)
    (hP : P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    Fintype.card I - 2 ≤ finrank K (labelForm traceKernel (tracePairing P)).range := by
  have hfull := odd_label_finrank_ge P hP h₂
  have hres := restrict_rank_loss (squarePolar LinearMap.id (tracePairing P))
    (traceKernel (K := K) (I := I))
  rw [traceKernel_codim] at hres
  change Fintype.card I - 2 ≤ finrank K
    ((squarePolar LinearMap.id (tracePairing P)).compl₁₂ traceKernel.subtype traceKernel.subtype).range
  exact Nat.sub_le_iff_le_add.2 (hfull.trans (by simpa only [mul_one] using hres))

#print axioms restrict_rank_loss
#print axioms nonscalar_label_finrank_ge
#print axioms traceZero_label_rank
#print axioms traceZero_odd_label_rank

end Mathproof.EvenTI.Reciprocal.Next


