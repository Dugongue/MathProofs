import EvenP3RecipLowEscapeMax
import EvenP3RecipLowCount

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (matAnti rank_comp_pairing)
open Mathproof.Problem17TracePairing (tracePairing)

variable {K I : Type*} [Field K] [Fintype K] [Fintype I] [DecidableEq I] [Nonempty I]

/-- A cumulative bound for the number of low restricted-rank Fourier labels.
Counting all matrix representatives also bounds the number of distinct
characters in characteristic two. -/
theorem traceZero_label_rank_count_le (s : ℕ) :
    Nat.card {P : Matrix I I K //
      finrank K (labelForm traceKernel (tracePairing P)).range ≤ s} ≤
      Nat.card K ^ (4 * s + 2 * Fintype.card I + 9) := by
  classical
  let n := Fintype.card I
  have hn : 0 < n := Fintype.card_pos
  let t := (s + 2) / n
  let S := {P : Matrix I I K // finrank K (labelForm traceKernel (tracePairing P)).range ≤ s}
  let E : Matrix I I K ≃ₐ[K] End K (I → K) := Matrix.toLinAlgEquiv'
  let Y := {f : End K (I → K) // ∃ a : K, finrank K (f - a • LinearMap.id).range ≤ 2*t+1}
  let : Finite (End K (I → K)) :=
    Finite.of_injective E.symm E.symm.injective
  let : Finite Y := Finite.of_injective (fun f : Y => f.val) Subtype.val_injective
  let enc (P : S) : Y := by
    refine ⟨E P.val, ?_⟩
    obtain ⟨w, a, hw, ha⟩ := exists_scalar_shift_rank_le P.val
    have hr := restrict_rank_loss (squarePolar LinearMap.id (tracePairing P.val))
      (traceKernel (K := K) (I := I))
    have hfull : finrank K (squarePolar LinearMap.id (tracePairing P.val)).range =
        finrank K (matAnti P.val).range := by rw [trace_squarePolar_factor, rank_comp_pairing]
    rw [hfull, traceKernel_codim, mul_one] at hr
    have hRP : finrank K (matAnti P.val).range ≤ s + 2 := hr.trans (Nat.add_le_add_right P.property _)
    have hnw : w*n ≤ finrank K (matAnti P.val).range := by simpa [n, Nat.mul_comm] using hw
    have hwt : w ≤ t := (Nat.le_div_iff_mul_le hn).mpr (hnw.trans hRP)
    have hf : E (P.val - a • 1) = E P.val - a • LinearMap.id := by
      rw [map_sub, map_smul, map_one] <;> rfl
    refine ⟨a, ?_⟩
    rw [← hf]
    exact ha.trans (by omega)
  have henc : Function.Injective enc := fun X Y he =>
    Subtype.ext (E.injective (congrArg Subtype.val he))
  apply (Nat.card_le_card_of_injective enc henc).trans
  refine (card_near_scalar_le (K := K) (V := I → K) (2*t+1)).trans ?_
  rw [Module.finrank_pi]
  apply Nat.pow_le_pow_right (Nat.card_pos (α := K))
  have hd : t * n ≤ s+2 := Nat.div_mul_le_self _ _
  change 2*n*(2*t+1)+1 ≤ 4*s+2*n+9
  calc
    _ = 4*(t*n)+2*n+1 := by ring
    _ ≤ 4*(s+2)+2*n+1 := by omega
    _ = _ := by ring

#print axioms traceZero_label_rank_count_le

end Mathproof.EvenTI.Reciprocal.SquareLow
