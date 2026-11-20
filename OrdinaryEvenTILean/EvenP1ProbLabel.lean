import EvenP1ProbRows
import EvenP1RectExposure
import Mathlib.LinearAlgebra.Dual.Basis

namespace Mathproof.EvenTI.Reciprocal.PartOne

open Matrix Module LinearMap
open scoped Matrix BigOperators
open Mathproof.EvenTI.Reciprocal.Next (traceKernel)
open Mathproof.Problem17TracePairing (tracePairing tracePairing_nondegenerate)

noncomputable section

variable {K I B L J : Type*} [Field K]
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    [Fintype L] [Fintype J]

def productAnnMatrix (U : L → Matrix I B K) (j : L) : Ann U →ₗ[K] Matrix I I K where
  toFun v := U j * rectDual.symm v.val
  map_add' u v := by
    change U j * rectDual.symm (u.val + v.val) =
        U j * rectDual.symm u.val + U j * rectDual.symm v.val
    rw [map_add, Matrix.mul_add]
  map_smul' c v := by
    change U j * rectDual.symm (c • v.val) = c • (U j * rectDual.symm v.val)
    rw [map_smul, Matrix.mul_smul]

def productAnn (U : L → Matrix I B K) (j : L) :
    Ann U →ₗ[K] traceKernel (K := K) (I := I) :=
  (productAnnMatrix U j).codRestrict _ fun v => ann_mul_trace U v j

def coeff (z : Dual K (J → traceKernel (K := K) (I := I))) (U : L → Matrix I B K) :
    (J → Ann U) →ₗ[K] (L → K) :=
  LinearMap.pi fun j => z.comp (LinearMap.pi fun t => (productAnn U j).comp (LinearMap.proj t))

theorem coeff_apply (z : Dual K (J → traceKernel (K := K) (I := I)))
    (U : L → Matrix I B K) (v : J → Ann U) (j : L) :
    coeff z U v j = z (fun t => productAnn U j (v t)) := rfl

theorem coeff_zero_of_comp_zero [DecidableEq L] {a : ℕ}
    (z : Dual K (J → traceKernel (K := K) (I := I)))
    (U : L → Matrix I B K) (V : Fin a → J → Ann U)
    (h : z.comp (selectedRows U V) = 0) :
    ∀ i, coeff z U (V i) = 0 := by
  intro i
  funext j
  rw [coeff_apply]
  have hx : selectedRows U V (Pi.single i (Pi.single j 1)) =
      fun t => productAnn U j (V i t) := by
    funext t
    apply Subtype.ext
    rw [selectedRows_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [Pi.single_eq_same, productAnn, productAnnMatrix]
      · intro k _ hki
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hki]
      · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · simp
  rw [← hx]
  exact LinearMap.congr_fun h _

/-- A nonzero label on the tuple picks a nontrivial single coordinate
represented by a nonscalar trace-pairing matrix. -/
theorem exists_nonscalar_component [DecidableEq J]
    (z : Dual K (J → traceKernel (K := K) (I := I))) (hz : z ≠ 0) :
    ∃ (t : J) (P : Matrix I I K), (∀ c : K, P ≠ c • 1) ∧
      (tracePairing P).comp traceKernel.subtype =
        z.comp (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t) := by
  have h : ∃ t,
      z.comp (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t) ≠ 0 := by
    by_contra! hall
    apply hz
    apply LinearMap.pi_ext'
    intro t
    rw [hall, LinearMap.zero_comp]
  obtain ⟨t, ht⟩ := h
  obtain ⟨c, hc⟩ := LinearMap.exists_extend (z.comp (LinearMap.single K
    (fun _ : J => traceKernel (K := K) (I := I)) t))
  obtain ⟨P, hP⟩ := ((tracePairing (K := K) (ι := I)).toDual tracePairing_nondegenerate).surjective c
  change tracePairing P = c at hP
  have he : (tracePairing P).comp traceKernel.subtype =
      z.comp (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t) := by
    rw [hP]
    exact hc
  refine ⟨t, P, ?_, he⟩
  intro a ha
  apply ht
  rw [← hc, ← hP, ha]
  apply LinearMap.ext
  intro x
  have hx : x.val.trace = 0 := x.property
  change ((a • (1 : Matrix I I K)) * x.val).trace = 0
  simp [Matrix.trace_smul, hx]

theorem coeff_rank_ge_of_component [DecidableEq J] [DecidableEq L]
    (z : Dual K (J → traceKernel (K := K) (I := I))) (U : L → Matrix I B K)
    (t : J) (P : Matrix I I K)
    (hP : (tracePairing P).comp traceKernel.subtype =
      z.comp (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t)) :
    Part1.coefficientRank P U ≤ finrank K (coeff z U).range := by
  let S := primalSpan U
  let f := Fintype.linearCombination K (fun j => S.mkQ (P * U j))
  let ds := S.dualQuotEquivDualAnnihilator
  let ev := (Pi.basisFun K L).dualBasis.equivFun
  let one := LinearMap.single K (fun _ : J => Ann U) t
  have h : (coeff z U).comp one = ev.toLinearMap.comp (f.dualMap.comp ds.symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    funext j
    change coeff z U (one v) j = ev (f.dualMap (ds.symm v)) j
    rw [coeff_apply, Basis.dualBasis_equivFun, Pi.basisFun_apply]
    have hv : (fun s => productAnn U j (one v s)) =
        (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t)
          (productAnn U j v) := by
      funext s
      by_cases hs : s = t
      · subst s
        simp [one, LinearMap.single_apply]
      · simp [one, LinearMap.single_apply, Pi.single_eq_of_ne hs]
    rw [hv]
    change (z.comp (LinearMap.single K (fun _ : J => traceKernel (K := K) (I := I)) t))
      (productAnn U j v) = ds.symm v (f (Pi.single j 1))
    rw [← hP]
    change (P * (U j * rectDual.symm v.val)).trace = ds.symm v (f (Pi.single j 1))
    rw [← Matrix.mul_assoc, ← rectDual_apply, LinearEquiv.apply_symm_apply]
    dsimp only [f]
    rw [Fintype.linearCombination_apply_single, one_smul]
    rfl
  have hcomp : (f.dualMap.comp ds.symm.toLinearMap).range = f.dualMap.range := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have hr := Submodule.finrank_mono (LinearMap.range_comp_le_range one (coeff z U))
  rw [h, LinearMap.range_comp, hcomp, LinearEquiv.finrank_map_eq,
    LinearMap.finrank_range_dualMap_eq_finrank_range] at hr
  have hfspan : f.range = Submodule.span K (Set.range fun j => S.mkQ (P * U j)) :=
    Fintype.range_linearCombination K _
  rw [hfspan] at hr
  exact hr

#print axioms coeff_zero_of_comp_zero
#print axioms exists_nonscalar_component
#print axioms coeff_rank_ge_of_component

end
end Mathproof.EvenTI.Reciprocal.PartOne
