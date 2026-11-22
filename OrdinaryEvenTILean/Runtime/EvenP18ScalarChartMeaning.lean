import EvenP17ScalarActiveWords
import Mathproof.Meta.Problem18IMPMatrixMemory20261001

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace EvenTI.P18Scalar

open Matrix EvenTI.Part8 EvenTI.Contract EvenTI.P17Scalar
open Mathproof.Problem18IMPMatrixMemory20261001 (index_lt)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The literal nonzero-chart-entry predicate computed by the paid stencil
driver is exactly cropped scalarity. The source data consist only of the
actual chart field digits, native row-site indices, and CRT residue words. -/
theorem chartEntryResidues_iff_scalarCrop
    (D : FieldEncoding K) {r p c : ℕ}
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (N : Matrix (Fin r) (Fin r) K) (U : (Matrix (Fin r) (Fin r) K)ˣ)
    (L : BaseUnitLog K) (site : Fin r → Fin c)
    (x : Fin c → ZMod (Fintype.card K-1)) (reference : Fin r)
    (hRef : ∃ j, (U.inv*P) reference j ≠ 0)
    (hLeft : Q*P=1)
    (hConj : N=U.val*Matrix.diagonal (fun i => (L.decode (x (site i)) : K))*U.inv)
    (hInvariant : N*P=P*(Q*N*P))
    (chart sites coords : List ℕ)
    (hChart : ∀ (i : Fin r) (j : Fin p),
      chart.getD (i.val*p+j.val) 0=(D ((U.inv*P) i j)).val)
    (hSites : ∀ i : Fin r, sites.getD i.val 0=(site i).val)
    (hCoords : ∀ i : Fin c, coords.getD i.val 0=(x i).val) :
    (∀ k < r*p, chart.getD k 0 ≠ (D 0).val →
      coords.getD (sites.getD (k/p) 0) 0=coords.getD (site reference).val 0) ↔
      ∃ a : K, Q*N*P=a • (1 : Matrix (Fin p) (Fin p) K) := by
  have hp : 0 < p := by obtain ⟨j,_⟩ := hRef; exact Nat.zero_lt_of_lt j.isLt
  have he :
      (∀ k < r*p, chart.getD k 0 ≠ (D 0).val →
        coords.getD (sites.getD (k/p) 0) 0=coords.getD (site reference).val 0) ↔
      ∀ i, (∃ j, (U.inv*P) i j ≠ 0) →
        (x (site i)).val=(x (site reference)).val := by
    constructor
    · intro h i hi
      obtain ⟨j,hj⟩ := hi
      have hNonzero : chart.getD (i.val*p+j.val) 0 ≠ (D 0).val := by
        rw [hChart]
        intro hz
        exact hj (D.injective (Fin.ext hz))
      have hh := h (i.val*p+j.val) (index_lt i j) hNonzero
      have hQuot : (i.val*p+j.val)/p=i.val := by
        rw [Nat.mul_comm i.val p,Nat.mul_add_div hp,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
      rw [hQuot,hSites,hCoords,hCoords] at hh
      exact hh
    · intro h k hk hz
      let i : Fin r := ⟨k/p,(Nat.div_lt_iff_lt_mul hp).mpr hk⟩
      let j : Fin p := ⟨k%p,Nat.mod_lt k hp⟩
      have hIndex : i.val*p+j.val=k := by
        simpa only [i,j,Nat.mul_comm] using Nat.div_add_mod k p
      have hNonzero : (U.inv*P) i j ≠ 0 := by
        intro hZero
        apply hz
        rw [← hIndex,hChart,hZero]
      have hh := h i ⟨j,hNonzero⟩
      change coords.getD (sites.getD i.val 0) 0=coords.getD (site reference).val 0
      rw [hSites,hCoords,hCoords]
      exact hh
  exact he.trans (scalarCrop_iff_activeExponentWords P Q N U L site x
    reference hRef hLeft hConj hInvariant).symm

#print axioms chartEntryResidues_iff_scalarCrop
end EvenTI.P18Scalar
