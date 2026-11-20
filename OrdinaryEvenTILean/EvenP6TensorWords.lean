import EvenCells
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace EvenTI.CellPreparation

open scoped BigOperators TensorProduct
open Module Matrix EvenOrdinaryTI.Cells

variable {K I J : Type} [Field K] [Fintype I] [DecidableEq I] [Fintype J]
  {N : I → Type} [∀ i, Fintype (N i)]
  {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
  {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

/-- Evaluate one cell directly from a dense coefficient array and its
computed mode-to-cell basis values. -/
def evaluateCell (T : ((i : I) → N i) → K) (j : J)
    (basisValue : ∀ i, N i → F j) : F j :=
  ∑ p : (i : I) → N i, algebraMap K (F j) (T p) * ∏ i, basisValue i (p i)

noncomputable def denseDecode (B : ∀ i, Basis (N i) K (A i)) :
    (((i : I) → N i) → K) ≃ₗ[K] (⨂[K] i, A i) :=
  (Basis.piTensorProduct B).equivFun.symm

private theorem pureCoordinates (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j))
    (j : J) (a : ∀ i, A i) :
    E (PiTensorProduct.tprod K a) j = ∏ i, embedding E j i (a i) := by
  simpa using cell_multiplication E a 1 j

theorem evaluateCell_eq (B : ∀ i, Basis (N i) K (A i))
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) (T : ((i : I) → N i) → K) (j : J)
    (basisValue : ∀ i, N i → F j) (hv : ∀ i a, basisValue i a = embedding E j i (B i a)) :
    evaluateCell T j basisValue = E (denseDecode B T) j := by
  classical
  have hx : denseDecode B T = ∑ p, T p • (Basis.piTensorProduct B) p := by
    rw [denseDecode, Basis.equivFun_symm_apply]
  rw [hx, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  have hm := E.toLinearEquiv.map_smul (T p) ((Basis.piTensorProduct B) p)
  change E (T p • (Basis.piTensorProduct B) p) = T p • E ((Basis.piTensorProduct B) p) at hm
  rw [hm, Pi.smul_apply, Algebra.smul_def, Basis.piTensorProduct_apply, pureCoordinates]
  simp only [hv]

/-- This is the full coefficient action of the mode multiplication tables.
It also applies when several modes use one shared unit or its inverse. -/
def wordAction (M : ∀ i, Matrix (N i) (N i) K) (T : ((i : I) → N i) → K) :
    ((i : I) → N i) → K :=
  fun p => ∑ q, (∏ i, M i (p i) (q i)) * T q

theorem denseDecode_wordAction (B : ∀ i, Basis (N i) K (A i)) (a : ∀ i, A i)
    (M : ∀ i, Matrix (N i) (N i) K)
    (hm : ∀ i p q, M i p q = (B i).repr (a i * B i q) p)
    (T : ((i : I) → N i) → K) :
    denseDecode B (wordAction M T) = PiTensorProduct.tprod K a * denseDecode B T := by
  classical
  apply (denseDecode B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext p
  change wordAction M T p =
    (Basis.piTensorProduct B).repr (PiTensorProduct.tprod K a * denseDecode B T) p
  have hx : denseDecode B T = ∑ q, T q • (Basis.piTensorProduct B) q := by
    rw [denseDecode, Basis.equivFun_symm_apply]
  rw [hx, Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro q _
  simp only [hm, Basis.piTensorProduct_apply, mul_smul_comm, map_smul,
    Finsupp.smul_apply, smul_eq_mul, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  exact mul_comm _ _

#print axioms evaluateCell_eq
#print axioms denseDecode_wordAction

end EvenTI.CellPreparation
