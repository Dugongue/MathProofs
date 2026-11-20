import EvenP6TensorWords

namespace EvenTI.CellPreparation

open scoped BigOperators TensorProduct
open Module

variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]
  {N : I → Type} [∀ i, Fintype (N i)]
  {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]

/-- Multiply two coefficient arrays in the tensor product of the mode
algebras using their local multiplication tables. -/
def multiplyCells (coeff : ∀ i, N i → N i → N i → K)
    (a b : ((i : I) → N i) → K) : ((i : I) → N i) → K :=
  fun p => ∑ q, ∑ r, a r * b q * ∏ i, coeff i (p i) (r i) (q i)

def unitCells (unitCoeff : ∀ i, N i → K) : ((i : I) → N i) → K :=
  fun p => ∏ i, unitCoeff i (p i)

theorem multiplyCells_eq (B : ∀ i, Basis (N i) K (A i))
    (coeff : ∀ i, N i → N i → N i → K)
    (h : ∀ i p r q, coeff i p r q = (B i).repr (B i r * B i q) p)
    (a b : ((i : I) → N i) → K) :
    denseDecode B (multiplyCells coeff a b) = denseDecode B a * denseDecode B b := by
  classical
  apply (denseDecode B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext p
  change multiplyCells coeff a b p =
    (Basis.piTensorProduct B).repr (denseDecode B a * denseDecode B b) p
  have hx (T : ((i : I) → N i) → K) :
      denseDecode B T = ∑ q, T q • (Basis.piTensorProduct B) q := by
    rw [denseDecode, Basis.equivFun_symm_apply]
  rw [hx a, hx b, Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Basis.piTensorProduct_apply, smul_mul_assoc, mul_smul_comm, map_smul,
    Finsupp.smul_apply, smul_eq_mul, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply, h, mul_assoc, Pi.mul_apply]
  ac_rfl

theorem unitCells_eq (B : ∀ i, Basis (N i) K (A i))
    (unitCoeff : ∀ i, N i → K) (h : ∀ i p, unitCoeff i p = (B i).repr 1 p) :
    denseDecode B (unitCells unitCoeff) = 1 := by
  apply (denseDecode B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext p
  change unitCells unitCoeff p = (Basis.piTensorProduct B).repr 1 p
  rw [PiTensorProduct.one_def, Basis.piTensorProduct_repr_tprod_apply]
  simp only [unitCells, h, Pi.one_apply]

#print axioms multiplyCells_eq
#print axioms unitCells_eq

end EvenTI.CellPreparation
