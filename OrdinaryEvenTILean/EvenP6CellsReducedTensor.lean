import EvenP6CellsTensor
import EvenP6CellsProduct
import EvenP6CellsCompactModels
import EvenCellsSplit

/-! Assemble the live tensor-product multiplication table with the field
splitter and the compact, invertible coordinate arithmetic. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped TensorProduct
open Module EvenOrdinaryTI.CellSplit

variable {K I : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] {N : I → Type} [∀ i, Fintype (N i)]
  {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
  {d : ℕ}

theorem tensorTable_isReduced (B : ∀ i, Basis (N i) K (A i))
    (u : ∀ i, N i → K) (m : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable u m)] [IsReduced (⨂[K] i, A i)]
    (hu : ∀ i p, u i p = (B i).repr 1 p)
    (hm : ∀ i p r q, m i p r q = (B i).repr (B i r * B i q) p) :
    IsReduced (TableWord (tensorTable u m)) := by
  let E := tensorTable_decode B u m hu hm
  constructor
  intro x hx
  apply E.injective
  rw [map_zero]
  exact IsReduced.eq_zero _ (hx.map E.toRingHom)

section Powers

variable {L : I → Type} [∀ i, Fintype (L i)] {G : ∀ i, L i → Type}
  [∀ i j, Field (G i j)] [∀ i j, Algebra K (G i j)] [∀ i j, Fintype (G i j)]

/-- The variable-order tensor product of mode field products is reduced,
so its actual coefficient word algebra admits the verified field split. -/
theorem tensorTable_isReduced_of_field_products
    (B : ∀ i, Basis (N i) K (∀ j, G i j))
    (u : ∀ i, N i → K) (m : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable u m)]
    (hu : ∀ i p, u i p = (B i).repr 1 p)
    (hm : ∀ i p r q, m i p r q = (B i).repr (B i r * B i q) p) :
    IsReduced (TableWord (tensorTable u m)) := by
  letI : IsReduced (⨂[K] i, (∀ j, G i j)) := isReduced_tensor_of_products
  exact tensorTable_isReduced B u m hu hm

end Powers

variable [∀ i, DecidableEq (N i)]

theorem tensorCell_field_certificate
    (u : ∀ i, N i → K) (m : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable u m)] [IsReduced (TableWord (tensorTable u m))]
    (enum : Fin (Fintype.card K) ≃ K) (e : Fin d ≃ ((i : I) → N i))
    (i : Fin (rawTensorCells u m enum e).length) :
    CellFieldCertificate (TableWord.coordinates (tensorTable u m) e)
      ((rawTensorCells u m enum e).get i) :=
  rawCell_field_of_reduced enum (TableWord.coordinates (tensorTable u m) e) i

#print axioms tensorTable_isReduced_of_field_products
#print axioms tensorCell_field_certificate

end EvenTI.CellProducer
