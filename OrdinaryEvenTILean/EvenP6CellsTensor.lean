import EvenP6CellsCoded
import EvenP6CellsCompute
import EvenP6TensorAlgebra

/-! The actual tensor-product coefficient multiplication feeds the field-cell
splitter on its real dense storage words. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped TensorProduct BigOperators
open Module EvenTI.CellPreparation

variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]
  {N : I → Type} [∀ i, Fintype (N i)]

/-- The tensor field-cell algebra operates directly on coefficient arrays. -/
def tensorTable (unitCoeff : ∀ i, N i → K)
    (mulCoeff : ∀ i, N i → N i → N i → K) :
    WordTable K ((i : I) → N i) :=
  ⟨unitCells unitCoeff, multiplyCells mulCoeff⟩

section Model

variable {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]

theorem tensorTable_laws (B : ∀ i, Basis (N i) K (A i))
    (unitCoeff : ∀ i, N i → K)
    (mulCoeff : ∀ i, N i → N i → N i → K)
    (hOne : ∀ i p, unitCoeff i p = (B i).repr 1 p)
    (hMul : ∀ i p r q, mulCoeff i p r q = (B i).repr (B i r * B i q) p) :
    WordTable.Laws (tensorTable unitCoeff mulCoeff) :=
  WordTable.laws_of_model _ (denseDecode B)
    (unitCells_eq B unitCoeff hOne) (multiplyCells_eq B mulCoeff hMul)

noncomputable def tensorTable_decode (B : ∀ i, Basis (N i) K (A i))
    (unitCoeff : ∀ i, N i → K) (mulCoeff : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable unitCoeff mulCoeff)]
    (hOne : ∀ i p, unitCoeff i p = (B i).repr 1 p)
    (hMul : ∀ i p r q, mulCoeff i p r q = (B i).repr (B i r * B i q) p) :
    TableWord (tensorTable unitCoeff mulCoeff) ≃ₐ[K] (⨂[K] i, A i) :=
  TableWord.modelEquiv _ (denseDecode B) (unitCells_eq B unitCoeff hOne)
    (multiplyCells_eq B mulCoeff hMul)

end Model

/-- Embed one mode's coefficient word into the joint coefficient table.
The other slots use their actual unit words. -/
def modeWord (unitCoeff : ∀ i, N i → K) (mulCoeff : ∀ i, N i → N i → N i → K)
    (i : I) (x : N i → K) : TableWord (tensorTable unitCoeff mulCoeff) :=
  ⟨fun p => ∏ j, Function.update unitCoeff i x j (p j)⟩

theorem modeWord_decode {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (B : ∀ i, Basis (N i) K (A i))
    (unitCoeff : ∀ i, N i → K) (mulCoeff : ∀ i, N i → N i → N i → K)
    (hOne : ∀ i p, unitCoeff i p = (B i).repr 1 p) (i : I) (x : N i → K) :
    denseDecode B (modeWord unitCoeff mulCoeff i x).val =
      PiTensorProduct.singleAlgHom (R := K) i ((B i).equivFun.symm x) := by
  classical
  apply (denseDecode B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext p
  change (∏ j, Function.update unitCoeff i x j (p j)) =
    (Basis.piTensorProduct B).repr (PiTensorProduct.singleAlgHom (R := K) i _) p
  change _ = (Basis.piTensorProduct B).repr
    (PiTensorProduct.tprod K (MonoidHom.mulSingle A i ((B i).equivFun.symm x))) p
  rw [Basis.piTensorProduct_repr_tprod_apply]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same,
      ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  · simpa only [Function.update_of_ne h, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
      using hOne j (p j)

section Execute

variable [Fintype K] [DecidableEq K] [∀ i, DecidableEq (N i)] {d : ℕ}
  (unitCoeff : ∀ i, N i → K) (mulCoeff : ∀ i, N i → N i → N i → K)
  [WordTable.Laws (tensorTable unitCoeff mulCoeff)]

/-- An exact collection of the field idempotents, as actual input-width
vectors. The semantical tensor basis never runs in this computation. -/
def rawTensorCells (enum : Fin (Fintype.card K) ≃ K)
    (e : Fin d ≃ ((i : I) → N i)) :
    List (TableWord (tensorTable unitCoeff mulCoeff)) :=
  rawCells enum (TableWord.coordinates _ e)

variable {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
  {J : Type} [Fintype J] [DecidableEq J]
  {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

/-- Exact correspondence between the actual tensor multiplication-table
splitter and every genuine product-of-fields presentation. -/
theorem rawTensorCells_exact (enum : Fin (Fintype.card K) ≃ K)
    (e : Fin d ≃ ((i : I) → N i)) (B : ∀ i, Basis (N i) K (A i))
    (hOne : ∀ i p, unitCoeff i p = (B i).repr 1 p)
    (hMul : ∀ i p r q, mulCoeff i p r q = (B i).repr (B i r * B i q) p)
    (E : (⨂[K] i, A i) ≃ₐ[K] (∀ j, F j)) :
    ∃ order : Fin (rawTensorCells unitCoeff mulCoeff enum e).length ≃ J,
      ∀ i, E (denseDecode B ((rawTensorCells unitCoeff mulCoeff enum e).get i).val) =
        Pi.single (order i) 1 := by
  let D := tensorTable_decode B unitCoeff mulCoeff hOne hMul
  exact rawCells_exact enum (TableWord.coordinates _ e) (D.trans E)

end Execute

#print axioms rawTensorCells_exact
#print axioms modeWord_decode

end EvenTI.CellProducer
