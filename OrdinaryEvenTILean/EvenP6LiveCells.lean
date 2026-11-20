import EvenP6BlockTable
import EvenP6CellsTensorMode
import EvenP6CellsReducedTensor
import EvenP6CellsBounds

/-! The actual products of primary field tables supply the joint tensor
table, the executable mode embeddings, and the computed compact field cells. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.CellProducer Module

variable {K : Type} [Field K] {d : ℕ} {width : Fin d → ℕ}
  {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]

abbrev LiveModeIndex (D : (i : Fin d) → Fin (width i) → Type) (i : Fin d) :=
  Σ v, D i v

abbrev LiveJointIndex (D : (i : Fin d) → Fin (width i) → Type) :=
  (i : Fin d) → LiveModeIndex D i

/-- Mixed-radix indexing of the exact tensor coordinate array. -/
def liveJointOrder (n : (i : Fin d) → Fin (width i) → ℕ) :
    Fin (∏ i : Fin d, ∑ v : Fin (width i), n i v) ≃ LiveJointIndex (fun i v => Fin (n i v)) :=
  finPiFinEquiv.symm.trans (Equiv.piCongrRight fun i => finSigmaFinEquiv.symm)

variable (t : ∀ i v, WordTable K (D i v))

def liveUnitCoeff (i : Fin d) : LiveModeIndex D i → K :=
  (blockTable (t i)).one

def liveMulCoeff (i : Fin d) : LiveModeIndex D i → LiveModeIndex D i → LiveModeIndex D i → K :=
  structureCoeff (blockTable (t i))

abbrev liveJointTable : WordTable K (LiveJointIndex D) :=
  tensorTable (liveUnitCoeff t) (liveMulCoeff t)

abbrev LiveJoint := TableWord (liveJointTable t)

section Model

variable {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)

noncomputable def liveModeBasis (i : Fin d) : Basis (LiveModeIndex D i) K ((v : Fin (width i)) → X i v) :=
  tableBasis (blockDecode (P i))

include P hOne hMul in
theorem liveUnitCoeff_eq (i : Fin d) (p : LiveModeIndex D i) :
    liveUnitCoeff t i p = (liveModeBasis P i).repr 1 p :=
  tableUnitCoeff_eq _ _ (blockTable_model (t i) (P i) (hOne i) (hMul i)).1 p

include P hOne hMul in
theorem liveMulCoeff_eq (i : Fin d) (p r q : LiveModeIndex D i) :
    liveMulCoeff t i p r q = (liveModeBasis P i).repr (liveModeBasis P i r * liveModeBasis P i q) p :=
  structureCoeff_eq _ _ (blockTable_model (t i) (P i) (hOne i) (hMul i)).2 p r q

include P hOne hMul in
theorem liveJoint_laws : WordTable.Laws (liveJointTable t) :=
  tensorTable_laws (liveModeBasis P) (liveUnitCoeff t) (liveMulCoeff t)
    (liveUnitCoeff_eq t P hOne hMul) (liveMulCoeff_eq t P hOne hMul)

variable [WordTable.Laws (liveJointTable t)]

include P hOne hMul in
theorem liveJoint_isReduced [Fintype K] [DecidableEq K] [∀ i v, Fintype (X i v)] : IsReduced (LiveJoint t) :=
  tensorTable_isReduced_of_field_products (liveModeBasis P) (liveUnitCoeff t) (liveMulCoeff t)
    (liveUnitCoeff_eq t P hOne hMul) (liveMulCoeff_eq t P hOne hMul)

theorem liveModeBasis_decode (i : Fin d) (x : LiveModeIndex D i → K) :
    (liveModeBasis P i).equivFun.symm x = blockDecode (P i) x := by
  apply (liveModeBasis P i).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext p
  change x p = (liveModeBasis P i).repr (blockDecode (P i) x) p
  unfold liveModeBasis tableBasis
  simp

/-- The mode embedding uses only per-factor coordinate encoders at
runtime. The chosen semantic basis occurs solely in its algebra laws. -/
def liveMode (i : Fin d) : ((v : Fin (width i)) → X i v) →ₐ[K] LiveJoint t := by
  let put (a : ∀ v, X i v) : LiveJoint t :=
    modeWord (liveUnitCoeff t) (liveMulCoeff t) i (fun p => (P i p.1).symm (a p.1) p.2)
  have laws : put 0 = 0 ∧ put 1 = 1 ∧
      (∀ x y, put (x + y) = put x + put y) ∧
      (∀ x y, put (x * y) = put x * put y) ∧
      (∀ r : K, put (algebraMap K (∀ v, X i v) r) = algebraMap K (LiveJoint t) r) := by
    let E := blockDecode (P i)
    have h := blockTable_model (t i) (P i) (hOne i) (hMul i)
    letI : WordTable.Laws (blockTable (t i)) := WordTable.laws_of_model _ E h.1 h.2
    let block := TableWord.modelEquiv _ E h.1 h.2
    have h1 : (liveModeBasis P i).equivFun.symm (blockTable (t i)).one = 1 :=
      (liveModeBasis_decode P i _).trans h.1
    have hm (a b : LiveModeIndex D i → K) :
        (liveModeBasis P i).equivFun.symm ((blockTable (t i)).multiply a b) =
          (liveModeBasis P i).equivFun.symm a * (liveModeBasis P i).equivFun.symm b := by
      simp only [liveModeBasis_decode]
      exact h.2 a b
    let f := (modeWordHom (liveModeBasis P) (liveUnitCoeff t) (liveMulCoeff t)
        (liveUnitCoeff_eq t P hOne hMul) (liveMulCoeff_eq t P hOne hMul) i (blockTable (t i)) h1 hm).comp
      block.symm.toAlgHom
    exact ⟨f.map_zero, f.map_one, f.map_add, f.map_mul, f.commutes⟩
  exact
    { toFun := put
      map_zero' := laws.1
      map_one' := laws.2.1
      map_add' := laws.2.2.1
      map_mul' := laws.2.2.2.1
      commutes' := laws.2.2.2.2 }

@[simp] theorem liveMode_apply (i : Fin d) (a : ∀ v, X i v) :
    liveMode t P hOne hMul i a =
      modeWord (liveUnitCoeff t) (liveMulCoeff t) i (fun p => (P i p.1).symm (a p.1) p.2) := rfl

end Model

section Cells

variable [Fintype K] [DecidableEq K] [WordTable.Laws (liveJointTable t)] {N : ℕ}
  (enum : Fin (Fintype.card K) ≃ K) (e : Fin N ≃ LiveJointIndex D)

def liveCoordinates : LiveJoint t ≃ₗ[K] (Fin N → K) :=
  TableWord.coordinates (liveJointTable t) e

def liveCells : List (LiveJoint t) :=
  rawCells enum (liveCoordinates t e)

theorem liveCells_length_le : (liveCells t enum e).length ≤ N := by
  haveI : Module.Finite K (LiveJoint t) := Module.Finite.of_basis (Basis.ofEquivFun (liveCoordinates t e))
  exact rawCells_length_le enum (liveCoordinates t e)

theorem liveCellCertificate [IsReduced (LiveJoint t)] (i : Fin (liveCells t enum e).length) :
    CellFieldCertificate (liveCoordinates t e) ((liveCells t enum e).get i) :=
  rawCell_field_of_reduced enum (liveCoordinates t e) i

end Cells

#print axioms liveJoint_laws
#print axioms liveJoint_isReduced
#print axioms liveMode
#print axioms liveCells_length_le
#print axioms liveCellCertificate

end EvenTI.CellPreparation
