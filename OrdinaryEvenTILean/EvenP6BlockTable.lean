import EvenP6CellsCoded
import Mathlib.LinearAlgebra.StdBasis

namespace EvenTI.CellPreparation

open EvenTI.CellProducer Module

variable {K L : Type} [Field K] {D : L → Type}

/-- Multiplication in a mode algebra is componentwise on its live primary
fields and its individually labelled base-field coordinates. -/
def blockTable (T : ∀ i, WordTable K (D i)) : WordTable K (Sigma D) where
  one p := (T p.1).one p.2
  multiply a b p := (T p.1).multiply
    (fun i => a ⟨p.1,i⟩) (fun i => b ⟨p.1,i⟩) p.2

variable {A : L → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]

def blockDecode (P : ∀ i, (D i → K) ≃ₗ[K] A i) :
    ((Sigma D) → K) ≃ₗ[K] ((i : L) → A i) where
  toFun v i := P i (fun j => v ⟨i,j⟩)
  invFun v i := (P i.1).symm (v i.1) i.2
  left_inv v := by
    funext p
    exact congrFun ((P p.1).symm_apply_apply (fun j => v ⟨p.1,j⟩)) p.2
  right_inv v := by
    funext i
    exact (P i).apply_symm_apply (v i)
  map_add' v w := funext fun i => (P i).map_add (fun j => v ⟨i,j⟩) (fun j => w ⟨i,j⟩)
  map_smul' c v := funext fun i => (P i).map_smul c (fun j => v ⟨i,j⟩)

theorem blockTable_model (T : ∀ i, WordTable K (D i))
    (P : ∀ i, (D i → K) ≃ₗ[K] A i)
    (h1 : ∀ i, P i (T i).one = 1)
    (hm : ∀ i a b, P i ((T i).multiply a b) = P i a * P i b) :
    blockDecode P (blockTable T).one = 1 ∧
    ∀ a b, blockDecode P ((blockTable T).multiply a b) = blockDecode P a * blockDecode P b := by
  exact ⟨funext h1, fun a b => funext (fun i => hm i (fun p => a ⟨i,p⟩) (fun p => b ⟨i,p⟩))⟩

section Basis

variable {R : Type} [Fintype R] [DecidableEq R]
  {B : Type} [CommRing B] [Algebra K B] (T : WordTable K R)
  (E : (R → K) ≃ₗ[K] B)

noncomputable def tableBasis : Basis R K B :=
  (Pi.basisFun K R).map E

def structureCoeff (p r q : R) : K :=
  T.multiply (Pi.single r 1) (Pi.single q 1) p

theorem structureCoeff_eq
    (hm : ∀ a b, E (T.multiply a b) = E a * E b) (p r q : R) :
    structureCoeff T p r q = (tableBasis E).repr (tableBasis E r * tableBasis E q) p := by
  change _ = (Pi.basisFun K R).repr
    (E.symm ((E ((Pi.basisFun K R) r)) * (E ((Pi.basisFun K R) q)))) p
  rw [Pi.basisFun_apply, Pi.basisFun_apply, ← hm, E.symm_apply_apply, Pi.basisFun_repr]
  rfl

theorem tableUnitCoeff_eq (h1 : E T.one = 1) (p : R) :
    T.one p = (tableBasis E).repr 1 p := by
  rw [← h1]
  change _ = (Pi.basisFun K R).repr (E.symm (E T.one)) p
  rw [E.symm_apply_apply, Pi.basisFun_repr]

end Basis

#print axioms blockTable_model
#print axioms structureCoeff_eq
#print axioms tableUnitCoeff_eq

end EvenTI.CellPreparation
