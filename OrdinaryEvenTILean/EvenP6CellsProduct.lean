import EvenP6CellsCompact

/-! The computed field factors give the global algebra equivalence. Its
forward map is the stored coordinate projection and its inverse is the
sum of decoded corner elements. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped BigOperators

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] [DecidableEq A] {d : ℕ}

abbrev ProducedCell (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (i : Fin (rawCells enum C).length) : Type :=
  CompactCell C ((rawCells enum C).get i)

def compactProductPack (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (x : A) : ∀ i, ProducedCell enum C i :=
  fun i => compactPack C ((rawCells enum C).get i) x

def compactProductUnpack (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (w : ∀ i, ProducedCell enum C i) : A :=
  ∑ i, cellDecoder C ((rawCells enum C).get i) (w i).val

/-- The exact generated field product, with executable maps in both directions. -/
def compactProductEquiv (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    [cert : ∀ i : Fin (rawCells enum C).length, CellFieldCertificate C ((rawCells enum C).get i)] :
    A ≃ₐ[K] (∀ i, ProducedCell enum C i) where
  toFun := compactProductPack enum C
  invFun := compactProductUnpack enum C
  left_inv x := by
    unfold compactProductPack compactProductUnpack
    simp only [compactPack_decode]
    rw [← Finset.sum_mul]
    have h : (∑ i : Fin (rawCells enum C).length, (rawCells enum C).get i) = 1 := by
      change (∑ i : Fin (rawCells enum C).length, (rawCells enum C)[i.val]) = 1
      rw [Fin.sum_univ_getElem]
      exact (rawCells_partition enum C).2.2
    rw [h, one_mul]
  right_inv w := by
    funext i
    apply compactDecode_injective C ((rawCells enum C).get i)
    change cellDecoder C ((rawCells enum C).get i)
      (compactPack C ((rawCells enum C).get i) (compactProductUnpack enum C w)).val =
        cellDecoder C ((rawCells enum C).get i) (w i).val
    unfold compactProductUnpack
    rw [compactPack_decode, Finset.mul_sum, Finset.sum_eq_single i]
    · exact cellDecode_fixed C (cert i).idem (w i).val
    · intro j _ hj
      change (rawCells enum C).get i * cellDecode C ((rawCells enum C).get j) (w j).val = 0
      calc
        _ = (rawCells enum C).get i * ((rawCells enum C).get j *
            cellDecode C ((rawCells enum C).get j) (w j).val) := by
          rw [cellDecode_fixed C (cert j).idem]
        _ = 0 := by
          rw [← mul_assoc, get_orthogonal (rawCells_partition enum C) i j hj.symm, zero_mul]
    · exact fun h => (h (Finset.mem_univ i)).elim
  map_add' x y := by
    funext i
    exact (compactAlgebraMap C ((rawCells enum C).get i) (AlgHom.id K A)).map_add x y
  map_mul' x y := by
    funext i
    exact (compactAlgebraMap C ((rawCells enum C).get i) (AlgHom.id K A)).map_mul x y
  commutes' r := by
    funext i
    exact (compactAlgebraMap C ((rawCells enum C).get i) (AlgHom.id K A)).commutes r

#print axioms compactProductEquiv

end EvenTI.CellProducer
