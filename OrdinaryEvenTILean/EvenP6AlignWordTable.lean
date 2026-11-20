import EvenP6AlignCoordinates
import EvenP6CellsCoded

/-! Compute base-field word arithmetic for a simple primary field
directly from the actual anchor and its first-vector Krylov chart. -/

namespace EvenTI.PrimaryAlignment

open Matrix Polynomial
open EvenTI.Contract EvenTI.CellProducer

variable {K : Type} [Field K] [DecidableEq K] {m : ℕ}

def simpleWordTable (A R : Matrix (Fin m) (Fin m) K) : WordTable K (Fin m) where
  one := R.mulVec (firstVector m)
  multiply c d := R.mulVec ((scalarMatrix A c).mulVec ((krylovMatrix A).mulVec d))

def prepareSimpleWordTable (A : Matrix (Fin m) (Fin m) K) : Option (WordTable K (Fin m)) :=
  (rawMatrixInverse (krylovMatrix A)).map (simpleWordTable A)

theorem prepareSimpleWordTable_eq_some (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (hd : p.natDegree = m) (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) :
    prepareSimpleWordTable A = some (simpleWordTable A (krylovMatrix A)⁻¹) := by
  unfold prepareSimpleWordTable
  rw [(rawMatrixInverse_eq_some_iff _ _).mpr ⟨krylovMatrix_isUnit p hp hd A hA, rfl⟩]
  rfl

/-- The arithmetic installed in the actual word table has exactly the
one and multiplication of (K[X]/p) in its monomial basis. -/
theorem simpleWordTable_model (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m)
    (A R : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0) (hR : R * krylovMatrix A = 1) :
    let D := (fieldBasis p hp hd).equivFun.symm
    D (simpleWordTable A R).one = 1 ∧
      ∀ c d, D ((simpleWordTable A R).multiply c d) = D c * D d := by
  let D := (fieldBasis p hp hd).equivFun.symm
  have restore (u : AdjoinRoot p) : D (R.mulVec (fieldVector p A hA u)) = u := by
    have h := krylovMatrix_mulVec p hp hd A hA (D.symm u)
    change (krylovMatrix A).mulVec (D.symm u) = fieldVector p A hA (D (D.symm u)) at h
    rw [D.apply_symm_apply] at h
    rw [← h, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec, D.apply_symm_apply]
  constructor
  · change D (R.mulVec (firstVector m)) = 1
    simpa only [fieldVector_one] using restore 1
  · intro c d
    change D (R.mulVec ((scalarMatrix A c).mulVec ((krylovMatrix A).mulVec d))) = D c * D d
    rw [scalarMatrix_eq_rootAction p hp hd A hA, krylovMatrix_mulVec p hp hd A hA,
      ← fieldVector_mul]
    exact restore (D c * D d)

theorem prepareSimpleWordTable_model (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m)
    (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0)
    (T : WordTable K (Fin m)) (hT : prepareSimpleWordTable A = some T) :
    let D := (fieldBasis p hp hd).equivFun.symm
    D T.one = 1 ∧ ∀ c d, D (T.multiply c d) = D c * D d := by
  unfold prepareSimpleWordTable at hT
  cases hR : rawMatrixInverse (krylovMatrix A) with
  | none => simp [hR] at hT
  | some R =>
    have h := Option.some.inj (by simpa only [hR, Option.map_some] using hT :
      some (simpleWordTable A R) = some T)
    rw [← h]
    exact simpleWordTable_model p hp hd A R hA (rawMatrixInverse_mul hR).2

theorem prepareSimpleWordTable_laws (p : K[X]) (hp : p.Monic) (hd : p.natDegree = m)
    (A : Matrix (Fin m) (Fin m) K) (hA : aeval A p = 0)
    (T : WordTable K (Fin m)) (hT : prepareSimpleWordTable A = some T) :
    WordTable.Laws T := by
  obtain ⟨hOne,hMul⟩ := prepareSimpleWordTable_model p hp hd A hA T hT
  exact WordTable.laws_of_model T (fieldBasis p hp hd).equivFun.symm hOne hMul

#print axioms prepareSimpleWordTable_eq_some
#print axioms prepareSimpleWordTable_model
#print axioms prepareSimpleWordTable_laws

end EvenTI.PrimaryAlignment
