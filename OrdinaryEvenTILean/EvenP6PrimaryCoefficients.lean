import CharpolyTable
import EvenDenseDecode
import Mathproof.Meta.P15FactorRefPoly20261007

namespace EvenTI.PrimaryProducer

open Polynomial Matrix
open scoped Polynomial
open EvenTI.Contract
open Mathproof.P15FactorRef20261007

variable {K : Type} [Field K] {n : ℕ}

/-- Ascending coefficients of the characteristic polynomial, using the
materialized Bird recurrence already verified in Problem 1.7. -/
def anchorCoefficients (A : Matrix (Fin n) (Fin n) K) : List K :=
  (Mathproof.Problem17CharpolyTable.coefficients n A).toList

@[simp] theorem anchorCoefficients_length (A : Matrix (Fin n) (Fin n) K) :
    (anchorCoefficients A).length = n + 1 := by
  simp [anchorCoefficients]

theorem anchorCoefficients_spec (A : Matrix (Fin n) (Fin n) K) :
    toPoly (anchorCoefficients A) = A.charpoly := by
  ext i
  rw [coeff_toPoly]
  by_cases hi : i < n + 1
  · have h := Mathproof.Problem17CharpolyTable.coefficients_eq A ⟨i, hi⟩
    simpa [anchorCoefficients, List.getD_eq_getElem, hi] using h
  · rw [List.getD_eq_default (anchorCoefficients A) 0 (by simpa using hi)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    omega

variable [Fintype K] [DecidableEq K]

/-- The actual finite-field digit equivalence supplies the scalar enumeration
and key for the checked list-polynomial operations. -/
def polynomialOps (digits : FieldEncoding K) : FOps K where
  zero := 0
  one := 1
  add := (· + ·)
  neg := Neg.neg
  mul := (· * ·)
  inv := Inv.inv
  beq x y := decide (x = y)
  key x := (digits x).val
  card := Fintype.card K
  elt i := if h : i < Fintype.card K then digits.symm ⟨i,h⟩ else 0

theorem polynomialOps_agree (digits : FieldEncoding K) : Agree (polynomialOps digits) where
  zero := rfl
  one := rfl
  add := fun _ _ => rfl
  neg := fun _ => rfl
  mul := fun _ _ => rfl
  inv := fun _ => rfl
  beq := fun _ _ => rfl
  key := fun _ _ h => digits.injective (Fin.ext h)
  card := rfl

#print axioms anchorCoefficients_spec
#print axioms polynomialOps_agree

end EvenTI.PrimaryProducer
