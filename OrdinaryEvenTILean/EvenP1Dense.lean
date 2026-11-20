import EvenReciprocalLaw
import EvenFlattening

namespace Mathproof.EvenTI.Reciprocal.Coverage

open EvenTI.Action Matrix

noncomputable section

variable {K : Type*} [Field K]
variable {R C D : Type*} [Fintype R] [Fintype C] [Fintype D]
variable [DecidableEq R] [DecidableEq C] [DecidableEq D]

/-- Matrices with mutually reciprocal row lists are exactly square units
written with possibly different coordinate sets on their two sides. -/
def basisPairsEquivUnits (left : R ≃ D) (right : C ≃ D) :
    BasisPairs K R C ≃ (Matrix D D K)ˣ where
  toFun A := {
    val := A.val.1.submatrix left.symm right.symm
    inv := A.val.2ᵀ.submatrix right.symm left.symm
    val_inv := by
      rw [Matrix.submatrix_mul_equiv, A.property.1, Matrix.submatrix_one_equiv]
    inv_val := by
      rw [Matrix.submatrix_mul_equiv, A.property.2, Matrix.submatrix_one_equiv] }
  invFun u :=
    ⟨(u.val.submatrix left right, (u.inv.submatrix right left)ᵀ), by
      rw [Matrix.transpose_transpose]
      constructor
      · rw [Matrix.submatrix_mul_equiv, u.val_inv, Matrix.submatrix_one_equiv]
      · rw [Matrix.submatrix_mul_equiv, u.inv_val, Matrix.submatrix_one_equiv]⟩
  left_inv A := by
    apply Subtype.ext
    apply Prod.ext
    · ext r c
      simp [Matrix.submatrix]
    · ext r c
      simp [Matrix.submatrix]
  right_inv u := by
    apply Units.ext
    ext i j
    simp [Matrix.submatrix]

private def unflatten {s n : Nat} (M : Matrix (Coord s n) (Coord s n) K) :
    Tensor K (s + s) n := fun c => M (cutEquiv.symm c).1 (cutEquiv.symm c).2

private theorem flatten_unflatten {s n : Nat} (M : Matrix (Coord s n) (Coord s n) K) :
    flatten (unflatten M) = M := by
  ext a b
  change M (cutEquiv.symm (cutEquiv (a, b))).1 (cutEquiv.symm (cutEquiv (a, b))).2 = _
  rw [Equiv.symm_apply_apply]

private theorem unflatten_flatten {s n : Nat} (T : Tensor K (s + s) n) :
    unflatten (flatten T) = T := by
  funext i
  change T (cutEquiv (cutEquiv.symm i)) = T i
  rw [Equiv.apply_symm_apply]

abbrev InvertibleCut (K : Type*) [Field K] (s n : Nat) :=
  {T : Tensor K (s + s) n // IsUnit (flatten T)}

def invertibleCutEquivUnits {s n : Nat} :
    InvertibleCut K s n ≃ (Matrix (Coord s n) (Coord s n) K)ˣ where
  toFun T := T.property.unit
  invFun u := ⟨unflatten u.val, by
    rw [flatten_unflatten]
    exact u.isUnit⟩
  left_inv T := by
    apply Subtype.ext
    exact (congrArg unflatten T.property.unit_spec).trans (unflatten_flatten T.val)
  right_inv u := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans (flatten_unflatten u.val)

/-- The literal uniform dense tensor law conditioned on the invertible cut
is the uniform reciprocal basis law. This equivalence uses the raw cut. -/
def invertibleCutEquivPairs {s n : Nat} (left : R ≃ Coord s n) (right : C ≃ Coord s n) :
    InvertibleCut K s n ≃ BasisPairs K R C :=
  invertibleCutEquivUnits.trans (basisPairsEquivUnits left right).symm

@[simp] theorem invertibleCutEquivPairs_primal {s n : Nat}
    (left : R ≃ Coord s n) (right : C ≃ Coord s n) (T : InvertibleCut K s n) :
    (invertibleCutEquivPairs left right T).val.1 = (flatten T.val).submatrix left right :=
  congrArg (fun M : Matrix (Coord s n) (Coord s n) K => M.submatrix left right)
    T.property.unit_spec

theorem invertibleCut_inverse_unique {s n : Nat} (T : InvertibleCut K s n) :
    T.property.unit.inv = (flatten T.val)⁻¹ := by
  let u := T.property.unit
  change u.inv = (flatten T.val)⁻¹
  have h : u.val = flatten T.val := T.property.unit_spec
  have hm : u.inv * flatten T.val = 1 := (congrArg (u.inv * ·) h).symm.trans u.inv_val
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp T.property
  calc
    _ = u.inv * (flatten T.val * (flatten T.val)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hm, Matrix.one_mul]

@[simp] theorem invertibleCutEquivPairs_dual {s n : Nat}
    (left : R ≃ Coord s n) (right : C ≃ Coord s n) (T : InvertibleCut K s n) :
    (invertibleCutEquivPairs left right T).val.2 =
      ((flatten T.val)⁻¹).transpose.submatrix left right := by
  change (T.property.unit.inv.submatrix right left)ᵀ = _
  rw [invertibleCut_inverse_unique]
  rfl

#print axioms invertibleCutEquivPairs
#print axioms invertibleCutEquivPairs_primal
#print axioms invertibleCutEquivPairs_dual

end
end Mathproof.EvenTI.Reciprocal.Coverage
