import EvenP5KernelBasis
import EvenP5InvCut

/-! Executable block intertwiners for the primary comparison. The equation
matrix uses the checked row-major kernel basis from the balanced-cut stage. -/

namespace EvenTI.PrimaryAlignment

open Matrix EvenTI.Contract
open scoped BigOperators

variable {K : Type} [Field K] [DecidableEq K] {a b : ℕ}

/-- Flatten the coefficient equations for `B X = X A` with target row first. -/
def intertwiningMatrix (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin b × Fin a) (Fin b × Fin a) K :=
  fun ij rs => (if ij.2 = rs.2 then B ij.1 rs.1 else 0) -
    (if ij.1 = rs.1 then A rs.2 ij.2 else 0)

def flattenMap (X : Matrix (Fin b) (Fin a) K) : Fin b × Fin a → K :=
  fun ij => X ij.1 ij.2

def unflattenMap (x : Fin b × Fin a → K) : Matrix (Fin b) (Fin a) K :=
  fun i j => x (i, j)

@[simp] theorem flattenMap_unflattenMap (x : Fin b × Fin a → K) :
    flattenMap (unflattenMap x) = x := by
  funext ⟨i, j⟩
  rfl

@[simp] theorem unflattenMap_flattenMap (X : Matrix (Fin b) (Fin a) K) :
    unflattenMap (flattenMap X) = X := rfl

theorem intertwiningMatrix_mulVec
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (X : Matrix (Fin b) (Fin a) K) :
    (intertwiningMatrix A B).mulVec (flattenMap X) = flattenMap (B * X - X * A) := by
  funext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, intertwiningMatrix, flattenMap, sub_mul,
    Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  have h₁ : (∑ r, ∑ s, (if j = s then B i r else 0) * X r s) =
      ∑ r, B i r * X r j := by
    simp [ite_mul, Finset.sum_ite_eq, eq_comm]
  have h₂ : (∑ r, ∑ s, (if i = r then A s j else 0) * X r s) =
      ∑ s, X i s * A s j := by
    rw [Finset.sum_comm]
    simp [ite_mul, Finset.sum_ite_eq, eq_comm, mul_comm]
  rw [h₁, h₂]

theorem intertwiningKernel_iff
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (X : Matrix (Fin b) (Fin a) K) :
    (intertwiningMatrix A B).mulVecLin (flattenMap X) = 0 ↔ B * X = X * A := by
  change (intertwiningMatrix A B).mulVec (flattenMap X) = 0 ↔ _
  rw [intertwiningMatrix_mulVec]
  constructor
  · intro h
    apply sub_eq_zero.mp
    ext i j
    exact congrFun h (i, j)
  · intro h
    rw [h, sub_self]
    rfl

/-- A basis generated from the actual pair of matrices. -/
def intertwinerBasis (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    List (Fin b × Fin a → K) :=
  rawKernelVectors (intertwiningMatrix A B) finProdFinEquiv finProdFinEquiv

section FiniteField

variable [Fintype K]

def boundedIntertwiners (F : FieldEncoding K) (budget : ℕ)
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    List (Matrix (Fin b) (Fin a) K) :=
  (linearChoices F (intertwinerBasis A B).get budget).map unflattenMap

theorem mem_boundedIntertwiners (F : FieldEncoding K) (budget : ℕ)
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (X : Matrix (Fin b) (Fin a) K) :
    X ∈ boundedIntertwiners F budget A B ↔ B * X = X * A ∧
      Fintype.card K ^ (intertwinerBasis A B).length ≤ budget := by
  let M := intertwiningMatrix A B
  have hInd : LinearIndependent K (intertwinerBasis A B).get :=
    rawKernelVectors_independent M finProdFinEquiv finProdFinEquiv
  have hSpan : Submodule.span K (Set.range (intertwinerBasis A B).get) = M.mulVecLin.ker :=
    rawKernelVectors_span M finProdFinEquiv finProdFinEquiv
  rw [boundedIntertwiners, linearChoices_eq_kernel F M.mulVecLin _ hInd hSpan]
  have h := mem_kernelChoices F M.mulVecLin (frameFromVectors M.mulVecLin _ hInd hSpan)
    budget (flattenMap X)
  rw [intertwiningKernel_iff] at h
  rw [← h]
  constructor
  · rintro hm
    obtain ⟨x, hx, hX⟩ := List.mem_map.mp hm
    have hx' : x = flattenMap X := by rw [← hX, flattenMap_unflattenMap]
    rwa [← hx']
  · intro hm
    exact List.mem_map.mpr ⟨flattenMap X, hm, unflattenMap_flattenMap X⟩

theorem boundedIntertwiners_length_le (F : FieldEncoding K) (budget : ℕ)
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    (boundedIntertwiners F budget A B).length ≤ budget := by
  simpa only [boundedIntertwiners, linearChoices, List.length_map] using
    coefficientChoices_length_le F (intertwinerBasis A B).length budget

def boundedUnits (F : FieldEncoding K) (budget : ℕ)
    (A B : Matrix (Fin a) (Fin a) K) : List (Matrix (Fin a) (Fin a) K) :=
  (boundedIntertwiners F budget A B).filter (fun X => (rawMatrixInverse X).isSome)

theorem mem_boundedUnits (F : FieldEncoding K) (budget : ℕ)
    (A B X : Matrix (Fin a) (Fin a) K) :
    X ∈ boundedUnits F budget A B ↔
      B * X = X * A ∧ Fintype.card K ^ (intertwinerBasis A B).length ≤ budget ∧ IsUnit X := by
  rw [boundedUnits, List.mem_filter, mem_boundedIntertwiners]
  have hi : (rawMatrixInverse X).isSome = true ↔ IsUnit X := by
    cases h : rawMatrixInverse X with
    | none => simp [Option.isSome, (rawMatrixInverse_eq_none_iff X).mp h]
    | some Y => simp [Option.isSome, ((rawMatrixInverse_eq_some_iff X Y).mp h).1]
  rw [hi, and_assoc]

theorem boundedUnits_length_le (F : FieldEncoding K) (budget : ℕ)
    (A B : Matrix (Fin a) (Fin a) K) :
    (boundedUnits F budget A B).length ≤ budget :=
  (List.length_filter_le _ _).trans (boundedIntertwiners_length_le F budget A B)

end FiniteField

#print axioms intertwiningMatrix_mulVec
#print axioms mem_boundedUnits
#print axioms boundedUnits_length_le

end EvenTI.PrimaryAlignment
