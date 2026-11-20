import EvenP3SingularNormalPair
import EvenP3SingularEnlarged
import EvenP3SingularLiteralCrop
import EvenP3SingularFiberMean

namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped BigOperators TensorProduct Matrix
open Matrix Module EvenTI.Action EvenTI.AnchorCovariance
open Mathproof.EvenOrdinaryTISingular.RectPolar
noncomputable section

variable {K : Type*} [Field K] {n a b k m : ℕ}

private def primal : Index a k → Option (Fin a ⊕ Fin k)
  | .inl i => some (.inr i)
  | .inr (.inl i) => some (.inl i)
  | .inr (.inr _) => none

private def dual : Index a k → Option (Fin a ⊕ Fin k)
  | .inl _ => none
  | .inr (.inl i) => some (.inl i)
  | .inr (.inr i) => some (.inr i)

private def enlargedEntry (X : Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K)
    (i j : Index a k) : K :=
  match primal i, dual j with
  | some x, some y => X x y
  | _, _ => 0

/-- Linear embedding induced by the primal and dual maps that realize a
singular pairing as the restriction of a perfect pairing. -/
def enlargedPair (a k : ℕ) :
    Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K →ₗ[K] Matrix (Index a k) (Index a k) K where
  toFun X := enlargedEntry X
  map_add' X Y := by
    ext i j
    change enlargedEntry (X+Y) i j = enlargedEntry X i j + enlargedEntry Y i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [enlargedEntry,primal,dual,Matrix.add_apply]
  map_smul' c X := by
    ext i j
    change enlargedEntry (c • X) i j = c • enlargedEntry X i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [enlargedEntry,primal,dual,Matrix.smul_apply]

private theorem enlargedPair_supported
    (X : Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K) :
    Supported (enlargedPair a k X) := by
  intro i j h
  change (match primal i, dual j with
    | some x, some y => X x y
    | _, _ => 0) = 0
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp_all [primal, dual, allowed]

def enlargedProjection (ell : Coord 2 n → K) (P : NormalPair ell a k) :
    (Coord 2 n → K) →ₗ[K] Matrix (Index a k) (Index a k) K :=
  (enlargedPair a k).comp (orient ell P).toLinearMap

theorem enlargedProjection_supported (ell : Coord 2 n → K) (P : NormalPair ell a k)
    (x : Coord 2 n → K) :
    Supported (enlargedProjection ell P x) :=
  enlargedPair_supported (orient ell P x)

theorem enlargedProjection_live (ell : Coord 2 n → K) (P : NormalPair ell a k)
    (x : Coord 2 n → K) :
    (enlargedProjection ell P x).submatrix live live = liveProjection ell P x := rfl

variable {ell rho : Coord 2 n → K}
variable (L : NormalPair ell a k) (R : NormalPair rho b m)

def enlargedMatrix :
    ((Coord 2 n → K) ⊗[K] (Coord 2 n → K)) →ₗ[K]
      Matrix (Index a k × Index b m) (Index a k × Index b m) K :=
  (kroneckerLinearEquiv (Index a k) (Index a k) (Index b m) (Index b m) K).toLinearMap.comp
    (TensorProduct.map (enlargedProjection ell L) (enlargedProjection rho R))

def liveMatrix :
    ((Coord 2 n → K) ⊗[K] (Coord 2 n → K)) →ₗ[K]
      Matrix (Fin a × Fin b) (Fin a × Fin b) K :=
  (kroneckerLinearEquiv (Fin a) (Fin a) (Fin b) (Fin b) K).toLinearMap.comp
    (TensorProduct.map (liveProjection ell L) (liveProjection rho R))

theorem enlargedMatrix_supported (U : (Coord 2 n → K) ⊗[K] (Coord 2 n → K)) :
    PairSupported (enlargedMatrix L R U) := by
  intro i j h
  induction U using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul x y =>
    change (kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (enlargedProjection ell L) (enlargedProjection rho R) (x ⊗ₜ[K] y))) i j = _
    rw [TensorProduct.map_tmul, kroneckerLinearEquiv_tmul]
    change enlargedProjection ell L x i.1 j.1 * enlargedProjection rho R y i.2 j.2 = 0
    by_cases hl : allowed i.1 j.1
    · rw [enlargedProjection_supported rho R y _ _ (fun hr => h ⟨hl,hr⟩), mul_zero]
    · rw [enlargedProjection_supported ell L x _ _ hl, zero_mul]

theorem enlargedMatrix_crop (U : (Coord 2 n → K) ⊗[K] (Coord 2 n → K)) :
    crop (enlargedMatrix L R U) = liveMatrix L R U := by
  induction U using TensorProduct.induction_on with
  | zero => simp [crop]
  | add x y hx hy => rw [map_add, map_add, ← hx, ← hy] <;> rfl
  | tmul x y =>
    change (kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (enlargedProjection ell L) (enlargedProjection rho R) (x ⊗ₜ[K] y))).submatrix
        (Prod.map live live) (Prod.map live live) =
      kroneckerLinearEquiv _ _ _ _ K
        (TensorProduct.map (liveProjection ell L) (liveProjection rho R) (x ⊗ₜ[K] y))
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, kroneckerLinearEquiv_tmul,
      kroneckerLinearEquiv_tmul]
    rfl

theorem liveMatrix_eq_liveJoint
    (S T : Submodule K (Coord 2 n → K))
    (hL : cropImage S (liveProjection ell L) ≤ TraceSpace K a)
    (hR : cropImage T (liveProjection rho R) ≤ TraceSpace K b)
    (A : DenseKernelFiber T S) :
    let U := matrixTensorEquiv K (Coord 2 n) (Coord 2 n) (flatten (l:=2) (r:=2) A.val)
    (partialTraceLeft (liveMatrix L R U ^ 2),
      partialTraceRight (liveMatrix L R U ^ 2)) =
      (liveJoint (liveProjection ell L) (liveProjection rho R) hL hR A).val := by
  let U := matrixTensorEquiv K (Coord 2 n) (Coord 2 n) (flatten (l:=2) (r:=2) A.val)
  have hLiteral := rawLiveCrop_embedded_eq T S (liveProjection ell L) (liveProjection rho R) A
  let X := rawLiveCrop T S (liveProjection ell L) (liveProjection rho R) A
  have hJ : PolarOperator.embed (subspaceTensor hL hR X) = liveMatrix L R U := by
    change kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (TraceSpace K a).subtype (TraceSpace K b).subtype
        (TensorProduct.map (Submodule.inclusion hL) (Submodule.inclusion hR) X)) = _
    rw [TensorProduct.map_map]
    change kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (cropImage S (liveProjection ell L)).subtype
        (cropImage T (liveProjection rho R)).subtype X) = _
    exact congrArg (kroneckerLinearEquiv (Fin a) (Fin a) (Fin b) (Fin b) K) hLiteral
  change (partialTraceLeft (liveMatrix L R U ^ 2), partialTraceRight (liveMatrix L R U ^ 2)) = _
  rw [← hJ]
  rfl

def rawEnlarged (A : Tensor K 4 n) : Matrix (Index a k × Index b m) (Index a k × Index b m) K :=
  enlargedMatrix L R (matrixTensorEquiv K _ _ (flatten (l:=2) (r:=2) A))

/-- The singular form choices supply their own live widths. On the exact
raw fiber, the corresponding two enlarged anchor spectra are the spectra
from the measured live crop, with exactly twice the respective radical
dimensions as padding. -/
theorem quadratic_charpoly_actual
    (S T : Submodule K (Coord 2 n → K))
    (hL : cropImage S (liveProjection ell L) ≤ TraceSpace K a)
    (hR : cropImage T (liveProjection rho R) ≤ TraceSpace K b)
    (A : DenseKernelFiber T S) :
    let Z := rawEnlarged L R A.val
    let J := liveJoint (liveProjection ell L) (liveProjection rho R) hL hR A
    (partialTraceLeft (Z ^ 2)).charpoly =
        Polynomial.X ^ (2*k) * (leftCoordinate J).charpoly ∧
    (partialTraceRight (Z ^ 2)).charpoly =
        Polynomial.X ^ (2*m) * (rightCoordinate J).charpoly := by
  dsimp only
  let U := matrixTensorEquiv K (Coord 2 n) (Coord 2 n) (flatten (l:=2) (r:=2) A.val)
  have h := quadratic_charpoly_padding (enlargedMatrix L R U) (enlargedMatrix_supported L R U)
  rw [enlargedMatrix_crop] at h
  have hlive := liveMatrix_eq_liveJoint L R S T hL hR A
  rw [show partialTraceLeft (liveMatrix L R U ^ 2) = _ from congrArg Prod.fst hlive,
      show partialTraceRight (liveMatrix L R U ^ 2) = _ from congrArg Prod.snd hlive] at h
  exact h

end
end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.quadratic_charpoly_actual




