import EvenP5CoordinateProjection
import EvenP5TransportSingular
import EvenP2SpectralFiber

namespace EvenTI.TrialProducer

open scoped Matrix TensorProduct
open Matrix EvenTI.Action EvenTI.AnchorCovariance
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Coverage
open Mathproof.EvenTI.Singular.Forms

variable {K : Type} [Field K] {l r n : ℕ}

def rawRetainedProjection (i : Fin (l + 1)) (ell : Coord (l + 1) n → K) :
    (Coord (l + 1) n → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun x := retainedForm i x * (retainedForm i ell)ᵀ
  map_add' x y := by
    have h : retainedForm i (x + y) = retainedForm i x + retainedForm i y := by
      ext a b
      rfl
    rw [h, Matrix.add_mul]
  map_smul' c x := by
    have h : retainedForm i (c • x) = c • retainedForm i x := by
      ext a b
      rfl
    rw [h, Matrix.smul_mul] <;> rfl

theorem rawRetainedProjection_eq (i : Fin (l + 1)) (ell : Coord (l + 1) n → K) :
    rawRetainedProjection i ell = physicalMatrixProjection i ell := by
  apply LinearMap.ext
  intro x
  exact (physicalMatrixProjection_apply_eq i ell x).symm

def rawPhysicalAnchors (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (T : Tensor K ((l + 1) + (r + 1)) n) :
    Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K :=
  let Z := coordinateProjection (rawRetainedProjection i ell) (rawRetainedProjection j rho)
    (flatten T)
  (partialTraceLeft (Z ^ 2), partialTraceRight (Z ^ 2))

theorem rawPhysicalAnchors_eq (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (T : Tensor K ((l + 1) + (r + 1)) n) :
    rawPhysicalAnchors i j ell rho T = literalSingularAnchors i j ell rho T := by
  unfold rawPhysicalAnchors
  rw [rawRetainedProjection_eq, rawRetainedProjection_eq, coordinateProjection_eq]
  rfl

/-- Produce all physical anchors on a balanced higher-order cut. The Boolean
coordinate follows the existing singular budget convention. -/
def rawHigherSingularAnchors (ell rho : Coord (l + 1) n → K)
    (T : Tensor K ((l + 1) + (l + 1)) n) (i : Fin (l + 1) × Bool) :
    Matrix (Fin n) (Fin n) K :=
  let P := rawPhysicalAnchors i.1 i.1 ell rho T
  if i.2 then P.2 else P.1

theorem rawHigherSingularAnchors_eq
    {R S : Submodule K (Coord (l + 1) n → K)} (p : GoodPair R S)
    (T : DenseKernelFiber R S) (i : Fin (l + 1) × Bool) :
    rawHigherSingularAnchors p.ell p.rho T.val i = singularModeAnchor p i T := by
  unfold rawHigherSingularAnchors singularModeAnchor
  rw [rawPhysicalAnchors_eq, ← singularPairAnchor_eq_literal]
  rcases i with ⟨i, b⟩
  cases b <;> rfl

#print axioms rawPhysicalAnchors_eq
#print axioms rawHigherSingularAnchors_eq

end EvenTI.TrialProducer
