import EvenP5CoordinateProjection
import EvenP5NormalFrame
import EvenP3SingularActual

namespace EvenTI.TrialProducer

open scoped Matrix TensorProduct
open Matrix EvenTI.Action EvenTI.AnchorCovariance
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [DecidableEq K] {n a b k m : ℕ}
variable {ell rho : Coord 2 n → K}

/-- Construct the enlarged anchors from the actual coordinate projections.
The normal frames supply both forward and inverse elementary operations. -/
def enlargedAnchorsFor (L : NormalPair ell a k) (R : NormalPair rho b m)
    (A : Tensor K 4 n) :
    Matrix (Index a k) (Index a k) K × Matrix (Index b m) (Index b m) K :=
  let Z := coordinateProjection (enlargedProjection ell L) (enlargedProjection rho R)
    (flatten (l := 2) (r := 2) A)
  (partialTraceLeft (Z ^ 2), partialTraceRight (Z ^ 2))

theorem enlargedAnchorsFor_eq (L : NormalPair ell a k) (R : NormalPair rho b m)
    (A : Tensor K 4 n) :
    enlargedAnchorsFor L R A =
      (partialTraceLeft (rawEnlarged L R A ^ 2), partialTraceRight (rawEnlarged L R A ^ 2)) := by
  unfold enlargedAnchorsFor
  rw [coordinateProjection_eq]
  rfl

abbrev RawEnlargedIndex (ell : Coord 2 n → K) :=
  Index (rawFrameWidth ell) (n - rawFrameWidth ell)

def rawEnlargedAnchors (ell rho : Coord 2 n → K) (A : Tensor K 4 n) :
    Matrix (RawEnlargedIndex ell) (RawEnlargedIndex ell) K ×
      Matrix (RawEnlargedIndex rho) (RawEnlargedIndex rho) K :=
  enlargedAnchorsFor (rawNormalFrame ell) (rawNormalFrame rho) A

theorem rawEnlargedAnchors_eq (ell rho : Coord 2 n → K) (A : Tensor K 4 n) :
    rawEnlargedAnchors ell rho A =
      (partialTraceLeft (rawEnlarged (rawNormalFrame ell) (rawNormalFrame rho) A ^ 2),
        partialTraceRight (rawEnlarged (rawNormalFrame ell) (rawNormalFrame rho) A ^ 2)) :=
  enlargedAnchorsFor_eq (rawNormalFrame ell) (rawNormalFrame rho) A

#print axioms enlargedAnchorsFor_eq
#print axioms rawEnlargedAnchors_eq

end EvenTI.TrialProducer
