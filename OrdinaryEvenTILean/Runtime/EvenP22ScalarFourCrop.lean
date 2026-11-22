import EvenP9RawAffine
import EvenP8OrderFourHomogeneous
import EvenP21ScalarFiber

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 12000

namespace EvenTI.P22Scalar
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.P12Scalar EvenTI.P21Scalar
open Mathproof.EvenOrdinaryTISingular.EnlargedCut

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

attribute [local irreducible] rawFrameWidth rawNormalFrame rawEnlargedWords

/-- The two recorded width tests determine the exact source word grid for
an enlarged trial. Keep its target grid as produced by the actual parser. -/
theorem pairedFour_sourceWords (T S : Dense K 1 n)
    (p q : CutFormPair K 2 2 n)
    (a : Matrix (RawEnlargedIndex p.1) (RawEnlargedIndex p.1) K)
    (b : Matrix (RawEnlargedIndex p.2) (RawEnlargedIndex p.2) K)
    (c : Matrix (RawEnlargedIndex q.1) (RawEnlargedIndex q.1) K)
    (d : Matrix (RawEnlargedIndex q.2) (RawEnlargedIndex q.2) K)
    (hL : rawFrameWidth q.1 = rawFrameWidth p.1)
    (hR : rawFrameWidth q.2 = rawFrameWidth p.2) :
    ∃ target : FourTargetGrid p.1 p.2,
      pairedTrialWords T S (.orderFour rfl p a b) (.orderFour rfl q c d) =
        some (sourceFourTrialWords p.1 p.2 T target) := by
  simp only [pairedTrialWords,dif_pos hL,dif_pos hR,castFour]
  exact ⟨_,rfl⟩

/-- The literal enlarged source payload changes no index in its own crop.
The target payload affects only the feasibility of the paired trial. -/
theorem fourSourceCrop_eq (T S : Dense K 1 n)
    (p q : CutFormPair K 2 2 n)
    (a : Matrix (RawEnlargedIndex p.1) (RawEnlargedIndex p.1) K)
    (b : Matrix (RawEnlargedIndex p.2) (RawEnlargedIndex p.2) K)
    (c : Matrix (RawEnlargedIndex q.1) (RawEnlargedIndex q.1) K)
    (d : Matrix (RawEnlargedIndex q.2) (RawEnlargedIndex q.2) K)
    (hL : rawFrameWidth q.1 = rawFrameWidth p.1)
    (hR : rawFrameWidth q.2 = rawFrameWidth p.2)
    (target : FourTargetGrid p.1 p.2)
    (hW : pairedTrialWords T S (.orderFour rfl p a b) (.orderFour rfl q c d)
      = some (sourceFourTrialWords p.1 p.2 T target))
    (G : FourNumericUnits p.1 p.2) :
    sourceTrialCrop T S (.orderFour rfl p a b) (.orderFour rfl q c d)
      (sourceFourTrialWords p.1 p.2 T target) hW G =
        recoverFourMatrices p.1 p.2 p.1 p.2 rfl rfl G := by
  have hs := hW
  simp only [pairedTrialWords,dif_pos hL,dif_pos hR,castFour,Option.some.injEq] at hs
  injection hs with ht
  subst target
  simp only [sourceTrialCrop,dif_pos hL,dif_pos hR]

#print axioms pairedFour_sourceWords
#print axioms fourSourceCrop_eq
end EvenTI.P22Scalar

