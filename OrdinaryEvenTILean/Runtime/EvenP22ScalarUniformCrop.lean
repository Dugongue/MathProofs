import EvenP22ScalarExactData
import EvenP22ScalarFourBound
import EvenP21ScalarBranch
import EvenP22ScalarCrop
import EvenP6PrimaryRestriction
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

set_option autoImplicit false
set_option maxHeartbeats 1250000
namespace EvenTI.P22Scalar
open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.LiveAlgebra EvenTI.Part8 EvenTI.P15Scalar EvenTI.P20Scalar EvenTI.P21Scalar
open EvenTI.PrimaryAlignment EvenTI.P12Scalar EvenOrdinaryTI.LiveRows
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
open Mathproof.EvenOrdinaryTISingular.EnlargedCut
variable (T S : Dense K l n) (P Q : PreparedTrial K l n) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
variable [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
variable (layout : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n=w.width p)
variable (U : SiteUnits w m) {t : ℕ} (Y : Fin t → Type)
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Fintype (Y j)]
variable (L : BaseUnitLog K)
local notation "kS" => (∑ p, CodeWidth w m p)
local notation "Words" => (Fin (VarCount (kS*2+1) (t+kS+1) (w.sites+2)) → ZMod (Fintype.card K-1))
local notation "slots" => (sharedBlockPhysicalSlot w.mode (branchIsFree w m) t w.sites)
local notation "recovered" => (fun z : Words => recoverTrialSites w m layout hw U U (nativeBaseAssignment w m Y L z))

attribute [local irreducible] rawFrameWidth rawNormalFrame rawEnlargedWords

/-- Every successful paired trial has one source support relation
that works for every homogeneous word. -/
theorem compiledCrop_fixedSupport (hPair : pairedTrialWords T S P Q=some w)
    (hn : 0 < n) (hRank : rawRetainedFullRank (l:=(l+1)+l) T=true) :
    ∃ active : ∀ i : Fin (w.sites+2), Fin (CodeWidth w m (w.mode i)) → Prop,
      ∀ z : Words, wordAction (fun i => (recovered z i).val) w.source=w.source →
        (rawScalarModes (sourceTrialCrop T S P Q w hPair (recovered z))=true ↔
          ∀ i v u, active i v → active i u → z (slots i v)=z (slots i u)) := by
  cases P <;> cases Q
  · rename_i a b
    exact ⟨fun _ _ => True, fun z _ => (compiledReciprocalCrop_scalar_iff
      T S w m layout hw U Y L a b hPair hn z).trans ⟨fun h i v u _ _ => h i v u,
        fun h i v u => h i v u trivial trivial⟩⟩
  · contradiction
  · contradiction
  · contradiction
  · rename_i hl p a b hr q c d
    subst l
    have hL : rawFrameWidth q.1=rawFrameWidth p.1 := by
      by_contra e
      simpa only [pairedTrialWords,dif_neg e,reduceCtorEq] using hPair
    have hR : rawFrameWidth q.2=rawFrameWidth p.2 := by
      by_contra e
      simpa only [pairedTrialWords,dif_pos hL,dif_neg e,reduceCtorEq] using hPair
    obtain ⟨target,ht⟩ := pairedFour_sourceWords T S p q a b c d hL hR
    have he : w=sourceFourTrialWords p.1 p.2 T target := Option.some.inj (hPair.symm.trans ht)
    refine ⟨fourNativeSupport w m layout hw U p.1 p.2
      (fourCompiledSiteOrder he) (fourCompiledWidth he), ?_⟩
    intro z hz
    exact compiledFourCrop_scalar_iff w m layout hw U Y T S p q a b c d hPair target he hn hRank L z hz
  · contradiction
  · contradiction
  · contradiction
  · rename_i p a q b
    exact ⟨fun _ _ => True, fun z _ => (compiledHigherCrop_scalar_iff
      T S w m layout hw U Y L p q a b hPair hn z).trans ⟨fun h i v u _ _ => h i v u,
        fun h i v u => h i v u trivial trivial⟩⟩

#print axioms compiledCrop_fixedSupport
end EvenTI.P22Scalar