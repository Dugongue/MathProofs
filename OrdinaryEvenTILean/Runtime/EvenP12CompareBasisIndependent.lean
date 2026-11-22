import EvenP11InstalledCutBasis
import EvenP11TrialSubstitution
import EvenP12CompareAssembly

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer EvenTI.Headline
open EvenTI.P10Oracle EvenTI.P10Scan
open Mathproof.EvenTI.GlobalCoverage
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The two complete kernel banks produced by Gaussian elimination;
their basis vectors can be ordered as returned by the machine. -/
structure CompleteCutBanks {a b n : ℕ} (T : Tensor K (a+b) n) where
  left : List (Coord a n → K)
  right : List (Coord b n → K)
  leftIndependent : LinearIndependent K left.get
  rightIndependent : LinearIndependent K right.get
  leftSpans : Submodule.span K (Set.range left.get) = (leftCutKernel T).ker
  rightSpans : Submodule.span K (Set.range right.get) = (rightCutKernel T).ker

variable (F : FieldEncoding K)
variable (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T)

def scanWithBanks {a b n : ℕ} (T : Tensor K (a+b) n)
    (gL : (Coord a n → K) → Bool) (gR : (Coord b n → K) → Bool) :
    List (CutFormPair K a b n) :=
  scanInstalledCutBasis F (banks T).left (banks T).right gL gR

theorem mem_scanWithBanks {a b n : ℕ} (T : Tensor K (a+b) n)
    (gL : (Coord a n → K) → Bool) (gR : (Coord b n → K) → Bool)
    (p : CutFormPair K a b n) :
    p ∈ scanWithBanks F banks T gL gR ↔ p ∈ rawCutBankForms F T gL gR :=
  installedCutBasis_membership F T (banks T).left (banks T).right (banks T).leftIndependent
    (banks T).rightIndependent (banks T).leftSpans (banks T).rightSpans gL gR p

def prepareFromBanks {l n : ℕ} (T : Dense K l n) : List (PreparedTrial K l n) :=
  match rawReciprocalAnchors T with
  | some A => [.reciprocal A]
  | none =>
    if h : l = 1 then
      (scanWithBanks F banks (castFour h T) (fun _ => true) (fun _ => true)).map (fourTrial h T)
    else
      (scanWithBanks F banks T rawRetainedFullRank rawRetainedFullRank).map (higherTrial T)

/-- Arbitrary complete elimination bases produce exactly the needed trial
members, even though the list order can depend on the basis. -/
theorem mem_prepareFromBanks {l n : ℕ} (T : Dense K l n) (p : PreparedTrial K l n) :
    p ∈ prepareFromBanks F banks T ↔ p ∈ prepareTrials F T := by
  unfold prepareFromBanks prepareTrials
  cases hrec : rawReciprocalAnchors T with
  | some A => rfl
  | none =>
    by_cases h : l = 1
    · simp only [dif_pos h, List.mem_map, mem_scanWithBanks, rawUnfilteredCutForms]
    · simp only [dif_neg h, List.mem_map, mem_scanWithBanks, rawFullRankCutForms]

noncomputable def comparePlanFromBanks (FP : FieldPresentation K) : TrialPlan K :=
  comparisonWithTrialProducer F FP (prepareFromBanks F banks)

theorem comparePlanFromBanks_complete (FP : FieldPresentation K)
    {d n : ℕ} (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) (T S : Tensor K d n)
    (hT : sourceAccepted T) : CompleteTrials (comparePlanFromBanks F banks FP) T S :=
  comparisonWithTrialProducer_complete F FP
    (fun T p h => (mem_prepareFromBanks F banks T p).mpr h) hd he hn T S hT

#print axioms mem_prepareFromBanks
#print axioms comparePlanFromBanks_complete

end EvenTI.P12Compare
