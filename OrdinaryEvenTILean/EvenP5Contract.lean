import EvenP5EncodedTrials
import EvenP5FourCoverage
import EvenP5HigherCoverage
import EvenP5ReciprocalCoverage

namespace EvenTI.TrialProducer

open Matrix EvenTI.Action EvenTI.Contract
open Mathproof.EvenTI.GlobalCoverage Mathproof.EvenTI.Reciprocal.Coverage
open Mathproof.EvenTI.OrderFour

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

def castFourChanges (h : l = 1) (g : Changes K ((l + 1) + (l + 1)) n) : Changes K (2 + 2) n :=
  Eq.mp (congrArg (fun a => Changes K ((a + 1) + (a + 1)) n) h) g

/-- An eligible pair of prepared trials uses the specified transporter.
Its source budget is the original branch's budget. The transport lemmas
for each branch certify the corresponding conjugations of its anchors. -/
inductive PreparedMatch (T : Dense K l n) (g : Changes K ((l + 1) + (l + 1)) n) :
    PreparedTrial K l n → PreparedTrial K l n → Prop
  | reciprocal (A : HigherModes l → Matrix (Fin n) (Fin n) K)
      (budget : Fintype.card K ^ reciprocalBudget A ≤
        (if l = 1 then n else n ^ ((l + 1) + (l + 1)))) :
      PreparedMatch T g (.reciprocal A) (.reciprocal (conjugateReciprocalAnchors g A))
  | four (hl : l = 1) (p : CutFormPair K 2 2 n)
      (budget : Fintype.card K ^ enlargedBudget p.1 p.2 (castFour hl T) ≤ n) :
      PreparedMatch T g (fourTrial hl T p) (fourTrial hl (act g T)
        (moveLeftForm (l := 2) (r := 2) (castFourChanges hl g) p.1,
          moveRightForm (l := 2) (r := 2) (castFourChanges hl g) p.2))
  | higher (hl : 2 ≤ l) (p : CutFormPair K (l + 1) (l + 1) n)
      (budget : Fintype.card K ^ physicalBudget (rawHigherSingularAnchors p.1 p.2 T) ≤
        n ^ ((l + 1) + (l + 1))) :
      PreparedMatch T g (higherTrial T p)
        (higherTrial (act g T) (moveLeftForm g p.1, moveRightForm g p.2))

/-- Every real isomorphism of a spectrally accepted source survives in the
actual trial lists on both inputs, with the correct source spectral budget. -/
theorem prepareTrials_complete (F : FieldEncoding K) (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (hl : 1 ≤ l)
    (h : sourceSpectralAccepted T) :
    ∃ p ∈ prepareTrials F T, ∃ q ∈ prepareTrials F (act g T), PreparedMatch T g p q := by
  by_cases horder : l = 1
  · subst l
    have hn : 5 ≤ n := by
      rcases h with ⟨_, hw, _⟩ | ⟨l, hl, he, _, _⟩
      · exact hw
      · omega
    rcases (four_spectral_iff hn T).mp h with ⟨hz, hs⟩ | ⟨hu, hb⟩
    · obtain ⟨p, hp, hq, hgate, _⟩ := fourSingular_accepted_follow F T g hz hs
      exact ⟨_, hp, _, hq, PreparedMatch.four (T := T) (g := g) rfl p hgate⟩
    · obtain ⟨A, hs, ht, hbudget⟩ := fourReciprocalTrials_follow F T g hn hu
      refine ⟨_, ?_, _, ?_, PreparedMatch.reciprocal A ?_⟩
      · rw [hs]
        simp
      · rw [ht]
        simp
      · simpa [hbudget] using hb
  · have hl' : 2 ≤ l := by omega
    have hn : 1 ≤ n := by
      rcases h with ⟨he, hw, _⟩ | ⟨s, hs, he, hw, _⟩
      · omega
      · exact hw
    rcases (higher_spectral_iff hl' hn T).mp h with ⟨hz, hs⟩ | ⟨hu, hb⟩
    · obtain ⟨p, hp, hq, hgate⟩ := higherSingular_accepted_follow F T g hl' hz hs
      exact ⟨_, hp, _, hq, PreparedMatch.higher hl' p hgate⟩
    · obtain ⟨A, hs, ht, hbudget⟩ := reciprocalTrials_follow F T g hn hu
      refine ⟨_, ?_, _, ?_, PreparedMatch.reciprocal A ?_⟩
      · rw [hs]
        simp
      · rw [ht]
        simp
      · simpa only [if_neg horder, hbudget] using hb

/-- The completeness theorem also applies when the two lists are built
from the exact dense comparison word encoding. -/
theorem prepareEncodedTrials_complete (F : FieldEncoding K) (T S : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (hg : act g T = S)
    (hl : 1 ≤ l) (hn : 2 ≤ n) (h : sourceSpectralAccepted T) :
    prepareEncodedTrials F (comparisonInput F T S) =
      some ⟨l, n, prepareTrials F T, prepareTrials F S⟩ ∧
      ∃ p ∈ prepareTrials F T, ∃ q ∈ prepareTrials F S, PreparedMatch T g p q := by
  refine ⟨prepareEncodedTrials_eq F T S hl hn, ?_⟩
  rw [← hg]
  exact prepareTrials_complete F T g hl h

#print axioms prepareTrials_complete
#print axioms prepareEncodedTrials_complete

end EvenTI.TrialProducer
