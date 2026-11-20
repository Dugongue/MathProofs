import EvenP5TrialList
import EvenDenseDecode

namespace EvenTI.TrialProducer

open EvenTI.Action EvenTI.Contract

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure PreparedPair (K : Type) [Field K] [DecidableEq K] where
  halfPred : ℕ
  n : ℕ
  sourceTrials : List (PreparedTrial K halfPred n)
  targetTrials : List (PreparedTrial K halfPred n)

private def prepareAt (F : FieldEncoding K) (P : ParsedPair K) (l : ℕ) : Option (PreparedPair K) :=
  if h : P.d = (l + 1) + (l + 1) then
    let e := congrArg (fun d => Tensor K d P.n) h
    some ⟨l, P.n, prepareTrials F (Eq.mp e P.source), prepareTrials F (Eq.mp e P.target)⟩
  else
    none

/-- The dense input decoder determines the cut indices. The two trial lists
are constructed from the actual words of the two input tensors. -/
def prepareEncodedTrials (F : FieldEncoding K) (words : List ℕ) :
    Option (PreparedPair K) := do
  let P ← decodePair F words
  prepareAt F P (P.d / 2 - 1)

theorem prepareEncodedTrials_eq (F : FieldEncoding K) {l n : ℕ}
    (T S : Dense K l n) (hl : 1 ≤ l) (hn : 2 ≤ n) :
    prepareEncodedTrials F (comparisonInput F T S) =
      some ⟨l, n, prepareTrials F T, prepareTrials F S⟩ := by
  have hd : 4 ≤ (l + 1) + (l + 1) := by omega
  have he : Even ((l + 1) + (l + 1)) := ⟨l + 1, rfl⟩
  unfold prepareEncodedTrials
  rw [decodePair_encode F T S hd he hn]
  have hdiv : ((l + 1) + (l + 1)) / 2 - 1 = l := by omega
  change prepareAt F ⟨(l + 1) + (l + 1), n, T, S⟩ (((l + 1) + (l + 1)) / 2 - 1) = _
  rw [hdiv]
  simp [prepareAt]

theorem prepareEncodedTrials_noDecode (F : FieldEncoding K) (w : List ℕ)
    (h : decodePair F w = none) : prepareEncodedTrials F w = none := by
  simp [prepareEncodedTrials, h]

#print axioms prepareEncodedTrials_eq
#print axioms prepareEncodedTrials_noDecode

end EvenTI.TrialProducer
