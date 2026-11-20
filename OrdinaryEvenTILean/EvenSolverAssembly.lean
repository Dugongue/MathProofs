import EvenWordDriver

namespace EvenTI.Contract

open Action
open Lax51.TuringPolytime (TuringPolytime)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem recognizeWords_invariant (F : FieldEncoding K)
    (accept : ∀ {d n}, Tensor K d n → Bool)
    (invariant : ∀ {d n} (T : Tensor K d n) (g : Changes K d n), accept (act g T) = accept T)
    {d n : Nat} (T : Tensor K d n) (g : Changes K d n) :
    recognizeWords F accept (sourceInput F (act g T)) = recognizeWords F accept (sourceInput F T) := by
  by_cases hd : 4 ≤ d
  · by_cases he : Even d
    · by_cases hn : 2 ≤ n
      · rw [recognizeWords_encode F accept _ hd he hn, recognizeWords_encode F accept _ hd he hn,
          invariant]
      · simp [recognizeWords, sourceInput, decodeSource, admissibleHeader, hn]
    · have he' : d % 2 ≠ 0 := fun h => he (Nat.even_iff.mpr h)
      simp [recognizeWords, sourceInput, decodeSource, admissibleHeader, he']
  · simp [recognizeWords, sourceInput, decodeSource, admissibleHeader, hd]

omit [DecidableEq K] in
noncomputable def rejectedSourceFraction (accept : ∀ {d n}, Tensor K d n → Bool) (d n : Nat) :
    Real := ((Finset.univ.filter fun T : Tensor K d n => accept T = false).card : Real) /
      Fintype.card (Tensor K d n)

theorem rejectedSourceFraction_eq (F : FieldEncoding K)
    (accept : ∀ {d n}, Tensor K d n → Bool) {d n : Nat}
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) :
    rejectDensity F (recognizeWords F accept) d n = rejectedSourceFraction accept d n := by
  unfold rejectDensity rejectedSourceFraction
  congr 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro T _
  rw [recognizeWords_encode F accept T hd he hn]
  cases hv : accept T <;> simp [hv]

/-- Assemble the frozen machine conclusion from the instantiated trial
procedures, the source coverage proof and the binary compiler receipts. -/
def assembleVerifiedSolver (F : FieldEncoding K)
    (accept : ∀ {d n}, Tensor K d n → Bool) (P : TrialPlan K) {q : Nat} (enum : Fin q ≃ Kˣ)
    (hInv : ∀ {d n} (T : Tensor K d n) (g : Changes K d n), accept (act g T) = accept T)
    (hUniform : ∀ ε : Real, 0 < ε → ∃ n₀ : Nat, 2 ≤ n₀ ∧ ∀ d n,
      4 ≤ d → Even d → n₀ ≤ n → rejectedSourceFraction (K := K) accept d n ≤ ε)
    (hRate : ∃ C : Real, 0 < C ∧ ∃ n₀ : Nat, 2 ≤ n₀ ∧ ∀ d n,
      6 ≤ d → Even d → n₀ ≤ n → rejectedSourceFraction (K := K) accept d n ≤ C / Real.log n)
    (hTrials : ∀ {d n : Nat}, 4 ≤ d → Even d → 2 ≤ n → ∀ T S : Tensor K d n,
      accept T = true →
        T ≠ 0 ∧ CompleteTrials P T S ∧
        (∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u))
    (hTimeRecognize : TuringPolytime (recognizeWords F accept))
    (hTimeCompare : TuringPolytime (compareWords F P))
    (hTimeCount : ∀ test : List Nat → List Nat,
      TuringPolytime test → TuringPolytime (countWords F P enum test)) : VerifiedSolver F where
  recognize := recognizeWords F accept
  compare := compareWords F P
  recognizesInTime := hTimeRecognize
  comparesInTime := hTimeCompare
  range := by
    intro d n T
    unfold recognizeWords
    split
    · exact Or.inl rfl
    · split <;> simp
  invariant T g := recognizeWords_invariant F accept hInv T g
  uniformCoverage := by
    intro ε hε
    obtain ⟨n₀, hn₀, h⟩ := hUniform ε hε
    refine ⟨n₀, fun d n hd he hn => ?_⟩
    rw [rejectedSourceFraction_eq F accept hd he (hn₀.trans hn)]
    exact h d n hd he hn
  higherOrderRate := by
    obtain ⟨C, hC, n₀, hn₀, h⟩ := hRate
    refine ⟨C, hC, n₀, hn₀, fun d n hd he hn => ?_⟩
    rw [rejectedSourceFraction_eq F accept (by omega) he (hn₀.trans hn)]
    exact h d n hd he hn
  exactAnswer := by
    intro d n hd he hn T S h
    rw [recognizeWords_encode F accept T hd he hn] at h
    have ha : accept T = true := by cases hh : accept T <;> simp_all
    obtain ⟨hne, htrials, hScalar⟩ := hTrials hd he hn T S ha
    exact compareWords_correct F P hd he hn hne htrials hScalar
  filteredCount := by
    intro test htest
    refine ⟨countWords F P enum test, hTimeCount test htest, ?_⟩
    intro d n hd he hn params T S h
    rw [recognizeWords_encode F accept T hd he hn] at h
    have ha : accept T = true := by cases hh : accept T <;> simp_all
    obtain ⟨hne, htrials, hScalar⟩ := hTrials hd he hn T S ha
    exact countWords_correct F P enum test params hd he hn hne htrials hScalar

#print axioms recognizeWords_invariant
#print axioms rejectedSourceFraction_eq
#print axioms assembleVerifiedSolver

end EvenTI.Contract
