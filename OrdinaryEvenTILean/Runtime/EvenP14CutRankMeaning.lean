import EvenP14CutChoiceCap
import EvenP14CutRankControl

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem rawRetainedFullRank_ne_zero {d n : ℕ} (hn : 0 < n) {x : Coord (d+1) n → K}
    (hx : rawRetainedFullRank x = true) : x ≠ 0 := by
  intro h
  subst x
  have hi := (rawRetainedFullRank_spec (0 : Coord (d+1) n → K)).mp hx ⟨0, by omega⟩
  have hz : retainedForm (⟨0,by omega⟩ : Fin (d+1)) (0 : Coord (d+1) n → K) = 0 := rfl
  rw [hz, Matrix.rank_zero] at hi
  omega

/-- Accepted numeric codes describe exactly the rank-filtered forms from the
same persisted basis, including the over-budget and empty-list cases. -/
theorem cappedRankedCutCodes_exact (D : FieldEncoding K)
    {d n c m : ℕ} (ord : Coord (d+1) n ≃ Fin m) (read : ℕ → K)
    (base budget : ℕ) (hn : 0 < n)
    (indexed : Fin (Fintype.card K^c) → Coord (d+1) n → K)
    (accepted : ℕ → Bool)
    (hIndexed : ∀ v, indexed v = ∑ i : Fin c, coefficients D c v i • cutBankBasis ord read base i)
    (hAccepted : ∀ v : Fin (Fintype.card K^c), accepted v.val = rawRetainedFullRank (indexed v))
    (x : Coord (d+1) n → K) :
    x ∈ bankForms (c := c) D ord read base budget rawRetainedFullRank ↔
      ∃ v : Fin (Fintype.card K^c),
        v.val ∈ (List.range (cappedCutChoiceCount (Fintype.card K) c budget)).filter accepted ∧
          x = indexed v := by
  by_cases h : Fintype.card K^c ≤ budget
  · simp only [bankForms,linearChoices,coefficientChoices,cappedCutChoiceCount,h,if_true,
      List.mem_filter,List.mem_map,List.mem_finRange,List.mem_range,Bool.and_eq_true,
      decide_eq_true_eq,true_and]
    constructor
    · rintro ⟨⟨_,⟨v,rfl⟩,rfl⟩,_,hv⟩
      refine ⟨v,⟨v.isLt,?_⟩,(hIndexed v).symm⟩
      simpa only [hAccepted v,hIndexed v] using hv
    · rintro ⟨v,⟨_,hv⟩,rfl⟩
      have hr : rawRetainedFullRank (indexed v) = true := (hAccepted v).symm.trans hv
      exact ⟨⟨coefficients D c v,⟨v,rfl⟩,(hIndexed v).symm⟩,
        rawRetainedFullRank_ne_zero hn hr,hr⟩
  · simp [bankForms,linearChoices,coefficientChoices,cappedCutChoiceCount,h]

#print axioms rawRetainedFullRank_ne_zero
#print axioms cappedRankedCutCodes_exact
end EvenTI.P12ComparePrep