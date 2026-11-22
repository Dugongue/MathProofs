import EvenP14CutScan

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Contract
open scoped BigOperators

variable {K I W : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W]

/-- Give the emitted natural codes their exact existing `bankForms`
meaning. Every visit stores the corresponding vector in the live result
bank, and this theorem identifies the accepted codes independently of
which exact kernel basis elimination emitted. -/
theorem cappedCutCodes_exact {c m : ℕ} (D : FieldEncoding K) (ord : I ≃ Fin m)
    (read : ℕ → K) (base budget : ℕ) (f : (I → K) →ₗ[K] W)
    (basis : Fin c → I → K) (hBasis : cutBankBasis ord read base = basis)
    (hInd : LinearIndependent K basis) (hSpan : Submodule.span K (Set.range basis) = f.ker)
    (x : I → K) :
    x ∈ bankForms (c := c) D ord read base budget (fun _ => true) ↔
      ∃ v : Fin (Fintype.card K^c), v.val ∈ (List.range (cappedCutChoiceCount (Fintype.card K) c budget)).filter
        (cutCodeGood (Fintype.card K) c (D 0).val) ∧ x = ∑ i, coefficients D c v i • basis i := by
  let q := Fintype.card K
  let Z := (D 0).val
  have hGood (v : Fin (q^c)) : cutCodeGood q c Z v.val = true ↔
      (∑ i, coefficients D c v i • basis i) ≠ 0 := by
    rw [cutCodeGood_spec,indexedCombination_ne_zero_iff D v f basis hInd hSpan]
    constructor
    · rintro ⟨i,hi,hne⟩
      exact ⟨⟨i,hi⟩,hne⟩
    · rintro ⟨i,hne⟩
      exact ⟨i.val,i.isLt,hne⟩
  unfold bankForms
  rw [hBasis]
  unfold linearChoices coefficientChoices cappedCutChoiceCount
  by_cases h : Fintype.card K ^ c ≤ budget
  · simp only [h,if_true,List.mem_filter,List.mem_range,List.mem_map,List.mem_finRange,
      Bool.and_true,decide_eq_true_eq,true_and]
    constructor
    · rintro ⟨⟨_,⟨v,rfl⟩,rfl⟩,hnz⟩
      exact ⟨v,⟨v.isLt,(hGood v).mpr hnz⟩,rfl⟩
    · rintro ⟨v,⟨_,hg⟩,rfl⟩
      exact ⟨⟨coefficients D c v,⟨v,rfl⟩,rfl⟩,(hGood v).mp hg⟩
  · simp [h]

#print axioms cappedCutCodes_exact
end EvenTI.P12ComparePrep
