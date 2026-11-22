import EvenP17TrialRoutedForms
import EvenP14CutScanMeaning
import EvenP10TrialPayloadExact

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep

variable {K W : Type} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup W] [Module K W]

private theorem basisForm_eq_sum {d n c : ℕ} (D : FieldEncoding K) (xs : Fin c → Coord d n → K)
    (v : Fin (Fintype.card K^c)) :
    basisForm D xs v=(∑ i, coefficients D c v i • xs i) := by
  funext x
  simp only [basisForm,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- The verified nonzero coefficient mask selects exactly the bank forms
of the reference enumeration from the captured dense records. The test
uses the actual field label of zero for the supplied encoding. -/
theorem capturedNonzeroCut_exact {d n c : ℕ} (D : FieldEncoding K)
    (read : ℕ → K) (base budget : ℕ) (f : (Coord d n → K) →ₗ[K] W)
    (xs : Fin c → Coord d n → K)
    (hBasis : cutBankBasis (inputCoordOrder n d) read base=xs)
    (hInd : LinearIndependent K xs) (hSpan : Submodule.span K (Set.range xs)=f.ker)
    (o₀ bank : List ℕ) (pos : ℕ)
    (hBank : bank.take pos =
      o₀++(List.range (cappedCutChoiceCount (Fintype.card K) c budget)).flatMap (basisFormWords D xs))
    (x : Coord d n → K) :
    x ∈ bankForms (c:=c) D (inputCoordOrder n d) read base budget (fun _ => true) ↔
      ∃ code ∈ (List.range (cappedCutChoiceCount (Fintype.card K) c budget)).filter
        (cutCodeGood (Fintype.card K) c (D 0).val),
        (((bank.take pos).drop (o₀.length+code*n^d)).take (n^d))=cutFormWords D x := by
  rw [cappedCutCodes_exact D (inputCoordOrder n d) read base budget f xs hBasis hInd hSpan]
  constructor
  · rintro ⟨v,hv,hx⟩
    have hCode := List.mem_range.mp (List.mem_of_mem_filter hv)
    refine ⟨v.val,hv,?_⟩
    rw [capturedCutForm_at D xs budget v.val hCode o₀ bank pos hBank,
      basisFormWords,dif_pos v.isLt,hx,basisForm_eq_sum]
  · rintro ⟨code,hCode,hx⟩
    have hCap := List.mem_range.mp (List.mem_of_mem_filter hCode)
    have hc : code<Fintype.card K^c := by
      have h : cappedCutChoiceCount (Fintype.card K) c budget≤Fintype.card K^c := by
        unfold cappedCutChoiceCount
        split <;> omega
      exact hCap.trans_le h
    rw [capturedCutForm_at D xs budget code hCap o₀ bank pos hBank,basisFormWords,dif_pos hc] at hx
    have h := cutFormWords_injective D hx
    exact ⟨⟨code,hc⟩,hCode,h.symm.trans (basisForm_eq_sum D xs _)⟩

#print axioms capturedNonzeroCut_exact
end EvenTI.P17Trial
