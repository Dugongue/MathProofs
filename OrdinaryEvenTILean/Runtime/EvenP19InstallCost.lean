import EvenP18TrialFormScatterLoop
import EvenP18TrialRawRankedFormsBinary

set_option autoImplicit false
namespace EvenTI.P19Install

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P17Trial EvenTI.P18Trial Lax51.BinaryWordEncoding Polynomial
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- One whole isolated two-cut capture and one selected replay have a
single polynomial time bound in the bit size of the original pair. -/
theorem captureReplay_boundedBits (D : FieldEncoding K) (F : FieldPresentation K) (j k : Fin 4) :
    ∃ p : Polynomial ℕ,
      ∀ {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n), 1≤l → 2≤n →
        let m := n^(l+1)
        let L := bitSize (comparisonInput D T U)
        (7*rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U j) l m n L j+
          (4+7*rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U k) l m n L k))+
          (12+2*(4+scatterPublicFormCost F (l+1) m)) ≤ p.eval L := by
  refine ⟨C 7*(rawRankedFormsPoly F j+rawRankedFormsPoly F k)+
    C 36+C 2*(C 24*X+C (27+installEncodedDigitCost F))*X,?_⟩
  intro l n T U hl hn
  dsimp only
  let L := bitSize (comparisonInput D T U)
  let m := n^(l+1)
  obtain ⟨_,hm,hd⟩ := cutInput_side_bounds D T U (show 1 ≤ l+1 by omega) hn
  have hTimeL := rawRankedFormsCost_le D F T U j hl hn
  have hTimeR := rawRankedFormsCost_le D F T U k hl hn
  have hSc : (24*(l+1)+27+installEncodedDigitCost F)*m ≤
      (24*L+(27+installEncodedDigitCost F))*L := by
    exact Nat.mul_le_mul (by change l+1 ≤ L at hd; omega) hm
  simp only [scatterPublicFormCost,eval_add,eval_mul,eval_X,eval_C]
  change _ ≤ 7*((rawRankedFormsPoly F j).eval L+(rawRankedFormsPoly F k).eval L)+
    36+2*(24*L+(27+installEncodedDigitCost F))*L
  rw [Nat.mul_assoc 2 (24*L+(27+installEncodedDigitCost F)) L]
  change rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U j) l m n L j ≤
    (rawRankedFormsPoly F j).eval L at hTimeL
  change rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U k) l m n L k ≤
    (rawRankedFormsPoly F k).eval L at hTimeR
  change (7*rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U j) l m n L j+
    (4+7*rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T U k) l m n L k))+
    (12+2*(4+((24*(l+1)+27+installEncodedDigitCost F)*m+6))) ≤ _
  omega

#print axioms captureReplay_boundedBits
end EvenTI.P19Install

