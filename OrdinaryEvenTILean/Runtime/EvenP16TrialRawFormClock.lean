import EvenP16TrialRawForm

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace EvenTI.P16Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial (emitFieldLabelCost)
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawSelectedFormPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawNonzeroBitPoly F j+C (emitFormInitCost+1)+
    (C 24*X+C (26+emitFieldLabelCost F))*X+C 6

theorem rawSelectedForm_bit_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K (d+d) n) (j : Fin 4)
    (hd : 2 ≤ d) (hn : 2 ≤ n)
    (v : Fin (Fintype.card K ^ cutKernelDimension T S j))
    (hCap : Fintype.card K ^ cutKernelDimension T S j ≤ n) :
    let c := cutKernelDimension T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^d
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord d n → K), Run B (rawSelectedForm D F j)
      (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w++[v.val]))
        τ ((rawSelectedFormPoly F j).eval L) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=cutFormWords D (fun x => ∑ i, coefficients D c v i * xs i x) ∧ τ.inp=[] := by
  dsimp only
  let c := cutKernelDimension T S j
  let q := Fintype.card K
  let m := n^d
  let L := bitSize (comparisonInput D T S)
  obtain ⟨τ,xs,hRun,hInd,hSpan,hOut,hIn⟩ := rawSelectedForm_run D F T S j hd hn v hCap
  obtain ⟨hnM,hmL,hdL⟩ := cutInput_side_bounds D T S (by omega : 1 ≤ d) hn
  have hcL : c ≤ L := (kernelFinrank_le _).trans hmL
  have hcost : 30*(m+q)+42+
      ((visitCutCandidateCost F c m+8)*cappedCutChoiceCount q c n+6) ≤
      (cutNonzeroPaidPoly F q).eval L :=
    nonzeroCutScanCost_le F hcL hmL (hnM.trans hmL)
  have hCount : 0 < cappedCutChoiceCount q c n := by
    rw [cappedCutChoiceCount,if_pos hCap]
    exact (Nat.zero_le v.val).trans_lt v.isLt
  have hSmall : cutCandidateCost F c m ≤ visitCutCandidateCost F c m+8 := by
    unfold visitCutCandidateCost
    omega
  have hMul := Nat.le_mul_of_pos_right (visitCutCandidateCost F c m+8) hCount
  have hCore : cutCandidateCost F c m ≤ (cutNonzeroPaidPoly F q).eval L :=
    hSmall.trans (hMul.trans (Nat.le_trans (by omega) hcost))
  have hEmit : emitHigherFormCost F d m ≤
      (24*L+(26+emitFieldLabelCost F))*L+6 := by
    simp only [emitHigherFormCost,Nat.add_assoc]
    gcongr
  refine ⟨τ,xs,hRun.mono ?_,hInd,hSpan,hOut,hIn⟩
  change rawCutSetupBitCost F L j+
      (emitFormInitCost+(1+(cutCandidateCost F c m+emitHigherFormCost F d m))) ≤
    (rawSelectedFormPoly F j).eval L
  simp only [rawSelectedFormPoly,rawNonzeroBitPoly,eval_add,eval_C,eval_mul,eval_X,rawSetupBitPoly_eval]
  change _ ≤ rawCutSetupBitCost F L j+(cutNonzeroPaidPoly F q).eval L+(emitFormInitCost+1)+
    (24*L+(26+emitFieldLabelCost F))*L+6
  omega

#print axioms rawSelectedForm_bit_run
end EvenTI.P16Trial