import EvenP15TrialRawOrderFourForm
import EvenP14CutRawClock

set_option autoImplicit false

namespace EvenTI.P15Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def orderFourFormPoly (F : FieldPresentation K) : Polynomial ℕ :=
  C (cutRankMakeOneCost F+orderFourConfigCost)+
    (C (300*macroBudget F)*(X+C 2)^4+(C (emitFieldLabelCost F+16)*X+C 6))

noncomputable def rawOrderFourFormPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawNonzeroBitPoly F j+C 1+orderFourFormPoly F

theorem orderFourFormCost_le (F : FieldPresentation K) {m L : ℕ} (hm : m ≤ L) :
    orderFourFormCost F m ≤ (orderFourFormPoly F).eval L := by
  simp only [orderFourFormCost,orderFourFormPoly,eval_add,eval_mul,eval_pow,eval_C,eval_X,
    Nat.mul_assoc]
  gcongr

theorem rawOrderFourFormProgram_bit_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n : ℕ} (T S : Tensor K (2+2) n) (j : Fin 4) (hn : 2 ≤ n)
    (v : Fin (Fintype.card K ^ selectedFourNullity T S j))
    (hCap : Fintype.card K ^ selectedFourNullity T S j ≤ n) :
    let c := selectedFourNullity T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^2
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord 2 n → K), Run B (rawOrderFourFormProgram D F j)
      (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w++[v.val]))
        τ ((rawOrderFourFormPoly F j).eval L) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=cutFormWords D (fun x => ∑ i, coefficients D c v i * xs i x) ∧ τ.inp=[] := by
  dsimp only
  let c := selectedFourNullity T S j
  let q := Fintype.card K
  let L := bitSize (comparisonInput D T S)
  obtain ⟨τ,xs,hR,hLin,hSpan,hOut,hIn⟩ := rawOrderFourFormProgram_run D F T S j hn v hCap
  obtain ⟨hnL,hmL,_⟩ := cutInput_side_bounds D T S (by decide : 1 ≤ 2) hn
  have hcL : c ≤ L := (kernelFinrank_le _).trans hmL
  have hcost : 30*(n^2+q)+42+
      ((visitCutCandidateCost F c (n^2)+8)*cappedCutChoiceCount q c n+6) ≤
      (cutNonzeroPaidPoly F q).eval L :=
    nonzeroCutScanCost_le F hcL hmL (hnL.trans hmL)
  have hcount : 0 < cappedCutChoiceCount q c n := by
    rw [cappedCutChoiceCount,if_pos hCap]
    exact Nat.lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  have hsmall : cutCandidateCost F c (n^2) ≤ visitCutCandidateCost F c (n^2)+8 := by
    unfold visitCutCandidateCost
    omega
  have hb := Nat.le_mul_of_pos_right (visitCutCandidateCost F c (n^2)+8) hcount
  have hcore : cutCandidateCost F c (n^2) ≤ (cutNonzeroPaidPoly F q).eval L :=
    hsmall.trans (hb.trans (Nat.le_trans (by omega) hcost))
  refine ⟨τ,xs,hR.mono ?_,hLin,hSpan,hOut,hIn⟩
  have hf : orderFourFormCost F (n^2) ≤ (orderFourFormPoly F).eval L := orderFourFormCost_le F hmL
  change rawCutSetupBitCost F L j+(1+(cutCandidateCost F c (n^2)+orderFourFormCost F (n^2))) ≤
    (rawOrderFourFormPoly F j).eval L
  simp only [rawOrderFourFormPoly,rawNonzeroBitPoly,eval_add,eval_C,rawSetupBitPoly_eval]
  change _ ≤ rawCutSetupBitCost F L j+(cutNonzeroPaidPoly F q).eval L+1+(orderFourFormPoly F).eval L
  omega

#print axioms rawOrderFourFormProgram_bit_run
end EvenTI.P15Trial