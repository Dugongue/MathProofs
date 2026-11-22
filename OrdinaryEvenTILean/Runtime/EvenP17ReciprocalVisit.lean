import EvenP17ExecutionCells
import EvenP16AnchorCosts
import Mathproof.Meta.Problem18FieldPresentation20260930

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1900000

namespace EvenTI.P17Execution

open EvenTI.P16Execution EvenTI.P16Trial EvenTI.P15Trial
open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def computeEmitReciprocal (D : FieldEncoding K) (F : FieldPresentation K) (mirror : Bool) : Com :=
  .seq (reciprocalAnchorGrid F mirror) (emitAnchorBlock D F)

private noncomputable def sampleField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem reciprocalOutputControls (F : FieldPresentation K) (mirror : Bool) :
    ∀ r ∈ [fieldVectorStart,fieldVectorLength,emitAnchorWidth],
      r ∉ scalarWrites (reciprocalAnchorGrid F mirror) := by
  cases mirror
  · change ∀ r ∈ [fieldVectorStart,fieldVectorLength,emitAnchorWidth],
      r ∉ scalarWrites (reciprocalAnchorGrid sampleField false)
    decide
  · change ∀ r ∈ [fieldVectorStart,fieldVectorLength,emitAnchorWidth],
      r ∉ scalarWrites (reciprocalAnchorGrid sampleField true)
    decide

/-- One reciprocal visit computes the retained anchor and appends its exact
serialized block. The original and reciprocal cuts can remain in low slots. -/
theorem computeEmitReciprocal_run (D : FieldEncoding K) (F : FieldPresentation K) {l n B S src inv cross square o tt uu z one : ℕ}
    {s : Env} (T : Tensor K ((l+1)+(l+1)) n) (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (mode : HigherModes l) (hn : 0 < n)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1 < B) (hNN : n*n+1 < B)
    (hA : (n^l)*(n^l)+1 < B)
    (hSrcSep : src+(n*n^l)*(n*n^l) ≤ cross) (hInvSep : inv+(n*n^l)*(n*n^l) ≤ cross)
    (hCross : cross+(n*n)*(n*n) ≤ square) (hSquare : square+(n*n)*(n*n) ≤ S) (hOut : o+n*n ≤ square) (hBefore : o ≤ cross)
    (hT : tt < src ∧ tt < inv ∧ tt < o) (hU : uu < src ∧ uu < inv ∧ uu < o) (hTU : tt≠uu)
    (hZ : z < o ∧ z < cross ∧ z≠tt ∧ z≠uu) (hOne : one < o ∧ one < cross ∧ one≠tt ∧ one≠uu)
    (hR : s.vars gRows=n*n) (hC : s.vars gCols=n*n) (hL : s.vars dL=(n^l)*(n^l))
    (hO : s.vars gOut=cross) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu) (hZR : s.vars dZ=z)
    (hNr : s.vars crossN=n) (hAr : s.vars crossA=n^l) (hStride : s.vars crossStride=n^(l-mode.2.val))
    (hSrc : s.vars crossSource=src) (hInv : s.vars crossInverse=inv)
    (hSide : s.vars anchorSideWord=n) (hCrossW : s.vars anchorCrossWord=cross)
    (hSquareW : s.vars anchorSquareWord=square) (hTraceW : s.vars anchorTraceWord=o)
    (hOneW : s.vars anchorUnitWord=one)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hLoad : InstalledCutMatrix F s l n src (flatten T)) (hRecip : InstalledCutMatrix F s l n inv N)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hVec : s.vars fieldVectorStart=o) (hLen : s.vars fieldVectorLength=n*n)
    (hWidth : s.vars emitAnchorWidth=n) :
    ∃ t, Run B (computeEmitReciprocal D F mode.1) s t
      (crossGridCost F mode.1 n (n^l)+squareTraceCost F n+emitAnchorBlockCost F n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k < o, k ≠ tt → k ≠ uu → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      t.inp=s.inp ∧ t.out=s.out++blockW (numberedAnchorWords D (numeric (rawReciprocalAnchor T N mode))) := by
  obtain ⟨u,ru,hSlots,hAnchor,hMemory,huIn,huOut⟩ :=
    reciprocalAnchorGrid_framed_run F T N mode hn hS hN hNN hA hSrcSep hInvSep hCross hSquare
      hOut hBefore hT hU hTU hZ hOne hR hC hL hO hTR hUR hZR hNr hAr hStride hSrc hInv
      hSide hCrossW hSquareW hTraceW hOneW hZero hUnit hLoad hRecip
  have hFrame := Frame.of_run ru
  have reg (r : String) (h : r ∈ [fieldVectorStart,fieldVectorLength,emitAnchorWidth]) :
      u.vars r=s.vars r := hFrame.vars r (reciprocalOutputControls F mode.1 r h)
  let A := numeric (rawReciprocalAnchor T N mode)
  have hRead (i : Fin (n*n)) :
      val F canonical qN.WS u (o+i.val) = A.matrix (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2 := by
    let p : Fin n × Fin n := finProdFinEquiv.symm i
    have hp' : (finProdFinEquiv p).val = p.1.val*n+p.2.val := by
      simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    have hi : (finProdFinEquiv p).val=i.val :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
    rw [← hi,hp']
    exact hAnchor p.1 p.2
  obtain ⟨t,rt,ho,ha,hi,hs,hRegisters⟩ := emitAnchorBlock_framed_run D F A hSlots hQ hP hNN
    (by change o+n*n ≤ S; omega)
    ((reg _ (by simp)).trans hVec) ((reg _ (by simp)).trans hLen)
    ((reg _ (by simp)).trans hWidth) hRead
  have hW : t.vars qN.WS=u.vars qN.WS := hRegisters _ (by decide) (by decide)
  refine ⟨t,ru.seq rt,hs,?_,hi.trans huIn,?_⟩
  · intro k hk hkt hku
    have hh : val F canonical qN.WS t k = val F canonical qN.WS u k := by
      unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
      rw [hW,ha]
    exact hh.trans (hMemory k hk hkt hku)
  · rw [ho,huOut]

#print axioms computeEmitReciprocal_run

open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots installed_scalar installed_arrays)

private def restoredAnchorRegs : List (String × Expr) :=
  [(gRows,.mul (.var crossN) (.var crossN)),
   (gCols,.mul (.var crossN) (.var crossN)),
   (dL,.mul (.var crossA) (.var crossA)),
   (gOut,.var anchorCrossWord)]

/-- Restore the actual crossed-grid argument registers after the square and
trace used the shared grid. Input addresses and all field slots survive. -/
def resetReciprocalArgs : Com := commands restoredAnchorRegs

theorem resetReciprocalArgs_run (F : FieldPresentation K)
    {B S n a cross : ℕ} {s : Env} (hs : Slots F canonical qN.WS S B s)
    (hn : s.vars crossN=n) (ha : s.vars crossA=a) (hc : s.vars anchorCrossWord=cross)
    (hnB : n < B) (haB : a < B) (hcB : cross < B) (hnn : n*n < B) (haa : a*a < B) :
    ∃ t, Run B resetReciprocalArgs s t 15 ∧ Slots F canonical qN.WS S B t ∧
      t.vars gRows=n*n ∧ t.vars gCols=n*n ∧ t.vars dL=a*a ∧ t.vars gOut=cross ∧
      (∀ r, r ∉ [gRows,gCols,dL,gOut] → t.vars r=s.vars r) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  let vals := [n*n,n*n,a*a,cross]
  let pairs := List.zip (restoredAnchorRegs.map Prod.fst) vals
  let t := install pairs s
  have ev (r : String) (v : ℕ) (h : s.vars r=v) (hv : v<B) :
      (Expr.var r).evalB B s=some v :=
    evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩
  have en := ev _ _ hn hnB
  have ea := ev _ _ ha haB
  have en2 := evalB_bin (op:=.mul) en en hnn
  have ea2 := evalB_bin (op:=.mul) ea ea haa
  have hb : List.Forall₂ (fun p v => p.2.evalB B s=some v) restoredAnchorRegs vals :=
    .cons en2 (.cons en2 (.cons ea2 (.cons (ev _ _ hc hcB) .nil)))
  have hSafe : ∀ r ∈ [gRows,gCols,dL,gOut], canonical.e ≠ r ∧ canonical.p ≠ r ∧
      canonical.modBase ≠ r ∧ canonical.exp ≠ r ∧ qN.WS ≠ r := by decide
  have hRoster (p : String × ℕ) (hp : p ∈ pairs) : p.1 ∈ [gRows,gCols,dL,gOut] := by
    have h : p.1 ∈ pairs.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
    exact h
  have hr0 : Run B resetReciprocalArgs s t 15 := commands_run restoredAnchorRegs vals s rfl hb (by
    simp [restoredAnchorRegs,NoVar,gRows,gCols,dL,gOut,crossN,crossA,anchorCrossWord])
  refine ⟨t,hr0,installed_slots F pairs s hs (fun p hp => hSafe _ (hRoster p hp)),
    ?_,?_,?_,?_,?_,installed_arrays pairs s⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r h
    exact installed_scalar pairs s r (fun p hp he => h (he ▸ hRoster p hp))

#print axioms resetReciprocalArgs_run

open Polynomial Lax51.BinaryWordEncoding
open EvenTI.P12ComparePrep (cutInput_side_bounds)

noncomputable def reciprocalVisitsCost (F : FieldPresentation K) (l n : ℕ) : ℕ :=
  12+(l+1)*(crossGridCost F true n (n^l)+squareTraceCost F n+
    (crossGridCost F false n (n^l)+squareTraceCost F n)+2*(emitAnchorBlockCost F n+40))

/-- Uniform clock for both retained-mode passes once the cuts are installed.
It includes output, header and per-visit control overhead. -/
theorem reciprocalVisitsCost_originalBits (D : FieldEncoding K) (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {l n : ℕ} (T S : Tensor K ((l+1)+(l+1)) n), 2 ≤ n →
      reciprocalVisitsCost F l n ≤ p.eval (bitSize (comparisonInput D T S)) := by
  obtain ⟨p₁,hp₁⟩ := anchorGrid_originalBitBudget D F true
  obtain ⟨p₂,hp₂⟩ := anchorGrid_originalBitBudget D F false
  refine ⟨C 12+X*(p₁+p₂+C 2*(C 52+C (emitFieldLabelCost F+16)*X^2)),?_⟩
  intro l n T S hn
  let L := bitSize (comparisonInput D T S)
  have hSize := cutInput_side_bounds D T S (show 1 ≤ l+1 by omega) hn
  have hnL : n ≤ L := hSize.1.trans hSize.2.1
  have hm : n*n ≤ L*L := Nat.mul_le_mul hnL hnL
  have hEmit : emitAnchorBlockCost F n+40 ≤ 52+(emitFieldLabelCost F+16)*(L*L) := by
    have hh := Nat.mul_le_mul_left (emitFieldLabelCost F+16) hm
    unfold emitAnchorBlockCost
    omega
  have hFirst := hp₁ T S hn
  have hSecond := hp₂ T S hn
  have hAll : crossGridCost F true n (n^l)+squareTraceCost F n+
      (crossGridCost F false n (n^l)+squareTraceCost F n)+2*(emitAnchorBlockCost F n+40) ≤
      p₁.eval L+p₂.eval L+2*(52+(emitFieldLabelCost F+16)*(L*L)) := by
    change _ ≤ p₁.eval (bitSize (comparisonInput D T S))+p₂.eval (bitSize (comparisonInput D T S))+_
    omega
  have hTotal := Nat.mul_le_mul hSize.2.2 hAll
  simp only [reciprocalVisitsCost,eval_add,eval_mul,eval_pow,eval_X,eval_C,pow_two]
  exact Nat.add_le_add_left hTotal 12

#print axioms reciprocalVisitsCost_originalBits
end EvenTI.P17Execution
