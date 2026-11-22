import EvenP10TrialPayload
import EvenP16AnchorSquareTrace
import EvenP16ReciprocalAnchorGrid
import EvenP16TrialAnchorEmit
import EvenP17RowTransvection
import EvenP5NormalFrame
import Mathproof.Meta.P15RecogIMPRank20261007
import Mathproof.Meta.Problem18Claude.Problem18ClaudeFieldMacrosInstancePow20261001
import Mathproof.Meta.Problem18Claude.Problem18ClaudeIMPElim20261001

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace EvenTI.P17Execution

open EvenTI.P16Execution EvenTI.Action EvenTI.Contract EvenTI.P15Execution
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dI dL dT dU dZ dO)
open Mathproof.P15RecogIMPGrid20261007 (Written gRows gCols gOut gU gV)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

/-- The complete reciprocal anchor computation after its cut and reciprocal
have been installed. Both mirror choices and every retained mode share the
same rectangular-grid and partial-trace checks. -/
theorem reciprocalAnchorGrid_framed_run (F : FieldPresentation K) {l n B S src inv cross square o tt uu z one : ℕ}
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
    (hLoad : InstalledCutMatrix F s l n src (flatten T)) (hRecip : InstalledCutMatrix F s l n inv N) :
    ∃ t, Run B (reciprocalAnchorGrid F mode.1) s t
      (crossGridCost F mode.1 n (n^l)+squareTraceCost F n) ∧ Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (o+(i.val*n+j.val)) = rawReciprocalAnchor T N mode i j) ∧
      (∀ k < o, k ≠ tt → k ≠ uu → val F canonical qN.WS t k = val F canonical qN.WS s k) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hZkeep : ¬ Written cross (n*n) (n*n) tt uu z := by unfold Written; omega
  have hOneKeep : ¬ Written cross (n*n) (n*n) tt uu one := by unfold Written; omega
  obtain ⟨u,hr,hs,hVals,hKeep,hRegs,hi,ho⟩ := crossGrid_run F mode.1 mode.2 hn hS hNN hA
    (by omega) (by omega) hSrcSep hInvSep (hCross.trans (by omega)) (by omega) (by omega) (by omega) hTU
    ⟨hT.1,hT.2.1⟩ ⟨hU.1,hU.2.1⟩ hZkeep hZero hR hC hL hO hTR hUR hZR hNr hAr hStride hSrc hInv
  let X : Matrix (Fin n × Fin n) (Fin n × Fin n) K := reciprocalFront (flatten T) mode * reciprocalBack N mode
  have hX (i j : Fin n × Fin n) : val F canonical qN.WS u
      (cross+(pairWordIndex i*(n*n)+pairWordIndex j)) = X i j := by
    have eq (p : Fin n × Fin n) : pairWordIndex p = (finProdFinEquiv p).val := by
      simp [pairWordIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [eq i,eq j,hVals _ (finProdFinEquiv i).isLt _ (finProdFinEquiv j).isLt]
    simpa only [Equiv.symm_apply_apply,X] using
      crossedSum_eq_panels F hn mode (finProdFinEquiv i) (finProdFinEquiv j) (flatten T) N hLoad hRecip
  obtain ⟨t,rt,hSt,hEnd,_,hSquareKeep,hIt,hOt⟩ := squareTrace_run F X hs hN hNN hCross hSquare hOut
    ⟨by omega,hT.2.2⟩ ⟨by omega,hU.2.2⟩ hTU hZ hOne
    ((hRegs dZ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hZR)
    ((hRegs dT (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTR)
    ((hRegs dU (by decide) (by decide) (by decide) (by decide) (by decide)).trans hUR)
    ((hRegs gRows (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR)
    ((hRegs gCols (by decide) (by decide) (by decide) (by decide) (by decide)).trans hC)
    ((hRegs anchorSideWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSide)
    ((hRegs anchorCrossWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCrossW)
    ((hRegs anchorSquareWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSquareW)
    ((hRegs anchorTraceWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTraceW)
    ((hRegs anchorUnitWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOneW)
    ((hKeep z (by omega) hZkeep).trans hZero) ((hKeep one (by omega) hOneKeep).trans hUnit) hX
  refine ⟨t,hr.seq rt,hSt,?_,?_,hIt.trans hi,hOt.trans ho⟩
  · intro i j
    rw [rawReciprocalAnchor_eq_products]
    exact hEnd i j
  · intro k hk hkt hku
    have hSFit : k < S := by omega
    have hNw (base m n : ℕ) (h : k < base) : ¬ Written base m n tt uu k := by
      unfold Written
      omega
    exact (hSquareKeep k hSFit (hNw square _ _ (by omega)) (hNw o _ _ hk)).trans
      (hKeep k hSFit (hNw cross _ _ (by omega)))

#print axioms reciprocalAnchorGrid_framed_run
end EvenTI.P17Execution

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace EvenTI.P17Execution

open EvenTI.P16Trial EvenTI.Contract EvenTI.P10Scan EvenTI.P15Trial EvenTI.PrimaryAlignment
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def blockLength : Expr := .add (.var fieldVectorLength) (.lit 1)

/-- Serialize one actually computed anchor in the literal length-prefixed
format used in the prepared trial's anchor list. -/
theorem emitAnchorBlock_framed_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn start : ℕ} {σ : Env} (A : NumberedAnchor K)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hW : A.width*A.width+1 < B)
    (hFit : start+A.width*A.width ≤ Sn)
    (hStart : σ.vars fieldVectorStart=start)
    (hLen : σ.vars fieldVectorLength=A.width*A.width)
    (hWidth : σ.vars emitAnchorWidth=A.width)
    (hRead : ∀ i : Fin (A.width*A.width),
      val F canonical qN.WS σ (start+i.val)=A.matrix (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) :
    ∃ τ, Run B (emitAnchorBlock D F) σ τ (emitAnchorBlockCost F A.width) ∧
      τ.out=σ.out++blockW (numberedAnchorWords D A) ∧ τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ r, r ≠ fieldVectorIndex → r ≠ labelAddress → τ.vars r=σ.vars r) := by
  let n := A.width
  let m := n*n
  change m+1 < B at hW
  have hN : n < B := by
    by_cases hz : n=0
    · omega
    · have hn : 0 < n := Nat.pos_of_ne_zero hz
      have hh : n ≤ m := Nat.le_mul_of_pos_right n hn
      omega
  have hL : (Expr.var fieldVectorLength).evalB B σ=some m :=
    evalB_var_iff.mpr ⟨hLen.symm,hLen ▸ (show m < B by omega)⟩
  have hb : blockLength.evalB B σ=some (m+1) :=
    evalB_bin (op := .add) hL (evalB_lit (by omega)) hW
  let ρ := {σ with out := σ.out++[m+1]}
  have hρ : Run B (.write blockLength) σ ρ 4 := Run.write hb
  have hn : (Expr.var emitAnchorWidth).evalB B ρ=some n :=
    evalB_var_iff.mpr ⟨hWidth.symm,hWidth ▸ hN⟩
  let α := {ρ with out := ρ.out++[n]}
  have hα : Run B (.write (.var emitAnchorWidth)) ρ α 2 := Run.write hn
  have hs : Slots F canonical qN.WS Sn B α := slots_frame F hSlots rfl rfl (fun _ _ => rfl) rfl
  obtain ⟨τ,hR,hO,hA,hI,hKeep⟩ := fieldVectorProgram_run D F hs hQ hP (by omega) hFit hStart hLen
  have hWords : ((List.range m).map fun i => (D (val F canonical qN.WS α (start+i))).val) =
      List.ofFn (fun i : Fin m => (D (A.matrix (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2)).val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hm : i < m := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact congrArg (fun x => (D x).val) (hRead ⟨i,hm⟩)
  have hFinal : Slots F canonical qN.WS Sn B τ := slots_frame F hs
    (congrFun hA _) (congrFun hA _) (fun a ha => hKeep a
      (fun e => (by decide : fieldVectorIndex ∉ regNames canonical) (e ▸ ha))
      (fun e => (by decide : labelAddress ∉ regNames canonical) (e ▸ ha)))
    (hKeep _ (by decide) (by decide))
  refine ⟨τ,?_,?_,hA,hI,hFinal,hKeep⟩
  · exact (hρ.seq (hα.seq hR)).mono (by unfold emitAnchorBlockCost; omega)
  · rw [hO,hWords]
    simp [α,ρ,blockW,numberedAnchorWords,m,n,List.append_assoc]

#print axioms emitAnchorBlock_framed_run
end EvenTI.P17Execution

set_option autoImplicit false

namespace EvenTI.P17Execution

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.P10Scan EvenTI.PrimaryAlignment
open Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15RecogIMPGrid20261007 (gRows)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def reciprocalCountWord : String := "even.reciprocal.record.count"

private def reciprocalLengthExpr : Expr :=
  .add (.lit 1) (.mul (.var reciprocalCountWord) (.add (.var gRows) (.lit 2)))

def emitReciprocalHeader : Com :=
  .seq (.write (.lit 0)) (.seq (.write reciprocalLengthExpr) (.write (.var reciprocalCountWord)))

def emitReciprocalHeaderCost : ℕ := 12

theorem emitReciprocalHeader_run {B n count : ℕ} {s : Env}
    (hFit : 1+count*(n*n+2) < B) (hN : n*n+2 < B)
    (hn : s.vars gRows=n*n) (hc : s.vars reciprocalCountWord=count) :
    Run B emitReciprocalHeader s
      {s with out := s.out++[0,1+count*(n*n+2),count]} emitReciprocalHeaderCost := by
  have hC : count ≤ count*(n*n+2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hProd : count*(n*n+2) < B := by omega
  let u : Env := {s with out := s.out++[0]}
  let v : Env := {s with out := u.out++[1+count*(n*n+2)]}
  have hRu : Run B (.write (.lit 0)) s u 2 := Run.write (evalB_lit (by omega))
  have hCV (w : Env) (h : w.vars=s.vars) :
      (Expr.var reciprocalCountWord).evalB B w=some count :=
    evalB_var_iff.mpr ⟨by rw [h,hc],by rw [h,hc]; omega⟩
  have hNV : (Expr.var gRows).evalB B u=some (n*n) :=
    evalB_var_iff.mpr ⟨by change n*n=s.vars gRows; exact hn.symm,
      by change s.vars gRows<B; rw [hn]; omega⟩
  have hLen : reciprocalLengthExpr.evalB B u=some (1+count*(n*n+2)) :=
    evalB_bin (op:=.add) (evalB_lit (by omega))
      (evalB_bin (op:=.mul) (hCV u rfl)
        (evalB_bin (op:=.add) hNV (evalB_lit (by omega)) hN) hProd) hFit
  have hRv : Run B (.write reciprocalLengthExpr) u v 8 := Run.write hLen
  have hRt : Run B (.write (.var reciprocalCountWord)) v {v with out := v.out++[count]} 2 :=
    Run.write (hCV v rfl)
  simpa only [emitReciprocalHeader,emitReciprocalHeaderCost,v,u,List.append_assoc,
    List.singleton_append,List.cons_append,List.nil_append,Nat.reduceAdd] using hRu.seq (hRv.seq hRt)

private theorem constantBlockLength {α : Type} (xs : List α) (enc : α → List ℕ)
    (w : ℕ) (hw : ∀ a ∈ xs, (enc a).length=w) :
    (xs.flatMap enc).length = xs.length*w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      hw a List.mem_cons_self,ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)),Nat.add_mul,Nat.one_mul]
    omega

theorem reciprocalTrialWords_exact (D : FieldEncoding K) {l n : ℕ}
    (A : HigherModes l → Matrix (Fin n) (Fin n) K) :
    let p := (PreparedTrial.reciprocal A : PreparedTrial K l n)
    let q := (l+1)+(l+1)
    preparedTrialWords D p =
      [0,1+q*(n*n+2),q] ++ ((numberedAnchors p).map (numberedAnchorWords D)).flatMap blockW := by
  dsimp only
  let p := (PreparedTrial.reciprocal A : PreparedTrial K l n)
  let xs := numberedAnchors p
  let ys := xs.map (numberedAnchorWords D)
  let q := (l+1)+(l+1)
  have hx : xs.length=q := by simp [xs,p,numberedAnchors,q,Nat.add_assoc]
  have hy : ys.length=q := by simp [ys,hx]
  have hBlock (w : List ℕ) (hw : w ∈ ys) : (blockW w).length=n*n+2 := by
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    have hb' : b ∈ List.ofFn (fun i : Fin q => numeric (A (reciprocalOrder l i))) := hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb'
    simp [blockW,numberedAnchorWords,numeric,Nat.add_assoc]
  have hLen := constantBlockLength ys blockW (n*n+2) hBlock
  have hE : (listW ys).length=1+q*(n*n+2) := by
    simp only [listW,List.length_cons,hLen,hy]
    omega
  change (0::pairW (listW ys) []) = [0,1+q*(n*n+2),q]++ys.flatMap blockW
  unfold pairW
  rw [hE,List.append_nil]
  simp [listW,hy]


theorem reciprocalOrder_first {l : ℕ} (i : Fin (l+1)) :
    reciprocalOrder l (Fin.castAdd (l+1) i) = (true,i) := by
  change (Equiv.boolProdEquivSum (Fin (l+1))).symm
    (Equiv.sumComm _ _ (finSumFinEquiv.symm (Fin.castAdd (l+1) i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem reciprocalOrder_second {l : ℕ} (i : Fin (l+1)) :
    reciprocalOrder l (Fin.natAdd (l+1) i) = (false,i) := by
  change (Equiv.boolProdEquivSum (Fin (l+1))).symm
    (Equiv.sumComm _ _ (finSumFinEquiv.symm (Fin.natAdd (l+1) i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

#print axioms reciprocalOrder_first
#print axioms reciprocalOrder_second
#print axioms emitReciprocalHeader_run
#print axioms reciprocalTrialWords_exact
end EvenTI.P17Execution

set_option autoImplicit false

namespace EvenTI.P17Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN)
open scoped Matrix

variable {K : Type} [Field K] [Fintype K]

/-- A transposed bank runs the same row command for the right elementary
operation. Its physical destination is precisely the requested column. -/
theorem columnTransvection_transposed_run (F : FieldPresentation K)
    {B Sn m n base : ℕ} {s : Env} (A : Matrix (Fin m) (Fin n) K)
    (i j : Fin n) (hij : i ≠ j) (c : K) (hSlots : Slots F canonical qN.WS Sn B s)
    (hbase : 5 ≤ base) (hfit : base+n*m ≤ Sn)
    (hN : s.vars qN.N=m) (hI : s.vars qN.u=base+j.val*m) (hJ : s.vars qN.w=base+i.val*m)
    (hCoeff : val F canonical qN.WS s 2 = -c)
    (hRead : ∀ a b, val F canonical qN.WS s (base+b.val*m+a.val)=A a b) :
    ∃ t, Run B (rowTransvection F) s t (rowTransvectionCost F m) ∧
      Slots F canonical qN.WS Sn B t ∧
      (∀ a b, val F canonical qN.WS t (base+b.val*m+a.val) =
        (A * Matrix.transvection i j c) a b) ∧
      (∀ x < Sn, (x < base+j.val*m ∨ base+j.val*m+m ≤ x) → x ≠ 3 → x ≠ 4 →
        val F canonical qN.WS t x = val F canonical qN.WS s x) ∧
      (∀ x, x ∉ regNames canonical → x ≠ qN.j → t.vars x=s.vars x) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,hRun,hS,hAt,hOff,hVars,hIn,hOut⟩ := rowTransvection_run F A.transpose
    j i hij.symm c hSlots hbase hfit hN hI hJ hCoeff (fun b a => hRead a b)
  refine ⟨t,hRun,hS,?_,hOff,hVars,hIn,hOut⟩
  intro a b
  rw [hAt b a]
  by_cases hb : b=j
  · subst b
    rw [Matrix.transvection_mul_apply_same,Matrix.mul_transvection_apply_same]
    rfl
  · rw [Matrix.transvection_mul_apply_of_ne j i b a hb c _,
      Matrix.mul_transvection_apply_of_ne i j a b hb c A]
    rfl

#print axioms columnTransvection_transposed_run
end EvenTI.P17Execution

set_option autoImplicit false

namespace EvenTI.P17Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPPivot20261001 (rowStart)
open Mathproof.Problem18ClaudeIMPElim20261001 (elimPhase elimCost elim_run rowStart_lt)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15RecogIMPRank20261007 (qN_valid)

variable {K : Type} [Field K] [Fintype K]

/-- Clear a live pivot column with the distinguished row placed first. The
width includes any additional columns carrying basis changes. -/
noncomputable def clearPivotColumn (F : FieldPresentation K) : Com :=
  elimPhase (fieldMacros F) qN

noncomputable def clearedColumns {rows width : ℕ} (A : Matrix (Fin (rows+1)) (Fin width) K)
    (pivot : Fin width) : Matrix (Fin (rows+1)) (Fin width) K :=
  fun i j => if i=0 then A i j else A i j-(A i pivot * (A 0 pivot)⁻¹)*A 0 j

theorem clearedColumns_pivot {rows width : ℕ} (A : Matrix (Fin (rows+1)) (Fin width) K)
    (pivot : Fin width) (h : A 0 pivot ≠ 0) {i : Fin (rows+1)} (hi : i≠0) :
    clearedColumns A pivot i pivot = 0 := by
  simp only [clearedColumns,hi,if_false,mul_assoc, inv_mul_cancel₀ h,mul_one,sub_self]

/-- A complete paid pivot pass reads the live pivot and updates every row.
If the input includes extra columns, the same proven operations act on them
without additional row searches or repetitions. -/
theorem clearPivotColumn_run (F : FieldPresentation K)
    {B S rows width : ℕ} {s : Env}
    (A : Matrix (Fin (rows+1)) (Fin width) K) (pivot : Fin width)
    (hs : Slots F canonical qN.WS S B s)
    (hu : s.vars qN.u=0) (hN : s.vars qN.N=width)
    (hc : s.vars qN.c=rows+1) (hp : s.vars qN.pv=pivot.val)
    (hfit : rowStart width (rows+1) ≤ S) (hRows : rows+1 < B)
    (hUnit : A 0 pivot ≠ 0)
    (hAt : ∀ i j, val F canonical qN.WS s (rowStart width i.val+j.val) = A i j) :
    ∃ t, Run B (clearPivotColumn F) s t (elimCost (fieldMacros F) qN width (rows+1)) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i j, val F canonical qN.WS t (rowStart width i.val+j.val) =
        clearedColumns A pivot i j) ∧
      (∀ k < S, rowStart width (rows+1) ≤ k → val F canonical qN.WS t k = val F canonical qN.WS s k) ∧
      (∀ x, x ∉ regNames canonical → x≠qN.w → x≠qN.j → t.vars x=s.vars x) ∧
        t.inp=s.inp ∧ t.out=s.out := by
  classical
  have hNz : val F canonical qN.WS s (rowStart width 0+pivot.val) ≠ 0 := by
    rw [show val F canonical qN.WS s (rowStart width 0+pivot.val) = A 0 pivot from hAt 0 pivot]
    exact hUnit
  obtain ⟨t,r,hS,hRowsAt,_,hKeep,hVars,_,hi,ho⟩ := elim_run
    (fieldMacros F) qN qN_valid hs hu hN hc hp (by omega) pivot.isLt hfit hNz hRows
  refine ⟨t,r,hS,?_,fun k hk he => hKeep k hk (.inr (.inr he)),hVars,hi,ho⟩
  intro i j
  by_cases h : i=0
  · subst i
    have hBefore : rowStart width (0 : ℕ)+j.val < rowStart width 1 := by
      have hlt := rowStart_lt (N:=width) (show 0<1 by decide)
      have hj := j.isLt
      omega
    have hBound := rowStart_lt (N:=width) (show 0 < rows+1 by omega)
    rw [show (0 : Fin (rows+1)).val=0 by rfl]
    rw [hKeep _ (by have hj := j.isLt; omega) (.inr (.inl ⟨by simp [rowStart],hBefore⟩))]
    change val F canonical qN.WS s (rowStart width 0+j.val) = clearedColumns A pivot 0 j
    rw [show val F canonical qN.WS s (rowStart width 0+j.val)=A 0 j from hAt 0 j]
    simp [clearedColumns]
  · have hh : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => h (Fin.ext h0))
    rw [hRowsAt i.val hh i.isLt j.val j.isLt]
    have hp0 : val F canonical qN.WS s (rowStart width 0+pivot.val)=A 0 pivot := hAt 0 pivot
    have hj0 : val F canonical qN.WS s (rowStart width 0+j.val)=A 0 j := hAt 0 j
    rw [hAt i j,hAt i pivot,hp0,hj0]
    simp [clearedColumns,h]

#print axioms clearPivotColumn_run
#print axioms clearedColumns_pivot
end EvenTI.P17Execution

set_option autoImplicit false

namespace EvenTI.P17Execution

open Matrix Matrix.TransvectionStruct
open EvenTI.TrialProducer
open scoped Matrix

variable {K : Type} [Field K] [Fintype K]

/-- A pass gives each destination row its one recorded transvection, while
leaving the common pivot row available to every other destination. -/
theorem transvectionRoster_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (p : Fin m) (c : Fin m → K) (rs : List (Fin m)) (hd : rs.Nodup)
    (hp : p ∉ rs) (i : Fin m) (j : Fin n) :
    ((rs.map fun a => Matrix.transvection a p (c a)).prod * A) i j =
      if i ∈ rs then A i j+c i*A p j else A i j := by
  induction rs generalizing i j with
  | nil => simp
  | cons a rs ih =>
    obtain ⟨ha,hd⟩ := List.nodup_cons.mp hd
    have hpa : p≠a := fun e => hp (List.mem_cons.mpr (.inl e))
    have hpr : p∉rs := fun hm => hp (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons,List.prod_cons,Matrix.mul_assoc]
    by_cases hi : i=a
    · subst i
      rw [Matrix.transvection_mul_apply_same,ih hd hpr a j]
      have ea := ih hd hpr p j
      simp [ha,hpr,ea]
    · rw [Matrix.transvection_mul_apply_of_ne a p i j hi,ih hd hpr i j]
      simp [hi]

private theorem nonpivotRows_injective {rows : ℕ} :
    Function.Injective (Fin.succ : Fin rows → Fin (rows+1)) :=
  fun _ _ e => Fin.ext (Nat.succ.inj (congrArg Fin.val e))

def clearedRowMoves {rows width : ℕ} (A : Matrix (Fin (rows+1)) (Fin width) K)
    (pivot : Fin width) : List (TransvectionStruct (Fin (rows+1)) K) :=
  (List.finRange rows).map fun i =>
    ⟨i.succ,0,by simp, -(A i.succ pivot * (A 0 pivot)⁻¹)⟩

/-- The entire paid column-clearing pass acts by a stored matrix unit on
all columns, including any columns that track the basis. -/
theorem clearedColumns_eq_unit {rows width : ℕ}
    (A : Matrix (Fin (rows+1)) (Fin width) K) (pivot : Fin width) :
    clearedColumns A pivot = (elementaryUnit (clearedRowMoves A pivot)).val * A := by
  let rs := (List.finRange rows).map (Fin.succ : Fin rows → Fin (rows+1))
  let c : Fin (rows+1) → K := fun a => -(A a pivot * (A 0 pivot)⁻¹)
  have hd : rs.Nodup := (List.nodup_finRange _).map nonpivotRows_injective
  have hmem (i : Fin (rows+1)) : i ∈ rs ↔ i≠0 := by
    simp only [rs,List.mem_map,List.mem_finRange,true_and]
    exact ⟨fun ⟨a,h⟩ => h ▸ (Fin.succ_ne_zero a),
      fun hi => ⟨i.pred hi,Fin.succ_pred i hi⟩⟩
  have hp : (0 : Fin (rows+1)) ∉ rs := fun hx => (hmem 0).mp hx rfl
  have hm : (elementaryUnit (clearedRowMoves A pivot)).val =
      (rs.map fun a => Matrix.transvection a 0 (c a)).prod := by
    simp [clearedRowMoves,elementaryUnit,List.map_map,rs,c,Function.comp_def]
  rw [hm]
  ext i j
  rw [transvectionRoster_apply A 0 c rs hd hp i j]
  by_cases hi : i=0
  · subst i
    simp [clearedColumns,hp]
  · have hh : i ∈ rs := (hmem i).mpr hi
    simp [clearedColumns,hi,hh,c,sub_eq_add_neg]

#print axioms transvectionRoster_apply
#print axioms clearedColumns_eq_unit
end EvenTI.P17Execution
