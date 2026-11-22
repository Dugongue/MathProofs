import EvenP15RecoverConstantTable
import Mathproof.Meta.Problem18PairLargeBank20261004
import EvenP15RecoverIncidenceBuild

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Action EvenTI.Contract EvenTI.Part8

set_option maxHeartbeats 2300000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def baseLogTable (F : FieldEncoding K) (L : BaseUnitLog K) : List ℕ :=
  List.ofFn fun j =>
    if h : F.symm j = 0 then 0 else (L.encode (Units.mk0 (F.symm j) h)).val

private theorem baseLogTable_lookup (F : FieldEncoding K) (L : BaseUnitLog K) (x : Kˣ) :
    (baseLogTable F L).getD (F (x : K)).val 0 = (L.encode x).val := by
  have hi := (F (x : K)).isLt
  unfold baseLogTable
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),List.getElem_ofFn]
  have he : (⟨(F (x : K)).val, _⟩ : Fin (Fintype.card K)) = F (x : K) := Fin.ext rfl
  rw [he,F.symm_apply_apply,dif_neg x.ne_zero]
  congr
  exact Units.ext rfl

def logArg : String := "even.recovery.log.arg"
def logValue : String := "even.recovery.log.value"

def logCode (F : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  constantWordTable logArg logValue 0 (baseLogTable F L)

/-- The base-field discrete logarithm is a fixed finite table, independent
of the extension degrees and of the input tensor. -/
theorem logCode_run (F : FieldEncoding K) (L : BaseUnitLog K) (x : Kˣ) {W : ℕ} {s : Env}
    (hW : Fintype.card K < W) (hx : s.vars logArg = (F (x : K)).val) :
    ∃ t, Run W (logCode F L) s t (6*Fintype.card K+2) ∧
      t.vars logValue = (L.encode x).val ∧ Frame (logCode F L) s t := by
  have h : 0+((baseLogTable F L).length) < W := by
    simpa only [Nat.zero_add,baseLogTable,List.length_ofFn] using hW
  have hWords : ∀ v ∈ baseLogTable F L, v < W := by
    intro v hv
    unfold baseLogTable at hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    split
    · omega
    · let M := Fintype.card K - 1
      have hM : 0 < M := Nat.sub_pos_of_lt Fintype.one_lt_card
      letI : NeZero M := ⟨hM.ne'⟩
      exact (ZMod.val_lt _).trans (by change Fintype.card K - 1 < W; omega)
  obtain ⟨t,hRun,hVal,hFrame⟩ :=
    constantWordTable_run logArg logValue (baseLogTable F L) ((F (x : K)).isLt.trans hW) hx h hWords
  refine ⟨t,?_,?_,hFrame⟩
  · simpa only [logCode,baseLogTable,List.length_ofFn] using hRun
  · simpa only [Nat.zero_le,if_true,Nat.sub_zero,baseLogTable_lookup] using hVal

#print axioms logCode_run


theorem logCode_preserves (F : FieldEncoding K) (L : BaseUnitLog K) (name : String)
    (h : name ≠ logValue) :
    name ∉ Mathproof.Problem18IMPFieldLayout20261001.scalarWrites (logCode F L) := by
  apply constantWordTable_preserves
  exact h

theorem logCode_arrayFrame (F : FieldEncoding K) (L : BaseUnitLog K) (name : String) :
    name ∉ Mathproof.Problem18IMPFieldLayout20261001.arrayWrites (logCode F L) := by
  apply constantWordTable_arrayFrame

end EvenTI.P15Recover

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open EvenTI.Action EvenTI.Contract EvenTI.Part8
open EvenTI.P12Compare (crtRhsBank)

set_option maxHeartbeats 2700000

def residualWordBank : String := "even.recovery.residue.unit_codes"
def residueLogRow : String := "even.recovery.residue.rhs_row"

private def readResidualWord : Com :=
  .assign logArg (.get residualWordBank (.var residueLogRow))
private def storeLogWord : Com :=
  .store crtRhsBank (.var residueLogRow) (.var logValue)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def installLogRow (F : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq readResidualWord (.seq (logCode F L) storeLogWord)

theorem installLogRow_run (F : FieldEncoding K) (L : BaseUnitLog K) (x : Kˣ)
    {r W : ℕ} {s : Env} (hWidth : Fintype.card K < W) (hRow : s.vars residueLogRow = r)
    (hr : r < W) (hSource : r < (s.arrs residualWordBank).length)
    (hWord : (s.arrs residualWordBank).getD r 0 = (F (x : K)).val)
    (hDest : r < (s.arrs crtRhsBank).length) :
    ∃ t, Run W (installLogRow F L) s t (6*Fintype.card K+8) ∧
      t.arrs crtRhsBank = (s.arrs crtRhsBank).set r (L.encode x).val ∧
      Frame (installLogRow F L) s t := by
  let q := (F (x : K)).val
  let u := s.setVar logArg q
  have hSome : (s.arrs residualWordBank)[r]? = some q := by
    rw [List.getElem?_eq_getElem hSource]
    simpa [q,List.getD,hSource] using congrArg some hWord
  have r0 : Run W readResidualWord s u 3 := Run.assign
    (evalB_get (ev_var hRow hr) hSome ((F (x : K)).isLt.trans hWidth))
  obtain ⟨v,r1,hValue,f1⟩ := logCode_run F L x hWidth (s:=u) (by simp [u,q])
  have hReg : v.vars residueLogRow = r := (f1.vars _ (logCode_preserves F L _ (by decide))).trans
    (by simpa [u,vars_setVar,show residueLogRow ≠ logArg by decide] using hRow)
  have hArr : v.arrs crtRhsBank = s.arrs crtRhsBank := f1.arrs _ (logCode_arrayFrame F L _)
  have hM : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  letI : NeZero (Fintype.card K - 1) := ⟨hM.ne'⟩
  have hVal : (L.encode x).val < W := (ZMod.val_lt _).trans (by omega)
  let t := v.setArr crtRhsBank r (L.encode x).val
  have r2 : Run W storeLogWord v t 3 := Run.store (ev_var hReg hr) (ev_var hValue hVal)
    (by rwa [hArr])
  have rr : Run W (installLogRow F L) s t (6*Fintype.card K+8) :=
    (r0.seq (r1.seq r2)).mono (by omega)
  exact ⟨t,rr,by simp [t,hArr],Frame.of_run rr⟩

#print axioms installLogRow_run


open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites arrayWrites) in
theorem installLogRow_scalarFrame (F : FieldEncoding K) (L : BaseUnitLog K) (k : String)
    (ha : k ≠ logArg) (hb : k ≠ logValue) : k ∉ scalarWrites (installLogRow F L) := by
  simp [installLogRow,readResidualWord,storeLogWord,scalarWrites,ha,logCode_preserves F L k hb]

open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites) in
theorem installLogRow_arrayFrame (F : FieldEncoding K) (L : BaseUnitLog K) (k : String)
    (hk : k ≠ crtRhsBank) : k ∉ arrayWrites (installLogRow F L) := by
  simp [installLogRow,readResidualWord,storeLogWord,arrayWrites,logCode_arrayFrame,hk]

end EvenTI.P15Recover

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairLargeBank20261004 (zeroBlock zeroBlock_run Clean)
open Mathproof.Problem18PairLargeWords20261004 (wcSrc wcDst wcCnt)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open EvenTI.Action EvenTI.Contract EvenTI.Part8
open EvenTI.P12Compare (crtRhsBank fixedCoordinateRhs)
open EvenTI.P14Recovery (baseRows)

set_option maxRecDepth 28000
set_option maxHeartbeats 4500000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def residualLength : Expr := .add (.var baseRows) (.var inputColsR)
private def clearLogs : Com := zeroBlock crtRhsBank (.lit 0) residualLength
private def logStart : Com := .assign residueLogRow (.lit 0)
private def logInc : Com := .assign residueLogRow (.add (.var residueLogRow) (.lit 1))
private def logStep (F : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq (installLogRow F L) logInc
private def logGuard : Cond := .lt (.var residueLogRow) (.var baseRows)

def installResidualLogs (F : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq clearLogs (.seq logStart (.while logGuard (logStep F L)))

def installResidualLogsCost (F : FieldEncoding K) (m n : ℕ) : ℕ :=
  20*(m+n)+(6*Fintype.card K+16)*m+24

private def logPrefixValue {m n : ℕ} (L : BaseUnitLog K)
    (x : Fin m → Kˣ) (p : ℕ) (j : Fin (m+n)) : ℕ :=
  if h : j.val < m then
    if j.val < p then (L.encode (x ⟨j.val,h⟩)).val else 0
  else 0

private structure LogState {m n : ℕ} (F : FieldEncoding K) (L : BaseUnitLog K) (x : Fin m → Kˣ)
    (p : ℕ) (s : Env) : Prop where
  len : (s.arrs crtRhsBank).length = m+n
  sourceLen : m ≤ (s.arrs residualWordBank).length
  source : ∀ i : Fin m, (s.arrs residualWordBank).getD i.val 0 = (F (x i : K)).val
  base : s.vars baseRows = m
  prefixData : ∀ j : Fin (m+n), (s.arrs crtRhsBank).getD j.val 0 = logPrefixValue L x p j

private theorem logStep_run {m n W : ℕ} {s : Env}
    (F : FieldEncoding K) (L : BaseUnitLog K) (x : Fin m → Kˣ) (r : Fin m)
    (hQ : Fintype.card K < W) (hmW : m < W)
    (hs : LogState (n:=n) F L x r.val s) (hr : s.vars residueLogRow = r.val) :
    ∃ t, Run W (logStep F L) s t (6*Fintype.card K+12) ∧
      t.vars residueLogRow = r.val+1 ∧ LogState (n:=n) F L x (r.val+1) t := by
  have hDest : r.val < (s.arrs crtRhsBank).length := by rw [hs.len]; have := r.isLt; omega
  obtain ⟨u,r0,hStore,f0⟩ := installLogRow_run F L (x r) hQ hr
    (r.isLt.trans hmW) (r.isLt.trans_le hs.sourceLen) (hs.source r) hDest
  have hR : u.vars residueLogRow = r.val :=
    (f0.vars _ (installLogRow_scalarFrame F L _ (by decide) (by decide))).trans hr
  let t := u.setVar residueLogRow (r.val+1)
  have r1 : Run W logInc u t 4 := Run.assign
    (ev_add (ev_var hR (r.isLt.trans hmW)) (evalB_lit (by omega))
      ((Nat.succ_le_of_lt r.isLt).trans_lt hmW))
  have rr : Run W (logStep F L) s t (6*Fintype.card K+12) := by
    simpa only [logStep,Nat.add_assoc] using r0.seq r1
  have hA : t.arrs residualWordBank = s.arrs residualWordBank :=
    f0.arrs _ (installLogRow_arrayFrame F L _ (by decide))
  refine ⟨t,rr,by simp [t],⟨(Frame.of_run rr).len _ |>.trans hs.len,
    by rw [hA]; exact hs.sourceLen,fun i => by rw [hA]; exact hs.source i,
    ?_,?_⟩⟩
  · exact (f0.vars _ (installLogRow_scalarFrame F L _ (by decide) (by decide))).trans hs.base
  · intro j
    change (u.arrs crtRhsBank).getD _ 0 = _
    rw [hStore]
    by_cases hd : j.val = r.val
    · rw [hd,getD_set_self' hDest]
      simp [logPrefixValue,hd,r.isLt]
    · rw [getD_set_ne' (Ne.symm hd),hs.prefixData j]
      have he : j.val < r.val+1 ↔ j.val < r.val := by omega
      simp [logPrefixValue,he]

/-- Physically install every base-logarithm RHS, with zeros in the fixed padding rows. -/
theorem installResidualLogs_run {m n W : ℕ} {s : Env}
    (F : FieldEncoding K) (L : BaseUnitLog K) (x : Fin m → Kˣ)
    (hW : m+n < W) (hQ : Fintype.card K < W) (h1 : 1 < W)
    (hBase : s.vars baseRows = m) (hN : s.vars inputColsR = n)
    (hLen : (s.arrs crtRhsBank).length = m+n)
    (hSource : m ≤ (s.arrs residualWordBank).length)
    (hData : ∀ i : Fin m, (s.arrs residualWordBank).getD i.val 0 = (F (x i : K)).val) :
    ∃ t, Run W (installResidualLogs F L) s t (installResidualLogsCost F m n) ∧
      t.arrs crtRhsBank = List.ofFn (fun r =>
        (fixedCoordinateRhs (fun j => L.encode (x j)) (0 : Fin n → ZMod (Fintype.card K-1)) 0 r).val) ∧
      Frame (installResidualLogs F L) s t := by
  have hmW : m < W := by omega
  have e : residualLength.evalB W s = some (m+n) :=
    ev_add (ev_var hBase hmW) (ev_var hN (by omega)) hW
  obtain ⟨u,r0,_,_,hUlen,hFill,_,_⟩ :=
    zeroBlock_run crtRhsBank s (d:=.lit 0) (n:=residualLength)
      (by simp [Clean,residualLength,NoVar,wcSrc,wcDst,wcCnt,baseRows,inputColsR] : Clean residualLength) (evalB_lit (by omega)) e
      (by rw [hLen]; simp) (by rwa [hLen]) h1
  have rr0 : Run W clearLogs s u (20*(m+n)+16) := r0
  let v := u.setVar residueLogRow 0
  have rr1 : Run W logStart u v 2 := Run.assign (evalB_lit (by omega))
  have fv := Frame.of_run (rr0.seq rr1)
  have hz : v.vars residueLogRow = 0 := by simp [v]
  have hV : LogState (n:=n) F L x 0 v := by
    have hKeep : v.arrs residualWordBank = s.arrs residualWordBank := fv.arrs _ (by decide)
    refine ⟨(fv.len _).trans hLen,by rw [hKeep]; exact hSource,fun i => by rw [hKeep]; exact hData i,
      (fv.vars _ (by decide)).trans hBase,?_⟩
    intro j
    change (u.arrs crtRhsBank).getD j.val 0 = _
    rw [hFill]
    simp [j.isLt,logPrefixValue]
  let I (s : Env) := s.vars residueLogRow ≤ m ∧ LogState (n:=n) F L x (s.vars residueLogRow) s
  let G (s : Env) := m-s.vars residueLogRow
  have ht (s : Env) (hs : I s) : logGuard.evalB W s =
      some (decide (s.vars residueLogRow < m)) :=
    evalB_condLt (ev_var rfl (hs.1.trans_lt hmW)) (ev_var hs.2.base hmW)
  have hs (s : Env) (hS : I s) (hg : logGuard.evalB W s = some true) :
      ∃ t, Run W (logStep F L) s t (6*Fintype.card K+12) ∧ I t ∧ G t < G s := by
    rw [ht s hS] at hg
    have he : s.vars residueLogRow < m := by simpa using hg
    let i : Fin m := ⟨_,he⟩
    obtain ⟨t,r,hn,hp⟩ := logStep_run F L x i hQ hmW hS.2 rfl
    refine ⟨t,r,⟨by rw [hn]; exact Nat.succ_le_of_lt he,by rw [hn]; exact hp⟩,?_⟩
    simp only [G,hn,i]
    omega
  have hi : I v := ⟨by simp [hz],by rwa [hz]⟩
  obtain ⟨t,r2,hI,hStop⟩ := Run.while_count I G (6*Fintype.card K+12)
    (fun s hs => ⟨_,ht s hs⟩) hs hi
  rw [ht t hI] at hStop
  have hDone : t.vars residueLogRow = m := by
    have hGe : ¬ t.vars residueLogRow < m := by simpa using hStop
    have := hI.1
    omega
  have rr : Run W (installResidualLogs F L) s t (installResidualLogsCost F m n) :=
    (rr0.seq (rr1.seq r2)).mono (by
      simp [installResidualLogsCost,G,hz,logGuard,Cond.size,Expr.size,
        show 4+(6*Fintype.card K+12)=6*Fintype.card K+16 by omega] <;> omega)
  refine ⟨t,rr,?_,Frame.of_run rr⟩
  apply List.ext_getElem (by rw [hI.2.len,List.length_ofFn])
  intro k hk hk'
  let j : Fin (m+n) := ⟨k,by rwa [hI.2.len] at hk⟩
  have he := hI.2.prefixData j
  rw [hDone,List.getD_eq_getElem _ _ hk] at he
  rw [List.getElem_ofFn]
  change (t.arrs crtRhsBank)[k] = (fixedCoordinateRhs (fun i => L.encode (x i))
    (0 : Fin n → ZMod (Fintype.card K-1)) 0 j).val
  rw [he]
  by_cases hx : j.val < m <;> simp [logPrefixValue,fixedCoordinateRhs,hx]

#print axioms installResidualLogs_run


theorem installResidualLogs_scalarFrame (F : FieldEncoding K) (L : BaseUnitLog K) (k : String)
    (h : k ∉ [wcSrc,wcDst,wcCnt,Mathproof.Problem18PairLargeWords20261004.wcIdx,
      residueLogRow,logArg,logValue]) :
    k ∉ scalarWrites (installResidualLogs F L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  have hLog := installLogRow_scalarFrame F L k h.2.2.2.2.2.1 h.2.2.2.2.2.2
  simp [installResidualLogs,clearLogs,logStart,logStep,logInc,zeroBlock,
    Mathproof.Problem18PairLargeWords20261004.zeroFill,Mathproof.Problem18PairLargeWords20261004.zeroBody,
    scalarWrites,hLog,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1]

theorem installResidualLogs_arrayFrame (F : FieldEncoding K) (L : BaseUnitLog K) (k : String)
    (h : k ≠ crtRhsBank) : k ∉ arrayWrites (installResidualLogs F L) := by
  have hLog := installLogRow_arrayFrame F L k h
  simp [installResidualLogs,clearLogs,logStart,logStep,logInc,zeroBlock,
    Mathproof.Problem18PairLargeWords20261004.zeroFill,Mathproof.Problem18PairLargeWords20261004.zeroBody,
    arrayWrites,hLog,h]

end EvenTI.P15Recover

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)
open EvenTI.P14Recovery
open EvenTI.P12Compare (fixedCoordinateMatrix fixedCoordinateRhs coordinateBank crtRhsBank crtActive recoverLinear)

set_option maxRecDepth 45000
set_option maxHeartbeats 6000000

def solveIncidence : Com := .seq buildIncidenceMatrix completeCoordinateRecovery

def solveIncidenceCost (M m n : ℕ) : ℕ :=
  buildIncidenceCost m n+completeCoordinateRecoveryCost M m n

/-- Run the installed ternary source bank through exact coefficient assembly
and full coordinate recovery. The source supplies residue RHS words only;
the actual matrix, all probe rows, and all prefix constraints are built here. -/
theorem solveIncidence_run {M W m n : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (b : Fin m → ZMod M)
    (hW : 4*M*M+4*M+10 < W) (hThree : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hData : IncidenceInput s src)
    (hCan : Canonical M (s.arrs constraintMatrix)) (hCap : (s.arrs constraintMatrix).length < W)
    (hRhs : s.arrs crtRhsBank = List.ofFn (fun r => (fixedCoordinateRhs (n := n) b 0 0 r).val))
    (hScratch : n = 0 → m ≤ (s.arrs EvenTI.P12ComparePrep.coefficientBank).length) :
    ∃ t, Run W solveIncidence s t (solveIncidenceCost M m n) ∧ Frame solveIncidence s t ∧
      match recoverLinear (incidenceMatrix M src) b with
      | some x => t.vars crtActive = 1 ∧ ∀ i, (t.arrs coordinateBank).getD i.val 0 = (x i).val
      | none => t.vars crtActive = 0 := by
  obtain ⟨u,ru,huCan,hCoeffs,hPad,fu⟩ := buildIncidenceMatrix_run src (by omega : 2*M+4<W)
    hThree (by omega) (by omega) (by omega) hData hCan hLayout.sourceLen hCap
    hLayout.rows hLayout.base hLayout.cols hLayout.modWord
  have hu : RecoveryLayout M m n u := by
    refine ⟨(fu.vars _ (by decide)).trans hLayout.rows,(fu.vars _ (by decide)).trans hLayout.cols,
      (fu.vars _ (by decide)).trans hLayout.modWord,(fu.vars _ (by decide)).trans hLayout.base,
      by rw [fu.len _]; exact hLayout.sourceLen,by rw [fu.len _]; exact hLayout.workLen,?_,
      (fu.len _).trans hLayout.coLen,(fu.len _).trans hLayout.tgLen,
      (fu.len _).trans hLayout.modLen,by rw [fu.len _]; exact hLayout.destLen⟩
    rw [fu.arrs matrixR (by decide)]
    exact hLayout.workCanon
  have huB : ConstraintBanks (incidenceMatrix M src) b 0 0 u := by
    refine ⟨huCan,?_,?_,(fu.arrs _ (by decide)).trans hRhs⟩
    · intro r j
      by_cases hr : r.val < m
      · rw [fixedCoordinateMatrix,dif_pos hr]
        exact hCoeffs ⟨r.val,hr⟩ j
      · simp only [fixedCoordinateMatrix,dif_neg hr,Nat.not_lt_zero,if_false]
        have hb := Nat.mul_le_mul_right n (Nat.le_of_not_gt hr)
        have hm : m*n ≤ r.val*n+j.val := by omega
        have hi : r.val*n+j.val < (m+n+1)*n :=
          (packed_lt r j).trans_le (Nat.mul_le_mul_right n (by omega))
        unfold decode
        rw [hPad _ hm hi,Nat.cast_zero]
    · intro j
      have hLe : m ≤ m+n := by omega
      have hAddr : m*n ≤ (m+n)*n+j.val := (Nat.mul_le_mul_right n hLe).trans (Nat.le_add_right _ _)
      exact hPad _ hAddr (packed_lt (Fin.last (m+n)) j)
  obtain ⟨t,rt,_,ht⟩ := completeCoordinateRecovery_run (incidenceMatrix M src) b hW hL hu huB
    (fun hn => by rw [fu.len _]; exact hScratch hn)
  have rr : Run W solveIncidence s t (solveIncidenceCost M m n) := ru.seq rt
  exact ⟨t,rr,Frame.of_run rr,ht⟩

#print axioms solveIncidence_run


section Prefix

open EvenTI.CellPreparation EvenOrdinaryTI.LiveRows

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s)

theorem incidenceInput_of_prefixBank (bank : PreparedPrefix) (hBank : PrefixBankExact X Y orig bank)
    {u : Env} (hLen : 3*RowCount t d ≤ bank.source.length) (hRead : u.arrs incidenceBank = bank.source) :
    IncidenceInput u (physicalSrc orig) := by
  exact ⟨by rw [hRead]; exact hLen,fun r e => by rw [hRead]; exact hBank.source r e⟩

theorem incidenceMatrix_eq_baseEquation :
    incidenceMatrix (Fintype.card K-1) (physicalSrc orig) =
      EvenTI.Part8.baseEquationMatrix (K:=K) orig := rfl

#print axioms incidenceInput_of_prefixBank
#print axioms incidenceMatrix_eq_baseEquation

end Prefix

end EvenTI.P15Recover

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open EvenTI.Action EvenTI.Contract EvenTI.Part8
open EvenTI.P14Recovery
open EvenTI.P12Compare (recoverLinear crtActive coordinateBank crtRhsBank)

set_option maxRecDepth 38000
set_option maxHeartbeats 5800000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def recoverBaseExponents (F : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq (installResidualLogs F L) solveIncidence

def recoverBaseExponentsCost (F : FieldEncoding K) (m n : ℕ) : ℕ :=
  installResidualLogsCost F m n+solveIncidenceCost (Fintype.card K-1) m n

local notation "H" => (Fintype.card K-1)
private local instance baseOrder : NeZero H := ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

set_option backward.isDefEq.respectTransparency false in
/-- Starting from the encoded base residuals and ternary addresses, install
both residue banks and return the complete checked CRT assignment. -/
theorem recoverBaseExponents_run {m n W : ℕ} {s : Env}
    (F : FieldEncoding K) (L : BaseUnitLog K) (src : Fin m → Fin 3 → Fin n) (rho : Fin m → Kˣ)
    (hW : 4*H*H+4*H+10 < W) (hThree : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout H m n s) (hData : IncidenceInput s src)
    (hCan : Canonical H (s.arrs constraintMatrix)) (hCap : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length = m+n)
    (hSource : m ≤ (s.arrs residualWordBank).length)
    (hResidual : ∀ i : Fin m, (s.arrs residualWordBank).getD i.val 0 = (F (rho i : K)).val)
    (hScratch : n = 0 → m ≤ (s.arrs EvenTI.P12ComparePrep.coefficientBank).length) :
    ∃ t, Run W (recoverBaseExponents F L) s t (recoverBaseExponentsCost F m n) ∧
      Frame (recoverBaseExponents F L) s t ∧
      match recoverLinear (incidenceMatrix H src) (fun i => L.encode (rho i)) with
      | some x => t.vars crtActive = 1 ∧ ∀ i, (t.arrs coordinateBank).getD i.val 0 = (x i).val
      | none => t.vars crtActive = 0 := by
  have hc : Fintype.card K < W := by omega
  obtain ⟨u,r₀,hrhs,fu⟩ := installResidualLogs_run F L rho (by omega) hc (by omega)
    hLayout.base hLayout.cols hRhs hSource hResidual
  have ha (a : String) (h : a ≠ crtRhsBank) : u.arrs a = s.arrs a :=
    fu.arrs a (installResidualLogs_arrayFrame F L a h)
  have hu : RecoveryLayout H m n u := by
    refine ⟨?_,?_,?_,?_,by rw [fu.len _]; exact hLayout.sourceLen,
      by rw [fu.len _]; exact hLayout.workLen,by rw [ha matrixR (by decide)]; exact hLayout.workCanon,
      (fu.len _).trans hLayout.coLen,(fu.len _).trans hLayout.tgLen,(fu.len _).trans hLayout.modLen,
      by rw [fu.len _]; exact hLayout.destLen⟩
    · exact (fu.vars _ (installResidualLogs_scalarFrame F L _ (by decide))).trans hLayout.rows
    · exact (fu.vars _ (installResidualLogs_scalarFrame F L _ (by decide))).trans hLayout.cols
    · exact (fu.vars _ (installResidualLogs_scalarFrame F L _ (by decide))).trans hLayout.modWord
    · exact (fu.vars _ (installResidualLogs_scalarFrame F L _ (by decide))).trans hLayout.base
  obtain ⟨t,r₁,_,ht⟩ := solveIncidence_run (M := H) (m := m) (n := n) src (fun i => L.encode (rho i)) hW hThree hL hu
    (hData.congr_env (ha incidenceBank (by decide))) (by rw [ha constraintMatrix (by decide)]; exact hCan)
    (by rw [fu.len _]; exact hCap) hrhs (fun h => by rw [fu.len _]; exact hScratch h)
  have rr : Run W (recoverBaseExponents F L) s t (recoverBaseExponentsCost F m n) := r₀.seq r₁
  refine ⟨t,rr,Frame.of_run rr,?_⟩
  cases hs : recoverLinear (incidenceMatrix H src) (fun i => L.encode (rho i)) <;>
    simpa only [hs] using ht

#print axioms recoverBaseExponents_run


/-- The base residual runtime is polynomial in its physical row and column
counts, with a coefficient depending only on the fixed base field. -/
theorem recoverBaseExponentsCost_le (F : FieldEncoding K) (m n : ℕ) :
    recoverBaseExponentsCost F m n ≤ 834000*(Nat.size H+Fintype.card K+m+n+2)^5 := by
  let X := Nat.size H+Fintype.card K+m+n+2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hm : m ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hmn : m+n+1 ≤ X := by dsimp [X]; omega
  have hq : Fintype.card K ≤ X := by dsimp [X]; omega
  have hx₂ : X^2 ≤ X^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hx₁ : X ≤ X^5 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0 < X) (by decide : 1 ≤ 5))
  have hx0 : 1 ≤ X^5 := one_le_pow₀ hx
  have hh : Nat.size H+m+n+2 ≤ X := by dsimp [X]; omega
  have hRec := (completeCoordinateRecoveryCost_le H m n).trans
    (Nat.mul_le_mul_left 833000 (Nat.pow_le_pow_left hh 5))
  have hMat := Nat.mul_le_mul hmn hn
  rw [←pow_two X] at hMat
  have hLog0 : 6*Fintype.card K+16 ≤ 22*X := by omega
  have hLog := Nat.mul_le_mul hLog0 hm
  rw [show 22*X*X = 22*X^2 by ring] at hLog
  change recoverBaseExponentsCost F m n ≤ 834000*X^5
  unfold recoverBaseExponentsCost solveIncidenceCost installResidualLogsCost buildIncidenceCost
  omega

#print axioms recoverBaseExponentsCost_le

end EvenTI.P15Recover
