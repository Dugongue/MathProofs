import EvenP17ReciprocalVisit
import EvenP17TrialReciprocalSweep

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1700000

namespace EvenTI.P17Execution

open EvenTI.P16Execution EvenTI.P16Trial EvenTI.P15Trial EvenTI.P17Trial
open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.TrialProducer
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def reciprocalPermanent : List String :=
  [dT,dU,dZ,crossN,crossA,crossSource,crossInverse,anchorSideWord,anchorCrossWord,
    anchorSquareWord,anchorTraceWord,anchorUnitWord,fieldVectorStart,fieldVectorLength,
    emitAnchorWidth,reciprocalSweepLimit]

def reciprocalFixed : List String := reciprocalSweepIndex :: crossStride :: reciprocalPermanent

private theorem digitBranch_noScalar (ts : List (ℕ × ℕ)) (yes no : Com)
    (hy : scalarWrites yes=∅) (hn : scalarWrites no=∅) :
    scalarWrites (digitBranch ts yes no)=∅ := by
  induction ts with
  | nil => exact hy
  | cons p ts ih => simp [digitBranch,scalarWrites,ih,hn]

private theorem fieldBranches_noScalar (D : FieldEncoding K) (F : FieldPresentation K) (xs : List K) :
    scalarWrites (fieldLabelBranches D F xs)=∅ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact digitBranch_noScalar _ _ _ rfl ih

private theorem emitter_scalars (D : FieldEncoding K) (F : FieldPresentation K) :
    scalarWrites (emitAnchorBlock D F) =
      ({fieldVectorIndex,labelAddress} : Finset String) := by
  simp [emitAnchorBlock,fieldVectorProgram,visitFieldVector,emitFieldLabel,
    scalarWrites,fieldBranches_noScalar,Finset.union_comm,Finset.union_assoc]

private noncomputable def frameField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem fixedGrid (F : FieldPresentation K) (mirror : Bool) :
    ∀ r ∈ reciprocalFixed, r ∉ scalarWrites (reciprocalAnchorGrid F mirror) := by
  cases mirror
  · change ∀ r ∈ reciprocalFixed, r ∉ scalarWrites (reciprocalAnchorGrid frameField false)
    decide
  · change ∀ r ∈ reciprocalFixed, r ∉ scalarWrites (reciprocalAnchorGrid frameField true)
    decide

private theorem fixedEmitter : ∀ r ∈ reciprocalFixed, r ∉ ({fieldVectorIndex,labelAddress} : Finset String) := by
  decide

private theorem fixedReset : ∀ r ∈ reciprocalFixed, r ∉ [gRows,gCols,dL,gOut] := by decide

noncomputable def reciprocalVisitWithReset (D : FieldEncoding K) (F : FieldPresentation K) (mirror : Bool) : Com :=
  .seq resetReciprocalArgs (computeEmitReciprocal D F mirror)

structure ReciprocalOffsets where
  src : ℕ
  inv : ℕ
  cross : ℕ
  square : ℕ
  out : ℕ
  tt : ℕ
  uu : ℕ
  zero : ℕ
  one : ℕ

structure ReciprocalInstalled (l n : ℕ) (L : ReciprocalOffsets) (s : Env) : Prop where
  width : s.vars crossN=n
  power : s.vars crossA=n^l
  source : s.vars crossSource=L.src
  inverse : s.vars crossInverse=L.inv
  side : s.vars anchorSideWord=n
  crossed : s.vars anchorCrossWord=L.cross
  squared : s.vars anchorSquareWord=L.square
  traced : s.vars anchorTraceWord=L.out
  unit : s.vars anchorUnitWord=L.one
  zero : s.vars dZ=L.zero
  temp1 : s.vars dT=L.tt
  temp2 : s.vars dU=L.uu
  start : s.vars fieldVectorStart=L.out
  length : s.vars fieldVectorLength=n*n
  emitWidth : s.vars emitAnchorWidth=n

noncomputable def reciprocalRecordBody (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  reciprocalTwoSweeps (reciprocalVisitWithReset D F true) (reciprocalVisitWithReset D F false)

noncomputable def reciprocalVisitCost (F : FieldPresentation K) (mirror : Bool) (l n : ℕ) : ℕ :=
  15+(crossGridCost F mirror n (n^l)+squareTraceCost F n+emitAnchorBlockCost F n)

private def anchorPayload (D : FieldEncoding K) {l n : ℕ}
    (A : HigherModes l → Matrix (Fin n) (Fin n) K) (p : HigherModes l) : List ℕ :=
  blockW (numberedAnchorWords D (numeric (A p)))

/-- A complete two-orientation traversal on the installed cut and reciprocal
banks. The public payload is emitted in the reference reciprocal order. -/
theorem reciprocalRecordBody_run (D : FieldEncoding K) (F : FieldPresentation K) {l n B S : ℕ}
    {σ : Env} (T : Tensor K ((l+1)+(l+1)) n)
    (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K) (L : ReciprocalOffsets)
    (hn : 2 ≤ n) (hN : n+1 < B) (hNN : n*n+1 < B) (hA : (n^l)*(n^l)+1 < B)
    (hLim : l+1 < B) (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hSrc : L.src+(n*n^l)*(n*n^l) ≤ L.out)
    (hInv : L.inv+(n*n^l)*(n*n^l) ≤ L.out)
    (hOut : L.out+n*n ≤ L.cross) (hCross : L.cross+(n*n)*(n*n) ≤ L.square)
    (hSquare : L.square+(n*n)*(n*n) ≤ S)
    (hT : L.tt < L.src ∧ L.tt < L.inv ∧ L.tt < L.out)
    (hU : L.uu < L.src ∧ L.uu < L.inv ∧ L.uu < L.out) (hTU : L.tt≠L.uu)
    (hZ : L.zero < L.out ∧ L.zero≠L.tt ∧ L.zero≠L.uu)
    (hOne : L.one < L.out ∧ L.one≠L.tt ∧ L.one≠L.uu)
    (hS : Slots F canonical qN.WS S B σ) (hRegs : ReciprocalInstalled l n L σ)
    (hLimit : σ.vars reciprocalSweepLimit=l+1)
    (hZero : val F canonical qN.WS σ L.zero=0) (hUnit : val F canonical qN.WS σ L.one=1)
    (hLoad : InstalledCutMatrix F σ l n L.src (flatten T))
    (hRecip : InstalledCutMatrix F σ l n L.inv N) :
    ∃ t, Run B (reciprocalRecordBody D F) σ t
      (((reciprocalVisitCost F true l n+12)*(l+1)+8)+
        ((reciprocalVisitCost F false l n+12)*(l+1)+8)) ∧
      Slots F canonical qN.WS S B t ∧ t.inp=σ.inp ∧
      t.out=σ.out++(List.ofFn (fun i =>
        anchorPayload D (rawReciprocalAnchor T N) (reciprocalOrder l i))).flatten := by
  let mem (s : Env) := ∀ k < L.out, k≠L.tt → k≠L.uu →
    val F canonical qN.WS s k=val F canonical qN.WS σ k
  let ctx (s : Env) := Slots F canonical qN.WS S B s ∧ mem s ∧
    ∀ r ∈ reciprocalPermanent, s.vars r=σ.vars r
  have haB : n^l < B := (Nat.le_mul_of_pos_right _ (pow_pos (show 0 < n by omega) l)).trans_lt (by omega)
  have hFitWord := hS.slots_word
  have valFrame {s t : Env} (hW : t.vars qN.WS=s.vars qN.WS) (hM : t.arrs=s.arrs)
      (k : ℕ) : val F canonical qN.WS t k = val F canonical qN.WS s k := by
    unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
    rw [hW,hM]

  have permits (r : String) (hr : r ∉ reciprocalPermanent) (hNames : r ∉ regNames canonical)
      (hW : r ≠ qN.WS) (s : Env) (x : ℕ) (hs : ctx s) : ctx (s.setVar r x) := by
    refine ⟨Slots.setVar F canonical hs.1 hNames hW x,?_,?_⟩
    · intro k hk ht hu
      exact (val_setVar F canonical hW s x k).trans (hs.2.1 k hk ht hu)
    · intro k hk
      have hkr : k ≠ r := fun e => hr (e ▸ hk)
      simp [hkr,hs.2.2 k hk]
  have buildRegs {s : Env} (h : ∀ r ∈ reciprocalPermanent, s.vars r=σ.vars r) :
      ReciprocalInstalled l n L s := by
    refine ⟨(h _ (by decide)).trans hRegs.width,(h _ (by decide)).trans hRegs.power,
      (h _ (by decide)).trans hRegs.source,(h _ (by decide)).trans hRegs.inverse,
      (h _ (by decide)).trans hRegs.side,(h _ (by decide)).trans hRegs.crossed,
      (h _ (by decide)).trans hRegs.squared,(h _ (by decide)).trans hRegs.traced,
      (h _ (by decide)).trans hRegs.unit,(h _ (by decide)).trans hRegs.zero,
      (h _ (by decide)).trans hRegs.temp1,(h _ (by decide)).trans hRegs.temp2,
      (h _ (by decide)).trans hRegs.start,(h _ (by decide)).trans hRegs.length,
      (h _ (by decide)).trans hRegs.emitWidth⟩
  let payload := anchorPayload D (rawReciprocalAnchor T N)
  let cost := fun mirror => reciprocalVisitCost F mirror l n
  have visit (mirror : Bool) (s : Env) (i : Fin (l+1)) (h : ctx s)
      (hi : s.vars reciprocalSweepIndex=i.val) (hStride : s.vars crossStride=n^(l-i.val))
      (_hWidth : s.vars crossN=n) :
      ∃ t, Run B (reciprocalVisitWithReset D F mirror) s t (cost mirror) ∧ ctx t ∧
        t.vars reciprocalSweepIndex=i.val ∧ t.vars crossStride=n^(l-i.val) ∧
        t.vars crossN=s.vars crossN ∧ t.vars crossA=s.vars crossA ∧
        t.vars reciprocalSweepLimit=s.vars reciprocalSweepLimit ∧
        t.inp=s.inp ∧ t.out=s.out++payload (mirror,i) := by
    have rr := buildRegs h.2.2
    obtain ⟨u,ru,hSu,hRows,hCols,hInner,hGo,hKeep,hArr,huIn,huOut⟩ :=
      resetReciprocalArgs_run F h.1 rr.width rr.power rr.crossed (by omega) haB
        (by omega) (by omega) (by omega)
    have hRegsU := buildRegs (fun r hr =>
      (hKeep r (fixedReset r (by simp [reciprocalFixed,hr]))).trans (h.2.2 r hr))
    have hUM (k : ℕ) (hk : k<L.out) (ht : k≠L.tt) (hu : k≠L.uu) :
        val F canonical qN.WS u k=val F canonical qN.WS σ k :=
      (valFrame (hKeep qN.WS (by decide)) hArr k).trans (h.2.1 k hk ht hu)
    have readFrame (b : ℕ) (hb : b+(n*n^l)*(n*n^l) ≤ L.out) (ht : L.tt<b)
        (hu : L.uu<b) (M : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
        (hM : InstalledCutMatrix F σ l n b M) :
        InstalledCutMatrix F u l n b M := by
      intro x y
      let ix := (EvenTI.Contract.inputCoordOrder n (l+1) x).val
      let iy := (EvenTI.Contract.inputCoordOrder n (l+1) y).val
      have hx : ix < n*n^l := by rw [←pow_succ']; exact (EvenTI.Contract.inputCoordOrder n (l+1) x).isLt
      have hy : iy < n*n^l := by rw [←pow_succ']; exact (EvenTI.Contract.inputCoordOrder n (l+1) y).isLt
      have haf := Mathproof.P15RecogIMPGrid20261007.out_lt (o0:=b) hx hy
      have e := hUM (b+(ix*(n*n^l)+iy)) (by omega) (by omega) (by omega)
      exact e.trans (hM x y)

    have keepReset (r : String) (hr : r ∈ reciprocalFixed) : u.vars r=s.vars r :=
      hKeep r (fixedReset r hr)
    obtain ⟨v,rv,hSv,hVM,hvIn,hvOut⟩ :=
      computeEmitReciprocal_run D F T N (mirror,i) (by omega) hSu hN hNN hA
        (by omega) (by omega) hCross hSquare (by omega) (by omega)
        hT hU hTU ⟨hZ.1,by omega,hZ.2.1,hZ.2.2⟩ ⟨hOne.1,by omega,hOne.2.1,hOne.2.2⟩
        hRows hCols hInner hGo hRegsU.temp1 hRegsU.temp2 hRegsU.zero
        hRegsU.width hRegsU.power ((keepReset _ (by decide)).trans hStride)
        hRegsU.source hRegsU.inverse hRegsU.side hRegsU.crossed hRegsU.squared hRegsU.traced hRegsU.unit
        ((hUM _ hZ.1 hZ.2.1 hZ.2.2).trans hZero)
        ((hUM _ hOne.1 hOne.2.1 hOne.2.2).trans hUnit)
        (readFrame _ hSrc hT.1 hU.1 _ hLoad) (readFrame _ hInv hT.2.1 hU.2.1 _ hRecip)
        hQ hP hRegsU.start hRegsU.length hRegsU.emitWidth
    have fv := Frame.of_run rv
    have keep (r : String) (hr : r ∈ reciprocalFixed) : v.vars r=s.vars r := by
      have hrw : r ∉ scalarWrites (computeEmitReciprocal D F mirror) := by
        simp only [computeEmitReciprocal,scalarWrites,emitter_scalars,Finset.mem_union,not_or]
        exact ⟨fixedGrid F mirror r hr,fixedEmitter r hr⟩
      exact (fv.vars r hrw).trans (keepReset r hr)
    have hCtx : ctx v :=
      ⟨hSv,fun k hk ht hu => (hVM k hk ht hu).trans (hUM k hk ht hu),
        fun r hr => (keep r (by simp [reciprocalFixed,hr])).trans (h.2.2 r hr)⟩
    refine ⟨v,ru.seq rv,hCtx,(keep _ (by decide)).trans hi,(keep _ (by decide)).trans hStride,
      keep _ (by decide),keep _ (by decide),keep _ (by decide),hvIn.trans huIn,?_⟩
    rw [hvOut,huOut]
    rfl
  obtain ⟨t,hRun,hTctx,htIn,htOut⟩ :=
    reciprocalTwoSweeps_run (reciprocalVisitWithReset D F) cost ctx payload hn (by omega) haB hLim
      (permits reciprocalSweepIndex (by decide) (by decide) (by decide))
      (permits crossStride (by decide) (by decide) (by decide))
      visit ⟨hS,fun _ _ _ _ => rfl,fun _ _ => rfl⟩ hRegs.width hRegs.power hLimit
  exact ⟨t,hRun,hTctx.1,htIn,htOut⟩

#print axioms reciprocalRecordBody_run
end EvenTI.P17Execution
