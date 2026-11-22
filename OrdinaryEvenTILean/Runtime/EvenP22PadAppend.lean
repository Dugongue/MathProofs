import EvenP20SweepAddress
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option maxRecDepth 24000

namespace EvenTI.P22Pad

open EvenTI.P20Sweep
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar NoVar)
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_mul ev_var)
open Mathproof.P15DecideIMPSplit20261007 (cpBlk cpBlk_run)
open Mathproof.P15DecideIMPCopy20261007 (copyCost)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots)

def frameCursor : String := "even.pad.frame.cursor"
abbrev frameCount : String := Mathproof.Problem17Primary46FactorCursor.cursor
def frameTemp : String := "even.pad.frame.column-bank"
def framePrefix : String := "even.pad.frame.columns"
def frameSource : String := "even.pad.frame.source"
def frameDestination : String := "even.pad.frame.destination"
def frameWords : String := "even.pad.frame.words"
def frameWidth : String := "even.pad.frame.width"

private def archiveRow : Expr := .add (.var savedOffset) (.var frameCursor)
private def liveWidth : Expr := .get savedWidths archiveRow
private def appendBindings : List (String × Expr) :=
  [(frameSource,.add (.var savedBank) (.mul archiveRow (.var savedStride))),
   (frameDestination,.add (.var frameTemp) (.mul (.var framePrefix) (.var savedAmbientSize))),
   (frameWords,.mul liveWidth (.var savedAmbientSize)),
   (frameWidth,liveWidth)]

noncomputable def appendFrameBlock : Com :=
  .seq (commands appendBindings)
    (.seq (cpBlk frameSource frameDestination frameWords)
      (.assign framePrefix (.add (.var framePrefix) (.var frameWidth))))

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def appendFrameBlockCost (F : FieldPresentation K) (len : ℕ) : ℕ :=
  ((appendBindings.map (fun p => p.2.size+1)).sum+1)+(6+copyCost F len+4)

structure AppendPorts (s : Env) (n offset i base stride target usedCols Z : ℕ) : Prop where
  ambient : s.vars savedAmbientSize=n
  archiveOffset : s.vars savedOffset=offset
  index : s.vars frameCursor=i
  archiveBase : s.vars savedBank=base
  archiveStride : s.vars savedStride=stride
  targetBase : s.vars frameTemp=target
  columns : s.vars framePrefix=usedCols
  zeroWord : s.vars dZ=Z
  oneWord : s.vars rOs=Z+1
  temp₀ : s.vars dT=Z+2
  temp₁ : s.vars dU=Z+3

private theorem appendIndependent :
    ∀ p ∈ appendBindings, ∀ r ∈ appendBindings, NoVar p.1 r.2 := by
  intro p hp r hr
  simp only [appendBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hr
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hr with rfl|rfl|rfl|rfl <;> simp [NoVar,frameSource,frameDestination,frameWords,frameWidth,frameTemp,framePrefix,archiveRow,liveWidth,savedOffset,savedBank,savedStride,savedAmbientSize,frameCursor]

/-- The archive's live width selects the number of copied columns.
Its saved vectors occupy a prefix of this row's durable frame bank. -/
theorem appendFrameBlock_run (F : FieldPresentation K)
    {W S n offset i width base stride target usedCols Z : ℕ} {s : Env}
    (hs : Slots F canonical qN.WS S W s)
    (p : AppendPorts s n offset i base stride target usedCols Z)
    (hWidth : (s.arrs savedWidths)[offset+i]?=some width)
    (hn : n<W) (hIndex : offset+i<W) (hStride : stride<W)
    (hWidths : width<W) (hPrefix : usedCols+width<W)
    (hSource : base+(offset+i)*stride+width*n≤target)
    (hTarget : target+(usedCols+width)*n≤Z)
    (hZ : Z+4≤S) (hW : S+10<W)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run W appendFrameBlock s t (appendFrameBlockCost F (width*n)) ∧
      Slots F canonical qN.WS S W t ∧ t.vars framePrefix=usedCols+width ∧
      (∀ k<width*n, val F canonical qN.WS t (target+usedCols*n+k)=
        val F canonical qN.WS s (base+(offset+i)*stride+k)) ∧
      (∀ k<S, (k<target+usedCols*n ∨ target+(usedCols+width)*n≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame appendFrameBlock s t := by
  let src := base+(offset+i)*stride
  let dst := target+usedCols*n
  let len := width*n
  have hMulCol : usedCols*n ≤ (usedCols+width)*n := Nat.mul_le_mul_right n (by omega)
  have hMulWid : width*n ≤ (usedCols+width)*n := Nat.mul_le_mul_right n (by omega)
  have hTmp : dst+len=target+(usedCols+width)*n := by dsimp [dst,len]; ring
  have hS : src+len≤target := hSource
  have hDZ : dst+len≤Z := hTmp.trans_le hTarget
  have hSD : src+len≤dst := hS.trans (Nat.le_add_right _ _)
  have hSZ : src+len≤Z := hSD.trans ((Nat.le_add_right _ _).trans hDZ)
  have hBP : base < W := by dsimp only [src,len] at hSZ; omega
  have hBProd : (offset+i)*stride<W := by dsimp only [src,len] at hSZ; omega
  have hDestProd : usedCols*n<W := by dsimp only [dst,len] at hDZ; omega
  have hSrcW : src<W := by omega
  have hDstW : dst<W := by omega
  have hLenW : len<W := by omega
  have er : archiveRow.evalB W s=some (offset+i) :=
    ev_add (ev_var p.archiveOffset (by omega)) (ev_var p.index (by omega)) hIndex
  have ew : liveWidth.evalB W s=some width := evalB_get er hWidth hWidths
  have en := ev_var p.ambient hn
  have eSrc : (.add (.var savedBank) (.mul archiveRow (.var savedStride)) : Expr).evalB W s=some src :=
    ev_add (ev_var p.archiveBase hBP) (ev_mul er (ev_var p.archiveStride hStride) hBProd) hSrcW
  have eDst : (.add (.var frameTemp) (.mul (.var framePrefix)
      (.var savedAmbientSize)) : Expr).evalB W s=some dst :=
    ev_add (ev_var p.targetBase (by omega)) (ev_mul (ev_var p.columns (by omega)) en hDestProd) hDstW
  have eLen : (.mul liveWidth (.var savedAmbientSize) : Expr).evalB W s=some len :=
    ev_mul ew en hLenW
  let u := s.setVar frameSource src |>.setVar frameDestination dst |>.setVar frameWords len |>.setVar frameWidth width
  have r₀ : Run W (commands appendBindings) s u
      ((appendBindings.map (fun p => p.2.size+1)).sum+1) :=
    commands_run appendBindings [src,dst,len,width] s rfl
      (List.Forall₂.cons eSrc (List.Forall₂.cons eDst (List.Forall₂.cons eLen (List.Forall₂.cons ew List.Forall₂.nil)))) appendIndependent
  have us : Slots F canonical qN.WS S W u :=
    Slots.setVar F canonical (Slots.setVar F canonical (Slots.setVar F canonical
      (Slots.setVar F canonical hs (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  have uv (k : ℕ) : val F canonical qN.WS u k=val F canonical qN.WS s k := by
    dsimp only [u]
    rw [val_setVar F canonical (by decide),val_setVar F canonical (by decide),
      val_setVar F canonical (by decide),val_setVar F canonical (by decide)]
  obtain ⟨v,r₁,hv,hCopied,hOutside,hRegs,_,_⟩ := cpBlk_run F frameSource frameDestination frameWords us
    (by decide) (by decide) (by decide)
    (by simp [u,frameSource,frameDestination,frameWords,frameWidth])
    (by simp [u,frameDestination,frameWords,frameWidth])
    (by simp [u,frameWords,frameWidth])
    (show u.vars dZ=Z from p.zeroWord) (show u.vars rOs=Z+1 from p.oneWord)
    (show u.vars dT=Z+2 from p.temp₀) (show u.vars dU=Z+3 from p.temp₁)
    ((uv _).trans hz) ((uv _).trans ho) (Or.inl hSD) hSZ hDZ hZ hW
  have hvPref : v.vars framePrefix=usedCols :=
    (hRegs _ (by decide)).trans (show u.vars framePrefix=usedCols from p.columns)
  have hvW : v.vars frameWidth=width := (hRegs _ (by decide)).trans rfl
  let t := v.setVar framePrefix (usedCols+width)
  have r₂ : Run W (.assign framePrefix (.add (.var framePrefix) (.var frameWidth))) v t 4 :=
    Run.assign (ev_add (ev_var hvPref (by omega)) (ev_var hvW hWidths) hPrefix)
  have r : Run W appendFrameBlock s t (appendFrameBlockCost F (width*n)) :=
    r₀.seq (r₁.seq r₂)
  have ht : Slots F canonical qN.WS S W t := Slots.setVar F canonical hv (by decide) (by decide) _
  refine ⟨t,r,ht,rfl,?_,?_,Frame.of_run r⟩
  · intro k hk
    exact (val_setVar F canonical (by decide) v _ _).trans ((hCopied k hk).trans (uv _))
  · intro k hk hOut h1 h2
    have hout : k<dst ∨ dst+len≤k := by rw [hTmp]; exact hOut
    exact (val_setVar F canonical (by decide) v _ _).trans ((hOutside k hk hout h1 h2).trans (uv _))

#print axioms appendFrameBlock_run
end EvenTI.P22Pad
