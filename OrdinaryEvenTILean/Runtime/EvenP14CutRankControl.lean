import EvenP14CutRankFrame

set_option autoImplicit false
set_option maxHeartbeats 1450000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 (qN dI dO dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut gU gV)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPKerBasis20261007 (KBLay XBs kK kAM kOUT)
open Mathproof.P15DecideIMPRowKer20261007 (rkProg tNR tD tRB)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutRankCursor : String := "even_compare_retained_mode"
def cutRankLimit : String := "even_compare_retained_limit"
def cutRankAccept : String := "even_compare_retained_accept"

def cutRankArgs (d n src RB AM OUT Z e : ℕ) : List (String × ℕ) :=
  [(cutRankLimit,d+1),(retainedSrc,src),(dT,Z+2),(dU,Z+3),(dZ,Z),(rOs,Z+1),
    (tNR,n^d),(tD,n),(tRB,RB),(kAM,AM),(kOUT,OUT),(qN.WS,e+1)]

def cutRankArgNames : List String := (cutRankArgs 0 0 0 0 0 0 0 0).map Prod.fst

def CutRankRegisterFresh (x : String) : Prop :=
  x ∉ scalarWrites rkProg ∧ x ∉ regNames canonical ∧ x ≠ dI ∧ x ≠ gU ∧ x ≠ gV ∧
    x ≠ dO ∧ x ≠ gRows ∧ x ≠ gCols ∧ x ≠ dL ∧ x ≠ gOut

noncomputable instance (x : String) : Decidable (CutRankRegisterFresh x) := by
  unfold CutRankRegisterFresh
  infer_instance

private theorem cutRankStatic_fresh : ∀ x ∈ cutRankArgNames, CutRankRegisterFresh x := by decide

structure CutRankBank (F : FieldPresentation K) {d n : ℕ} (x : Coord (d+1) n → K)
    (src RB AM OUT Z Sn B : ℕ) (σ : Env) : Prop where
  slots : Slots F canonical qN.WS Sn B σ
  regs : ∀ p ∈ cutRankArgs d n src RB AM OUT Z F.e, σ.vars p.1 = p.2
  source : ∀ u : Coord (d+1) n,
    val F canonical qN.WS σ (src+(inputCoordOrder n (d+1) u).val) = x u
  zero : val F canonical qN.WS σ Z = 0
  one : val F canonical qN.WS σ (Z+1) = 1

theorem CutRankBank.setVar (F : FieldPresentation K) {d n src RB AM OUT Z Sn B : ℕ}
    {x : Coord (d+1) n → K} {σ : Env} (h : CutRankBank F x src RB AM OUT Z Sn B σ)
    (name : String) (v : ℕ)
    (h₁ : name ∉ regNames canonical) (h₂ : name ≠ qN.WS) (h₃ : name ∉ cutRankArgNames) :
    CutRankBank F x src RB AM OUT Z Sn B (σ.setVar name v) := by
  refine ⟨Slots.setVar F canonical h.slots h₁ h₂ v,?_,?_,?_,?_⟩
  · intro p hp
    have hh : p.1 ∈ cutRankArgNames := by
      change p.1 ∈ (cutRankArgs d n src RB AM OUT Z F.e).map Prod.fst
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    have hne : p.1 ≠ name := fun e => h₃ (e ▸ hh)
    exact (by simp [vars_setVar,hne] : (σ.setVar name v).vars p.1 = σ.vars p.1)
      |>.trans (h.regs p hp)
  · intro u
    exact (val_setVar F canonical h₂ σ v _).trans (h.source u)
  · exact (val_setVar F canonical h₂ σ v _).trans h.zero
  · exact (val_setVar F canonical h₂ σ v _).trans h.one

def retainedCutPass {d n : ℕ} (x : Coord (d+1) n → K) (i : Fin (d+1)) : Bool :=
  (rawKernelVectors (retainedForm i x).transpose (cutOrder d n) (Equiv.refl (Fin n))).isEmpty

theorem rawRetainedFullRank_eq_all {d n : ℕ} (x : Coord (d+1) n → K) :
    rawRetainedFullRank x = true ↔ ∀ i, retainedCutPass x i = true := by
  simp [rawRetainedFullRank,retainedCutPass,List.all_eq_true]

def cutRankModeCost (F : FieldPresentation K) (L : ℕ) : ℕ :=
  8 + (300*(macroBudget F*(L+2)^4) + 34500*(macroBudget F*(6*L)^5))

theorem cutRankModeBank_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n src RB AM OUT Z Sn B L : ℕ} {σ : Env} (x : Coord (d+1) n → K)
    (i : Fin (d+1)) (hd : 1 ≤ d) (hn : 2 ≤ n) (hL : n^(d+1) ≤ L)
    (layout : KBLay (n^d) n AM OUT Z Sn B)
    (hSourceLow : (n+1)*XBs (n^d) n ≤ src)
    (hSrcFit : src+n^d*n ≤ RB) (hDstFit : RB+n^d*n ≤ AM)
    (h : CutRankBank F x src RB AM OUT Z Sn B σ)
    (hStride : σ.vars retainedStride = n^(d-i.val)) :
    ∃ τ, Run B cutRankModeCall σ τ (cutRankModeCost F L) ∧
      CutRankBank F x src RB AM OUT Z Sn B τ ∧
      (∀ s < Sn, (n+1)*XBs (n^d) n ≤ s → (s < RB ∨ OUT+n*n ≤ s) → s ≠ Z+2 → s ≠ Z+3 →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ s, CutRankRegisterFresh s → τ.vars s = σ.vars s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ∧ τ.vars kK ≤ n ∧
      (τ.vars kK = 0 ↔ retainedCutPass x i = true) := by
  have hAMout := layout.am_out
  have hOUTz := layout.out_z
  have hScratch := layout.z_s
  have hBound := layout.s_b
  obtain ⟨τ,hRun,hS,hIn,hOut,hSource,hMem,hZero,hOne,hVars,hK,hTest⟩ :=
    cutRankModeCall_run D F x i hd hn hL layout hSourceLow (by omega) hDstFit hSrcFit
      (by omega) hScratch (by omega) h.slots
      (h.regs (retainedSrc,src) (by simp [cutRankArgs])) hStride
      (h.regs (dT,Z+2) (by simp [cutRankArgs])) (h.regs (dU,Z+3) (by simp [cutRankArgs]))
      (h.regs (dZ,Z) (by simp [cutRankArgs])) (h.regs (rOs,Z+1) (by simp [cutRankArgs]))
      (h.regs (tNR,n^d) (by simp [cutRankArgs])) (h.regs (tD,n) (by simp [cutRankArgs]))
      (h.regs (tRB,RB) (by simp [cutRankArgs])) (h.regs (kAM,AM) (by simp [cutRankArgs]))
      (h.regs (kOUT,OUT) (by simp [cutRankArgs])) (h.regs (qN.WS,F.e+1) (by simp [cutRankArgs]))
      h.source h.zero h.one
  have hv (s : String) (hs : CutRankRegisterFresh s) : τ.vars s = σ.vars s := by
    rcases hs with ⟨a,b,c,d,e,f,g,h,i,j⟩
    exact hVars s a b c d e f g h i j
  refine ⟨τ,hRun,⟨hS,?_,hSource,hZero,hOne⟩,hMem,hv,hIn,hOut,hK,hTest⟩
  intro p hp
  have hh : p.1 ∈ cutRankArgNames := by
    change p.1 ∈ (cutRankArgs d n src RB AM OUT Z F.e).map Prod.fst
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact (hv _ (cutRankStatic_fresh _ hh)).trans (h.regs p hp)

#print axioms cutRankModeBank_run
end EvenTI.P12ComparePrep
