import EvenP17RecoverArchive
import Primary48Two

/-! Expand the selected-anchor archive into a composable transaction. The
raw mode is factored, its external archive survives, and the caller's entire
field workspace is restored for the physical mode-power initializer. -/
namespace EvenTI.P20Recover

open scoped Polynomial Matrix
open Matrix Polynomial EvenTI.P17Recover EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment
open EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18IMPPolynomialProductCall20261002 (WS)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15FactorIMP20261007 (Snf slots_ws)
open Mathproof.Problem17BudgetExec (secondCoeffs)
open Mathproof.Problem17Primary48RawReady (ports)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Ready Capacity Retained retained_of_eq)
open Mathproof.Problem17Primary48Two (Snapshot)
open Mathproof.Problem17Repeat46
  (savedReg CopyFresh savedMem savedScratch memWords scratchWords checkpointed checkpointCost)
open Problem17Factor46 (basisWords multiplicities)

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option maxRecDepth 85000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def modeArchive (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool)
    (O : Output) : Com := checkpointed ports (selectedAnchorArchive D F right O)

structure ModeArchiveControl (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool)
    (O : Output) : Prop where
  saved : ∀ y ∈ ports, savedReg y ∉ scalarWrites (selectedAnchorArchive D F right O)
  scratch : savedScratch ∉ arrayWrites (selectedAnchorArchive D F right O)
  memory : savedMem ∉ arrayWrites (selectedAnchorArchive D F right O)
  mReg : memWords ∉ scalarWrites (selectedAnchorArchive D F right O)
  sReg : scratchWords ∉ scalarWrites (selectedAnchorArchive D F right O)
  size : CopyFresh O.size
  sizeOutside : O.size ∉ ports

noncomputable def modeArchiveBodyCost (F : FieldPresentation K) (N h i : ℕ) (f : K[X]) : ℕ :=
  (19*i+22+(3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
    Mathproof.Problem17Primary48RawArchive.cost F N h f

theorem modeArchive_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) (O : Output) {B N h base scratch m l : ℕ} {s : Env}
    (old A : Matrix (Fin (h+1)) (Fin (h+1)) K) (hA : anchors.get i=⟨h+1,A⟩)
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hQ : Fintype.card K ≤ B) (hB : 1 < B) (hLen : z.length < B)
    (hBank : s.arrs "data"=sentinelWords z) (hBase : s.vars loadBase=base)
    (ready : Ready F N B h base scratch old s) (d : Distinct O) (cap : Capacity F N B O s)
    (snap : Snapshot B m l s) (ctrl : ModeArchiveControl D F right O) :
    ∃ t, Run B (modeArchive D F right O) s t
      (checkpointCost ports m l (modeArchiveBodyCost F N h i.val A.charpoly)) ∧
      Slots F canonical qN.WS (Snf N) B t ∧ Retained F N O A.charpoly t ∧
      (∀ y ∈ ports, t.vars y=s.vars y) ∧
      t.arrs canonical.mem=s.arrs canonical.mem ∧
      t.arrs canonical.scratch=s.arrs canonical.scratch ∧
      (∀ k, val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame (modeArchive D F right O) s t := by
  have hRun := Mathproof.Problem17Primary48Transaction.run
    (k:=modeArchiveBodyCost F N h i.val A.charpoly) ports (selectedAnchorArchive D F right O)
    Mathproof.Problem17Primary48RawReady.ports_separated
    (fun y hy => ⟨Mathproof.Problem17Primary48RawReady.saved_ports_fresh y hy,ctrl.saved y hy⟩)
    ⟨ctrl.memory,ctrl.scratch⟩ (by decide) ⟨ctrl.mReg,ctrl.sReg⟩
    snap.mReg snap.sReg snap.mLen snap.sLen snap.savedMLen snap.savedSLen snap.mFit snap.sFit
    snap.mWords snap.sWords snap.regWords (Retained F N O A.charpoly)
    (fun η τ ha hv hR =>
      retained_of_eq F hR (ha _ d.wordsMem d.wordsScratch) (ha _ d.multMem d.multScratch)
        (hv _ ctrl.size ctrl.sizeOutside))
  have hExec (ρ : Env)
      (sm : ρ.arrs savedMem=s.arrs canonical.mem)
      (ss : ρ.arrs savedScratch=s.arrs canonical.scratch)
      (ha : ∀ a, a ≠ savedMem → a ≠ savedScratch → ρ.arrs a=s.arrs a)
      (hv : ∀ x, CopyFresh x → x ∉ ports.map savedReg → ρ.vars x=s.vars x)
      (_ : ρ.inp=s.inp) (_ : ρ.out=s.out) :
      ∃ η, Run B (selectedAnchorArchive D F right O) ρ η (modeArchiveBodyCost F N h i.val A.charpoly) ∧
        Retained F N O A.charpoly η := by
    have keep (r : String) (hr : r ∈ ports) : ρ.vars r=s.vars r := by
      obtain ⟨hf,hk⟩ := Mathproof.Problem17Primary48RawReady.basic_port_fresh r hr
      exact hv r hf hk
    have lens (a : String) : (ρ.arrs a).length=(s.arrs a).length := by
      by_cases h₁ : a=savedMem
      · subst a; rw [sm,snap.mLen,snap.savedMLen]
      · by_cases h₂ : a=savedScratch
        · subst a; rw [ss,snap.sLen,snap.savedSLen]
        · rw [ha _ h₁ h₂]
    have γ : Ready F N B h base scratch old ρ :=
      Mathproof.Problem17Primary48RawReady.transport F ready keep
        (ha _ (by decide) (by decide)) (ha _ (by decide) (by decide))
        (lens _) (lens _) (lens _)
    have hStart := hv (anchorListStart right) (by cases right <;> decide) (by cases right <;> decide)
    have hForms := hv (formStart right) (by cases right <;> decide) (by cases right <;> decide)
    have hEnd := hv (formEnd right) (by cases right <;> decide) (by cases right <;> decide)
    have ρκ : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms ρ := by
      refine ⟨?_,?_,?_⟩
      · rw [hStart,hForms,hEnd]; exact hSec.ordered
      · rw [hStart,hForms]; exact hSec.anchors
      · rw [hForms,hEnd]; exact hSec.forms
    have hρCap : Capacity F N B O ρ := by
      refine ⟨?_,?_,?_,?_⟩ <;> rw [lens]
      · exact cap.words
      · exact cap.wordsFit
      · exact cap.mult
      · exact cap.multFit
    obtain ⟨η,r,hArc,_⟩ := selectedAnchorArchive_run D F z forms right anchors i O old A
      hA ρκ hiB ((hv _ (by decide) (by decide)).trans hI) hQ hB hLen
      ((ha _ (by decide) (by decide)).trans hBank) ((hv _ (by decide) (by decide)).trans hBase)
      γ d hρCap
    exact ⟨η,r,hArc⟩
  obtain ⟨τ,r,hPorts,hMem,hScratch,hArc,fr⟩ := hRun hExec
  have slots := slots_frame F (slots_ws F ready.bank.slots ready.ws (by decide)) hMem hScratch
    (fun r hr => hPorts r (by unfold ports; exact List.mem_append_left _ hr)) (hPorts _ (by decide))
  refine ⟨τ,r,slots,hArc,hPorts,hMem,hScratch,?_,fr⟩
  intro k
  unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
  rw [hMem,hPorts qN.WS (by decide)]

#print axioms modeArchive_run
end EvenTI.P20Recover

