import EvenP17RecoverAnchorLoad
import Primary48RawReady

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16000

namespace EvenTI.P17Recover

open EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18IMPPolynomialProductCall20261002 (WS)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15FactorIMP20261007 (Bank GQ Snf L0f rC rL0 rN rOS rWK slots_ws)
open Mathproof.Problem17CharpolyExec (setupInput setupCoeff setupWidth setupScratch setupExp address)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Ready Capacity Retained)
open Mathproof.Problem17Primary48RawReady (ports)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def selectedAnchorArchive (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) (O : Output) : Com :=
  .seq (loadSelectedAnchor D F right) (Mathproof.Problem17Primary48RawArchive.program F O)

private theorem archivePortsFresh (right : Bool) :
    ∀ r ∈ ports, r ≠ liveAnchorWidth ∧ r ≠ inputBase ∧ r ≠ loadLength ∧
      ¬loadChanges r ∧ r ∉ scalarWrites (selectAnchor right) := by cases right <;> decide

/-- Replace the input slice of an initialized factor bank by a serialized
anchor and execute the checked charpoly, factoring, and archive routines.
The auxiliary factor bank and its address registers are supplied by the caller. -/
theorem selectedAnchorArchive_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) (O : Output) {B N h base scratch : ℕ} {s : Env}
    (old A : Matrix (Fin (h+1)) (Fin (h+1)) K) (hA : anchors.get i=⟨h+1,A⟩)
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hQ : Fintype.card K ≤ B) (hB : 1 < B) (hLen : z.length < B)
    (hBank : s.arrs "data"=sentinelWords z) (hBase : s.vars loadBase=base)
    (ready : Ready F N B h base scratch old s) (d : Distinct O) (cap : Capacity F N B O s) :
    ∃ t, Run B (selectedAnchorArchive D F right O) s t
      ((19*i.val+22+(3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
        Mathproof.Problem17Primary48RawArchive.cost F N h A.charpoly) ∧
      Retained F N O A.charpoly t ∧ Frame (selectedAnchorArchive D F right O) s t := by
  have hFit : base+(h+1)*(h+1) ≤ Snf N := by
    obtain ⟨_,h₁,_,_,_,_,_,_,h₂,_,_⟩ := ready.layout
    change base+(h+1)*(h+1) ≤ scratch at h₁
    change address h scratch 5+5 ≤ Snf N at h₂
    unfold address at h₂
    omega
  have hS : Slots F canonical qN.WS (Snf N) B s := slots_ws F ready.bank.slots ready.ws (by decide)
  obtain ⟨u,ru,hu,_,hV,_,_,_,_,hKeep⟩ := loadSelectedAnchor_run D F z forms right anchors i
    hSec hiB hI hS hQ hB hLen hBank hBase (by rw [hA]; exact hFit)
  simp only [hA] at ru
  let installed (I : NumberedAnchor K) :=
    ∀ k : Fin (I.width*I.width), val F canonical qN.WS u (base+k.val) =
      I.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hInstalled : installed (anchors.get i) := hV
  have hMatrix : installed ⟨h+1,A⟩ := hA ▸ hInstalled
  have hM : MatBlock F u base A := by
    intro j k
    let idx : Fin ((h+1)*(h+1)) := finProdFinEquiv (j,k)
    have idxEq : idx.val=j.val*(h+1)+k.val := by
      simp [idx,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    change val F canonical qN.WS u (base+(j.val*(h+1)+k.val))=A j k
    rw [← idxEq]
    simpa only [idx,Equiv.symm_apply_apply] using hMatrix idx
  have hReg (r : String) (hr : r ∈ ports) : u.vars r=s.vars r := by
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := archivePortsFresh right r hr
    exact hKeep r h₁ h₂ h₃ h₄ h₅
  have hW : u.vars qN.WS=u.vars WS := by rw [hReg qN.WS (by decide),hReg WS (by decide),ready.ws]
  have f := Frame.of_run ru
  have hb : Bank F N B u :=
    ⟨slots_ws F hu hW.symm (by decide),
      by rw [hReg GQ.WS (by decide),hReg WS (by decide),ready.bank.qws],
      (hReg _ (by decide)).trans ready.bank.mod,(hReg _ (by decide)).trans ready.bank.ws,
      (f.len _).trans ready.bank.len,
      (hReg _ (by decide)).trans ready.bank.rc,(hReg _ (by decide)).trans ready.bank.rl,
      (hReg _ (by decide)).trans ready.bank.rn,(hReg _ (by decide)).trans ready.bank.ro,
      (hReg _ (by decide)).trans ready.bank.rw⟩
  have huReady : Ready F N B h base scratch A u :=
    ⟨hb,hW,ready.layout,(hReg _ (by decide)).trans ready.input,
      (hReg _ (by decide)).trans ready.coeff,(hReg _ (by decide)).trans ready.width,
      (hReg _ (by decide)).trans ready.scratch,(hReg _ (by decide)).trans ready.exp,hM,
      ready.reserve,ready.word,by rw [f.len]; exact ready.orig,by rw [f.len]; exact ready.origWord,
      by rw [f.len]; exact ready.basis,by rw [f.len]; exact ready.basisWord,
      by rw [f.len]; exact ready.mult,by rw [f.len]; exact ready.multWord⟩
  have huCap : Capacity F N B O u :=
    ⟨by rw [f.len]; exact cap.words,by rw [f.len]; exact cap.wordsFit,
      by rw [f.len]; exact cap.mult,by rw [f.len]; exact cap.multFit⟩
  obtain ⟨t,rt,ha,_⟩ := Mathproof.Problem17Primary48RawArchive.run F A O huReady d huCap
  have r : Run B (selectedAnchorArchive D F right O) s t _ := ru.seq rt
  exact ⟨t,r,ha,Frame.of_run r⟩

#print axioms selectedAnchorArchive_run
end EvenTI.P17Recover
