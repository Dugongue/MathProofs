import EvenP20RecoverModeLoad
import EvenP20RecoverModeArchive

/-! Turn one raw numbered mode into a retained factor archive and live
field powers for a future factor sweep. -/
namespace EvenTI.P20Recover

open scoped Polynomial Matrix
open Matrix Polynomial EvenTI.P17Recover EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment
open EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15FactorIMP20261007 (Snf)
open Mathproof.Problem17Primary46FactorCursor (cursor)
open Mathproof.Problem17Primary48RawReady (ports)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Ready Capacity Retained retained_of_eq)
open Mathproof.Problem17Primary48Two (Snapshot)
open Mathproof.Problem17Repeat46 (checkpointCost)

set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxRecDepth 90000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure ModeInitFrame (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool)
    (O : Output) : Prop where
  data : "data" ∉ arrayWrites (modeArchive D F right O)
  requested : anchorWanted ∉ scalarWrites (modeArchive D F right O)
  load : loadBase ∉ scalarWrites (modeArchive D F right O)
  start : anchorListStart right ∉ scalarWrites (modeArchive D F right O)
  mid : formStart right ∉ scalarWrites (modeArchive D F right O)
  stop : formEnd right ∉ scalarWrites (modeArchive D F right O)
  power : ∀ r ∈ modePowerNames, r ∉ scalarWrites (modeArchive D F right O)
  poly : O.words ∉ arrayWrites (loadModePowers D F right)
  mult : O.mult ∉ arrayWrites (loadModePowers D F right)
  count : O.size ∉ scalarWrites (loadModePowers D F right)
  workspace : qN.WS ∉ scalarWrites (loadModePowers D F right)

noncomputable def initSelectedMode (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) (O : Output) : Com :=
  .seq (modeArchive D F right O) (loadModePowers D F right)

theorem initSelectedMode_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) (O : Output) {B N h base scratch m l SB Z : ℕ} {s : Env}
    (old A : Matrix (Fin (h+1)) (Fin (h+1)) K) (hA : anchors.get i=⟨h+1,A⟩)
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hQ : Fintype.card K ≤ B) (hB : 1 < B) (hLen : z.length < B)
    (hBank : s.arrs "data"=sentinelWords z) (hBase : s.vars loadBase=base)
    (ready : Ready F N B h base scratch old s) (d : Distinct O) (cap : Capacity F N B O s)
    (snap : Snapshot B m l s) (ctrl : ModeArchiveControl D F right O)
    (sep : ModeInitFrame D F right O)
    (P : ModePowerPorts s (h+1) SB base Z)
    (hSB : SB+((h+1)+1)*((h+1)*(h+1)) ≤ base) (hMB : base+(h+1)*(h+1) ≤ Z)
    (hZS : Z+4 ≤ Snf N) (hWB : Snf N+(h+1)+(h+1)+12 < B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run B (initSelectedMode D F right O) s t
      (checkpointCost ports m l (modeArchiveBodyCost F N h i.val A.charpoly)+
        ((19*i.val+22+(3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
          (Mathproof.Problem17Primary46Powers.cost F (h+1) (h+1)+2))) ∧
      Slots F canonical qN.WS (Snf N) B t ∧ Retained F N O A.charpoly t ∧
      t.vars liveAnchorWidth=h+1 ∧ t.vars cursor=0 ∧ t.vars qN.WS=s.vars qN.WS ∧
      MatBlock F t base A ∧ (∀ j ≤ h+1, MatBlock F t (SB+j*((h+1)*(h+1))) (A^j)) ∧
      val F canonical qN.WS t Z=0 ∧ val F canonical qN.WS t (Z+1)=1 ∧
      t.arrs "data"=sentinelWords z ∧
      (∀ k < Snf N, (k<base ∨ base+(h+1)*(h+1)≤k) → (k<SB ∨ SB+((h+1)+1)*((h+1)*(h+1))≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame (initSelectedMode D F right O) s t := by
  obtain ⟨u,r₀,s₀,arch,hPorts,_,_,mem₀,fr₀⟩ :=
    modeArchive_run D F z forms right anchors i O old A hA hSec hiB hI hQ hB hLen hBank hBase
      ready d cap snap ctrl
  have sections : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms u := by
    have h₁ := fr₀.vars _ sep.start
    have h₂ := fr₀.vars _ sep.mid
    have h₃ := fr₀.vars _ sep.stop
    exact ⟨by rw [h₁,h₂,h₃]; exact hSec.ordered,
      by rw [h₁,h₂]; exact hSec.anchors,by rw [h₂,h₃]; exact hSec.forms⟩
  have keep (r : String) (hr : r ∈ modePowerNames) : u.vars r=s.vars r :=
    fr₀.vars _ (sep.power r hr)
  have Pu : ModePowerPorts u (h+1) SB base Z :=
    ⟨(keep _ (by decide)).trans P.size,(keep _ (by decide)).trans P.output,
      (keep _ (by decide)).trans P.input,(keep _ (by decide)).trans P.width,
      (keep _ (by decide)).trans P.square,(keep _ (by decide)).trans P.anchor,
      (keep _ (by decide)).trans P.length,(keep _ (by decide)).trans P.zero,
      (keep _ (by decide)).trans P.one,(keep _ (by decide)).trans P.first,
      (keep _ (by decide)).trans P.second⟩
  obtain ⟨τ,r₁,s₁,hWidth,hCursor,mat,powers,z₁,o₁,data,mem₁,fr₁⟩ :=
    loadModePowers_run D F z forms right anchors i A hA sections hiB
      ((fr₀.vars _ sep.requested).trans hI) s₀ hQ hB hLen ((fr₀.arrs _ sep.data).trans hBank)
      ((fr₀.vars _ sep.load).trans hBase) Pu (by omega) hSB hMB hZS hWB
      ((mem₀ Z).trans hz) ((mem₀ (Z+1)).trans ho)
  have run : Run B (initSelectedMode D F right O) s τ _ := r₀.seq r₁
  have arch' := retained_of_eq F arch (fr₁.arrs _ sep.poly) (fr₁.arrs _ sep.mult) (fr₁.vars _ sep.count)
  exact ⟨τ,run,s₁,arch',hWidth,hCursor,(fr₁.vars _ sep.workspace).trans (hPorts _ (by decide)),mat,powers,z₁,o₁,data,
    fun k hk h₁ h₂ h₃ h₄ => (mem₁ k hk h₁ h₂ h₃ h₄).trans (mem₀ k),Frame.of_run run⟩

#print axioms initSelectedMode_run
end EvenTI.P20Recover

