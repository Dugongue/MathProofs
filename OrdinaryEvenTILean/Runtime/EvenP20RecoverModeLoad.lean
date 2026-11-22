import EvenP17RecoverAnchorLoad
import Primary46Powers
import Primary46FactorCursor

/-! Load the actual selected mode anchor, materialize its powers in the
shared field bank, and reset the physical factor cursor. -/
namespace EvenTI.P20Recover

open EvenTI.P17Recover EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15RecogIMPPow20261007
open Mathproof.P15RecogIMPMath20261007
open Mathproof.P15GBFPowers20261007
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPMatPow20261007 (mpN mpR)
open Mathproof.Problem17Primary46FactorCursor (cursor)

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 90000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure ModePowerPorts (s : Env) (n SB MB Z : ℕ) : Prop where
  size : s.vars mpN=n
  output : s.vars mpR=SB
  input : s.vars rIn0=SB
  width : s.vars rn=n
  square : s.vars rNN=n*n
  anchor : s.vars rHH=MB
  length : s.vars wK1=n+1
  zero : s.vars dZ=Z
  one : s.vars rOs=Z+1
  first : s.vars dT=Z+2
  second : s.vars dU=Z+3

def modePowerNames : List String := [mpN,mpR,rIn0,rn,rNN,rHH,wK1,dZ,rOs,dT,dU]

def resetFactorCursor : Com := .assign cursor (.lit 0)

noncomputable def loadModePowers (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) : Com :=
  .seq (loadSelectedAnchor D F right)
    (.seq Mathproof.Problem17Primary46Powers.program resetFactorCursor)

private theorem power_names_fresh (right : Bool) : ∀ x ∈ modePowerNames,
    x ≠ liveAnchorWidth ∧ x ≠ inputBase ∧ x ≠ loadLength ∧ ¬loadChanges x ∧
      x ∉ scalarWrites (selectAnchor right) := by cases right <;> decide

theorem loadModePowers_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) {n SB MB Z Sn B : ℕ} {s : Env} (A : Matrix (Fin n) (Fin n) K)
    (hAnchor : anchors.get i=⟨n,A⟩)
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hS : Slots F canonical qN.WS Sn B s) (hQ : Fintype.card K ≤ B)
    (hB : 1 < B) (hLen : z.length < B) (hBank : s.arrs "data"=sentinelWords z)
    (hBase : s.vars loadBase=MB) (P : ModePowerPorts s n SB MB Z)
    (hn : 0<n) (hSB : SB+(n+1)*(n*n) ≤ MB) (hMB : MB+n*n ≤ Z)
    (hZS : Z+4≤Sn) (hWB : Sn+n+n+12<B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run B (loadModePowers D F right) s t
      ((19*i.val+22+(3+(11+encodedBankLoadCost F contiguousAddress (n*n))))+
        (Mathproof.Problem17Primary46Powers.cost F n n+2)) ∧
      Slots F canonical qN.WS Sn B t ∧ t.vars liveAnchorWidth=n ∧ t.vars cursor=0 ∧
      MatBlock F t MB A ∧ (∀ j ≤ n, MatBlock F t (SB+j*(n*n)) (A^j)) ∧
      val F canonical qN.WS t Z=0 ∧ val F canonical qN.WS t (Z+1)=1 ∧
      t.arrs "data"=sentinelWords z ∧
      (∀ k < Sn, (k < MB ∨ MB+n*n ≤ k) → (k < SB ∨ SB+(n+1)*(n*n) ≤ k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame (loadModePowers D F right) s t := by
  obtain ⟨u,r₀,s₀,hWidth,hV,mem₀,hData,_,_,f₀⟩ :=
    loadSelectedAnchor_run D F z forms right anchors i hSec hiB hI hS hQ hB hLen hBank hBase
      (by rw [hAnchor]; change MB+n*n≤Sn; omega)
  simp only [hAnchor] at r₀ hWidth mem₀
  let installed (I : NumberedAnchor K) :=
    ∀ k : Fin (I.width*I.width), val F canonical qN.WS u (MB+k.val)=
      I.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have rawMat : installed ⟨n,A⟩ := hAnchor ▸ (show installed (anchors.get i) from hV)
  have hMat : MatBlock F u MB A := by
    intro j k
    let idx : Fin (n*n) := finProdFinEquiv (j,k)
    have idxEq : idx.val=j.val*n+k.val := by simp [idx,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    change val F canonical qN.WS u (MB+(j.val*n+k.val))=A j k
    rw [← idxEq]
    simpa only [idx,Equiv.symm_apply_apply] using rawMat idx
  have keep₀ (x : String) (hx : x ∈ modePowerNames) : u.vars x=s.vars x := by
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := power_names_fresh right x hx
    exact f₀ x h₁ h₂ h₃ h₄ h₅
  have z₀ := (mem₀ Z (Or.inr hMB)).trans hz
  have o₀ := (mem₀ (Z+1) (Or.inr (by omega))).trans ho
  obtain ⟨v,r₁,s₁,powers,mem₁,reg₁,_,_⟩ := Mathproof.Problem17Primary46Powers.run F A hn s₀
    ((keep₀ _ (by decide)).trans P.size) ((keep₀ _ (by decide)).trans P.output)
    ((keep₀ _ (by decide)).trans P.input) ((keep₀ _ (by decide)).trans P.width)
    ((keep₀ _ (by decide)).trans P.square) ((keep₀ _ (by decide)).trans P.anchor)
    ((keep₀ _ (by decide)).trans P.length) ((keep₀ _ (by decide)).trans P.zero)
    ((keep₀ _ (by decide)).trans P.one) ((keep₀ _ (by decide)).trans P.first)
    ((keep₀ _ (by decide)).trans P.second) hMat z₀ o₀ hSB hMB hZS hWB
  let t := v.setVar cursor 0
  have r₂ : Run B resetFactorCursor v t 2 := Run.assign (evalB_lit (by omega))
  have mem₂ (k : ℕ) : val F canonical qN.WS t k=val F canonical qN.WS v k :=
    val_setVar F canonical (by decide) _ _ _
  have run : Run B (loadModePowers D F right) s t _ := r₀.seq (r₁.seq r₂)
  refine ⟨t,run,Slots.setVar F canonical s₁ (by decide) (by decide) _,
    ((Frame.of_run r₂).vars _ (by decide)).trans ((reg₁ _ (by decide)).trans hWidth),rfl,
    ?_,?_,?_,?_,?_,?_,Frame.of_run run⟩
  · intro a b
    have hIdx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    rw [mem₂,mem₁ _ (by omega) (Or.inr (by omega)) (by omega) (by omega)]
    exact hMat a b
  · intro j hj a b
    exact (mem₂ _).trans (powers j hj a b)
  · exact (mem₂ Z).trans ((mem₁ Z (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans z₀)
  · exact (mem₂ (Z+1)).trans ((mem₁ (Z+1) (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans o₀)
  · exact ((Frame.of_run r₂).arrs _ (by decide)).trans (((Frame.of_run r₁).arrs _ (by decide)).trans hData)
  · intro k hk h₁ h₂ h₃ h₄
    exact (mem₂ k).trans ((mem₁ k hk h₂ h₃ h₄).trans (mem₀ k h₁))

#print axioms loadModePowers_run
end EvenTI.P20Recover

