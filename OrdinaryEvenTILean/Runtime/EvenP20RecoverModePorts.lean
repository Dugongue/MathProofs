import EvenP20RecoverModeInit
import EvenP20RecoverCall

/-! Rebind the physical primary-kernel registers after loading and factoring
a raw mode. These assignments leave the archive, existing chart banks and
the new anchor powers in the same memory. -/
namespace EvenTI.P20Recover

open scoped Polynomial Matrix
open Matrix Polynomial EvenTI.P17Recover EvenTI.P18Recover EvenTI.Contract
open EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPMatPow20261007 (mpN mpNN mpP mpR mpT)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)
open Mathproof.P15GBFAffine20261007 (afSB)
open Mathproof.P15FactorIMP20261007 (Snf)
open Mathproof.Problem17Primary46FactorCursor (cursor)
open Mathproof.Problem17Primary46Reload (key)
open Mathproof.Problem17Primary48RawReady (ports)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Ready Capacity Retained retained_of_eq)
open Mathproof.Problem17Primary48Two (Snapshot)
open Mathproof.Problem17Repeat46 (checkpointCost)

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 90000

def modePrimaryEntries (n SB TB RB PB AM OB Z : ℕ) : List (String × ℕ) :=
  [(dL,n+1),(gRows,n),(gCols,n),(gOut,PB),(mpN,n),(mpNN,n*n),
    (afSB,SB),(mpP,PB),(mpR,RB),(mpT,TB),(tNR,n),(tD,n),(tRB,RB),
    (kAM,AM),(kOUT,OB),(dZ,Z),(rOs,Z+1),(dT,Z+2),(dU,Z+3)]

theorem modePrimaryEntries_names (n SB TB RB PB AM OB Z : ℕ) :
    (modePrimaryEntries n SB TB RB PB AM OB Z).map Prod.fst = primaryPortNames := rfl

def ModePrimaryTags (s : Env) (n SB TB RB PB AM OB Z : ℕ) : Prop :=
  ∀ p ∈ modePrimaryEntries n SB TB RB PB AM OB Z,
    s.vars (key primaryLayoutTag p.1) = p.2

theorem restorePrimaryPorts_arrayWrites : arrayWrites restorePrimaryPorts=∅ := by decide

private theorem primaryTags_restore_fresh : ∀ r ∈ primaryPortNames,
    key primaryLayoutTag r ∉ scalarWrites restorePrimaryPorts := by decide

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Install the actual frozen numeric layout using the checked register-copy
sequence for the primary caller. -/
theorem bindModePrimaryPorts_run (F : FieldPresentation K)
    {n SB TB RB PB AM OB Z Sn B : ℕ} {s : Env} (S : Slots F canonical qN.WS Sn B s)
    (tags : ModePrimaryTags s n SB TB RB PB AM OB Z)
    (fit : ∀ p ∈ modePrimaryEntries n SB TB RB PB AM OB Z, p.2 < B) :
    ∃ t, Run B restorePrimaryPorts s t 39 ∧ Slots F canonical qN.WS Sn B t ∧
      PrimaryPorts t n n SB TB RB PB AM OB Z ∧
      ModePrimaryTags t n SB TB RB PB AM OB Z ∧
      (∀ k, val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      t.arrs=s.arrs ∧ Frame restorePrimaryPorts s t := by
  have bound (r : String) (hr : r ∈ primaryPortNames) : s.vars (key primaryLayoutTag r) < B := by
    rw [← modePrimaryEntries_names n SB TB RB PB AM OB Z] at hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    rw [tags p hp]
    exact fit p hp
  obtain ⟨t,r,slots,inst,mem,fr⟩ := Mathproof.Problem17Primary46Reload.run F
    primaryLayoutTag primaryPortNames S (by decide) (by decide) (by decide) bound
  have name_mem (p : String × ℕ) (hp : p ∈ modePrimaryEntries n SB TB RB PB AM OB Z) :
      p.1 ∈ primaryPortNames := by
    rw [← modePrimaryEntries_names n SB TB RB PB AM OB Z]
    exact List.mem_map_of_mem hp
  have at_port (p : String × ℕ) (hp : p ∈ modePrimaryEntries n SB TB RB PB AM OB Z) :
      t.vars p.1=p.2 := (inst p.1 (name_mem p hp)).trans (tags p hp)
  have newPorts : PrimaryPorts t n n SB TB RB PB AM OB Z := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact at_port (dL,n+1) (by simp [modePrimaryEntries])
    · exact at_port (gRows,n) (by simp [modePrimaryEntries])
    · exact at_port (gCols,n) (by simp [modePrimaryEntries])
    · exact at_port (gOut,PB) (by simp [modePrimaryEntries])
    · exact at_port (mpN,n) (by simp [modePrimaryEntries])
    · exact at_port (mpNN,n*n) (by simp [modePrimaryEntries])
    · exact at_port (afSB,SB) (by simp [modePrimaryEntries])
    · exact at_port (mpP,PB) (by simp [modePrimaryEntries])
    · exact at_port (mpR,RB) (by simp [modePrimaryEntries])
    · exact at_port (mpT,TB) (by simp [modePrimaryEntries])
    · exact at_port (tNR,n) (by simp [modePrimaryEntries])
    · exact at_port (tD,n) (by simp [modePrimaryEntries])
    · exact at_port (tRB,RB) (by simp [modePrimaryEntries])
    · exact at_port (kAM,AM) (by simp [modePrimaryEntries])
    · exact at_port (kOUT,OB) (by simp [modePrimaryEntries])
    · exact at_port (dZ,Z) (by simp [modePrimaryEntries])
    · exact at_port (rOs,Z+1) (by simp [modePrimaryEntries])
    · exact at_port (dT,Z+2) (by simp [modePrimaryEntries])
    · exact at_port (dU,Z+3) (by simp [modePrimaryEntries])
  refine ⟨t,r,slots,newPorts,?_,mem,?_,fr⟩
  · intro p hp
    exact (fr.vars _ (primaryTags_restore_fresh _ (name_mem p hp))).trans (tags p hp)
  · funext a
    exact fr.arrs a (by
      change a ∉ arrayWrites restorePrimaryPorts
      rw [restorePrimaryPorts_arrayWrites]
      simp)

noncomputable def initModeWithPrimaryPorts (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) (O : Output) : Com :=
  .seq (initSelectedMode D F right O) restorePrimaryPorts

noncomputable def initModeWithPrimaryPortsCost (F : FieldPresentation K) (N h m l i : ℕ)
    (f : K[X]) : ℕ :=
  (checkpointCost ports m l (modeArchiveBodyCost F N h i f)+
    ((19*i+22+(3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
      (Mathproof.Problem17Primary46Powers.cost F (h+1) (h+1)+2)))+39

theorem initModeWithPrimaryPorts_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) (O : Output) {B N h base scratch m l SB TB RB PB AM OB Z : ℕ} {s : Env}
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
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1)
    (tags : ModePrimaryTags s (h+1) SB TB RB PB AM OB Z)
    (fit : ∀ p ∈ modePrimaryEntries (h+1) SB TB RB PB AM OB Z, p.2 < B)
    (fresh : ∀ r ∈ primaryPortNames, key primaryLayoutTag r ∉ scalarWrites (initSelectedMode D F right O))
    (sizeFresh : O.size ∉ scalarWrites restorePrimaryPorts) :
    ∃ t, Run B (initModeWithPrimaryPorts D F right O) s t
        (initModeWithPrimaryPortsCost F N h m l i.val A.charpoly) ∧
      Slots F canonical qN.WS (Snf N) B t ∧ Retained F N O A.charpoly t ∧
      PrimaryPorts t (h+1) (h+1) SB TB RB PB AM OB Z ∧
      ModePrimaryTags t (h+1) SB TB RB PB AM OB Z ∧
      t.vars liveAnchorWidth=h+1 ∧ t.vars cursor=0 ∧ t.vars qN.WS=s.vars qN.WS ∧
      MatBlock F t base A ∧ (∀ j ≤ h+1, MatBlock F t (SB+j*((h+1)*(h+1))) (A^j)) ∧
      val F canonical qN.WS t Z=0 ∧ val F canonical qN.WS t (Z+1)=1 ∧
      t.arrs "data"=sentinelWords z ∧
      (∀ k < Snf N, (k<base ∨ base+(h+1)*(h+1)≤k) → (k<SB ∨ SB+((h+1)+1)*((h+1)*(h+1))≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ a, a ∉ arrayWrites (initSelectedMode D F right O) → t.arrs a=s.arrs a) ∧
      Frame (initModeWithPrimaryPorts D F right O) s t := by
  obtain ⟨u,r₀,s₀,a₀,n₀,i₀,w₀,m₀,p₀,z₀,o₀,data₀,mem₀,fr₀⟩ :=
    initSelectedMode_run D F z forms right anchors i O old A hA hSec hiB hI hQ hB hLen hBank
      hBase ready d cap snap ctrl sep P hSB hMB hZS hWB hz ho
  have tags₀ : ModePrimaryTags u (h+1) SB TB RB PB AM OB Z := by
    intro p hp
    have hn : p.1 ∈ primaryPortNames := by
      rw [← modePrimaryEntries_names (h+1) SB TB RB PB AM OB Z]
      exact List.mem_map_of_mem hp
    exact (fr₀.vars _ (fresh _ hn)).trans (tags p hp)
  obtain ⟨t,r₁,s₁,p₁,tags₁,mem₁,arrays₁,fr₁⟩ := bindModePrimaryPorts_run F s₀ tags₀ fit
  have arc : Retained F N O A.charpoly t :=
    retained_of_eq F a₀ (congrFun arrays₁ _) (congrFun arrays₁ _) (fr₁.vars _ sizeFresh)
  have run : Run B (initModeWithPrimaryPorts D F right O) s t _ := r₀.seq r₁
  refine ⟨t,run,s₁,arc,p₁,tags₁,(fr₁.vars _ (by decide)).trans n₀,
    (fr₁.vars _ (by decide)).trans i₀,(fr₁.vars _ (by decide)).trans w₀,?_,?_,
    (mem₁ _).trans z₀,(mem₁ _).trans o₀,(congrFun arrays₁ _).trans data₀,?_,?_,Frame.of_run run⟩
  · intro a b
    exact (mem₁ _).trans (m₀ a b)
  · intro j hj a b
    exact (mem₁ _).trans (p₀ j hj a b)
  · intro k hk ha hb h₁ h₂
    exact (mem₁ k).trans (mem₀ k hk ha hb h₁ h₂)
  · intro a ha
    exact (congrFun arrays₁ a).trans (fr₀.arrs a ha)

#print axioms bindModePrimaryPorts_run
#print axioms initModeWithPrimaryPorts_run
end EvenTI.P20Recover

