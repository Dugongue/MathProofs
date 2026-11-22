import EvenP19RecoverColdChart
import Primary46Reload

/-! Reload the chart-specific addresses from stable layout registers after the
factor kernel has used the same mutable IMP registers for its own workspace. -/
namespace EvenTI.P19Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial EvenTI.P18Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kK kAM kOUT XBs)
open Mathproof.P15DecideIMPRowKer20261007 (tRB)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC svLB svW svY)
open Mathproof.Problem17Primary46Reload (key)

set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxRecDepth 80000

def chartLayoutTag : String := "even.p19.recover.chart.layout."

def chartLayoutEntries (n AB CB RB AM OUT LB W YB Z D : ℕ) : List (String × ℕ) :=
  [(svM,0),(svL,n),(svC,CB),(tRB,RB),(kAM,AM),(kOUT,OUT),(svLB,LB),
    (svW,W),(svY,YB),(dZ,Z),(rOs,Z+1),(dT,Z+2),(dU,Z+3),
    (anchorBase,AB),(chartOutputBase,D),(chartRhs,CB)]

def chartLayoutNames : List String := (chartLayoutEntries 0 0 0 0 0 0 0 0 0 0 0).map Prod.fst

theorem chartLayoutEntries_names (n AB CB RB AM OUT LB W YB Z D : ℕ) :
    (chartLayoutEntries n AB CB RB AM OUT LB W YB Z D).map Prod.fst = chartLayoutNames := rfl

def readChartLayout : Com := Mathproof.Problem17Primary46Reload.program chartLayoutTag chartLayoutNames

def ChartLayoutRegisters (σ : Env) (n AB CB RB AM OUT LB W YB Z D : ℕ) : Prop :=
  ∀ p ∈ chartLayoutEntries n AB CB RB AM OUT LB W YB Z D,
    σ.vars (key chartLayoutTag p.1)=p.2

noncomputable def reloadKernelChart : Com := .seq readChartLayout liveKernelChart

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n w : ℕ}

theorem readChartLayout_run (F : FieldPresentation K) {AB CB RB AM OUT LB W YB Z D Sn B : ℕ} {σ : Env}
    (S : Slots F canonical qN.WS Sn B σ)
    (Ready : ChartLayoutRegisters σ n AB CB RB AM OUT LB W YB Z D)
    (fit : ∀ p ∈ chartLayoutEntries n AB CB RB AM OUT LB W YB Z D, p.2<B) :
    ∃ τ, Run B readChartLayout σ τ 33 ∧ Slots F canonical qN.WS Sn B τ ∧
      ChartBankPorts τ 0 n AB CB RB AM OUT LB W YB Z D ∧
      (∀ s, val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      Frame readChartLayout σ τ := by
  have hWord (r : String) (hr : r ∈ chartLayoutNames) : σ.vars (key chartLayoutTag r) < B := by
    rw [← chartLayoutEntries_names n AB CB RB AM OUT LB W YB Z D] at hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    rw [Ready _ hp]
    exact fit _ hp
  obtain ⟨τ,r,s,hInst,hm,fr⟩ := Mathproof.Problem17Primary46Reload.run F chartLayoutTag chartLayoutNames S
    (by decide) (by decide) (by decide) hWord
  have inst (p : String × ℕ) (hp : p ∈ chartLayoutEntries n AB CB RB AM OUT LB W YB Z D) :
      τ.vars p.1=p.2 := by
    have hMem : p.1 ∈ chartLayoutNames := by
      rw [← chartLayoutEntries_names n AB CB RB AM OUT LB W YB Z D]
      exact List.mem_map_of_mem hp
    rw [hInst _ hMem, Ready _ hp]
  refine ⟨τ,r,s,⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩,hm,fr⟩
  · exact inst (svM,0) (by simp [chartLayoutEntries])
  · exact inst (svL,n) (by simp [chartLayoutEntries])
  · exact inst (svC,CB) (by simp [chartLayoutEntries])
  · exact inst (tRB,RB) (by simp [chartLayoutEntries])
  · exact inst (kAM,AM) (by simp [chartLayoutEntries])
  · exact inst (kOUT,OUT) (by simp [chartLayoutEntries])
  · exact inst (svLB,LB) (by simp [chartLayoutEntries])
  · exact inst (svW,W) (by simp [chartLayoutEntries])
  · exact inst (svY,YB) (by simp [chartLayoutEntries])
  · exact inst (dZ,Z) (by simp [chartLayoutEntries])
  · exact inst (rOs,Z+1) (by simp [chartLayoutEntries])
  · exact inst (dT,Z+2) (by simp [chartLayoutEntries])
  · exact inst (dU,Z+3) (by simp [chartLayoutEntries])
  · exact inst (anchorBase,AB) (by simp [chartLayoutEntries])
  · exact inst (chartOutputBase,D) (by simp [chartLayoutEntries])
  · simpa only [Nat.zero_mul,Nat.add_zero] using inst (chartRhs,CB) (by simp [chartLayoutEntries])

theorem reloadKernelChart_run (F : FieldPresentation K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (xs : Fin w → Fin n → K)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval A f).mulVecLin)
    {AB CB RB AM OUT LB W YB Z D Sn B : ℕ} {σ : Env}
    (S : Slots F canonical qN.WS Sn B σ)
    (Ready : ChartLayoutRegisters σ n AB CB RB AM OUT LB W YB Z D)
    (fit : ∀ p ∈ chartLayoutEntries n AB CB RB AM OUT LB W YB Z D, p.2<B)
    (G : ChartBankLayout w n AB CB RB AM OUT LB W YB Z D Sn B)
    (hRank : σ.vars kK=w) (hWS : σ.vars qN.WS=F.e+1)
    (hA : MatBlock F σ AB A)
    (hX : ∀ (i : Fin w) (k : Fin n), val F canonical qN.WS σ (CB+(i.val*n+k.val))=xs i k)
    (h₀ : val F canonical qN.WS σ Z=0) (h₁ : val F canonical qN.WS σ (Z+1)=1) :
    ∃ τ, Run B reloadKernelChart σ τ (33+(8+chartBankCost F w n)) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      ChartPrefix F τ D w A xs ∧
      (∀ k < Sn, (w+1+1)*XBs n (w+1) ≤ k → (k < RB ∨ YB+w ≤ k) →
        (k < CB+w*n ∨ CB+w*n+n ≤ k) → (k < D ∨ D+w*w ≤ k) →
        k ≠ Z+2 → k ≠ Z+3 → val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame reloadKernelChart σ τ := by
  obtain ⟨ρ,r₀,s₀,p₀,mem₀,fr₀⟩ := readChartLayout_run F S Ready fit
  obtain ⟨τ,r₁,s₁,k,rows,mem₁,_⟩ := liveKernelChart_run F A f xs hInd hSpan s₀ p₀ G
    ((fr₀.vars kK (by decide)).trans hRank) ((fr₀.vars qN.WS (by decide)).trans hWS)
    (fun a b => (mem₀ _).trans (hA a b)) (fun i k => (mem₀ _).trans (hX i k))
    ((mem₀ _).trans h₀) ((mem₀ _).trans h₁)
  have run : Run B reloadKernelChart σ τ _ := r₀.seq r₁
  refine ⟨τ,run,s₁,k,rows,?_,Frame.of_run run⟩
  intro v hv hlo hs hGrid hDest hz₁ hz₂
  exact (mem₁ v hv hlo hs hGrid hDest hz₁ hz₂).trans (mem₀ v)

#print axioms readChartLayout_run
#print axioms reloadKernelChart_run
end EvenTI.P19Recover

