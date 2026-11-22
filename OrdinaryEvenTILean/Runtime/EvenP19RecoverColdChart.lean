import EvenP19RecoverArchiveFrame
import EvenP19RecoverChartBank

/-! Start the complete chart builder directly from a physical kernel's width
and output bank. -/
namespace EvenTI.P19Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial EvenTI.P18Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kK XBs)

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n w : ℕ}

noncomputable def liveKernelChart : Com := .seq setChartWidth buildChartBank

theorem liveKernelChart_run (F : FieldPresentation K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (xs : Fin w → Fin n → K)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval A f).mulVecLin)
    {AB CB RB AM OUT LB W YB Z D Sn B oldWidth : ℕ} {σ : Env}
    (S : Slots F canonical qN.WS Sn B σ)
    (P : ChartBankPorts σ oldWidth n AB CB RB AM OUT LB W YB Z D)
    (G : ChartBankLayout w n AB CB RB AM OUT LB W YB Z D Sn B)
    (hRank : σ.vars kK=w) (hWS : σ.vars qN.WS=F.e+1)
    (hA : MatBlock F σ AB A)
    (hX : ∀ (i : Fin w) (k : Fin n), val F canonical qN.WS σ (CB+(i.val*n+k.val))=xs i k)
    (h₀ : val F canonical qN.WS σ Z=0) (h₁ : val F canonical qN.WS σ (Z+1)=1) :
    ∃ τ, Run B liveKernelChart σ τ (8+chartBankCost F w n) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      ChartPrefix F τ D w A xs ∧
      (∀ k < Sn, (w+1+1)*XBs n (w+1) ≤ k → (k < RB ∨ YB+w ≤ k) →
        (k < CB+w*n ∨ CB+w*n+n ≤ k) → (k < D ∨ D+w*w ≤ k) →
        k ≠ Z+2 → k ≠ Z+3 → val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame liveKernelChart σ τ := by
  have wb := G.words
  have hCol := G.solve.columns
  have hRB := G.solve.transpose
  have hAM := G.solve.kernel.am_out
  have hOUT := G.solve.kernel.out_z
  have hZ := G.solve.kernel.z_s
  have hFit : CB+w*n < B := by rw [Nat.succ_mul] at hCol; omega
  obtain ⟨u,r₀,s₀,hw,hRhs,hVal,fr₀⟩ := setChartWidth_run F S hRank P.solve.dim P.solve.cb
    (by omega) (by omega) hFit
  have keep (r : String) (h : r ∉ scalarWrites setChartWidth) : u.vars r=σ.vars r := fr₀.vars _ h
  have P₀ : ChartBankPorts u w n AB CB RB AM OUT LB W YB Z D :=
    ⟨⟨hw,(keep _ (by decide)).trans P.solve.dim,(keep _ (by decide)).trans P.solve.cb,
      (keep _ (by decide)).trans P.solve.rb,(keep _ (by decide)).trans P.solve.am,
      (keep _ (by decide)).trans P.solve.out,(keep _ (by decide)).trans P.solve.lb,
      (keep _ (by decide)).trans P.solve.work,(keep _ (by decide)).trans P.solve.y,
      (keep _ (by decide)).trans P.solve.z,(keep _ (by decide)).trans P.solve.one,
      (keep _ (by decide)).trans P.solve.first,(keep _ (by decide)).trans P.solve.second⟩,
      (keep _ (by decide)).trans P.anchor,(keep _ (by decide)).trans P.output,hRhs⟩
  obtain ⟨τ,r₁,s₁,hCursor,chart,_,mem₁,_⟩ := chartBank_run F A f xs hInd hSpan s₀ P₀ G
    ((keep _ (by decide)).trans hWS) (fun a b => (hVal _).trans (hA a b))
    (fun i k => (hVal _).trans (hX i k)) ((hVal _).trans h₀) ((hVal _).trans h₁)
  have r : Run B liveKernelChart σ τ (8+chartBankCost F w n) := r₀.seq r₁
  refine ⟨τ,r,s₁,hCursor,chart,?_,Frame.of_run r⟩
  intro k hk hlo hsolve hGrid hDest hz₁ hz₂
  exact (mem₁ k hk hlo hsolve hGrid hDest hz₁ hz₂).trans (hVal k)

#print axioms liveKernelChart_run
end EvenTI.P19Recover

