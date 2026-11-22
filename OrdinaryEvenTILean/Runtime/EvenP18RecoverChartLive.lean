import EvenP18RecoverChart
import Mathproof.Meta.Problem18IMPMatrixMemory20261001

/-! Compute one live primary anchor chart column from the raw square matrix and
the consecutive primary basis columns, forming the solve RHS by a paid grid. -/
namespace EvenTI.P18Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007 (Mac rOs v)
open Mathproof.P15RecogIMPTail20261007 (Mf)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT)
open Mathproof.P15DecideIMPRowKer20261007 (tRB)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC svLB svW svY svOK solveProg solveCost)

set_option autoImplicit false
set_option maxHeartbeats 4500000

def anchorBase := "even.p18.recover.chart.anchor"
def columnBase := "even.p18.recover.chart.column"

def chartA : Expr := .add (.add (.var anchorBase) (.mul (.var gU) (.var dL))) (.var dI)
def chartB : Expr := .add (.var columnBase) (.var dI)

noncomputable def livePrimaryChartColumn : Com := .seq (gridProg Mac chartA chartB) solveProg

def liveChartPorts : List String := [dL,dT,dU,dZ,gRows,gCols,gOut,anchorBase,columnBase]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem livePrimaryChartColumn_run (F : FieldPresentation K) {n w : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (xs : Fin w → Fin n → K)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval A f).mulVecLin)
    (j : Fin w) {AB CB RB AM OUT LB W YB Z Sn B : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS Sn B σ) (P : ChartPorts σ w n CB RB AM OUT LB W YB Z)
    (G : ChartGeometry w n CB RB AM OUT LB W YB Z Sn B)
    (hWord : n+1 < B)
    (hw : σ.vars qN.WS = F.e+1)
    (hCols : ∀ i : Fin w, ∀ k : Fin n, val F canonical qN.WS σ (CB+(i.val*n+k.val)) = xs i k)
    (hA : MatBlock F σ AB A)
    (hAB : σ.vars anchorBase=AB) (hVB : σ.vars columnBase=CB+j.val*n)
    (hRow : σ.vars gRows=n) (hCol : σ.vars gCols=1)
    (hDot : σ.vars dL=n) (hOut : σ.vars gOut=CB+w*n)
    (hMatBefore : AB+n*n ≤ CB) (hWorkAfter : CB+w*n+n ≤ Z)
    (hz : val F canonical qN.WS σ Z = 0)
    (ho : val F canonical qN.WS σ (Z+1) = 1) :
    ∃ τ, Run B livePrimaryChartColumn σ τ (gridCost (Mf F) chartA chartB n n 1 + solveCost F w n) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars svOK=1 ∧
      ∑ i : Fin w, val F canonical qN.WS τ (YB+i.val) • xs i = A.mulVec (xs j) ∧
      (∀ y : Fin w → K, (∑ i, y i • xs i = A.mulVec (xs j)) →
        ∀ i, y i = val F canonical qN.WS τ (YB+i.val)) ∧
      Frame livePrimaryChartColumn σ τ := by
  have hZS := G.kernel.z_s
  have hSn := hS.slots_word
  have idx (i c : ℕ) (hi : i<n) (hc : c<n) : i*n+c < n*n := by
    calc
      _ < i*n+n := Nat.add_lt_add_left hc _
      _ = (i+1)*n := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hi
  have vidx (c : ℕ) (hc : c<n) : j.val*n+c < w*n := by
    calc
      _ < j.val*n+n := Nat.add_lt_add_left hc _
      _ = (j.val+1)*n := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  obtain ⟨u,r,s,prod,mem,reg,_,_,_⟩ :=
    grid_run (Mf F) liveChartPorts (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      chartA chartB
      (by simp [chartA,VarsIn,liveChartPorts]) (by simp [chartB,VarsIn,liveChartPorts])
      (L:=n) (U:=n) (W:=1) (o0:=CB+w*n) (tt:=Z+2) (uu:=Z+3) (z:=Z)
      (fa:=fun i _ t => AB+i*n+t) (fb:=fun _ _ t => CB+j.val*n+t)
      hS hDot P.first P.second P.z hRow hCol hOut
      (by
        intro η hη i hi c hc t ht ih ch th
        have hi' := idx i t hi ht
        change (Expr.add (Expr.add (.var anchorBase) (.mul (.var gU) (.var dL))) (.var dI)).evalB B η =
          some (AB+i*n+t)
        exact ev_add (ev_add
          (ev_var ((hη _ (by decide)).trans hAB) (by omega))
          (ev_mul (ev_var ih (by omega)) (ev_var ((hη _ (by decide)).trans hDot) (by omega)) (by omega))
          (by omega)) (ev_var th (by omega)) (by omega))
      (by
        intro η hη i hi c hc t ht ih ch th
        have hi' := vidx t ht
        change (Expr.add (.var columnBase) (.var dI)).evalB B η = some (CB+j.val*n+t)
        exact ev_add (ev_var ((hη _ (by decide)).trans hVB) (by omega)) (ev_var th (by omega)) (by omega))
      (by
        intro i hi c hc t ht
        have hi' := idx i t hi ht
        refine ⟨by omega,?_⟩
        rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by
        intro i hi c hc t ht
        have hi' := vidx t ht
        refine ⟨by omega,?_⟩
        rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by rintro ⟨h₁,h₂⟩; omega)
      (by rintro ⟨h₁,h₂⟩; omega)
      hz hWord hWord (by omega) (by omega)
  have hRhs (k : Fin n) : val F canonical qN.WS u (CB+(w*n+k.val)) = A.mulVec (xs j) k := by
    have pp := prod k.val k.isLt 0 (by decide)
    simp only [Nat.mul_one,Nat.add_zero] at pp
    rw [← Nat.add_assoc,pp,Matrix.mulVec,dotProduct,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_assoc AB, hA, Nat.add_assoc CB, hCols]
  have hLiveCols (i : Fin w) (k : Fin n) :
      val F canonical qN.WS u (CB+(i.val*n+k.val)) = xs i k := by
    have hi : i.val*n+k.val < w*n := calc
      _ < i.val*n+n := Nat.add_lt_add_left k.isLt _
      _ = (i.val+1)*n := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
    rw [mem _ (by omega) (by rintro (⟨h₁,h₂⟩ | h | h) <;> omega)]
    exact hCols i k
  have Pu : ChartPorts u w n CB RB AM OUT LB W YB Z :=
    ⟨(reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.m,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.dim,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.cb,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.rb,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.am,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.out,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.lb,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.work,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.y,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.z,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.one,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.first,
      (reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.second⟩
  have hZu : val F canonical qN.WS u Z=0 := by
    rw [mem _ (by omega) (by rintro (⟨h₁,h₂⟩ | h | h) <;> omega),hz]
  have hOu : val F canonical qN.WS u (Z+1)=1 := by
    rw [mem _ (by omega) (by rintro (⟨h₁,h₂⟩ | h | h) <;> omega),ho]
  obtain ⟨τ,r₂,s₂,ok,hResult,hUnique,_⟩ := primaryChartColumn_run F A f xs hInd hSpan j s Pu G
    ((reg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw) hLiveCols hRhs hZu hOu
  have rFull : Run B livePrimaryChartColumn σ τ _ := r.seq r₂
  exact ⟨τ,rFull,s₂,ok,hResult,hUnique,Frame.of_run rFull⟩

#print axioms livePrimaryChartColumn_run
end EvenTI.P18Recover

