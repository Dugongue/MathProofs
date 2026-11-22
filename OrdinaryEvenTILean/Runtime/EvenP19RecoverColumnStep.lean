import EvenP19RecoverFramed
import Mathproof.Meta.P15DecideIMPSplit20261007

/-! One paid iteration for building the complete restricted-anchor chart.
A pointer selects the next live primary basis column. The checked solver's
output is copied to an independent durable region. -/
namespace EvenTI.P19Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial EvenTI.P18Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007 (rOs v lit setGrid)
open Mathproof.P15RecogIMPTail20261007 (Mf setGrid_run slots_setGrid val_setGrid vars_setGrid)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT XBs)
open Mathproof.P15DecideIMPRowKer20261007 (tRB)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC svLB svW svY solveCost)
open Mathproof.P15DecideIMPSplit20261007 (cpBlk cpBlk_run)
open Mathproof.P15DecideIMPCopy20261007 (copyCost)

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 100000

def chartCursor := "even.p19.recover.chart.cursor"
def chartOutputBase := "even.p19.recover.chart.output.base"
def chartOutputCol := "even.p19.recover.chart.output.column"
def chartRhs := "even.p19.recover.chart.rhs"

def columnOffset (base width : String) : Expr :=
  .add (.var base) (.mul (.var chartCursor) (.var width))

def configureChart : Com :=
  .seq (setGrid (v svL) (lit 1) (v svL) (v chartRhs))
    (.seq (.assign columnBase (columnOffset svC svL))
      (.assign chartOutputCol (columnOffset chartOutputBase svM)))

noncomputable def chartStep : Com :=
  .seq configureChart
    (.seq livePrimaryChartColumn
      (.seq (cpBlk svY chartOutputCol svM)
        (.assign chartCursor (.add (.var chartCursor) (.lit 1)))))

def staticChartPorts : List String :=
  [svM,svL,svC,tRB,kAM,kOUT,svLB,svW,svY,dZ,rOs,dT,dU,
    qN.WS,anchorBase,chartOutputBase,chartRhs]

theorem chartPorts_of_eq {s t : Env} {w n CB RB AM OUT LB W YB Z : ℕ}
    (P : ChartPorts s w n CB RB AM OUT LB W YB Z)
    (keep : ∀ r ∈ staticChartPorts, t.vars r=s.vars r) :
    ChartPorts t w n CB RB AM OUT LB W YB Z :=
  ⟨(keep _ (by decide)).trans P.m,(keep _ (by decide)).trans P.dim,
    (keep _ (by decide)).trans P.cb,(keep _ (by decide)).trans P.rb,
    (keep _ (by decide)).trans P.am,(keep _ (by decide)).trans P.out,
    (keep _ (by decide)).trans P.lb,(keep _ (by decide)).trans P.work,
    (keep _ (by decide)).trans P.y,(keep _ (by decide)).trans P.z,
    (keep _ (by decide)).trans P.one,(keep _ (by decide)).trans P.first,
    (keep _ (by decide)).trans P.second⟩

private theorem configureStatic : ∀ r ∈ staticChartPorts, r ∉ scalarWrites configureChart := by decide
private theorem callStatic : ∀ r ∈ (chartCursor::chartOutputCol::staticChartPorts),
    r ∉ scalarWrites livePrimaryChartColumn := by decide
private theorem copyStatic : ∀ r ∈ (chartCursor::staticChartPorts),
    r ∉ scalarWrites (cpBlk svY chartOutputCol svM) := by decide

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure ChartBankPorts (σ : Env) (w n AB CB RB AM OUT LB W YB Z D : ℕ) : Prop where
  solve : ChartPorts σ w n CB RB AM OUT LB W YB Z
  anchor : σ.vars anchorBase=AB
  output : σ.vars chartOutputBase=D
  rhs : σ.vars chartRhs=CB+w*n

structure ChartBankLayout (w n AB CB RB AM OUT LB W YB Z D Sn B : ℕ) : Prop where
  solve : ChartGeometry w n CB RB AM OUT LB W YB Z Sn B
  anchorLow : (w+1+1)*XBs n (w+1) ≤ AB
  anchorHigh : AB+n*n ≤ CB
  outLow : YB+w ≤ D
  outHigh : D+w*w ≤ Z
  words : Sn+n+w+10 < B

noncomputable def chartStepCost (F : FieldPresentation K) (w n : ℕ) : ℕ :=
  20+(gridCost (Mf F) chartA chartB n n 1+solveCost F w n)+(6+copyCost F w)+4

private theorem configureChart_run (F : FieldPresentation K)
    {w n AB CB RB AM OUT LB W YB Z D Sn B : ℕ} {σ : Env}
    (P : ChartBankPorts σ w n AB CB RB AM OUT LB W YB Z D)
    (G : ChartBankLayout w n AB CB RB AM OUT LB W YB Z D Sn B)
    (S : Slots F canonical qN.WS Sn B σ) (j : Fin w) (hJ : σ.vars chartCursor=j.val) :
    ∃ τ, Run B configureChart σ τ 20 ∧ Slots F canonical qN.WS Sn B τ ∧
      τ.vars gRows=n ∧ τ.vars gCols=1 ∧ τ.vars dL=n ∧ τ.vars gOut=CB+w*n ∧
      τ.vars columnBase=CB+j.val*n ∧ τ.vars chartOutputCol=D+j.val*w ∧
      τ.vars chartCursor=j.val ∧
      (∀ k, val F canonical qN.WS τ k = val F canonical qN.WS σ k) := by
  have hZ := G.solve.kernel.z_s
  have hB := G.words
  have hR := G.solve.columns
  have hA := G.solve.transpose
  have hOut := G.outHigh
  have hW := G.solve.y
  have hL := G.outLow
  have hLayout := G.solve.kernel.am_out
  have hO := G.solve.kernel.out_z
  have hRhs : CB+w*n+n ≤ RB := by simpa [Nat.succ_mul,Nat.add_assoc] using hR
  have hJn := Nat.mul_le_mul_right n (Nat.le_of_lt j.isLt)
  have hJw := Nat.mul_le_mul_right w (Nat.le_of_lt j.isLt)
  let u := (((σ.setVar gRows n).setVar gCols 1).setVar dL n).setVar gOut (CB+w*n)
  have ru : Run B (setGrid (v svL) (lit 1) (v svL) (v chartRhs)) σ u 8 :=
    setGrid_run (v svL) (lit 1) (v svL) (v chartRhs) [svL,chartRhs]
      (by decide) (by simp [v,VarsIn]) (by simp [lit,VarsIn])
      (by simp [v,VarsIn]) (by simp [v,VarsIn])
      (ev_var P.solve.dim (by omega)) (evalB_lit (by omega))
      (ev_var P.solve.dim (by omega)) (ev_var P.rhs (by omega))
  have ug (r : String) (h₁ : r ≠ gRows) (h₂ : r ≠ gCols) (h₃ : r ≠ dL)
      (h₄ : r ≠ gOut) : u.vars r=σ.vars r := vars_setGrid _ _ _ _ _ _ h₁ h₂ h₃ h₄
  let v₁ := u.setVar columnBase (CB+j.val*n)
  have rv₁ : Run B (.assign columnBase (columnOffset svC svL)) u v₁ 6 :=
    Run.assign (ev_add
      (ev_var ((ug _ (by decide) (by decide) (by decide) (by decide)).trans P.solve.cb) (by omega))
      (ev_mul (ev_var ((ug _ (by decide) (by decide) (by decide) (by decide)).trans hJ) (by have := j.isLt; omega))
        (ev_var ((ug _ (by decide) (by decide) (by decide) (by decide)).trans P.solve.dim) (by omega))
        (by omega)) (by omega))
  have vx (r : String) (h₁ : r ≠ gRows) (h₂ : r ≠ gCols) (h₃ : r ≠ dL)
      (h₄ : r ≠ gOut) (h₅ : r ≠ columnBase) : v₁.vars r=σ.vars r := by
    simp only [v₁,vars_setVar,if_neg h₅]
    exact ug r h₁ h₂ h₃ h₄
  let t := v₁.setVar chartOutputCol (D+j.val*w)
  have rt : Run B (.assign chartOutputCol (columnOffset chartOutputBase svM)) v₁ t 6 :=
    Run.assign (ev_add
      (ev_var ((vx _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.output) (by omega))
      (ev_mul (ev_var ((vx _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hJ) (by have := j.isLt; omega))
        (ev_var ((vx _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans P.solve.m) (by omega))
        (by omega)) (by omega))
  have rr : Run B configureChart σ t 20 := ru.seq (rv₁.seq rt)
  refine ⟨t,rr,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Slots.setVar F canonical
      (Slots.setVar F canonical (slots_setGrid F S _ _ _ _) (by decide) (by decide) _)
      (by decide) (by decide) _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ((Frame.of_run rr).vars chartCursor (by decide)).trans hJ
  · intro k
    rw [show t=v₁.setVar chartOutputCol _ from rfl,val_setVar F canonical (by decide),
      show v₁=u.setVar columnBase _ from rfl,val_setVar F canonical (by decide)]
    exact val_setGrid F σ n 1 n (CB+w*n) k

theorem chartStep_run (F : FieldPresentation K) {w n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (xs : Fin w → Fin n → K)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval A f).mulVecLin)
    (j : Fin w) {AB CB RB AM OUT LB W YB Z D Sn B : ℕ} {σ : Env}
    (S : Slots F canonical qN.WS Sn B σ)
    (P : ChartBankPorts σ w n AB CB RB AM OUT LB W YB Z D)
    (G : ChartBankLayout w n AB CB RB AM OUT LB W YB Z D Sn B)
    (hWS : σ.vars qN.WS=F.e+1) (hJ : σ.vars chartCursor=j.val)
    (hA : MatBlock F σ AB A)
    (hX : ∀ (i : Fin w) (k : Fin n), val F canonical qN.WS σ (CB+(i.val*n+k.val))=xs i k)
    (h0 : val F canonical qN.WS σ Z=0) (h1 : val F canonical qN.WS σ (Z+1)=1) :
    ∃ τ, Run B chartStep σ τ (chartStepCost F w n) ∧ Slots F canonical qN.WS Sn B τ ∧
      τ.vars chartCursor=j.val+1 ∧
      (∑ i : Fin w, val F canonical qN.WS τ (D+(j.val*w+i.val)) • xs i = A.mulVec (xs j)) ∧
      (∀ r ∈ staticChartPorts, τ.vars r=σ.vars r) ∧
      (∀ k < Sn, (w+1+1)*XBs n (w+1) ≤ k → (k < RB ∨ YB+w ≤ k) →
        (k < CB+w*n ∨ CB+w*n+n ≤ k) → (k < D+j.val*w ∨ D+j.val*w+w ≤ k) →
        k ≠ Z+2 → k ≠ Z+3 → val F canonical qN.WS τ k = val F canonical qN.WS σ k) ∧
      Frame chartStep σ τ := by
  have hB := G.words
  have hZ := G.solve.kernel.z_s
  have hLow := G.outLow
  have hHigh := G.outHigh
  have hD : D+j.val*w+w ≤ Z := by
    have h := Nat.mul_le_mul_right w (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at h
    omega
  have hR : CB+w*n+n ≤ Z := by
    have h1 := G.solve.columns
    have h2 := G.solve.transpose
    have h3 := G.solve.kernel.am_out
    have h4 := G.solve.kernel.out_z
    rw [Nat.succ_mul] at h1
    omega
  obtain ⟨u,r₀,s₀,rows,cols,dot,rhs,uc,dst,uj,mem₀⟩ := configureChart_run F P G S j hJ
  have fr₀ := Frame.of_run r₀
  have f₀ (r : String) (hr : r ∈ staticChartPorts) : u.vars r=σ.vars r :=
    fr₀.vars _ (configureStatic _ hr)
  have A₀ : MatBlock F u AB A := fun a b => (mem₀ _).trans (hA a b)
  obtain ⟨v₂,r₁,s₁,_,coord,_,mem₁,fr₁⟩ := livePrimaryChartColumnFramed_run F A f xs
    hInd hSpan j s₀ (chartPorts_of_eq P.solve f₀) G.solve (by omega)
    ((f₀ _ (by decide)).trans hWS) (fun i k => (mem₀ _).trans (hX i k)) A₀
    ((f₀ _ (by decide)).trans P.anchor) uc rows cols dot rhs G.anchorHigh hR
    ((mem₀ _).trans h0) ((mem₀ _).trans h1)
  have f₁ (r : String) (hr : r ∈ staticChartPorts) : v₂.vars r=σ.vars r :=
    (fr₁.vars _ (callStatic _ (by simp [hr]))).trans (f₀ r hr)
  have z₁ : val F canonical qN.WS v₂ Z=0 := by
    rw [mem₁ _ (by omega) (by have := G.anchorLow; have := G.anchorHigh; omega)
      (Or.inr (by omega)) (Or.inr hR) (by omega) (by omega), mem₀, h0]
  have o₁ : val F canonical qN.WS v₂ (Z+1)=1 := by
    rw [mem₁ _ (by omega) (by have := G.anchorLow; have := G.anchorHigh; omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega), mem₀, h1]
  obtain ⟨v₃,r₂,s₂,data,mem₂,reg₂,_,_⟩ := cpBlk_run F svY chartOutputCol svM s₁
    (by decide) (by decide) (by decide)
    ((f₁ _ (by decide)).trans P.solve.y)
    ((fr₁.vars _ (callStatic _ (by decide))).trans dst)
    ((f₁ _ (by decide)).trans P.solve.m)
    ((f₁ _ (by decide)).trans P.solve.z) ((f₁ _ (by decide)).trans P.solve.one)
    ((f₁ _ (by decide)).trans P.solve.first) ((f₁ _ (by decide)).trans P.solve.second)
    z₁ o₁ (Or.inl (by omega)) G.solve.y hD hZ (by omega)
  have j₃ : v₃.vars chartCursor=j.val :=
    (reg₂ _ (copyStatic _ (by decide))).trans ((fr₁.vars _ (callStatic _ (by decide))).trans uj)
  let τ := v₃.setVar chartCursor (j.val+1)
  have r₃ : Run B (.assign chartCursor (.add (.var chartCursor) (.lit 1))) v₃ τ 4 :=
    Run.assign (ev_add (ev_var j₃ (by have := j.isLt; omega)) (evalB_lit (by omega))
      (by have := j.isLt; omega))
  have r : Run B chartStep σ τ (chartStepCost F w n) :=
    (r₀.seq (r₁.seq (r₂.seq r₃))).mono (by unfold chartStepCost; omega)
  have finalMem (k : ℕ) : val F canonical qN.WS τ k=val F canonical qN.WS v₃ k :=
    val_setVar F canonical (by decide) _ _ _
  refine ⟨τ,r,Slots.setVar F canonical s₂ (by decide) (by decide) _,rfl,?_,?_,?_,Frame.of_run r⟩
  · have he (i : Fin w) : val F canonical qN.WS τ (D+(j.val*w+i.val)) =
        val F canonical qN.WS v₂ (YB+i.val) := by
      rw [finalMem,← Nat.add_assoc,data _ i.isLt]
    simp only [he]
    exact coord
  · intro r hr
    have near : r ≠ chartCursor := by
      intro he; subst r; exact (show chartCursor ∉ staticChartPorts by decide) hr
    simp only [τ,vars_setVar,if_neg near]
    exact (reg₂ _ (copyStatic _ (by simp [hr]))).trans (f₁ r hr)
  · intro k hk hlo harea hGrid hDest hz₁ hz₂
    exact (finalMem k).trans ((mem₂ k hk hDest hz₁ hz₂).trans
      ((mem₁ k hk hlo harea hGrid hz₁ hz₂).trans (mem₀ k)))

#print axioms chartStep_run
end EvenTI.P19Recover

