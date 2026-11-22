import EvenP19RecoverColumnStep

/-! One finite RAM program builds the whole restriction chart. The loop reads
the real basis width and selects every physical column exactly once. -/
namespace EvenTI.P19Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial EvenTI.P18Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs)
open Mathproof.P15DecideIMPSolve20261007 (svM)

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 100000

def chartLoopGuard : Cond := .lt (.var chartCursor) (.var svM)

noncomputable def buildChartBank : Com :=
  .seq (.assign chartCursor (.lit 0)) (.while chartLoopGuard chartStep)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n w : ℕ}

noncomputable def chartBankCost (F : FieldPresentation K) (w n : ℕ) : ℕ :=
  (4+chartStepCost F w n)*w+6

def ChartPrefix (F : FieldPresentation K) (s : Env) (D count : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (xs : Fin w → Fin n → K) : Prop :=
  ∀ j : Fin w, j.val<count →
    ∑ i : Fin w, val F canonical qN.WS s (D+(j.val*w+i.val)) • xs i = A.mulVec (xs j)

theorem chartBank_run (F : FieldPresentation K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (xs : Fin w → Fin n → K)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval A f).mulVecLin)
    {AB CB RB AM OUT LB W YB Z D Sn B : ℕ} {σ : Env}
    (S : Slots F canonical qN.WS Sn B σ)
    (P : ChartBankPorts σ w n AB CB RB AM OUT LB W YB Z D)
    (G : ChartBankLayout w n AB CB RB AM OUT LB W YB Z D Sn B)
    (hWS : σ.vars qN.WS=F.e+1)
    (hA : MatBlock F σ AB A)
    (hX : ∀ (i : Fin w) (k : Fin n), val F canonical qN.WS σ (CB+(i.val*n+k.val))=xs i k)
    (h₀ : val F canonical qN.WS σ Z=0)
    (h₁ : val F canonical qN.WS σ (Z+1)=1) :
    ∃ τ, Run B buildChartBank σ τ (chartBankCost F w n) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      ChartPrefix F τ D w A xs ∧
      (∀ r ∈ staticChartPorts, τ.vars r=σ.vars r) ∧
      (∀ k < Sn, (w+1+1)*XBs n (w+1) ≤ k → (k < RB ∨ YB+w ≤ k) →
        (k < CB+w*n ∨ CB+w*n+n ≤ k) → (k < D ∨ D+w*w ≤ k) →
        k ≠ Z+2 → k ≠ Z+3 → val F canonical qN.WS τ k = val F canonical qN.WS σ k) ∧
      Frame buildChartBank σ τ := by
  let Keep (s : Env) : Prop := ∀ k < Sn, (w+1+1)*XBs n (w+1) ≤ k →
    (k < RB ∨ YB+w ≤ k) → (k < CB+w*n ∨ CB+w*n+n ≤ k) →
    (k < D ∨ D+w*w ≤ k) → k ≠ Z+2 → k ≠ Z+3 →
    val F canonical qN.WS s k = val F canonical qN.WS σ k
  let I (s : Env) : Prop :=
    Slots F canonical qN.WS Sn B s ∧ s.vars chartCursor ≤ w ∧
      (∀ r ∈ staticChartPorts, s.vars r=σ.vars r) ∧
      MatBlock F s AB A ∧
      (∀ (i : Fin w) (k : Fin n), val F canonical qN.WS s (CB+(i.val*n+k.val))=xs i k) ∧
      val F canonical qN.WS s Z=0 ∧ val F canonical qN.WS s (Z+1)=1 ∧
      ChartPrefix F s D (s.vars chartCursor) A xs ∧ Keep s
  let V (s : Env) := w-s.vars chartCursor
  have wb := G.words
  have zCap := G.solve.kernel.z_s
  have low := G.anchorLow
  have high := G.anchorHigh
  have oLow := G.outLow
  have oHigh := G.outHigh
  have colFit : CB+w*n+n ≤ RB := by
    simpa [Nat.succ_mul,Nat.add_assoc] using G.solve.columns
  have workFit : RB ≤ YB := by
    have := G.solve.transpose
    have := G.solve.kernel.am_out
    have := G.solve.out
    have := G.solve.labels
    have := G.solve.work
    omega
  have guard (s : Env) (h : I s) : chartLoopGuard.evalB B s=
      some (decide (s.vars chartCursor < w)) := by
    have hw : s.vars svM=w := (h.2.2.1 _ (by decide)).trans P.solve.m
    have hc := h.2.1
    exact evalB_condLt (evalB_var (by omega)) (ev_var hw (by omega))
  let σ₀ := σ.setVar chartCursor 0
  have r₀ : Run B (.assign chartCursor (.lit 0)) σ σ₀ 2 := Run.assign (evalB_lit (by omega))
  have v₀ (k : ℕ) : val F canonical qN.WS σ₀ k = val F canonical qN.WS σ k :=
    val_setVar F canonical (by decide) _ _ _
  have hI : I σ₀ := by
    refine ⟨Slots.setVar F canonical S (by decide) (by decide) _,by simp [σ₀],?_,
      fun a b => (v₀ _).trans (hA a b),fun i k => (v₀ _).trans (hX i k),
      (v₀ _).trans h₀,(v₀ _).trans h₁,?_,fun k _ _ _ _ _ _ _ => v₀ k⟩
    · intro r hr
      have hh : r ≠ chartCursor := fun e => (show chartCursor ∉ staticChartPorts by decide) (e ▸ hr)
      simp [σ₀,vars_setVar,hh]
    · intro j hj
      have hh : σ₀.vars chartCursor=0 := rfl
      omega
  have inner (s : Env) (h : I s) (hg : chartLoopGuard.evalB B s=some true) :
      ∃ t, Run B chartStep s t (chartStepCost F w n) ∧ I t ∧ V t < V s := by
    have hi : s.vars chartCursor < w := by
      rw [guard s h] at hg
      exact of_decide_eq_true (Option.some.inj hg)
    obtain ⟨hs,hc,hreg,ha,hx,hz₀,hz₁,done,unchanged⟩ := h
    let j : Fin w := ⟨s.vars chartCursor,hi⟩
    have Ps : ChartBankPorts s w n AB CB RB AM OUT LB W YB Z D :=
      ⟨chartPorts_of_eq P.solve hreg,(hreg _ (by decide)).trans P.anchor,
        (hreg _ (by decide)).trans P.output,(hreg _ (by decide)).trans P.rhs⟩
    obtain ⟨t,rt,st,it,current,reg,mem,_⟩ := chartStep_run F A f xs hInd hSpan j hs Ps G
      ((hreg _ (by decide)).trans hWS) rfl ha hx hz₀ hz₁
    have leJ : j.val+1 ≤ w := j.isLt
    have lastD : D+j.val*w+w ≤ D+w*w := by
      have h := Nat.mul_le_mul_right w leJ
      rw [Nat.succ_mul] at h
      omega
    have highKeep (k : ℕ) (hk : k=Z ∨ k=Z+1) :
        val F canonical qN.WS t k=val F canonical qN.WS s k :=
      mem k (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (by omega) (by omega)
    have belowKeep (k : ℕ) (hlo : AB ≤ k) (hh : k < CB+w*n) :
        val F canonical qN.WS t k=val F canonical qN.WS s k :=
      mem k (by omega) (by omega) (Or.inl (by omega)) (Or.inl hh)
        (Or.inl (by omega)) (by omega) (by omega)
    refine ⟨t,rt,⟨st,by rw [it]; exact leJ,fun r hr => (reg r hr).trans (hreg r hr),?_,?_,
      (highKeep Z (Or.inl rfl)).trans hz₀,(highKeep (Z+1) (Or.inr rfl)).trans hz₁,?_,?_⟩,?_⟩
    · intro a b
      have ix := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
      rw [belowKeep _ (by omega) (by omega)]
      exact ha a b
    · intro a b
      have ix := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
      rw [belowKeep _ (by omega) (by omega)]
      exact hx a b
    · intro p hp
      by_cases hSame : p=j
      · subst p
        exact current
      · have prev : p.val < j.val := by
          rw [it] at hp
          have ne : p.val ≠ j.val := fun e => hSame (Fin.ext e)
          omega
        have dx : D+(p.val*w+w) ≤ D+j.val*w := by
          have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt prev)
          rw [Nat.succ_mul] at hh
          omega
        have entry (a : Fin w) :
            val F canonical qN.WS t (D+(p.val*w+a.val)) =
              val F canonical qN.WS s (D+(p.val*w+a.val)) :=
          mem _ (by have := a.isLt; omega) (by omega) (Or.inr (by omega))
            (Or.inr (by omega)) (Or.inl (by have := a.isLt; omega)) (by omega) (by omega)
        simpa only [entry] using done p prev
    · intro k hk hLo hSolve hR hD hA hB
      have hDest : k < D+j.val*w ∨ D+j.val*w+w ≤ k :=
        hD.imp (fun hh => by omega) (fun hh => by omega)
      exact (mem k hk hLo hSolve hR hDest hA hB).trans (unchanged k hk hLo hSolve hR hD hA hB)
    · rw [show V t=w-t.vars chartCursor from rfl,it]
      change w-(j.val+1) < w-j.val
      have := j.isLt
      omega
  obtain ⟨τ,r,h,stop⟩ := Run.while_count I V (chartStepCost F w n)
    (fun s hs => ⟨_,guard s hs⟩) inner hI
  have hPos : τ.vars chartCursor=w := by
    have hLE := h.2.1
    rw [guard τ h] at stop
    exact le_antisymm hLE (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj stop)))
  obtain ⟨ht,_,reg,_,_,_,_,done,mem⟩ := h
  have run : Run B buildChartBank σ τ (chartBankCost F w n) := (r₀.seq r).mono (by
    have hh : V σ₀=w := by simp [V,σ₀]
    rw [hh]
    change 2+((1+3+chartStepCost F w n)*w+1+3) ≤ (4+chartStepCost F w n)*w+6
    rw [show 1+3=4 by decide]
    omega)
  exact ⟨τ,run,ht,hPos,by simpa only [hPos] using done,reg,mem,Frame.of_run run⟩

/-- The physical chart bank obeys the matrix intertwining identity for the
primary basis it actually received. -/
theorem chartPrefix_intertwines (F : FieldPresentation K) {s : Env} {D : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (xs : Fin w → Fin n → K)
    (h : ChartPrefix F s D w A xs) :
    let C : Matrix (Fin n) (Fin w) K := fun i j => xs j i
    let T : Matrix (Fin w) (Fin w) K :=
      fun i j => val F canonical qN.WS s (D+(j.val*w+i.val))
    C*T=A*C := by
  dsimp only
  ext i j
  have hCol := congrFun (h j j.isLt) i
  change (∑ k : Fin w, xs k i * val F canonical qN.WS s (D+(j.val*w+k.val))) =
    ∑ k : Fin n, A i k * xs j k
  simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hCol

#print axioms chartPrefix_intertwines
#print axioms chartBank_run
end EvenTI.P19Recover

