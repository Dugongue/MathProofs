import EvenP16TrialRectangular
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P16Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames NoVar)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)

structure RectangularWords where
  rows : String
  inner : String
  columns : String
  left : String
  right : String
  output : String

def RectangularWords.regs (R : RectangularWords) : List String :=
  [R.rows,R.inner,R.columns,R.left,R.right,R.output]

def rectangularTargets : List String :=
  [gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut]

def rectangularBindings (R : RectangularWords) : List (String×Expr) :=
  [(gRows,.var R.rows),(dL,.var R.inner),(gCols,.var R.columns),
   (rectangularLeftBase,.var R.left),(rectangularRightBase,.var R.right),(gOut,.var R.output)]

private theorem safeBindings (R : RectangularWords)
    (h : ∀ r ∈ R.regs, r ∉ rectangularTargets) :
    ∀ p ∈ rectangularBindings R, ∀ q ∈ rectangularBindings R, NoVar p.1 q.2 := by
  have h₀ : (rectangularBindings R).map Prod.fst = rectangularTargets := rfl
  have h₁ : (rectangularBindings R).map Prod.snd = R.regs.map Expr.var := rfl
  intro p hp q hq
  have hP : p.1 ∈ rectangularTargets := h₀ ▸ List.mem_map.mpr ⟨p,hp,rfl⟩
  have hQ : q.2 ∈ R.regs.map Expr.var := h₁ ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
  obtain ⟨v,hv,hEq⟩ := List.mem_map.mp hQ
  rw [← hEq]
  exact fun hv' => h v hv (hv' ▸ hP)

variable {K : Type} [Field K] [Fintype K]

noncomputable def rectangularCall (F : FieldPresentation K) (transpose : Bool)
    (R : RectangularWords) : Com :=
  .seq (commands (rectangularBindings R)) (rectangularProduct F transpose)

/-- Install all six call arguments from live saved words, execute the paid
product, and preserve the banks and control words needed by the next call. -/
theorem rectangularCall_run (F : FieldPresentation K) (transpose : Bool) (R : RectangularWords)
    {m k r a b o z t u Sn B : ℕ} {σ : Env}
    (hSafe : ∀ x ∈ R.regs, x ∉ rectangularTargets)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hLeft : a+m*k ≤ o) (hRight : b+(if transpose then r*k else k*r) ≤ o)
    (hFit : o+m*r ≤ Sn)
    (ht : t < Sn) (hu : u < Sn) (htu : t ≠ u)
    (hts : o+m*r ≤ t ∨ (t < a ∧ t < b))
    (hus : o+m*r ≤ u ∨ (u < a ∧ u < b))
    (hz : z < Sn) (hzW : ¬ Written o m r t u z) (hz0 : val F canonical qN.WS σ z=0)
    (hWords : m+1 < B ∧ k+1 < B ∧ r+1 < B)
    (hm : σ.vars R.rows=m) (hk : σ.vars R.inner=k) (hr : σ.vars R.columns=r)
    (ha : σ.vars R.left=a) (hb : σ.vars R.right=b) (ho : σ.vars R.output=o)
    (hRegT : σ.vars dT=t) (hRegU : σ.vars dU=u) (hRegZ : σ.vars dZ=z) :
    ∃ τ, Run B (rectangularCall F transpose R) σ τ (13+rectangularCost F transpose m k r) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ i < m, ∀ j < r, val F canonical qN.WS τ (o+(i*r+j)) =
        ∑ x ∈ Finset.range k, val F canonical qN.WS σ (a+(i*k+x)) *
          val F canonical qN.WS σ (rightIndex transpose b k r x j)) ∧
      (∀ s < Sn, ¬ Written o m r t u s → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      (∀ x, x ∉ rectangularTargets → x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x=σ.vars x) ∧
      (∀ x, x ≠ canonical.mem → x ≠ canonical.scratch → τ.arrs x=σ.arrs x) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
  let args := [(gRows,m),(dL,k),(gCols,r),(rectangularLeftBase,a),(rectangularRightBase,b),(gOut,o)]
  let ρ := install args σ
  have hS := hSlots.slots_word
  have hB : b < B := by
    have hh := Nat.le_add_right b (if transpose then r*k else k*r)
    omega
  have r₀ : Run B (commands (rectangularBindings R)) σ ρ 13 :=
    commands_run (rectangularBindings R) [m,k,r,a,b,o] σ rfl
      (.cons (ev_var hm (by omega)) (.cons (ev_var hk (by omega)) (.cons (ev_var hr (by omega))
       (.cons (ev_var ha (by omega)) (.cons (ev_var hb hB) (.cons (ev_var ho (by omega)) .nil))))))
      (safeBindings R hSafe)
  have fieldSafe : ∀ p ∈ args, canonical.e ≠ p.1 ∧ canonical.p ≠ p.1 ∧
      canonical.modBase ≠ p.1 ∧ canonical.exp ≠ p.1 ∧ qN.WS ≠ p.1 := by
    intro p hp
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h|h|h|h|h|h <;> subst p <;> simp only [Prod.fst] <;> decide
  have hSlots' : Slots F canonical qN.WS Sn B ρ := installed_slots F args σ hSlots fieldSafe
  have hReg (x : String) (hx : x ∉ rectangularTargets) : ρ.vars x=σ.vars x :=
    installed_scalar args σ x (fun p hp he => hx (List.mem_map.mpr ⟨p,hp,he.symm⟩))
  have hVal (i : ℕ) : val F canonical qN.WS ρ i=val F canonical qN.WS σ i := by
    unfold val slice
    rw [hReg _ (by decide),(installed_arrays args σ).1]
  obtain ⟨τ,r₁,hSlot,hOut,hFrame,hVars,hArray,hIn,hTape⟩ :=
    rectangularProduct_run F transpose hSlots' hLeft hRight hFit ht hu htu hts hus hz hzW
      ((hVal z).trans hz0) hWords
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
      ((hReg _ (by decide)).trans hRegT) ((hReg _ (by decide)).trans hRegU)
      ((hReg _ (by decide)).trans hRegZ)
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
      (by simp [ρ,args,install,gRows,dL,gCols,rectangularLeftBase,rectangularRightBase,gOut])
  refine ⟨τ,r₀.seq r₁,hSlot,?_,?_,?_,?_,hIn,hTape⟩
  · intro i hi j hj
    rw [hOut i hi j hj]
    simp only [hVal]
  · intro i hi h
    exact (hFrame i hi h).trans (hVal i)
  · intro x hx hcore hi hg hh ho'
    exact (hVars x hcore hi hg hh ho').trans (hReg x hx)
  · intro x hx hy
    exact (hArray x hx hy).trans (congrFun (installed_arrays args σ).1 x)

#print axioms rectangularCall_run
end EvenTI.P16Trial