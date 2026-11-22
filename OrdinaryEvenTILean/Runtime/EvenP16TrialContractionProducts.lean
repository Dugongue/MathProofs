import EvenP16TrialRectangularCall

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P16Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007

def contractionTensorWidth : String := "even.contraction.width.tensor"
def contractionLeftWidth : String := "even.contraction.width.left"
def contractionRightWidth : String := "even.contraction.width.right"
def contractionTensorBase : String := "even.contraction.tensor"
def contractionLeftBase : String := "even.contraction.left"
def contractionRightBase : String := "even.contraction.right"
def contractionTempBase : String := "even.contraction.temp"
def contractionOutBase : String := "even.contraction.out"

private def front : RectangularWords :=
  ⟨contractionTensorWidth,contractionTensorWidth,contractionRightWidth,
    contractionTensorBase,contractionRightBase,contractionTempBase⟩

private def back : RectangularWords :=
  ⟨contractionLeftWidth,contractionTensorWidth,contractionRightWidth,
    contractionLeftBase,contractionTempBase,contractionOutBase⟩

variable {K : Type} [Field K] [Fintype K]

noncomputable def contractionProducts (F : FieldPresentation K) : Com :=
  .seq (rectangularCall F true front) (rectangularCall F false back)

noncomputable def contractionProductsCost (F : FieldPresentation K) (m l r : ℕ) : ℕ :=
  (13+rectangularCost F true m m r)+(13+rectangularCost F false l m r)

/-- Run both coefficient contractions on live banks. The native cut coordinates
need no permutation before calling the ordinary products. -/
theorem contractionProducts_run (F : FieldPresentation K)
    {B Sn m l r ta la ra tmp o z t u : ℕ} {σ : Env}
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hTemp : tmp+m*r ≤ o) (hOut : o+l*r ≤ Sn)
    (hTensorBefore : ta+m*m ≤ tmp) (hRightBefore : ra+r*m ≤ tmp)
    (hLeftBefore : la+l*m ≤ tmp)
    (hT : t < ta ∧ t < ra ∧ t < la)
    (hU : u < ta ∧ u < ra ∧ u < la)
    (hTU : t ≠ u)
    (hZ : z < tmp ∧ z < o ∧ z ≠ t ∧ z ≠ u)
    (hZero : val F canonical qN.WS σ z=0)
    (hW : m+1 < B ∧ l+1 < B ∧ r+1 < B)
    (hm : σ.vars contractionTensorWidth=m) (hl : σ.vars contractionLeftWidth=l)
    (hr : σ.vars contractionRightWidth=r)
    (hTa : σ.vars contractionTensorBase=ta) (hLa : σ.vars contractionLeftBase=la)
    (hRa : σ.vars contractionRightBase=ra)
    (hTmp : σ.vars contractionTempBase=tmp) (hO : σ.vars contractionOutBase=o)
    (hRz : σ.vars dZ=z) (hRt : σ.vars dT=t) (hRu : σ.vars dU=u) :
    ∃ τ, Run B (contractionProducts F) σ τ (contractionProductsCost F m l r) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ i < l, ∀ j < r, val F canonical qN.WS τ (o+(i*r+j)) =
        ∑ x ∈ Finset.range m, val F canonical qN.WS σ (la+(i*m+x)) *
          (∑ y ∈ Finset.range m, val F canonical qN.WS σ (ta+(x*m+y)) *
            val F canonical qN.WS σ (ra+(j*m+y)))) ∧
      (∀ k < Sn, ¬ Written tmp m r t u k → ¬ Written o l r t u k →
        val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      (∀ x, x ∉ rectangularTargets → x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x=σ.vars x) ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  have ht : t < Sn := by omega
  have hu : u < Sn := by omega
  have hz : z < Sn := by omega
  have htf : t < tmp := by omega
  have huf : u < tmp := by omega
  have hzf : ¬ Written tmp m r t u z := by unfold Written; omega
  have hzo : ¬ Written o l r t u z := by unfold Written; omega
  obtain ⟨η,r₁,hS₁,hY,hFrame₁,hVars₁,_,hIn₁,hOut₁⟩ :=
    rectangularCall_run F true front (by decide) hSlots hTensorBefore
      (by simpa using hRightBefore) (by omega) ht hu hTU
      (Or.inr ⟨hT.1,hT.2.1⟩) (Or.inr ⟨hU.1,hU.2.1⟩)
      hz hzf hZero ⟨hW.1,hW.1,hW.2.2⟩ hm hm hr hTa hRa hTmp hRt hRu hRz
  have hKeep (x : String) (h₁ : x ∉ rectangularTargets) (h₂ : x ∉ regNames canonical)
      (h₃ : x ≠ dI) (h₄ : x ≠ gU) (h₅ : x ≠ gV) (h₆ : x ≠ dO) :
      η.vars x=σ.vars x := hVars₁ x h₁ h₂ h₃ h₄ h₅ h₆
  have hZero' := (hFrame₁ z hz hzf).trans hZero
  obtain ⟨τ,r₂,hS₂,hX,hFrame₂,hVars₂,_,hIn₂,hOut₂⟩ :=
    rectangularCall_run F false back (by decide) hS₁ (by omega)
      (by simpa using hTemp) hOut ht hu hTU
      (Or.inr ⟨hT.2.2,htf⟩) (Or.inr ⟨hU.2.2,huf⟩)
      hz hzo hZero' ⟨hW.2.1,hW.1,hW.2.2⟩
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hLa)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTmp)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hO)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRt)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRu)
      ((hKeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRz)
  refine ⟨τ,r₁.seq r₂,hS₂,?_,?_,?_,hIn₂.trans hIn₁,hOut₂.trans hOut₁⟩
  · intro i hi j hj
    rw [hX i hi j hj]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    have ha : la+(i*m+x) < tmp := (out_lt hi hx').trans_le hLeftBefore
    have hLo : la ≤ la+(i*m+x) := Nat.le_add_right _ _
    have hKeep := hFrame₁ (la+(i*m+x)) (by omega) (by unfold Written; omega)
    simp only [rightIndex,Bool.false_eq_true,if_false]
    rw [hKeep,hY x hx' j hj] <;> simp [rightIndex]
  · intro k hk h₁ h₂
    exact (hFrame₂ k hk h₂).trans (hFrame₁ k hk h₁)
  · intro x hx hCore hi hg hh hO'
    exact (hVars₂ x hx hCore hi hg hh hO').trans (hKeep x hx hCore hi hg hh hO')

#print axioms contractionProducts_run
end EvenTI.P16Trial