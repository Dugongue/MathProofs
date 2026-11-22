import Mathproof.Meta.P15DecideIMPEGens20261007
import Mathproof.Meta.P15DecideIMPRowKer20261007

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P16Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def retainedProjectionWidth : String := "even.trial.projection.width"
def retainedProjectionStride : String := "even.trial.projection.stride"
def retainedProjectionForm : String := "even.trial.projection.form"

private def remainder (x n : Expr) : Expr := x.sub ((x.div n).mul n)

private def equalityIndicator (n a b : Expr) : Expr :=
  (((n.add a).sub b).div n).mul (((n.add b).sub a).div n)

private def maskAddress : Expr :=
  (Expr.var dZ).add
    (equalityIndicator (.var retainedProjectionWidth) ((.var gU : Expr).div (.var retainedProjectionWidth))
        ((.var gV : Expr).div (.var retainedProjectionStride)))

private def coefficientAddress : Expr :=
  (Expr.var retainedProjectionForm).add
    (((remainder (.var gV) (.var retainedProjectionStride)).mul (.var retainedProjectionWidth)).add
      (remainder (.var gU) (.var retainedProjectionWidth)))

private theorem quotientIndicator {n a b : ℕ} (ha : a < n) (hb : b < n) :
    ((n+a-b)/n)*((n+b-a)/n)=if a=b then 1 else 0 := by
  have hn : 0 < n := by omega
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [if_neg (ne_of_lt hab),Nat.div_eq_of_lt (show n+a-b < n by omega),zero_mul]
  · subst b
    rw [if_pos rfl, Nat.add_sub_cancel, Nat.div_self hn,one_mul]
  · rw [if_neg (ne_of_gt hab),Nat.div_eq_of_lt (show n+b-a < n by omega),mul_zero]

private theorem remainder_eval {B a n : ℕ} {σ : Env} {x y : Expr}
    (hx : x.evalB B σ = some a) (hy : y.evalB B σ = some n)
    (ha : a < B) :
    (remainder x y).evalB B σ = some (a%n) := by
  have hq : a/n < B := (Nat.div_le_self _ _).trans_lt ha
  have hp : a/n*n < B := (Nat.div_mul_le_self _ _).trans_lt ha
  have h := ev_sub hx (ev_mul (ev_div hx hy hq) hy hp)
    (show a-a/n*n < B by omega)
  rw [hmdg] at h
  simpa only [remainder,Nat.mod_eq_sub_div_mul,Nat.mul_comm] using h

private theorem equality_eval {B n a b : ℕ} {σ : Env} {e x y : Expr}
    (hn : e.evalB B σ = some n) (ha : x.evalB B σ = some a) (hb : y.evalB B σ = some b)
    (hA : a < n) (hB : b < n) (hWide : 2*n < B) :
    (equalityIndicator e x y).evalB B σ = some (if a=b then 1 else 0) := by
  have hs := ev_sub (ev_add hn ha (by omega)) hb (by omega)
  have ht := ev_sub (ev_add hn hb (by omega)) ha (by omega)
  have hqa : (n+a-b)/n < B :=
    (Nat.div_le_self _ _).trans_lt (by omega)
  have hqb : (n+b-a)/n < B :=
    (Nat.div_le_self _ _).trans_lt (by omega)
  have hW : ((n+a-b)/n)*((n+b-a)/n) < B := by
    rw [quotientIndicator hA hB]
    split <;> omega
  simpa only [equalityIndicator,quotientIndicator hA hB] using
    ev_mul (ev_div hs hn hqa) (ev_div ht hn hqb) hW

variable {K : Type} [Field K] [Fintype K]

noncomputable def retainedProjectionGrid (F : FieldPresentation K) : Com :=
  gridProg (fieldMacros F) maskAddress coefficientAddress

noncomputable def retainedProjectionGridCost (F : FieldPresentation K) (n s : ℕ) : ℕ :=
  gridCost (fieldMacros F) maskAddress coefficientAddress 1 (n*n) (n*s)

private def gridKeep : List String :=
  [dL,dT,dU,dZ,gRows,gCols,gOut,retainedProjectionWidth,retainedProjectionStride,retainedProjectionForm]

/-- Construct the full coefficient matrix of the retained-mode projection.
Tensor input coordinates use the retained-mode-first layout. The form bank
uses the transposed retained layout produced by the checked gather routine. -/
theorem retainedProjectionGrid_run (F : FieldPresentation K)
    {n s src dst z t u Sn B : ℕ} {σ : Env}
    (hn : 0 < n) (hs : 0 < s) (hWide : 2*n < B)
    (hRows : n*n+1 < B) (hCols : n*s+1 < B)
    (hSrc : src+n*s ≤ dst) (hFit : dst+(n*n)*(n*s) ≤ Sn)
    (ht : t < Sn) (hu : u < Sn) (htu : t ≠ u)
    (htDst : dst+(n*n)*(n*s) ≤ t) (huDst : dst+(n*n)*(n*s) ≤ u)
    (hOneFit : z+1 < Sn)
    (hz : ¬ Written dst (n*n) (n*s) t u z)
    (ho : ¬ Written dst (n*n) (n*s) t u (z+1))
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hZero : val F canonical qN.WS σ z=0) (hOne : val F canonical qN.WS σ (z+1)=1)
    (hRegL : σ.vars dL=1) (hRegT : σ.vars dT=t) (hRegU : σ.vars dU=u)
    (hRegZ : σ.vars dZ=z) (hRegRows : σ.vars gRows=n*n)
    (hRegCols : σ.vars gCols=n*s) (hRegOut : σ.vars gOut=dst)
    (hRegW : σ.vars retainedProjectionWidth=n) (hRegS : σ.vars retainedProjectionStride=s)
    (hRegA : σ.vars retainedProjectionForm=src) :
    ∃ τ, Run B (retainedProjectionGrid F) σ τ (retainedProjectionGridCost F n s) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ i < n*n, ∀ j < n*s,
        val F canonical qN.WS τ (dst+(i*(n*s)+j)) =
          if i/n=j/s then val F canonical qN.WS σ (src+(j%s*n+i%n)) else 0) ∧
      (∀ k < Sn, ¬ Written dst (n*n) (n*s) t u k →
        val F canonical qN.WS τ k = val F canonical qN.WS σ k) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x = σ.vars x) ∧
      (∀ a, a ≠ canonical.mem → a ≠ canonical.scratch → τ.arrs a = σ.arrs a) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let fa := fun (i j _ : ℕ) => z+(if i/n=j/s then 1 else 0)
  let fb := fun (i j _ : ℕ) => src+(j%s*n+i%n)
  have hMem := hSlots.slots_word
  have hSbound : s < B := (Nat.le_mul_of_pos_left s hn).trans_lt (by omega)
  have hAeval : VarsIn (dI :: dO :: gU :: gV :: gridKeep) maskAddress := by
    simp [maskAddress,equalityIndicator,VarsIn,gridKeep]
  have hBeval : VarsIn (dI :: dO :: gU :: gV :: gridKeep) coefficientAddress := by
    simp [coefficientAddress,remainder,VarsIn,gridKeep]
  have hFitt (i j : ℕ) : src+(j%s*n+i%n) < src+n*s :=
    by simpa only [Nat.mul_comm s n] using
      out_lt (o0 := src) (Nat.mod_lt j hs) (Nat.mod_lt i hn)
  have ha (τ : Env) (hkeep : ∀ x ∈ gridKeep, τ.vars x=σ.vars x)
      (i : ℕ) (hi : i < n*n) (j : ℕ) (hj : j < n*s) (k : ℕ) (_hk : k < 1)
      (hri : τ.vars gU=i) (hrj : τ.vars gV=j) (_hrk : τ.vars dI=k) :
      maskAddress.evalB B τ=some (fa i j k) := by
    have ei := ev_var hri (show i < B by omega)
    have ej := ev_var hrj (show j < B by omega)
    have en := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegW) (show n < B by omega)
    have es := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegS) hSbound
    have hi' : i/n < n := Nat.div_lt_of_lt_mul hi
    have hj' : j/s < n := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm n s] using hj)
    have ei' := ev_div ei en (show i/n < B by omega)
    have ej' := ev_div ej es (show j/s < B by omega)
    have ee := equality_eval en ei' ej' hi' hj' hWide
    have ez := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegZ) (show z < B by omega)
    have hh : fa i j k < B := by dsimp [fa]; split <;> omega
    exact ev_add ez ee hh
  have hb (τ : Env) (hkeep : ∀ x ∈ gridKeep, τ.vars x=σ.vars x)
      (i : ℕ) (hi : i < n*n) (j : ℕ) (hj : j < n*s) (k : ℕ) (_hk : k < 1)
      (hri : τ.vars gU=i) (hrj : τ.vars gV=j) (_hrk : τ.vars dI=k) :
      coefficientAddress.evalB B τ=some (fb i j k) := by
    have ei := ev_var hri (show i < B by omega)
    have ej := ev_var hrj (show j < B by omega)
    have en := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegW) (show n < B by omega)
    have es := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegS) hSbound
    have er := remainder_eval ei en (by omega)
    have et := remainder_eval ej es (by omega)
    have ee := hFitt i j
    have ep := ev_mul et en (show j%s*n < B by omega)
    have ef := ev_add ep er (show j%s*n+i%n < B by omega)
    have ew := ev_var ((hkeep _ (by simp [gridKeep])).trans hRegA) (show src < B by omega)
    exact ev_add ew ef (show fb i j k < B by dsimp [fb]; omega)
  obtain ⟨τ, hr,hSlot,hVal,hFrame,hVars,hArray,hIn,hOut⟩ :=
    grid_run (fieldMacros F) gridKeep (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) maskAddress coefficientAddress hAeval hBeval
      hSlots hRegL hRegT hRegU hRegZ hRegRows hRegCols hRegOut ha hb
      (by
        intro i _ j _ k _
        dsimp [fa]
        split
        · exact ⟨hOneFit,ho⟩
        · simpa only [Nat.add_zero] using And.intro (show z < Sn by omega) hz)
      (by
        intro i _ j _ k _
        have hh := hFitt i j
        refine ⟨by dsimp [fb]; omega,?_⟩
        unfold fb
        rintro (⟨h₁,_⟩ | he | he) <;> omega)
      hFit ht hu (by omega) htu hz (by omega) (by omega) hZero
      (by omega) hRows hCols (by omega)
  refine ⟨τ,hr,hSlot,?_,hFrame,hVars,hArray,hIn,hOut⟩
  intro i hi j hj
  rw [hVal i hi j hj,Finset.sum_range_one]
  by_cases h : i/n=j/s
  · simp [fa,fb,h,hOne]
  · simp [fa,fb,h,hZero]

#print axioms retainedProjectionGrid_run
end EvenTI.P16Trial