import Mathproof.Meta.P15DecideIMPEGens20261007
import Mathproof.Meta.P15DecideIMPRowKer20261007

set_option autoImplicit false
set_option maxHeartbeats 1700000

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

def crossShuffleLeft : String := "even.trial.shuffle.left"
def crossShuffleRight : String := "even.trial.shuffle.right"
def crossShuffleSource : String := "even.trial.shuffle.source"
def crossShuffleOne : String := "even.trial.shuffle.one"

private def residue (x d : Expr) : Expr := x.sub ((x.div d).mul d)

private def address : Expr :=
  let L : Expr := .var crossShuffleLeft
  let R : Expr := .var crossShuffleRight
  let i : Expr := .var gU
  let j : Expr := .var gV
  let row := ((i.div R).mul L).add (j.div R)
  let col := ((residue i R).mul R).add (residue j R)
  (Expr.var crossShuffleSource).add ((row.mul (R.mul R)).add col)

def crossShuffleIndex (b l r i j : ℕ) : ℕ :=
  b+((i/r*l+j/r)*(r*r)+(i%r*r+j%r))

private theorem residue_eval {B x d : ℕ} {σ : Env} {e f : Expr}
    (he : e.evalB B σ=some x) (hf : f.evalB B σ=some d) (hB : x < B) :
    (residue e f).evalB B σ=some (x%d) := by
  have hd := ev_div he hf ((Nat.div_le_self _ _).trans_lt hB)
  have hm := ev_mul hd hf ((Nat.div_mul_le_self _ _).trans_lt hB)
  have h := ev_sub he hm (show x-x/d*d < B by omega)
  rw [hmdg] at h
  exact h

private theorem index_lt_bound {b l r i j : ℕ} (hr : 0 < r)
    (hi : i < l*r) (hj : j < l*r) :
    crossShuffleIndex b l r i j < b+(l*l)*(r*r) := by
  have hi' : i/r < l := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm l r] using hi)
  have hj' : j/r < l := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm l r] using hj)
  have hRow : i/r*l+j/r < l*l := by
    simpa only [Nat.zero_add] using out_lt (o0 := 0) hi' hj'
  have hCol : i%r*r+j%r < r*r := by
    simpa only [Nat.zero_add] using out_lt (o0 := 0) (Nat.mod_lt i hr) (Nat.mod_lt j hr)
  exact out_lt hRow hCol

variable {K : Type} [Field K] [Fintype K]

noncomputable def crossShuffle (F : FieldPresentation K) : Com :=
  gridProg (fieldMacros F) (.var crossShuffleOne) address

noncomputable def crossShuffleCost (F : FieldPresentation K) (l r : ℕ) : ℕ :=
  gridCost (fieldMacros F) (.var crossShuffleOne) address 1 (l*r) (l*r)

private def shuffleKeep : List String :=
  [dL,dT,dU,dZ,gRows,gCols,gOut,crossShuffleLeft,crossShuffleRight,crossShuffleSource,crossShuffleOne]

/-- Pair the two tensor modes in the contraction so the next matrix
square acts on the actual mixed coordinate product. -/
theorem crossShuffle_run (F : FieldPresentation K) {B Sn l r b o z t u one : ℕ} {σ : Env}
    (hl : 0 < l) (hr : 0 < r) (hDim : l*r+1 < B)
    (hBefore : b+(l*l)*(r*r) ≤ o) (hFit : o+(l*r)*(l*r) ≤ Sn)
    (ht : t < Sn) (hu : u < Sn) (htu : t ≠ u)
    (htO : o+(l*r)*(l*r) ≤ t ∨ t < b) (huO : o+(l*r)*(l*r) ≤ u ∨ u < b)
    (hz : z < Sn) (hzW : ¬ Written o (l*r) (l*r) t u z)
    (hOne : one < Sn) (hOneW : ¬ Written o (l*r) (l*r) t u one)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hZval : val F canonical qN.WS σ z=0) (hOval : val F canonical qN.WS σ one=1)
    (hReg1 : σ.vars dL=1) (hRegT : σ.vars dT=t) (hRegU : σ.vars dU=u)
    (hRegZ : σ.vars dZ=z) (hRegRows : σ.vars gRows=l*r) (hRegCols : σ.vars gCols=l*r)
    (hRegOut : σ.vars gOut=o)
    (hRegL : σ.vars crossShuffleLeft=l) (hRegR : σ.vars crossShuffleRight=r)
    (hRegB : σ.vars crossShuffleSource=b) (hRegOne : σ.vars crossShuffleOne=one) :
    ∃ τ, Run B (crossShuffle F) σ τ (crossShuffleCost F l r) ∧ Slots F canonical qN.WS Sn B τ ∧
      (∀ i < l*r, ∀ j < l*r, val F canonical qN.WS τ (o+(i*(l*r)+j)) =
        val F canonical qN.WS σ (crossShuffleIndex b l r i j)) ∧
      (∀ a < Sn, ¬ Written o (l*r) (l*r) t u a → val F canonical qN.WS τ a=val F canonical qN.WS σ a) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x=σ.vars x) ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  have hS := hSlots.slots_word
  have hLB := Nat.le_mul_of_pos_right l hr
  have hRB := Nat.le_mul_of_pos_left r hl
  have hr2 : 0 < r*r := Nat.mul_pos hr hr
  have hSquare : r*r ≤ (l*l)*(r*r) := Nat.le_mul_of_pos_left _ (Nat.mul_pos hl hl)
  let fa := fun (_ _ _ : ℕ) => one
  let fb := fun (i j _ : ℕ) => crossShuffleIndex b l r i j
  obtain ⟨τ,hRun,hSlot,hOut,hFrame,hVars,_,hIn,hTape⟩ :=
    grid_run (fieldMacros F) shuffleKeep (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (.var crossShuffleOne) address
      (by simp [VarsIn,shuffleKeep]) (by simp [address,residue,VarsIn,shuffleKeep])
      hSlots hReg1 hRegT hRegU hRegZ hRegRows hRegCols hRegOut
      (fa := fa) (fb := fb)
      (by intro σ' hk i hi j hj x hx hri hrj hrx
          exact ev_var ((hk _ (by decide)).trans hRegOne) (show one < B by omega))
      (by
        intro σ' hk i hi j hj x hx hri hrj hrx
        have hiB : i < B := by omega
        have hjB : j < B := by omega
        have eI := ev_var hri hiB
        have eJ := ev_var hrj hjB
        have eL := ev_var ((hk _ (by decide)).trans hRegL) (show l < B by omega)
        have eR := ev_var ((hk _ (by decide)).trans hRegR) (show r < B by omega)
        have eB := ev_var ((hk _ (by decide)).trans hRegB) (show b < B by omega)
        have eQi := ev_div eI eR ((Nat.div_le_self _ _).trans_lt hiB)
        have eQj := ev_div eJ eR ((Nat.div_le_self _ _).trans_lt hjB)
        have eRi := residue_eval eI eR hiB
        have eRj := residue_eval eJ eR hjB
        have hh := index_lt_bound (b := b) hr hi hj
        unfold crossShuffleIndex at hh
        have hMulB : (i/r*l+j/r)*(r*r) < B := by omega
        have hRowB := (Nat.le_mul_of_pos_right (i/r*l+j/r) hr2).trans_lt hMulB
        have hHeadB := (Nat.le_add_right (i/r*l) (j/r)).trans_lt hRowB
        have eRow := ev_add (ev_mul eQi eL hHeadB) eQj hRowB
        have eCol := ev_add (ev_mul eRi eR (show i%r*r < B by omega)) eRj
          (show i%r*r+j%r < B by omega)
        have eRR := ev_mul eR eR (show r*r < B by omega)
        have em := ev_mul eRow eRR (show (i/r*l+j/r)*(r*r) < B by omega)
        exact ev_add eB (ev_add em eCol (by omega))
          (show fb i j x < B by dsimp [fb,crossShuffleIndex]; omega))
      (fun _ _ _ _ _ _ => ⟨hOne,hOneW⟩)
      (by
        intro i hi j hj x hx
        have hh := index_lt_bound (b := b) hr hi hj
        have hLo : b ≤ crossShuffleIndex b l r i j := by unfold crossShuffleIndex; omega
        refine ⟨by dsimp [fb]; omega,?_⟩
        dsimp [fb]
        rintro (⟨_,_⟩ | h | h) <;> omega)
      hFit ht hu hz htu hzW (by omega) (by omega) hZval (by omega)
      hDim hDim (by omega)
  refine ⟨τ,hRun,hSlot,?_,hFrame,hVars,hIn,hTape⟩
  intro i hi j hj
  rw [hOut i hi j hj,Finset.sum_range_one]
  simp [fa,fb,hOval]

#print axioms crossShuffle_run
end EvenTI.P16Trial