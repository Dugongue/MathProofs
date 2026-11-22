import Mathproof.Meta.P15GSSXgcdRun20261007
import Mathproof.Meta.P15DecideIMPEGens20261007

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.P15GSSGcd20261007 (ga gb)
open Mathproof.P15GSSXgcdRun20261007 (xgcdIMP xgcdIMP_run)
open Mathproof.P15GSSXgcdSmith20261007 (reduced_kill)
open Mathproof.P15GSSXgcdStep20261007 (apR zpR readState stateBounds)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open PNat.XgcdType

def bezoutGcd : String := "even_recover_unary_gcd"
def bezoutCoefficient : String := "even_recover_unary_coefficient"

def saveBezout : Com :=
  .seq (.assign bezoutGcd (.add (.var apR) (.lit 1)))
    (.assign bezoutCoefficient (.add (.var zpR) (.lit 1)))

def paidBezout : Com := .seq xgcdIMP saveBezout

/-- Run the installed extended-gcd machine, extracting a nonnegative
coefficient for the input multiplier modulo the positive input modulus. -/
theorem paidBezout_run {W a d : ℕ} {σ : Env}
    (hA : σ.vars ga = a) (hD : σ.vars gb = d) (ha : 0 < a) (hd : 0 < d)
    (hWord : max a d + 2 < W) :
    ∃ τ, Run W paidBezout σ τ (256 * Nat.size d + 208) ∧
      τ.vars bezoutGcd = Nat.gcd a d ∧ τ.vars bezoutCoefficient ≤ d ∧
      (a : ZMod d) * (τ.vars bezoutCoefficient : ZMod d) = (Nat.gcd a d : ZMod d) ∧
      Frame paidBezout σ τ := by
  obtain ⟨ρ,hr,hs,hred,hv,hg,_⟩ := xgcdIMP_run (W := W) (σ := σ)
    (by simpa only [hA]) (by simpa only [hD]) (by simpa only [hA,hD])
  rw [hA,hD] at hv hg
  rw [hD] at hr
  have B := stateBounds (readState ρ)
  rw [hv] at B
  have hWₐ : a+2 < W := (Nat.add_le_add_right (le_max_left _ _) _).trans_lt hWord
  have hW_d : d+2 < W := (Nat.add_le_add_right (le_max_right _ _) _).trans_lt hWord
  have h1W : 1 < W := by omega
  let u := (readState ρ).zp+1
  let g := (readState ρ).ap+1
  have hu : u ≤ d := B.2.2.2.1
  have hga : g ≤ a := B.2.2.2.2.1
  have hge : g = Nat.gcd a d := hg
  let ρ₁ := ρ.setVar bezoutGcd g
  let τ := ρ₁.setVar bezoutCoefficient u
  have e₁ : (Expr.add (.var apR) (.lit 1)).evalB W ρ = some g := by
    have hval : ρ.vars apR = (readState ρ).ap := rfl
    exact ev_add (ev_var hval (by omega)) (evalB_lit h1W)
      (show g < W by omega)
  have e₂ : (Expr.add (.var zpR) (.lit 1)).evalB W ρ₁ = some u := by
    have hval : ρ₁.vars zpR = (readState ρ).zp := by
      simp [ρ₁,vars_setVar,show zpR ≠ bezoutGcd by decide,readState]
    exact ev_add (ev_var hval (by omega)) (evalB_lit h1W)
      (show u < W by omega)
  have r₁ : Run W (.assign bezoutGcd (.add (.var apR) (.lit 1))) ρ ρ₁ 4 := Run.assign e₁
  have r₂ : Run W (.assign bezoutCoefficient (.add (.var zpR) (.lit 1))) ρ₁ τ 4 := Run.assign e₂
  have rr : Run W paidBezout σ τ (256 * Nat.size d+208) :=
    (hr.seq (r₁.seq r₂)).mono (by omega)
  have eg : τ.vars bezoutGcd = g := by
    simp [τ,ρ₁,vars_setVar,show bezoutGcd ≠ bezoutCoefficient by decide]
  have eu : τ.vars bezoutCoefficient = u := by simp [τ]
  use τ,rr,eg.trans hge,eu ▸ hu
  constructor
  · have hK := (reduced_kill (M := d) (readState ρ) hs hred).2.2
    simpa only [hv,ZMod.natCast_self,mul_zero,zero_mul,add_zero,hg,eu,u,Nat.cast_add,Nat.cast_one,mul_comm]
      using hK
  · exact Frame.of_run rr

#print axioms paidBezout_run

end EvenTI.P12Compare
