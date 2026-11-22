import EvenP11SpectralCost
import Mathproof.Meta.Problem18IMPNaturalPower20261001

set_option autoImplicit false

namespace EvenTI.LiveSpectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPNaturalPower20261001

def budgetNames : Names := ⟨"even.budget.base","even.budget.exp","even.budget.power","even.budget.index"⟩
def budgetCap : String := "even.budget.cap"
def budgetAccept : String := "even.budget.accept"

def budgetCompare : Com :=
  .seq (naturalPowerRoutine budgetNames)
    (.ite (.lt (.var budgetCap) (.var budgetNames.out))
      (.assign budgetAccept (.lit 0)) (.assign budgetAccept (.lit 1)))

def budgetWordWidth (q L : Nat) : Nat := (q+2)*(4*L^2+1)+1

theorem budgetWordWidth_fit {q e cap L : Nat} (he : e ≤ 4*L^2) (hc : cap ≤ L) :
    e < 2^(budgetWordWidth q L) ∧ cap < 2^(budgetWordWidth q L) ∧
      (q+1)^(e+1) < 2^(budgetWordWidth q L) := by
  have hqe : (q+1)^(e+1) ≤ (2^(q+2))^(e+1) :=
    Nat.pow_le_pow_left (show q+1 ≤ 2^(q+2) by have h := Nat.lt_two_pow_self (n := q+2); omega) _
  have hp : (q+2)*(e+1) < budgetWordWidth q L := by
    calc
      _ ≤ (q+2)*(4*L^2+1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right he 1)
      _ < _ := Nat.lt_succ_self _
  have hl : 1 ≤ q+2 := by omega
  have hscale : 4*L^2+1 ≤ (q+2)*(4*L^2+1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (4*L^2+1) hl
  have hL : L ≤ 4*L^2+1 := by
    have h := Nat.le_mul_self L
    rw [pow_two]
    omega
  have hbits := Nat.lt_two_pow_self (n := budgetWordWidth q L)
  have hwle : 4*L^2+1 ≤ budgetWordWidth q L := hscale.trans (Nat.le_succ _)
  refine ⟨(show e ≤ budgetWordWidth q L by omega).trans_lt hbits,
    (show cap ≤ budgetWordWidth q L by omega).trans_lt hbits, ?_⟩
  rw [← pow_mul] at hqe
  exact hqe.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hp)

/-- The budget comparison after an exponent has been computed. Its physical
execution has polynomial fuel and word width in the dense input length. -/
theorem budgetCompare_run {B q e cap L : Nat} {σ : Env}
    (hq : σ.vars budgetNames.base = q) (he : σ.vars budgetNames.exponent = e)
    (hc : σ.vars budgetCap = cap) (hE : e ≤ 4*L^2) (hC : cap ≤ L)
    (hB : 2^(budgetWordWidth q L) ≤ B) :
    ∃ τ, Run B budgetCompare σ τ (20*(4*L^2+1)+6) ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      τ.arrs = σ.arrs ∧
      τ.vars budgetAccept = if q^e ≤ cap then 1 else 0 := by
  obtain ⟨heB,hcB,hpB⟩ := budgetWordWidth_fit hE hC (q := q)
  have hOneB : 1 < B := by
    have h := Nat.lt_two_pow_self (n := budgetWordWidth q L)
    have hw : 0 < budgetWordWidth q L := by unfold budgetWordWidth; omega
    omega
  have hpow := naturalPower_run_bounded budgetNames σ (by decide) (by decide) (by decide)
    (by rw [he]; exact heB.trans_le hB) (by rw [hq,he]; exact hpB.trans_le hB)
  rw [he] at hpow
  let μ := state budgetNames σ e
  have hc' : σ.vars "even.budget.cap" = cap := hc
  have hq' : σ.vars "even.budget.base" = q := hq
  have hμc : μ.vars budgetCap = cap := by simp [μ,state,budgetNames,budgetCap,hc']
  have hμp : μ.vars budgetNames.out = q^e := by simp [μ,state,budgetNames,hq']
  have hp : q^e < B := by
    have hp' : q^e ≤ (q+1)^(e+1) := (Nat.pow_le_pow_left (by omega) e).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    exact hp'.trans_lt (hpB.trans_le hB)
  have hd : (Cond.lt (.var budgetCap) (.var budgetNames.out)).evalB B μ = some (decide (cap < q^e)) := by
    apply evalB_condLt
    · simpa only [hμc] using evalB_var (σ := μ) (x := budgetCap) (by rw [hμc]; exact hcB.trans_le hB)
    · simpa only [hμp] using evalB_var (σ := μ) (x := budgetNames.out) (by rw [hμp]; exact hp)
  by_cases h : cap < q^e
  · refine ⟨μ.setVar budgetAccept 0, (hpow.seq (Run.ite_true (by simpa [h] using hd)
      (Run.assign (evalB_lit (show 0 < B by omega))))).mono ?_, rfl, rfl, rfl, ?_⟩
    · simp only [Cond.size,Expr.size]; omega
    · simp [show ¬q^e ≤ cap by omega]
  · refine ⟨μ.setVar budgetAccept 1, (hpow.seq (Run.ite_false (by simpa [h] using hd)
      (Run.assign (evalB_lit hOneB)))).mono ?_, rfl, rfl, rfl, ?_⟩
    · simp only [Cond.size,Expr.size]; omega
    · simp [show q^e ≤ cap by omega]

#print axioms budgetCompare_run
end EvenTI.LiveSpectral
