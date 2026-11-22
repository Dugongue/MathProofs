import EvenP12CompareRecoverBezout
import EvenP12CompareRecoverUnary
import Mathproof.Meta.P15DecideIMPRowKer20261007

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.P15GSSGcd20261007 (ga gb)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def unaryTarget : String := "even_recover_unary_target"
def unaryPeriod : String := "even_recover_unary_period"
def unaryRepresentative : String := "even_recover_unary_rep"
def unaryOK : String := "even_recover_unary_ok"

private def remainderExpr (x y : Expr) : Expr := .sub x (.mul (.div x y) y)

private theorem remainderExpr_eval {W x y : ℕ} {e f : Expr} {σ : Env}
    (he : e.evalB W σ = some x) (hf : f.evalB W σ = some y) (hx : x < W) :
    (remainderExpr e f).evalB W σ = some (x%y) := by
  have hq := (Nat.div_le_self x y).trans_lt hx
  have hprod := (Nat.div_mul_le_self x y).trans_lt hx
  have hrem := (Nat.mod_le x y).trans_lt hx
  unfold remainderExpr
  exact (ev_sub he (ev_mul (ev_div he hf hq) hf hprod) (by rwa [hmdg])).trans
    (congrArg some (hmdg x y))

private def periodCode : Com := .assign unaryPeriod (.div (.var gb) (.var bezoutGcd))

private def divisibilityTest : Cond :=
  .eq (remainderExpr (.var unaryTarget) (.var bezoutGcd)) (.lit 0)

private def residueProduct : Expr := .mul (.div (.var unaryTarget) (.var bezoutGcd))
  (.var bezoutCoefficient)

private def commitUnary : Com :=
  .seq (.assign unaryRepresentative (remainderExpr residueProduct (.var unaryPeriod)))
    (.assign unaryOK (.lit 1))

def normalizeTail : Com :=
  .seq periodCode (.ite divisibilityTest commitUnary (.assign unaryOK (.lit 0)))

private theorem normalizeTail_run {W b d g u : ℕ} {σ : Env}
    (hh : 1 < W) (hB : b < W) (hD : d < W) (hG : g < W) (hU : u < W)
    (hprod : b*u < W) (hb : σ.vars unaryTarget = b) (hd : σ.vars gb = d)
    (hg : σ.vars bezoutGcd = g) (hu : σ.vars bezoutCoefficient = u) :
    ∃ τ, Run W normalizeTail σ τ 140 ∧ τ.vars unaryPeriod = d/g ∧
      (g ∣ b → τ.vars unaryOK = 1 ∧ τ.vars unaryRepresentative = (b/g*u)%(d/g)) ∧
      (¬g ∣ b → τ.vars unaryOK = 0) := by
  let ρ := σ.setVar unaryPeriod (d/g)
  have ediv : (Expr.div (.var gb) (.var bezoutGcd)).evalB W σ = some (d/g) :=
    ev_div (ev_var hd hD) (ev_var hg hG) ((Nat.div_le_self _ _).trans_lt hD)
  have r₀ : Run W periodCode σ ρ 4 := Run.assign ediv
  have hb' : ρ.vars unaryTarget = b := by
    simpa [ρ,vars_setVar,show unaryTarget ≠ unaryPeriod by decide] using hb
  have hg' : ρ.vars bezoutGcd = g := by
    simpa [ρ,vars_setVar,show bezoutGcd ≠ unaryPeriod by decide] using hg
  have hu' : ρ.vars bezoutCoefficient = u := by
    simpa [ρ,vars_setVar,show bezoutCoefficient ≠ unaryPeriod by decide] using hu
  have hperiod : ρ.vars unaryPeriod = d/g := by simp [ρ]
  have ere : (remainderExpr (.var unaryTarget) (.var bezoutGcd)).evalB W ρ = some (b%g) :=
    remainderExpr_eval (ev_var hb' hB) (ev_var hg' hG) hB
  have et : divisibilityTest.evalB W ρ = some (decide (b%g=0)) :=
    evalB_condEq ere (evalB_lit (show 0 < W by omega))
  by_cases h : g ∣ b
  · have et' : divisibilityTest.evalB W ρ = some true := by
      simpa only [Nat.dvd_iff_mod_eq_zero.mp h,decide_true] using et
    have hq := Nat.div_le_self b g
    have hp := (Nat.mul_le_mul_right u hq).trans_lt hprod
    have eprod : residueProduct.evalB W ρ = some (b/g*u) :=
      ev_mul (ev_div (ev_var hb' hB) (ev_var hg' hG) (hq.trans_lt hB))
        (ev_var hu' hU) hp
    have er : (remainderExpr residueProduct (.var unaryPeriod)).evalB W ρ =
        some ((b/g*u)%(d/g)) :=
      remainderExpr_eval eprod (ev_var hperiod ((Nat.div_le_self _ _).trans_lt hD)) hp
    let ρ₁ := ρ.setVar unaryRepresentative ((b/g*u)%(d/g))
    let τ := ρ₁.setVar unaryOK 1
    have r₁ : Run W
        (.assign unaryRepresentative (remainderExpr residueProduct (.var unaryPeriod))) ρ ρ₁
        (1+(remainderExpr residueProduct (.var unaryPeriod)).size) := Run.assign er
    have r₂ : Run W (.assign unaryOK (.lit 1)) ρ₁ τ 2 := Run.assign (evalB_lit hh)
    refine ⟨τ,(r₀.seq (Run.ite_true (d := .assign unaryOK (.lit 0)) et' (r₁.seq r₂))).mono
      (by decide),?_,?_,fun h' => False.elim (h' h)⟩
    · simp [τ,ρ₁,vars_setVar,show unaryPeriod ≠ unaryOK by decide,
        show unaryPeriod ≠ unaryRepresentative by decide,hperiod]
    · intro _
      exact ⟨by simp [τ],by simp [τ,ρ₁,vars_setVar,show unaryRepresentative ≠ unaryOK by decide]⟩
  · have hmod : b%g ≠ 0 := fun he => h (Nat.dvd_iff_mod_eq_zero.mpr he)
    have et' : divisibilityTest.evalB W ρ = some false := by
      simpa only [hmod,decide_false] using et
    let τ := ρ.setVar unaryOK 0
    have r₁ : Run W (.assign unaryOK (.lit 0)) ρ τ 2 := Run.assign (evalB_lit (by omega))
    refine ⟨τ,(r₀.seq (Run.ite_false (c := commitUnary) et' r₁)).mono (by decide),?_ ,
      fun h' => False.elim (h h'),fun _ => by simp [τ]⟩
    simp [τ,vars_setVar,show unaryPeriod ≠ unaryOK by decide,hperiod]

private theorem normalize_of_bezout (a b d u : ℕ) (hd : 0 < d)
    (hu : (a : ZMod d)*(u : ZMod d) = (Nat.gcd a d : ZMod d))
    (h : Nat.gcd a d ∣ b) (x : ℕ) :
    a*x ≡ b [MOD d] ↔ x ≡ ((b/Nat.gcd a d*u)%(d/Nat.gcd a d)) [MOD d/Nat.gcd a d] := by
  let g := Nat.gcd a d
  let p := d/g
  let r := b/g*u
  have hr : a*r ≡ b [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    dsimp [r,g]
    -- Put the quotient outside the Bézout multiplication.
    simp only [Nat.cast_mul]
    rw [← mul_assoc, mul_comm (a : ZMod d), mul_assoc, hu,
      ← Nat.cast_mul, Nat.div_mul_cancel h]
  constructor
  · intro hx
    have hx' : x ≡ r [MOD p] := by
      simpa [p,g,Nat.gcd_comm] using (hx.trans hr.symm).cancel_left_div_gcd hd
    exact hx'.trans (Nat.mod_modEq _ _).symm
  · intro hx
    have hx' := hx.trans (Nat.mod_modEq r p)
    have hscaled := (hx'.mul_left' g).mul_left (a/g)
    have hp : g*p = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have ha : a/g*g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hh : a*x ≡ a*r [MOD d] := by
      simpa only [show g*(d/Nat.gcd a d) = d from hp, ← Nat.mul_assoc,ha] using hscaled
    exact hh.trans hr

/-- Fully physical normalization of a unary linear congruence. Adding the
positive modulus allows the same xgcd program to handle a zero coefficient. -/
def paidNormalize : Com :=
  .seq (.assign ga (.add (.var ga) (.var gb)))
    (.seq paidBezout normalizeTail)

theorem paidNormalize_run {W a b d : ℕ} {σ : Env}
    (hd₀ : 0 < d) (hWord : a+d+2 < W) (hbw : b < W) (hprod : b*d < W)
    (ha : σ.vars ga = a) (hb : σ.vars unaryTarget = b) (hd : σ.vars gb = d) :
    ∃ τ, Run W paidNormalize σ τ (256*Nat.size d+360) ∧
      τ.vars unaryPeriod = d / Nat.gcd a d ∧
      (Nat.gcd a d ∣ b ↔ τ.vars unaryOK = 1) ∧
      (τ.vars unaryOK = 1 → τ.vars unaryRepresentative < τ.vars unaryPeriod ∧
        ∀ x, a*x ≡ b [MOD d] ↔ x ≡ τ.vars unaryRepresentative [MOD τ.vars unaryPeriod]) := by
  let ρ := σ.setVar ga (a+d)
  have eAdd : (Expr.add (.var ga) (.var gb)).evalB W σ = some (a+d) :=
    ev_add (ev_var ha (by omega)) (ev_var hd (by omega)) (by omega)
  have r₀ : Run W (.assign ga (.add (.var ga) (.var gb))) σ ρ 4 := Run.assign eAdd
  have h₁ : ρ.vars ga = a+d := by simp [ρ]
  have h₂ : ρ.vars gb = d := by simpa [ρ,vars_setVar,show gb ≠ ga by decide] using hd
  have hmw : max (a+d) d+2 < W := by rw [max_eq_left (by omega)]; exact hWord
  obtain ⟨η,r₁,hg,hu,hBez,hFrame⟩ := paidBezout_run h₁ h₂ (by omega) hd₀ hmw
  have hg' : η.vars bezoutGcd = Nat.gcd a d := by simpa only [Nat.gcd_add_self_left] using hg
  let u := η.vars bezoutCoefficient
  have hBez' : (a : ZMod d)*(u : ZMod d) = (Nat.gcd a d : ZMod d) := by
    simpa only [u,Nat.cast_add,ZMod.natCast_self,add_zero,Nat.gcd_add_self_left] using hBez
  have hU : u < W := hu.trans_lt (by omega)
  have hG : Nat.gcd a d < W := (Nat.gcd_le_right _ hd₀).trans_lt (by omega)
  have hP : b*u < W := (Nat.mul_le_mul_left _ hu).trans_lt hprod
  have hβ : η.vars unaryTarget = b := by
    rw [hFrame.vars _ (by decide)]
    simpa [ρ,vars_setVar,show unaryTarget ≠ ga by decide] using hb
  have hδ : η.vars gb = d := (hFrame.vars _ (by decide)).trans h₂
  obtain ⟨τ,r₂,ht,hs₁,hs₀⟩ := normalizeTail_run (by omega) hbw (by omega) hG hU hP hβ hδ hg' rfl
  have hYes : (Nat.gcd a d ∣ b ↔ τ.vars unaryOK = 1) := by
    refine ⟨fun h => (hs₁ h).1,?_⟩
    intro h
    by_contra hh
    exact Nat.zero_ne_one ((hs₀ hh).symm.trans h)
  refine ⟨τ,(r₀.seq (r₁.seq r₂)).mono (by omega),ht,hYes,?_⟩
  intro h
  have hGcd := hYes.mpr h
  have hr := (hs₁ hGcd).2
  rw [hr,ht]
  exact ⟨Nat.mod_lt _ (Nat.div_gcd_pos_of_pos_right _ hd₀),normalize_of_bezout a b d u hd₀ hBez' hGcd⟩

/-- Generalized CRT is one call to the same unary solver, followed by
an affine lift of its answer. -/
theorem merge_as_unary (r period s d x : ℕ) (hr : r < period) (hd : 0 < d) :
    (x ≡ r [MOD period] ∧ x ≡ s [MOD d]) ↔
      ∃ k, x = r+period*k ∧ period*k ≡ s+d-r%d [MOD d] := by
  have hs : (s+d-r%d)+r ≡ s [MOD d] := by
    have hrem : r%d ≤ s+d := ((Nat.mod_lt r hd).le).trans (Nat.le_add_left d s)
    calc
      (s+d-r%d)+r ≡ (s+d-r%d)+r%d [MOD d] :=
        (Nat.mod_modEq r d).symm.add_left _
      _ = s+d := Nat.sub_add_cancel hrem
      _ ≡ s [MOD d] := by simp
  have hrel (k : ℕ) : r+period*k ≡ s [MOD d] ↔ period*k ≡ s+d-r%d [MOD d] := by
    constructor
    · intro h
      have h' : period*k+r ≡ s [MOD d] := by simpa only [Nat.add_comm] using h
      exact Nat.ModEq.add_right_cancel' r (h'.trans hs.symm)
    · intro h
      simpa only [Nat.add_comm r (period*k)] using (h.add_right r).trans hs
  constructor
  · rintro ⟨hp,hdx⟩
    have hp' : x%period=r := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using hp
    have hi : x=r+period*(x/period) := by
      rw [← hp',Nat.mod_add_div]
    exact ⟨x/period,hi,(hrel _).mp (hi ▸ hdx)⟩
  · rintro ⟨k,rfl,hk⟩
    refine ⟨?_,(hrel _).mpr hk⟩
    simp [Nat.add_modEq_left_iff,Nat.dvd_mul_right]

/-- The least successful unary residue lifts to the merged CRT representative. -/
theorem lift_merged_class (r period s d k₀ l x : ℕ)
    (hr : r < period) (hd : 0 < d) (hk : k₀ < l)
    (hn : ∀ k, period*k ≡ s+d-r%d [MOD d] ↔ k ≡ k₀ [MOD l]) :
    r+period*k₀ < period*l ∧
      ((x ≡ r [MOD period] ∧ x ≡ s [MOD d]) ↔
        x ≡ r+period*k₀ [MOD period*l]) := by
  have hp : 0 < period := by omega
  refine ⟨?_,?_⟩
  · calc
      r+period*k₀ < period+period*k₀ := Nat.add_lt_add_right hr _
      _ = period*(k₀+1) := by ring
      _ ≤ period*l := Nat.mul_le_mul_left _ hk
  · rw [merge_as_unary r period s d x hr hd]
    constructor
    · rintro ⟨k,rfl,hk'⟩
      exact (((hn k).mp hk').mul_left' period).add_left r
    · intro hx
      have hx₀ : x ≡ r+period*k₀ [MOD period] :=
        hx.of_dvd (Nat.dvd_mul_right _ _)
      have hr₀ : r+period*k₀ ≡ r [MOD period] := by
        simp [Nat.add_modEq_left_iff,Nat.dvd_mul_right]
      have he : x%period = r := by
        simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using hx₀.trans hr₀
      have hval : x = r+period*(x/period) := by
        rw [← he,Nat.mod_add_div]
      refine ⟨x/period,hval,(hn _).mpr ?_⟩
      apply Nat.ModEq.mul_left_cancel' hp.ne'
      apply Nat.ModEq.add_left_cancel' r
      simpa only [← hval] using hx
#print axioms paidNormalize_run
#print axioms merge_as_unary
#print axioms lift_merged_class

end EvenTI.P12Compare
