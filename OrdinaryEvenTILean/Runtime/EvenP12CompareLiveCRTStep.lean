import EvenP12CompareRecoverPhysUnary
import Mathproof.Meta.IMPAutoTactics20261004

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (noRead)
open Mathproof.P15GSSGcd20261007 (ga gb)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def shiftedCoefficient (a period d : ℕ) : ℕ := (a*period)%d

def shiftedTarget (a b r d : ℕ) : ℕ := b%d+d-(a*r)%d

private theorem shifted_row (r period a b d k : ℕ) (hd : 0 < d) :
    a*(r+period*k) ≡ b [MOD d] ↔
      shiftedCoefficient a period d*k ≡ shiftedTarget a b r d [MOD d] := by
  have hrem : (a*r)%d ≤ b%d+d := ((Nat.mod_lt _ hd).le).trans (Nat.le_add_left _ _)
  have hshift : shiftedTarget a b r d+a*r ≡ b [MOD d] := by
    calc
      shiftedTarget a b r d + a*r ≡ shiftedTarget a b r d+(a*r)%d [MOD d] :=
        (Nat.mod_modEq (a*r) d).symm.add_left _
      _ = b%d+d := Nat.sub_add_cancel hrem
      _ ≡ b [MOD d] := by simp [Nat.mod_modEq]
  have hcoeff : a*(r+period*k) ≡ shiftedCoefficient a period d*k+a*r [MOD d] := by
    rw [show a*(r+period*k) = (a*period)*k+a*r by ring]
    exact ((Nat.mod_modEq (a*period) d).symm.mul_right k).add_right _
  constructor
  · intro h
    exact Nat.ModEq.add_right_cancel' (a*r) (hcoeff.symm.trans (h.trans hshift.symm))
  · intro h
    exact hcoeff.trans ((h.add_right _).trans hshift)

/-- Substituting the entire accumulated class turns the next row into one
unary equation in the quotient coordinate. -/
theorem shifted_class (r period a b d x : ℕ) (hr : r < period) (hd : 0 < d) :
    (x ≡ r [MOD period] ∧ a*x ≡ b [MOD d]) ↔
      ∃ k, x = r+period*k ∧ shiftedCoefficient a period d*k ≡ shiftedTarget a b r d [MOD d] := by
  constructor
  · rintro ⟨hp,hx⟩
    have hrem : x%period=r := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using hp
    have hs : x=r+period*(x/period) := by rw [← hrem,Nat.mod_add_div]
    exact ⟨x/period,hs,(shifted_row r period a b d _ hd).mp (hs ▸ hx)⟩
  · rintro ⟨k,rfl,hk⟩
    exact ⟨by simp [Nat.add_modEq_left_iff],(shifted_row r period a b d _ hd).mpr hk⟩

theorem shifted_period_dvd (a period d M : ℕ) (hd : 0 < d)
    (hp : period ∣ M) (hM : d ∣ M) :
    period*(d/Nat.gcd (shiftedCoefficient a period d) d) ∣ M := by
  have hprod : shiftedCoefficient a period d*(M/period) ≡ a*M [MOD d] := by
    unfold shiftedCoefficient
    have h := (Nat.mod_modEq (a*period) d).mul_right (M/period)
    simpa only [Nat.mul_assoc,Nat.mul_div_cancel' hp] using h
  have hzero := hprod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hM a))
  have hzero' : shiftedCoefficient a period d*(M/period) ≡ shiftedCoefficient a period d*0
      [MOD d] := by simpa only [Nat.mul_zero] using hzero
  have hdiv := (Nat.modEq_zero_iff_dvd.mp (hzero'.cancel_left_div_gcd hd))
  rw [Nat.gcd_comm d] at hdiv
  simpa only [Nat.mul_div_cancel' hp] using Nat.mul_dvd_mul_left period hdiv

theorem lift_shifted_class (r period a b d k₀ l x : ℕ)
    (hr : r < period) (hd : 0 < d) (hk : k₀ < l)
    (hn : ∀ k, shiftedCoefficient a period d*k ≡ shiftedTarget a b r d [MOD d] ↔ k ≡ k₀ [MOD l]) :
    r+period*k₀ < period*l ∧
      ((x ≡ r [MOD period] ∧ a*x ≡ b [MOD d]) ↔ x ≡ r+period*k₀ [MOD period*l]) := by
  refine ⟨?_,?_⟩
  · calc
      r+period*k₀ < period+period*k₀ := Nat.add_lt_add_right hr _
      _ = period*(k₀+1) := by ring
      _ ≤ period*l := Nat.mul_le_mul_left _ hk
  · rw [shifted_class r period a b d x hr hd]
    constructor
    · rintro ⟨k,rfl,hk'⟩
      exact (((hn k).mp hk').mul_left' period).add_left r
    · intro hx
      have hper := (hx.of_dvd (Nat.dvd_mul_right period l)).trans
        (show r+period*k₀ ≡ r [MOD period] by simp [Nat.add_modEq_left_iff])
      have hm : x%period = r := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hr] using hper
      have hv : x=r+period*(x/period) := by rw [← hm,Nat.mod_add_div]
      refine ⟨x/period,hv,(hn _).mpr ?_⟩
      apply Nat.ModEq.mul_left_cancel' (show period ≠ 0 by omega)
      apply Nat.ModEq.add_left_cancel' r
      simpa only [← hv] using hx

def crtRepresentative : String := "even_recover_crt_rep"
def crtPeriod : String := "even_recover_crt_period"
def crtActive : String := "even_recover_crt_active"
def rowCoefficient : String := "even_recover_crt_row_a"
def rowTarget : String := "even_recover_crt_row_b"
def rowModulus : String := "even_recover_crt_row_d"

private def remWord (x y : Expr) : Expr := .sub x (.mul (.div x y) y)

private theorem eval_remWord {W x y : ℕ} {e f : Expr} {σ : Env}
    (he : e.evalB W σ = some x) (hf : f.evalB W σ = some y) :
    (remWord e f).evalB W σ = some (x%y) := by
  have hx := Expr.lt_of_evalB he
  have hq := (Nat.div_le_self x y).trans_lt hx
  have hp := (Nat.div_mul_le_self x y).trans_lt hx
  have hm := (Nat.mod_le x y).trans_lt hx
  unfold remWord
  exact (ev_sub he (ev_mul (ev_div he hf hq) hf hp) (by rwa [hmdg])).trans
    (congrArg some (hmdg x y))

private def shiftedCoeffExpr : Expr :=
  remWord (.mul (.var rowCoefficient) (.var crtPeriod)) (.var rowModulus)

private def shiftedTargetExpr : Expr :=
  .sub (.add (remWord (.var rowTarget) (.var rowModulus)) (.var rowModulus))
    (remWord (.mul (.var rowCoefficient) (.var crtRepresentative)) (.var rowModulus))

private def setupCRT : Com :=
  .seq (.assign ga shiftedCoeffExpr)
    (.seq (.assign unaryTarget shiftedTargetExpr)
      (.seq (.assign gb (.var rowModulus)) (.assign unaryOK (.lit 0))))

/-- Successful normalization commits the lifted representative and period.
Failure records an empty intersection. -/
private def commitCRT : Com :=
  .seq (.assign crtRepresentative
    (.add (.var crtRepresentative) (.mul (.var crtPeriod) (.var unaryRepresentative))))
    (.assign crtPeriod (.mul (.var crtPeriod) (.var unaryPeriod)))

private def chooseCRT : Com :=
  .ite (.eq (.var unaryOK) (.lit 1)) commitCRT (.assign crtActive (.lit 0))

def intersectRow : Com := .seq setupCRT (.seq paidNormalize chooseCRT)

def intersectRowCost (M : ℕ) : ℕ := 256*Nat.size M+580

private theorem runRegisterBound {W N : ℕ} {c : Com} {σ τ : Env}
    (hr : Run W c σ τ N) (hn : noRead c) (x : String) (h : σ.vars x < W) :
    τ.vars x < W := by
  obtain ⟨k,hk,hs⟩ := hr
  clear hk
  revert hn h
  induction hs with
  | skip => exact fun _ h => h
  | assign he =>
    intro _ h
    rw [vars_setVar]
    split
    · exact Expr.lt_of_evalB he
    · exact h
  | store _ _ _ => exact fun _ h => h
  | seq _ _ ih ih' => exact fun hn h => ih' hn.2 (ih hn.1 h)
  | ite_true _ _ ih => exact fun hn h => ih hn.1 h
  | ite_false _ _ ih => exact fun hn h => ih hn.2 h
  | while_true _ _ _ ih ih' => exact fun hn h => ih' hn (ih hn h)
  | while_false _ => exact fun _ h => h
  | read _ => exact fun hn _ => False.elim hn
  | write _ => exact fun _ h => h

private theorem setupCRT_run {W M r p a b d : ℕ} {σ : Env}
    (hW : 4*M*M+4*M+10 < W) (hrp : r < p) (hp : p ≤ M)
    (ha : a ≤ M) (hb : b ≤ M) (hd : d ≤ M)
    (hR : σ.vars crtRepresentative = r) (hP : σ.vars crtPeriod = p)
    (hA : σ.vars rowCoefficient = a) (hB : σ.vars rowTarget = b) (hD : σ.vars rowModulus = d) :
    ∃ τ, Run W setupCRT σ τ 100 ∧
      τ.vars ga = shiftedCoefficient a p d ∧ τ.vars unaryTarget = shiftedTarget a b r d ∧
      τ.vars gb = d ∧ τ.vars unaryOK = 0 := by
  have haB : a < W := by omega
  have hbB : b < W := by omega
  have hdB : d < W := by omega
  have hpB : p < W := by omega
  have hrB : r < W := by omega
  have hprod (j : ℕ) (hj : j ≤ M) : a*j < W :=
    (Nat.mul_le_mul ha hj).trans_lt (by nlinarith)
  let σ₁ := σ.setVar ga (shiftedCoefficient a p d)
  let σ₂ := σ₁.setVar unaryTarget (shiftedTarget a b r d)
  let σ₃ := σ₂.setVar gb d
  let τ := σ₃.setVar unaryOK 0
  have run₁ : Run W (.assign ga shiftedCoeffExpr) σ σ₁ (1+shiftedCoeffExpr.size) := by
    apply Run.assign
    exact eval_remWord (ev_mul (ev_var hA haB) (ev_var hP hpB) (hprod p hp)) (ev_var hD hdB)
  have uA : σ₁.vars rowCoefficient = a := by
    simpa [σ₁,vars_setVar,show rowCoefficient ≠ ga by decide] using hA
  have uB : σ₁.vars rowTarget = b := by
    simpa [σ₁,vars_setVar,show rowTarget ≠ ga by decide] using hB
  have uD : σ₁.vars rowModulus = d := by
    simpa [σ₁,vars_setVar,show rowModulus ≠ ga by decide] using hD
  have uR : σ₁.vars crtRepresentative = r := by
    simpa [σ₁,vars_setVar,show crtRepresentative ≠ ga by decide] using hR
  have eD := ev_var uD hdB
  have hbd : b%d+d < W := by have := Nat.mod_le b d; omega
  have run₂ : Run W (.assign unaryTarget shiftedTargetExpr) σ₁ σ₂ (1+shiftedTargetExpr.size) := by
    apply Run.assign
    have he := ev_add (eval_remWord (ev_var uB hbB) eD) eD hbd
    have hsub := (Nat.sub_le (b%d+d) ((a*r)%d)).trans_lt hbd
    exact ev_sub he (eval_remWord (ev_mul (ev_var uA haB) (ev_var uR hrB)
      (hprod r (by omega))) eD) hsub
  have uD₂ : σ₂.vars rowModulus = d := by
    simpa [σ₂,vars_setVar,show rowModulus ≠ unaryTarget by decide] using uD
  have run₃ : Run W (.assign gb (.var rowModulus)) σ₂ σ₃ 2 := Run.assign (ev_var uD₂ hdB)
  have run₄ : Run W (.assign unaryOK (.lit 0)) σ₃ τ 2 := Run.assign (evalB_lit (by omega))
  have hRun : Run W setupCRT σ τ 100 := (run₁.seq (run₂.seq (run₃.seq run₄))).mono (by decide)
  refine ⟨τ,hRun,?_,?_,?_,?_⟩
  · simp [τ,σ₃,σ₂,σ₁,vars_setVar,show ga ≠ unaryOK by decide,show ga ≠ gb by decide,
      show ga ≠ unaryTarget by decide]
  · simp [τ,σ₃,σ₂,vars_setVar,show unaryTarget ≠ unaryOK by decide,show unaryTarget ≠ gb by decide]
  · simp [τ,σ₃,vars_setVar,show gb ≠ unaryOK by decide]
  · simp [τ]

/-- Paid row intersection, including exact success and prefix-preserving
rejection. All successful states remain canonical modulo a divisor of M. -/
theorem intersectRow_run {W M r p a b d : ℕ} {σ : Env}
    (hM : 0 < M) (hW : 4*M*M+4*M+10 < W)
    (hr : r < p) (hp : p ∣ M) (hd : 0 < d) (hdM : d ∣ M)
    (ha : a ≤ M) (hb : b ≤ M)
    (hR : σ.vars crtRepresentative = r) (hP : σ.vars crtPeriod = p)
    (hAct : σ.vars crtActive = 1)
    (hA : σ.vars rowCoefficient = a) (hB : σ.vars rowTarget = b) (hD : σ.vars rowModulus = d) :
    ∃ τ, Run W intersectRow σ τ (intersectRowCost M) ∧ Frame intersectRow σ τ ∧
      ((τ.vars crtActive = 1 ∧ τ.vars crtRepresentative < τ.vars crtPeriod ∧
        τ.vars crtPeriod ∣ M ∧
        ∀ x, (x ≡ r [MOD p] ∧ a*x ≡ b [MOD d]) ↔
          x ≡ τ.vars crtRepresentative [MOD τ.vars crtPeriod]) ∨
       (τ.vars crtActive = 0 ∧ ∀ x, ¬(x ≡ r [MOD p] ∧ a*x ≡ b [MOD d]))) := by
  have hpM := Nat.le_of_dvd hM hp
  have hdle := Nat.le_of_dvd hM hdM
  obtain ⟨ρ,hsetup,hsA,hsB,hsD,hsOK⟩ :=
    setupCRT_run hW hr hpM ha hb hdle hR hP hA hB hD
  let a' := shiftedCoefficient a p d
  let b' := shiftedTarget a b r d
  let l := d/Nat.gcd a' d
  have ha' : a' < d := Nat.mod_lt _ hd
  have hb' : b' ≤ 2*M := by
    have hh := Nat.mod_lt b hd
    unfold b' shiftedTarget
    omega
  have hp' : b'*d < W := by
    have hm := Nat.mul_le_mul hb' hdle
    nlinarith
  have hWord : a'+d+2 < W := by omega
  obtain ⟨η,hNorm,hPer,hYes,hSpec⟩ :=
    paidNormalize_run hd hWord (by omega) hp' hsA hsB hsD
  have hf := Frame.of_run (hsetup.seq hNorm)
  have hR' : η.vars crtRepresentative = r := (hf.vars _ (by decide)).trans hR
  have hP' : η.vars crtPeriod = p := (hf.vars _ (by decide)).trans hP
  have hAct' : η.vars crtActive = 1 := (hf.vars _ (by decide)).trans hAct
  have hPeriod : η.vars unaryPeriod = l := hPer
  have hLt : η.vars unaryOK < W := runRegisterBound hNorm
    (noRead_of_check (by decide)) _ (by rw [hsOK]; omega)
  have hguard := evalB_condEq (evalB_var (σ := η) (x := unaryOK) hLt) (evalB_lit (n := 1) (by omega))
  have hcost : Nat.size d ≤ Nat.size M := Nat.size_le_size hdle
  by_cases he : η.vars unaryOK = 1
  · have hg : (Cond.eq (.var unaryOK) (.lit 1)).evalB W η = some true := by
      simpa [he] using hguard
    let k := η.vars unaryRepresentative
    obtain ⟨hk,hwhat⟩ := hSpec he
    have hk' : k < l := by simpa only [k,hPeriod] using hk
    have hwhat' : ∀ x, a'*x ≡ b' [MOD d] ↔ x ≡ k [MOD l] := by
      simpa only [k,hPeriod] using hwhat
    have hl : p*l ∣ M := shifted_period_dvd a p d M hd hp hdM
    have hpl : p*l ≤ M := Nat.le_of_dvd hM hl
    have hlD : l ≤ d := Nat.div_le_self _ _
    have hLift := lift_shifted_class r p a b d k l 0 hr hd hk' hwhat'
    have hrep : r+p*k < p*l := hLift.1
    have hkB : k < W := by omega
    have hmul : p*k < W := by omega
    let η₁ := η.setVar crtRepresentative (r+p*k)
    let τ := η₁.setVar crtPeriod (p*l)
    have e₁ : (Expr.add (.var crtRepresentative) (.mul (.var crtPeriod) (.var unaryRepresentative))).evalB W η =
        some (r+p*k) :=
      ev_add (ev_var hR' (by omega)) (ev_mul (ev_var hP' (by omega)) (ev_var rfl hkB) hmul) (by omega)
    have eP : η₁.vars crtPeriod = p := by
      simpa [η₁,vars_setVar,show crtPeriod ≠ crtRepresentative by decide] using hP'
    have eL : η₁.vars unaryPeriod = l := by
      simpa [η₁,vars_setVar,show unaryPeriod ≠ crtRepresentative by decide] using hPeriod
    have e₂ : (Expr.mul (.var crtPeriod) (.var unaryPeriod)).evalB W η₁ = some (p*l) :=
      ev_mul (ev_var eP (by omega)) (ev_var eL (by omega)) (by omega)
    have r₁ : Run W (.assign crtRepresentative
        (.add (.var crtRepresentative) (.mul (.var crtPeriod) (.var unaryRepresentative)))) η η₁ 6 :=
      Run.assign e₁
    have r₂ : Run W (.assign crtPeriod (.mul (.var crtPeriod) (.var unaryPeriod))) η₁ τ 4 :=
      Run.assign e₂
    have hChoose : Run W chooseCRT η τ 14 := Run.ite_true hg (r₁.seq r₂)
    have hRun : Run W intersectRow σ τ (intersectRowCost M) :=
      (hsetup.seq (hNorm.seq hChoose)).mono (by unfold intersectRowCost; omega)
    have tA : τ.vars crtActive = 1 := by
      simpa [τ,η₁,vars_setVar,show crtActive ≠ crtPeriod by decide,
        show crtActive ≠ crtRepresentative by decide] using hAct'
    have tR : τ.vars crtRepresentative = r+p*k := by
      simp [τ,η₁,vars_setVar,show crtRepresentative ≠ crtPeriod by decide]
    have tP : τ.vars crtPeriod = p*l := by simp [τ]
    refine ⟨τ,hRun,Frame.of_run hRun,Or.inl ⟨tA,?_,?_,?_⟩⟩
    · rw [tR,tP]; exact hrep
    · rw [tP]; exact hl
    · intro x
      rw [tR,tP]
      exact (lift_shifted_class r p a b d k l x hr hd hk' hwhat').2
  · have hg : (Cond.eq (.var unaryOK) (.lit 1)).evalB W η = some false := by
      simpa [he] using hguard
    let τ := η.setVar crtActive 0
    have r₁ : Run W (.assign crtActive (.lit 0)) η τ 2 := Run.assign (evalB_lit (by omega))
    have hChoose : Run W chooseCRT η τ 6 := Run.ite_false hg r₁
    have hRun : Run W intersectRow σ τ (intersectRowCost M) :=
      (hsetup.seq (hNorm.seq hChoose)).mono (by unfold intersectRowCost; omega)
    refine ⟨τ,hRun,Frame.of_run hRun,Or.inr ⟨by simp [τ],?_⟩⟩
    intro x hx
    obtain ⟨k,_,hk⟩ := (shifted_class r p a b d x hr hd).mp hx
    apply he
    apply hYes.mp
    exact (hk.dvd_iff (Nat.gcd_dvd_right a' d)).mp
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a' d) k)

#print axioms shifted_period_dvd
#print axioms lift_shifted_class
#print axioms intersectRow_run

end EvenTI.P12Compare
