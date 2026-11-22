import EvenP12CountPreOneQuery

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle

set_option autoImplicit false
variable {K : Type} [Field K] [Fintype K]

def modeQueryWords (F : FieldEncoding K) (u : Kˣ) (z : List Nat) (e m n a b : Nat) : List Nat :=
  [e] ++ ((z.take e).drop 1) ++ [m,n] ++ ((z.take b).drop a).map (scalarDigit F u) ++ [0]

def unitPrograms (F : FieldEncoding K) : List Kˣ → Com
  | [] => .skip
  | u :: us => .seq (oneQueryProgram F u) (unitPrograms F us)

theorem unitPrograms_run (F : FieldEncoding K) (us : List Kˣ) (z : List Nat)
    {B e m n a b : Nat} {σ : Env}
    (he : σ.vars "paramEnd" = e) (hm : σ.vars "modeWord" = m) (hn : σ.vars "dimWord" = n)
    (ha : σ.vars "matrixStart" = a) (hb : σ.vars "matrixEnd" = b)
    (he1 : 1 ≤ e) (hez : e ≤ z.length) (hab : a ≤ b) (hbz : b ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hB : Fintype.card K + 1 < B) (hMb : m < B) (hNb : n < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (unitPrograms F us) σ τ
        (us.length*(13 * e + (4 * (Fintype.card K + 1) + 13)*(b-a)+26)+1) ∧
      (∀ v, v ≠ "cursor" → v ≠ "stop" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ us.flatMap (fun u => modeQueryWords F u z e m n a b) := by
  induction us generalizing σ with
  | nil =>
    exact ⟨σ,by simpa [unitPrograms] using (Run.skip (B := B) (σ := σ)),
      fun _ _ _ _ => rfl,rfl,rfl,by simp⟩
  | cons u us ih =>
    obtain ⟨t,hr,hv,harr,hin,hout⟩ :=
      oneQueryProgram_run F u z he hm hn ha hb he1 hez hab hbz hBank hLen hB hMb hNb hWords
    have he' := (hv "paramEnd" (by decide) (by decide) (by decide)).trans he
    have hm' := (hv "modeWord" (by decide) (by decide) (by decide)).trans hm
    have hn' := (hv "dimWord" (by decide) (by decide) (by decide)).trans hn
    have ha' := (hv "matrixStart" (by decide) (by decide) (by decide)).trans ha
    have hb' := (hv "matrixEnd" (by decide) (by decide) (by decide)).trans hb
    obtain ⟨τ,rr,hv',harr',hin',hout'⟩ :=
      ih he' hm' hn' ha' hb' ((congrFun harr "data").trans hBank)
    refine ⟨τ,(hr.seq rr).mono ?_,?_,harr'.trans harr,hin'.trans hin,?_⟩
    · rw [List.length_cons,Nat.succ_mul us.length
        (13 * e + (4 * (Fintype.card K + 1) + 13)*(b-a)+26)]
      omega
    · intro v hc hs hw
      exact (hv' v hc hs hw).trans (hv v hc hs hw)
    · rw [hout',hout,List.flatMap_cons]; simp only [modeQueryWords,List.append_assoc]

/-- A mode increment advances both ends of the matrix interval in lockstep. -/
def advanceMode : Com :=
  .seq (.assign "modeWord" (.add (.var "modeWord") (.lit 1)))
    (.seq (.assign "matrixStart" (.var "matrixEnd"))
      (.assign "matrixEnd" (.add (.var "matrixEnd") (.var "square"))))

def modesProgram (F : FieldEncoding K) (us : List Kˣ) : Com :=
  .while (.lt (.var "modeWord") (.var "modeStop"))
    (.seq (unitPrograms F us) advanceMode)

theorem advanceMode_run {B m a b s : Nat} {σ : Env}
    (hm : σ.vars "modeWord" = m) (ha : σ.vars "matrixStart" = a)
    (hb : σ.vars "matrixEnd" = b) (hs : σ.vars "square" = s)
    (hMb : m + 1 < B) (hBb : b + s < B) :
    Run B advanceMode σ
      (((σ.setVar "modeWord" (m+1)).setVar "matrixStart" b).setVar "matrixEnd" (b+s)) 10 := by
  let t := σ.setVar "modeWord" (m+1)
  let u := t.setVar "matrixStart" b
  have r₁ : Run B (.assign "modeWord" (.add (.var "modeWord") (.lit 1))) σ t 4 := by
    apply Run.assign
    exact evalB_bin (op := .add)
      (by simp [evalB_var_iff,hm]; omega) (evalB_lit (by omega)) hMb
  have r₂ : Run B (.assign "matrixStart" (.var "matrixEnd")) t u 2 := by
    apply Run.assign
    simp [evalB_var_iff,t,hb]
    omega
  have r₃ : Run B (.assign "matrixEnd" (.add (.var "matrixEnd") (.var "square"))) u
      (u.setVar "matrixEnd" (b+s)) 4 := by
    apply Run.assign
    exact evalB_bin (op := .add)
      (by simp [evalB_var_iff,u,t,hb]; omega)
      (by simp [evalB_var_iff,u,t,hs]; omega) hBb
  exact r₁.seq (r₂.seq r₃)

/-- Serialize all modes in their input order, with the same ordered list of
units at each mode, using the checked immutable input bank. -/
theorem modesProgram_run (F : FieldEncoding K) (us : List Kˣ) (z : List Nat)
    {B e d n a s : Nat} {σ : Env}
    (he : σ.vars "paramEnd" = e) (hn : σ.vars "dimWord" = n)
    (hm : σ.vars "modeWord" = 1) (hd : σ.vars "modeStop" = d+1)
    (ha : σ.vars "matrixStart" = a) (hb : σ.vars "matrixEnd" = a+s)
    (hs : σ.vars "square" = s)
    (he1 : 1 ≤ e) (hez : e ≤ z.length) (hrange : a + d*s ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length + s < B) (hB : Fintype.card K + 1 < B)
    (hDb : d+1 < B) (hNb : n < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (modesProgram F us) σ τ
        ((us.length*(13 * e + (4 * (Fintype.card K + 1) + 13)*s+26)+15)*d+4) ∧
      τ.out = σ.out ++ (List.range d).flatMap
        (fun i => us.flatMap (fun u => modeQueryWords F u z e (i+1) n (a+i*s) (a+(i+1)*s))) := by
  let data (i : Nat) := us.flatMap
    (fun u => modeQueryWords F u z e (i+1) n (a+i*s) (a+(i+1)*s))
  let C := us.length*(13 * e + (4 * (Fintype.card K + 1) + 13)*s+26)
  let i (t : Env) : Nat := t.vars "modeWord" - 1
  let I (t : Env) : Prop := 1 ≤ t.vars "modeWord" ∧ i t ≤ d ∧
    t.vars "modeStop" = d+1 ∧ t.vars "paramEnd" = e ∧ t.vars "dimWord" = n ∧
      t.vars "square" = s ∧ t.vars "matrixStart" = a + i t * s ∧
      t.vars "matrixEnd" = a + (i t + 1)*s ∧ t.arrs = σ.arrs ∧
      t.out ++ (List.range' (i t) (d - i t)).flatMap data =
        σ.out ++ (List.range d).flatMap data
  let V (t : Env) := d - i t
  let guard := Cond.lt (.var "modeWord") (.var "modeStop")
  have ev (t : Env) (ht : I t) : guard.evalB B t =
      some (decide (t.vars "modeWord" < d+1)) := by
    have h₁ : t.vars "modeWord" < B := by
      have hc := ht.1
      have hd := ht.2.1
      dsimp [i] at hd
      omega
    have he₁ := evalB_var (B := B) (σ := t) (x := "modeWord") h₁
    have he₂ : (Expr.var "modeStop").evalB B t = some (d+1) := by
      rw [evalB_var_iff,ht.2.2.1]
      exact ⟨rfl,hDb⟩
    exact evalB_condLt he₁ he₂
  have hStep (t : Env) (ht : I t) (hGuard : guard.evalB B t = some true) :
      ∃ t', Run B (.seq (unitPrograms F us) advanceMode) t t' (C+11) ∧ I t' ∧ V t' < V t := by
    rw [ev t ht] at hGuard
    have hm₁ : t.vars "modeWord" < d+1 := by simpa using hGuard
    have hi : i t < d := by dsimp [i]; omega
    have hm₂ : t.vars "modeWord" = i t+1 := by have := ht.1; dsimp [i]; omega
    have hg : a + (i t+1)*s ≤ z.length :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right s (by omega : i t+1 ≤ d)) a).trans hrange
    have hl : a + i t*s ≤ a + (i t+1)*s := by rw [Nat.add_mul]; omega
    have hb₁ : Fintype.card K + 1 < B := hB
    obtain ⟨u,hu,hpres,harr,hin,hout⟩ :=
      unitPrograms_run F us z ht.2.2.2.1 hm₂ ht.2.2.2.2.1 ht.2.2.2.2.2.2.1
        ht.2.2.2.2.2.2.2.1 he1 hez hl hg ((congrFun ht.2.2.2.2.2.2.2.2.1 "data").trans hBank)
          (by omega) hb₁ (by rw [← hm₂]; omega) hNb hWords
    have huMode := hpres "modeWord" (by decide) (by decide) (by decide)
    have huStart := (hpres "matrixStart" (by decide) (by decide) (by decide)).trans ht.2.2.2.2.2.2.1
    have huEnd := (hpres "matrixEnd" (by decide) (by decide) (by decide)).trans ht.2.2.2.2.2.2.2.1
    have huSquare := (hpres "square" (by decide) (by decide) (by decide)).trans ht.2.2.2.2.2.1
    let t' := ((u.setVar "modeWord" (t.vars "modeWord"+1)).setVar "matrixStart" (a+(i t+1)*s)).setVar
      "matrixEnd" (a+(i t+1)*s+s)
    have hAdvance : Run B advanceMode u t' 10 :=
      advanceMode_run huMode huStart huEnd huSquare (by omega) (by omega)
    have hlength : a+(i t+1)*s-(a+i t*s) = s := by rw [Nat.add_mul,Nat.one_mul]; omega
    rw [hlength] at hu
    have hi' : i t' = i t + 1 := by
      change t.vars "modeWord" + 1 - 1 = i t + 1
      omega
    have hrange' : List.range' (i t) (d-i t) = i t :: List.range' (i t+1) (d-(i t+1)) := by
      conv_lhs => rw [show d-i t = (d-(i t+1))+1 by omega,List.range'_succ]
    have hh := ht.2.2.2.2.2.2.2.2.2
    rw [hrange',List.flatMap_cons,← List.append_assoc] at hh
    change (t.out ++ data (i t)) ++ _ = _ at hh
    exact ⟨t',hu.seq hAdvance,by
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp [t']
      · omega
      · simpa [t',hpres "modeStop" (by decide) (by decide) (by decide)] using ht.2.2.1
      · simpa [t',hpres "paramEnd" (by decide) (by decide) (by decide)] using ht.2.2.2.1
      · simpa [t',hpres "dimWord" (by decide) (by decide) (by decide)] using ht.2.2.2.2.1
      · simpa [t'] using huSquare
      · simp [t',hi']
      · rw [hi']
        change a + (i t + 1)*s + s = a + ((i t + 1) + 1)*s
        rw [Nat.add_mul (i t+1) 1 s,Nat.one_mul,Nat.add_assoc]
      · simpa [t',harr] using ht.2.2.2.2.2.2.2.2.1
      · simpa [hi',t',hout,data] using hh
      ,by simp [V,hi']; omega⟩
  have hInitial : I σ := by
    simp [I,i,he,hn,hm,hd,ha,hb,hs,List.range_eq_range']
  obtain ⟨τ,hr,ht,hf⟩ := Run.while_count I V (C+11) (fun t ht => ⟨_,ev t ht⟩) hStep hInitial
  rw [ev τ ht] at hf
  have hFin : i τ = d := by
    have h₁ := ht.1
    have h₂ := ht.2.1
    have h₃ : ¬ τ.vars "modeWord" < d+1 := by simpa using hf
    dsimp [i] at *
    omega
  refine ⟨τ,hr.mono ?_,?_⟩
  · change (4+(C+11))*(d-(σ.vars "modeWord"-1))+4 ≤ (C+15)*d+4
    rw [hm,show 4+(C+11)=C+15 by omega]
    simp
  · simpa [hFin,data] using ht.2.2.2.2.2.2.2.2.2

#print axioms modesProgram_run
#print axioms unitPrograms_run
#print axioms advanceMode_run
end EvenTI.P12CountPre
