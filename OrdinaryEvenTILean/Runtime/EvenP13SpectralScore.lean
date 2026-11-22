import EvenP13SpectralSum
import Mathproof.Meta.Problem18P34Machine20261002Layout
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

set_option autoImplicit false
set_option maxHeartbeats 4500000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPPolynomialCompiler20261001

def scoreWords (q : Nat) : List Nat → List Nat
  | cap :: _ :: xs => [if q ^ anchorSum xs ≤ cap-1 then 1 else 0]
  | _ => [0]

def scoreHeader : Com :=
  .seq (.read divisionCap) <| .seq (.read sumWord) <|
  .seq (.assign divisionCap (.sub (.var divisionCap) (.lit 1))) <|
  .seq (.assign sumLeft (.sub (.var sumLeft) (.lit 2)))
    (.assign divisionExponent (.lit 0))

def scoreTail (q : Nat) : Com :=
  .seq scoreHeader <| .seq sumLoop <| .seq (divisionBudget q) (.write (.var divisionAnswer))

def scoreCode (q : Nat) : Com :=
  .seq (.read sumLeft) <|
    .ite (.lt (.var sumLeft) (.lit 2)) (.write (.lit 0)) (scoreTail q)

private theorem anchorSum_le (xs : List Nat) (E : Nat) (h : ∀ a ∈ xs, a ≤ E) :
    anchorSum xs ≤ xs.length*E := by
  induction xs with
  | nil => simp [anchorSum]
  | cons a xs ih =>
    have ha := h a (by simp)
    have hrest := ih (fun v hv => h v (by simp [hv]))
    simp only [anchorSum,List.map_cons,List.sum_cons] at hrest ⊢
    rw [List.length_cons,Nat.succ_mul]
    omega

theorem scoreCode_run (q B : Nat) (ws : List Nat) (σ : Env)
    (hq : 2 ≤ q) (hqB : q < B) (h1 : 2 < B)
    (hi : σ.inp = ws.length :: ws) (hLen : ws.length < B)
    (hVal : ∀ a ∈ ws, a < B)
    (hSum : ∀ xs, ws = ws.take 2 ++ xs → anchorSum xs < B)
    (hSize : ∀ a ∈ ws, Nat.size (a-1) ≤ bitSize ws+1)
    (hbSize : bitSize ws+1 < B) :
    ∃ τ, Run B (scoreCode q) σ τ (15*ws.length+12*(bitSize ws+1)+50) ∧
      τ.out = σ.out ++ scoreWords q ws := by
  let a : Env := {σ.setVar sumLeft ws.length with inp := ws}
  have r₀ : Run B (.read sumLeft) σ a 1 := Run.read hi
  have e₀ : (Cond.lt (.var sumLeft) (.lit 2)).evalB B a = some (decide (ws.length < 2)) := by
    exact evalB_condLt (by simpa [a,vars_setVar] using
      (evalB_var (B := B) (σ := a) (x := sumLeft) (by simpa [a,vars_setVar] using hLen)))
      (evalB_lit h1)
  cases ws with
  | nil =>
    have r := r₀.seq (Run.ite_true (d := scoreTail q)
      (show _ = some true from e₀) (Run.write (evalB_lit (show 0 < B by omega))))
    exact ⟨_,r.mono (by simp [Cond.size,Expr.size] <;> omega),rfl⟩
  | cons c tail =>
    cases tail with
    | nil =>
      have r := r₀.seq (Run.ite_true (d := scoreTail q)
        (show _ = some true from e₀) (Run.write (evalB_lit (show 0 < B by omega))))
      exact ⟨_,r.mono (by simp [Cond.size,Expr.size] <;> omega),rfl⟩
    | cons z xs =>
      have hc := hVal c (by simp)
      have hXs : xs.length < B := by simpa using (show xs.length < B by simp at hLen; omega)
      have hfit : anchorSum xs < B := hSum xs (by simp)
      let s₁ : Env := {a.setVar divisionCap c with inp := z::xs}
      let s₂ : Env := {s₁.setVar sumWord z with inp := xs}
      let s₃ := s₂.setVar divisionCap (c-1)
      let s₄ := s₃.setVar sumLeft xs.length
      let s₅ := s₄.setVar divisionExponent 0
      have r₁ : Run B (.read divisionCap) a s₁ 1 := Run.read rfl
      have r₂ : Run B (.read sumWord) s₁ s₂ 1 := Run.read rfl
      have eC : (Expr.var divisionCap).evalB B s₂ = some c := by
        have he : s₂.vars divisionCap = c := by simp [s₂,s₁,sumWord,divisionCap,vars_setVar]
        rw [← he]
        exact evalB_var (he ▸ hc)
      have ec : (Expr.sub (.var divisionCap) (.lit 1)).evalB B s₂ = some (c-1) :=
        evalB_bin eC (evalB_lit (by omega)) (by change c-1 < B; omega)
      have hleft : s₃.vars sumLeft = xs.length+2 := by
        simp [s₃,s₂,s₁,a,sumLeft,sumWord,divisionCap,vars_setVar,Nat.add_assoc]
      have eL : (Expr.var sumLeft).evalB B s₃ = some (xs.length+2) := by
        rw [← hleft]
        exact evalB_var (by rw [hleft]; simp at hLen; omega)
      have el : (Expr.sub (.var sumLeft) (.lit 2)).evalB B s₃ = some xs.length := by
        simpa using evalB_bin (op := .sub) eL (evalB_lit h1)
          (by change xs.length+2-2 < B; omega)
      have rh : Run B scoreHeader a s₅ 12 := r₁.seq (r₂.seq
        ((Run.assign (x := divisionCap) ec).seq ((Run.assign (x := sumLeft) el).seq
          (Run.assign (x := divisionExponent) (evalB_lit (by omega))))))
      have hL₅ : s₅.vars sumLeft = s₅.inp.length := by
        simp [s₅,s₄,s₃,s₂,sumLeft,divisionExponent,vars_setVar]
      obtain ⟨t,rSum,hExp,_,fSum⟩ := sumLoop_run hL₅
        (by exact hXs) (fun v hv => hVal v (by simpa [s₅,s₄,s₃,s₂] using Or.inr (Or.inr hv)))
        (by simpa [s₅,s₄,s₃,s₂,vars_setVar] using hfit) (by omega)
      have hCap : t.vars divisionCap = c-1 := by
        rw [fSum.vars _ (by decide)]
        simp [s₅,s₄,s₃,vars_setVar,sumLeft,divisionExponent,divisionCap]
      have hExp' : t.vars divisionExponent = anchorSum xs := by
        simpa [s₅,s₄,s₃,s₂,vars_setVar] using hExp
      have hb := hSize c (by simp)
      obtain ⟨u,ru,hu,_,ho⟩ := divisionBudget_run hq hqB (by omega) hfit
        (hb.trans_lt hbSize) hCap hExp'
      have hw : Run B (.write (.var divisionAnswer)) u
          {u with out := u.out ++ scoreWords q (c::z::xs)} 2 := by
        have hj : u.vars divisionAnswer < B := by rw [hu]; split <;> omega
        have e := evalB_var (B := B) (σ := u) (x := divisionAnswer) hj
        rw [hu] at e
        exact Run.write e
      have et : (Cond.lt (.var sumLeft) (.lit 2)).evalB B a = some false := by
        rw [e₀]
        simp
      have run : Run B (scoreCode q) σ _ _ := r₀.seq
        (Run.ite_false et (rh.seq (rSum.seq (ru.seq hw))))
      refine ⟨_,run.mono ?_,?_⟩
      · simp [Cond.size,Expr.size,s₅,s₄,s₃,s₂]
        omega
      · simp [ho,fSum.out (by apply noWrite_of_check; rfl),s₅,s₄,s₃,s₂,s₁,a]

theorem scoreWords_turingPolytime (q : Nat) (hq : 2 ≤ q) : TuringPolytime (scoreWords q) := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp
    (Mathproof.Problem18P34Machine20261002Layout.layout (scoreCode q))
    (scoreCode q) (scoreWords q) (Polynomial.X + Polynomial.C (q+8))
    (27*Polynomial.X+62) (Mathproof.Problem18P34Machine20261002Layout.layout_ok _)
  intro xs
  let b := bitSize xs
  let B := 2^(2*b+q+9)
  have hShift : 2^(2*b+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hqB : q < B := (Nat.lt_two_pow_self (n := q)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hlen : xs.length ≤ b := Lax51Proofs.Encoding.length_le_bitSize xs
  have hL : xs.length < B := by
    exact (hlen.trans_lt (Nat.lt_two_pow_self (n := b))).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hV a (ha : a ∈ xs) : a < 2^(b+1) :=
    Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one ha
  have hSum (ys : List Nat) (hys : xs = xs.take 2 ++ ys) : anchorSum ys < B := by
    have hl : ys.length ≤ b := by
      have he := congrArg List.length hys
      simp only [List.length_append] at he
      omega
    have hh := anchorSum_le ys (2^(b+1)) (fun a ha =>
      (hV a (by rw [hys]; exact List.mem_append_right _ ha)).le)
    have h2 : ys.length < 2^b := hl.trans_lt Nat.lt_two_pow_self
    have hm := Nat.mul_lt_mul_of_pos_right h2 (pow_pos (by decide : 0 < (2 : Nat)) (b+1))
    rw [← pow_add,show b+(b+1)=2*b+1 by omega] at hm
    exact (hh.trans_lt hm).trans_le hShift
  have hSize a (ha : a ∈ xs) : Nat.size (a-1) ≤ b+1 :=
    Nat.size_le.mpr ((Nat.sub_le _ _).trans_lt (hV a ha))
  have hb : b+1 < B := (Nat.lt_two_pow_self (n := b+1)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  let σ := initEnv (fun _ => 0) (xs.length::xs)
  obtain ⟨τ,h,ho⟩ := scoreCode_run q B xs σ hq hqB (by omega) rfl hL
    (fun a ha => (hV a ha).trans_le (show 2^(b+1) ≤ B from Nat.pow_le_pow_right (by decide) (by change b+1 ≤ 2*b+q+9; omega)))
    hSum hSize hb
  have hB : B = 2^((Polynomial.X+Polynomial.C (q+8) : Polynomial Nat).eval (bitSize xs)
      + bitSize xs + 1) := by
    dsimp only [B,b]
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    exact congrArg (fun e : Nat => 2^e) (by omega)
  refine ⟨fun _ => 0,τ,?_,by simpa [σ,initEnv] using ho⟩
  rw [← hB]
  apply h.mono
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp [b] at hlen
  omega

#print axioms scoreWords_turingPolytime
end EvenTI.P13Spectral
