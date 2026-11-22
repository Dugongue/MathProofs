import EvenP12CountPostSource
import EvenP10ScanCodec

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P12ComparePrep

open EvenTI.P10Scan EvenTI.P12CountPre
open EvenTI.P12CountPost (inputLoad_ok_of postSourceLayout)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

def pairComponent (first : Bool) (xs : List ℕ) : List ℕ :=
  if first then (unpairW xs).1 else (unpairW xs).2

private def pairCopy : Com := bankLoop (.write (.var "word"))

private def pairBoundaryGuard : Cond :=
  .lt (.var "word") (.bin .sub (.var "length") (.lit 1))

private def pairBoundary : Com :=
  .seq (.assign "word" (.get "data" (.lit 0)))
    (.seq (.assign "stop" (.var "length"))
      (.ite pairBoundaryGuard (.assign "stop" (.add (.var "word") (.lit 1))) .skip))

private def pairRoute (first : Bool) : Com :=
  if first then .seq (.assign "cursor" (.lit 1)) pairCopy
  else .seq (.assign "cursor" (.var "stop")) (.seq (.assign "stop" (.var "length")) pairCopy)

private def pairComponentBody (first : Bool) : Com :=
  .ite (.lt (.lit 0) (.var "length")) (.seq pairBoundary (pairRoute first)) .skip

def pairComponentProgram (first : Bool) : Com :=
  .seq (.read "length") (.seq inputLoadLoop (pairComponentBody first))

theorem pairComponentProgram_ok (first : Bool) : Com.Ok postSourceLayout (pairComponentProgram first) := by
  have hLoad : Com.Ok postSourceLayout inputLoadLoop := inputLoad_ok_of _ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simp [Com.Ok,postSourceLayout],hLoad,?_⟩
  cases first <;> simp [pairComponentBody,pairBoundary,pairBoundaryGuard,pairRoute,pairCopy,
    bankLoop,bankGuard,bankBody,advanceCursor,Com.Ok,Expr.Ok,Cond.Ok,condExpr,postSourceLayout]

private theorem pairBoundary_run (m : ℕ) (tail : List ℕ) {B : ℕ} {σ : Env}
    (hB : 2<B) (hLen : (m::tail).length<B) (hm : m<B)
    (hLength : σ.vars "length"=(m::tail).length)
    (hData : σ.arrs "data" = sentinelWords (m::tail)) :
    ∃ τ, Run B pairBoundary σ τ 20 ∧ τ.vars "length"=(m::tail).length ∧
      τ.vars "stop"=min m tail.length+1 ∧ τ.arrs "data"=sentinelWords (m::tail) ∧
      τ.out=σ.out := by
  let ρ := σ.setVar "word" m
  let η := ρ.setVar "stop" (m::tail).length
  have r₁ : Run B (.assign "word" (.get "data" (.lit 0))) σ ρ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by rw [hData]; rfl) hm)
  have evL : (Expr.var "length").evalB B ρ = some (m::tail).length :=
    evalB_var_iff.mpr ⟨by simp [ρ,hLength],by simpa [ρ,hLength] using hLen⟩
  have r₂ : Run B (.assign "stop" (.var "length")) ρ η 2 := Run.assign evL
  have ew : (Expr.var "word").evalB B η = some m :=
    evalB_var_iff.mpr ⟨by simp [η,ρ],by simp [η,ρ,hm]⟩
  have el : (Expr.var "length").evalB B η = some (m::tail).length :=
    evalB_var_iff.mpr ⟨by simp [η,ρ,hLength],by simpa [η,ρ,hLength] using hLen⟩
  have eg : pairBoundaryGuard.evalB B η = some (decide (m<tail.length)) := by
    have eTail : (Expr.bin .sub (.var "length") (.lit 1)).evalB B η = some tail.length := by
      have hTail : tail.length < B := by rw [List.length_cons] at hLen; omega
      have hx := evalB_bin (op := .sub) el (evalB_lit (by omega : 1<B))
        (by simpa [Bop.apply] using hTail)
      simpa using hx
    exact evalB_condLt ew eTail
  by_cases ht : m < tail.length
  · let τ := η.setVar "stop" (m+1)
    have r₃ : Run B (.assign "stop" (.add (.var "word") (.lit 1))) η τ 4 :=
      Run.assign (evalB_bin (op := .add) ew (evalB_lit (by omega))
        (show m+1 < B by rw [List.length_cons] at hLen; omega))
    have guard : pairBoundaryGuard.evalB B η = some true := by simpa [ht] using eg
    refine ⟨τ,(r₁.seq (r₂.seq (Run.ite_true (d:=.skip) guard r₃))).mono ?_,?_,?_,?_,?_⟩
    · decide
    · simp [τ,η,ρ,hLength]
    · simp [τ,Nat.min_eq_left ht.le]
    · simpa [τ,η,ρ] using hData
    · rfl
  · have guard : pairBoundaryGuard.evalB B η = some false := by simpa [ht] using eg
    refine ⟨η,(r₁.seq (r₂.seq (Run.ite_false
      (c:=.assign "stop" (.add (.var "word") (.lit 1))) guard Run.skip))).mono ?_,?_,?_,?_,?_⟩
    · decide
    · simp [η,ρ,hLength]
    · simp [η,Nat.min_eq_right (Nat.le_of_not_gt ht)]
    · simpa [η,ρ] using hData
    · rfl

private theorem pairCopy_run (xs : List ℕ) {start stop B : ℕ} {σ : Env}
    (h : start ≤ stop) (hs : stop ≤ xs.length) (hc : σ.vars "cursor"=start)
    (ht : σ.vars "stop"=stop) (hbank : σ.arrs "data"=sentinelWords xs)
    (hLen : xs.length<B) (hb : 2<B) (hv : ∀ x ∈ xs, x<B) :
    ∃ τ, Run B pairCopy σ τ (13*(stop-start)+4) ∧
      τ.out=σ.out++(xs.take stop).drop start := by
  obtain ⟨τ,hr,_,_,_,_,ho⟩ := bankLoop_run xs (.write (.var "word")) id
    (fun ξ hWord => show Run B (.write (.var "word")) ξ
      {ξ with out := ξ.out++[ξ.vars "word"]} 2 from Run.write (evalB_var hWord))
    h hs hc ht hbank hLen (by omega) hv
  exact ⟨τ,hr,by simpa using ho⟩

theorem pairComponentBody_run (first : Bool) (xs : List ℕ) {B : ℕ} {σ : Env}
    (hB : 2<B) (hLen : xs.length<B) (hw : ∀ x ∈ xs, x<B)
    (hLength : σ.vars "length"=xs.length) (hBank : σ.arrs "data"=sentinelWords xs) :
    ∃ τ, Run B (pairComponentBody first) σ τ (14*xs.length+50) ∧
      τ.out=σ.out++pairComponent first xs := by
  have el : (Expr.var "length").evalB B σ = some xs.length :=
    evalB_var_iff.mpr ⟨hLength.symm,hLength ▸ hLen⟩
  have eg := evalB_condLt (evalB_lit (B := B) (σ := σ) (n := 0) (by omega)) el
  cases xs with
  | nil =>
    refine ⟨σ,(Run.ite_false (c := .seq pairBoundary (pairRoute first)) (by simpa using eg) Run.skip).mono ?_,?_⟩
    · decide
    · simp [pairComponent,unpairW]
  | cons m tail =>
    have hGuard : (Cond.lt (.lit 0) (.var "length")).evalB B σ = some true := by simpa using eg
    let stop := min m tail.length+1
    have hs : stop ≤ (m::tail).length := Nat.succ_le_succ (Nat.min_le_right _ _)
    have hsB : stop<B := hs.trans_lt hLen
    obtain ⟨ρ,r₁,hL,hStop,hData,hOut⟩ :=
      pairBoundary_run m tail hB hLen (hw m (by simp)) hLength hBank
    cases first
    · let ρ₀ := ρ.setVar "cursor" stop
      let ρ₁ := ρ₀.setVar "stop" (m::tail).length
      have es : (Expr.var "stop").evalB B ρ = some stop :=
        evalB_var_iff.mpr ⟨hStop.symm,hStop ▸ hsB⟩
      have r₂ : Run B (.assign "cursor" (.var "stop")) ρ ρ₀ 2 := Run.assign es
      have eL : (Expr.var "length").evalB B ρ₀ = some (m::tail).length :=
        evalB_var_iff.mpr ⟨by simp [ρ₀,hL],by simpa [ρ₀,hL] using hLen⟩
      have r₃ : Run B (.assign "stop" (.var "length")) ρ₀ ρ₁ 2 := Run.assign eL
      obtain ⟨τ,r₄,hτ⟩ := pairCopy_run (m::tail) (σ := ρ₁) hs (Nat.le_refl _)
        (by simp [ρ₀,ρ₁]) (by simp [ρ₁]) (by simpa [ρ₀,ρ₁] using hData) hLen hB hw
      have r := Run.ite_true (d:=.skip) hGuard (r₁.seq (r₂.seq (r₃.seq r₄)))
      refine ⟨τ,r.mono (by simp [Cond.size]; omega),?_⟩
      simp only [ρ₀,ρ₁,out_setVar,hOut,List.take_length] at hτ
      change τ.out = σ.out ++ tail.drop m
      rw [hτ]
      change σ.out++tail.drop (min m tail.length) = σ.out++tail.drop m
      by_cases h : m ≤ tail.length
      · simp [Nat.min_eq_left h]
      · simp [Nat.min_eq_right (by omega : tail.length ≤ m),List.drop_eq_nil_of_le (by omega : tail.length ≤ m)]
    · let ρ₀ := ρ.setVar "cursor" 1
      have r₂ : Run B (.assign "cursor" (.lit 1)) ρ ρ₀ 2 :=
        Run.assign (evalB_lit (by omega))
      obtain ⟨τ,r₃,hτ⟩ := pairCopy_run (m::tail) (σ := ρ₀) (show 1 ≤ stop by unfold stop; omega) hs
        (by simp [ρ₀]) (by simpa [ρ₀,stop] using hStop) (by simpa [ρ₀] using hData) hLen hB hw
      have r := Run.ite_true (d:=.skip) hGuard (r₁.seq (r₂.seq r₃))
      refine ⟨τ,r.mono (by simp [Cond.size]; omega),?_⟩
      simp only [ρ₀,out_setVar,hOut,stop,List.take_succ_cons,List.drop_succ_cons,List.drop_zero] at hτ
      change τ.out = σ.out ++ tail.take m
      rw [hτ]
      change σ.out++tail.take (min m tail.length) = σ.out++tail.take m
      by_cases h : m ≤ tail.length
      · simp [Nat.min_eq_left h]
      · simp [Nat.min_eq_right (by omega : tail.length ≤ m),List.take_of_length_le (by omega : tail.length ≤ m)]

theorem pairComponent_turingPolytime (first : Bool) : TuringPolytime (pairComponent first) := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp postSourceLayout (pairComponentProgram first) (pairComponent first)
    (Polynomial.C 3) (50*Polynomial.X+80) (pairComponentProgram_ok first)
  intro xs
  let B := 2^(3+bitSize xs+1)
  have hB : 2<B :=
    (show 2<2^3 by decide).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hBits := Lax51Proofs.Encoding.length_le_bitSize xs
  have hBase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hLen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hBase
  have hv : ∀ x ∈ xs, x<B := fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hBase
  let σ := initEnv (fun _ => xs.length+1) (xs.length::xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have r₁ : Run B (.read "length") σ s 1 := Run.read rfl
  obtain ⟨t,r₂,hLength,hLoaded,hOut,_⟩ := inputLoad_run xs (σ:=s)
    (by simp [s]) (by simp [s,σ,initEnv]) rfl
    (by simp [s,σ,initEnv,inputBuffer_zero]) hLen (by omega) hv
  obtain ⟨τ,r₃,hOut'⟩ := pairComponentBody_run first xs hB hLen hv hLength
    (hLoaded.trans (inputBuffer_full _))
  refine ⟨fun _ => xs.length+1,τ,?_,?_⟩
  · simp only [Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    exact (r₁.seq (r₂.seq r₃)).mono (by omega)
  · simpa [hOut,s,σ,initEnv] using hOut'

theorem unpairW_fst_turingPolytime : TuringPolytime (fun w => (unpairW w).1) :=
  pairComponent_turingPolytime true

theorem unpairW_snd_turingPolytime : TuringPolytime (fun w => (unpairW w).2) :=
  pairComponent_turingPolytime false

#print axioms unpairW_fst_turingPolytime
#print axioms unpairW_snd_turingPolytime
end EvenTI.P12ComparePrep
