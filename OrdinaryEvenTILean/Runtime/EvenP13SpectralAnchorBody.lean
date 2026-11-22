import EvenP13SpectralAnchorRaw
import EvenP13SpectralAnchorShape
import EvenP12ComparePrepRaw

set_option autoImplicit false
set_option maxRecDepth 45000
set_option maxHeartbeats 6500000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P12ComparePrep
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.P15FactorIMP20261007 (Snf)
open Mathproof.Problem17RecognizerAllocation (width)
open Mathproof.Problem17RepeatedBudget (repeatedBudget)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def anchorWordResult (D : FieldEncoding K) : List Nat → List Nat
  | n :: xs =>
    if (0 < n ∧ xs.length = n*n) ∧ xs.all (fun a => decide (a < Fintype.card K)) = true then
      [storedAnchorExponent D (numeric (readAnchorMatrix D n (n::xs)))]
    else [0]
  | [] => [0]

theorem numberedAnchor_reencode (D : FieldEncoding K) (n : Nat) (xs : List Nat)
    (hl : xs.length = n*n) (hv : ∀ a ∈ xs, a < Fintype.card K) :
    numberedAnchorWords D (numeric (readAnchorMatrix D n (n::xs))) = n :: xs := by
  change n :: (List.ofFn fun i : Fin (n*n) =>
    (D (readAnchorMatrix D n (n::xs)
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).val) = n :: xs
  apply congrArg (List.cons n)
  apply List.ext_getElem (by simpa using hl.symm)
  intro i h₁ h₂
  simp only [List.getElem_ofFn,readAnchorMatrix,List.drop_succ_cons,List.drop_zero]
  have he : finProdFinEquiv ((finProdFinEquiv.symm (⟨i,by simpa [hl] using h₂⟩ : Fin (n*n))).1,
      (finProdFinEquiv.symm (⟨i,by simpa [hl] using h₂⟩ : Fin (n*n))).2) =
      (⟨i,by simpa [hl] using h₂⟩ : Fin (n*n)) := finProdFinEquiv.apply_symm_apply _
  rw [he,List.getD_eq_getElem _ _ h₂]
  have hx := hv _ (List.getElem_mem h₂)
  simp [readFieldDigit,hx]

def flagged : Cond := .eq (.var digitGood) (.lit 1)

noncomputable def anchorBody (D : FieldEncoding K) (F : FieldPresentation K) (input : String) : Com :=
  .seq (markShape input)
    (.ite flagged
      (.seq (.assign digitIndex (.lit 1)) <|
        .seq (digitLoop (Fintype.card K) input)
          (.ite flagged (loadedAnchorProgram D F input) (.write (.lit 0))))
      (.write (.lit 0)))

def AnchorInputs (F : FieldPresentation K) (t B : ℕ) (σ : Env) : Prop :=
  OneAnchorLayout (width (t+1)) B t ∧ width (t+1) < B ∧
  σ.arrs canonical.mem = List.replicate (F.e+1+Snf (width (t+1))*F.e) 0 ∧
  (σ.arrs canonical.scratch).length = 16*(F.e+1) ∧
  F.e+1+Snf (width (t+1))*F.e < B ∧ 16*(F.e+1) < B

theorem anchorBody_run (D : FieldEncoding K) (F : FieldPresentation K)
    (input : String) (ws : List Nat) {B C : Nat} {σ : Env}
    (hIn : input ≠ canonical.mem) (hArr : σ.arrs input = ws)
    (hLen : σ.vars anchorLength = ws.length) (hSize : ws.length*ws.length+2 < B)
    (hWords : ∀ a ∈ ws, a < B)
    (hq : Fintype.card K < B) (hp : (F.p+1)^2 < B)
    (he : (F.p+1)^(F.e+1) < B)
    (hReady : ∀ t xs, ws = (t+1)::xs → xs.length = (t+1)*(t+1) →
      AnchorInputs F t B σ ∧ loadedAnchorCost F t ≤ C) :
    ∃ τ, Run B (anchorBody D F input) σ τ (16*ws.length+ C +75) ∧
      τ.out = σ.out ++ anchorWordResult D ws := by
  have hB : 1 < B := by omega
  obtain ⟨s,rs,hs,hsBound,fs⟩ := markShape_run input ws hArr hLen hSize hWords
  have hsGood : s.vars digitGood < B := hsBound.trans_lt hB
  have eS : flagged.evalB B s = some (decide (s.vars digitGood = 1)) :=
    evalB_condEq (evalB_var hsGood) (evalB_lit hB)
  by_cases h : anchorShape ws
  · cases hws : ws with
    | nil => simp [hws,anchorShape] at h
    | cons n xs =>
      rcases show 0 < n ∧ xs.length = n*n by simpa [hws,anchorShape] using h with ⟨hn,hxs⟩
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
      have hg : s.vars digitGood = 1 := hs.mpr h
      have ep : flagged.evalB B s = some true := by rw [eS]; simp [hg]
      let μ := s.setVar digitIndex 1
      have r₀ : Run B (.assign digitIndex (.lit 1)) s μ 2 := Run.assign (evalB_lit hB)
      have hWsL : ws.length < B := (Nat.le_mul_self _).trans_lt (by omega)
      have hLive : μ.arrs input = (t+1)::xs := by
        change s.arrs input = _
        rw [fs.arrs input (by simp [markShape,markShapeBody,arrayWrites]),hArr,hws]
      have hLiveLength : μ.vars anchorLength = xs.length+1 := by
        simp only [μ,vars_setVar,show anchorLength ≠ digitIndex by decide,if_false]
        rw [fs.vars anchorLength (by simp [markShape,markShapeBody,scalarWrites,anchorLength,digitGood,shapeSide]),
          hLen,hws,List.length_cons]
      have hLiveGood : μ.vars digitGood = 1 := by
        simp only [μ,vars_setVar,show digitGood ≠ digitIndex by decide,if_false]
        exact hg
      obtain ⟨v,rv,hv,hvBound,fv⟩ := digitLoop_run (Fintype.card K) (t+1) input xs
        (σ := μ) hLive hLiveLength (by simp [μ,vars_setVar]) hLiveGood
        hB hq (by simpa [hws] using hWsL)
        (fun a ha => hWords a (by simp [hws,ha]))
      have hvGood : v.vars digitGood < B := hvBound.trans_lt hB
      have eV : flagged.evalB B v = some (decide (v.vars digitGood = 1)) :=
        evalB_condEq (evalB_var hvGood) (evalB_lit hB)
      have f₀ := Frame.of_run r₀
      have outEqual : v.out = σ.out := (fv.out (by apply noWrite_of_check; rfl)).trans
        ((f₀.out (by apply noWrite_of_check; rfl)).trans (fs.out (by apply noWrite_of_check; rfl)))
      have sameArray (b : String) : v.arrs b = σ.arrs b :=
        (fv.arrs b (by simp [digitLoop,digitStep,arrayWrites])).trans ((f₀.arrs b (by simp [arrayWrites])).trans (fs.arrs b (by simp [markShape,markShapeBody,arrayWrites])))
      by_cases ha : ∀ a ∈ xs, a < Fintype.card K
      · have hy : flagged.evalB B v = some true := by rw [eV]; simp [hv.mpr ha]
        obtain ⟨⟨hL,hWidth,hMem,hScr,hMemB,hScrB⟩,hc⟩ := hReady t xs hws hxs
        let A := readAnchorMatrix D (t+1) ((t+1)::xs)
        have hLabel : v.arrs input = numberedAnchorWords D (numeric A) := by
          rw [sameArray,hArr,hws,numberedAnchor_reencode D _ xs hxs ha]
        have hf : 1+(t+1)*(t+1)<B := by rw [← hxs,Nat.add_comm]; simpa [hws] using hWsL
        obtain ⟨τ,rt,_,ht⟩ := loadedAnchor_run D F A input hIn hLabel hL hWidth hq.le
          (by rw [sameArray]; exact hMem) (by rw [sameArray]; exact hScr)
          hMemB hScrB hp he hf
        refine ⟨τ,(rs.seq (Run.ite_true ep (r₀.seq (rv.seq (Run.ite_true hy rt))))).mono ?_,?_⟩
        · simp only [flagged,Cond.size,Expr.size]
          simp only [hws,List.length_cons] at *
          omega
        · rw [ht,outEqual]
          have hd : xs.all (fun a => decide (a < Fintype.card K)) = true := by
            simp only [List.all_eq_true,decide_eq_true_eq]
            exact ha
          simp [anchorWordResult,hn,hxs,hd,A]
      · have hy : flagged.evalB B v = some false := by
          rw [eV]; exact congrArg some (decide_eq_false (fun heq => ha (hv.mp heq)))
        let τ := {v with out := v.out ++ [0]}
        have rt : Run B (.write (.lit 0)) v τ 2 := Run.write (evalB_lit (by omega))
        refine ⟨τ,(rs.seq (Run.ite_true ep (r₀.seq (rv.seq (Run.ite_false hy rt))))).mono ?_,?_⟩
        · simp only [flagged,Cond.size,Expr.size]
          simp only [hws,List.length_cons] at *
          omega
        · simp [τ,outEqual,anchorWordResult,hn,hxs,List.all_eq_true,ha]
  · have ep : flagged.evalB B s = some false := by rw [eS]; exact congrArg some (decide_eq_false (fun heq => h (hs.mp heq)))
    let τ := {s with out := s.out ++ [0]}
    have rt : Run B (.write (.lit 0)) s τ 2 := Run.write (evalB_lit (by omega))
    refine ⟨τ,(rs.seq (Run.ite_false ep rt)).mono (by simp [flagged,Cond.size,Expr.size] <;> omega),?_⟩
    have ho : anchorWordResult D ws = [0] := by
      cases ws with
      | nil => rfl
      | cons n xs =>
        have hbad : ¬ (0 < n ∧ xs.length = n*n) := h
        simp [anchorWordResult,hbad]
    simp [τ,ho,fs.out (by apply noWrite_of_check; rfl)]

#print axioms anchorBody_run
end EvenTI.P13Spectral
