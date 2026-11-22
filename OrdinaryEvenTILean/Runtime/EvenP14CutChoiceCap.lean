import EvenP12ComparePrepFour
import EvenP10WordsHeader
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1250000

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.P10Words (capPow capLoop capLoop_run capPow_le)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites run_frame)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands install commands_run)

def cutChoiceBudget : String := "even_compare_choice_budget"
def cutChoiceLength : String := "even_compare_choice_length"

def cappedCutChoiceCount (q c budget : ℕ) : ℕ :=
  if q^c ≤ budget then q^c else 0

def capChoiceBindings (q : ℕ) : List (String × Expr) :=
  [("left",.add (.var shapePower.out) (.lit q)), ("n",.lit q),("i",.lit 0),("r",.lit 1)]

def capChoiceSetup (q : ℕ) (j : Fin 4) : Com :=
  .seq (.assign "d" (.var (nullityAt j))) (commands (capChoiceBindings q))

def selectChoiceCount : Com :=
  .ite (.lt (.var cutChoiceBudget) (.var "r"))
    (.assign cutChoiceLength (.lit 0)) (.assign cutChoiceLength (.var "r"))

def capChoiceProgram (q : ℕ) (j : Fin 4) : Com :=
  .seq (capChoiceSetup q j) (.seq capLoop selectChoiceCount)

private theorem capChoiceBindings_safe (q : ℕ) :
    ∀ p ∈ capChoiceBindings q, ∀ r ∈ capChoiceBindings q, NoVar p.1 r.2 := by
  intro p hp r hr
  simp only [capChoiceBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hr
  rcases hp with rfl|rfl|rfl|rfl <;>
    rcases hr with rfl|rfl|rfl|rfl <;>
      simp [NoVar,shapePower,show ("left" : String) ≠ shapePower.out by decide]

/-- Bounded physical computation of the coefficient range from the live
cut-nullity register. The program never constructs a word larger than the
polynomial workspace cap, even when the true enumeration is rejected. -/
theorem capChoiceProgram_run (q m c budget B : ℕ) (j : Fin 4) (σ : Env)
    (hq : 1 ≤ q) (hc : c ≤ m) (hm : budget ≤ m)
    (hB : (m+q+1)*(m+q+1) < B)
    (hmLive : σ.vars shapePower.out = m) (hDim : σ.vars (nullityAt j) = c)
    (hBudget : σ.vars cutChoiceBudget = budget) :
    ∃ τ, Run B (capChoiceProgram q j) σ τ (30*(m+q)+42) ∧
      τ.vars cutChoiceLength = cappedCutChoiceCount q c budget ∧
      (∀ r, r ∉ ["left","d","n","i","r",cutChoiceLength] → τ.vars r = σ.vars r) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hbPlus : m+q+1 < B :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < m+q+1)).trans_lt hB
  let μ := σ.setVar "d" c
  have eD : (Expr.var (nullityAt j)).evalB B σ = some c :=
    evalB_var_iff.mpr ⟨hDim.symm,hDim ▸ (by omega : c < B)⟩
  have rD : Run B (.assign "d" (.var (nullityAt j))) σ μ 2 := Run.assign eD
  let vals := [m+q,q,0,1]
  let ρ := install (List.zip ((capChoiceBindings q).map Prod.fst) vals) μ
  have he : List.Forall₂ (fun p v => p.2.evalB B μ = some v) (capChoiceBindings q) vals := by
    have hMs : μ.vars shapePower.out = m := by
      simpa only [μ,vars_setVar,show shapePower.out ≠ "d" by decide,if_false] using hmLive
    have hM : (Expr.var shapePower.out).evalB B μ = some m :=
      evalB_var_iff.mpr ⟨hMs.symm,hMs ▸ (by omega : m < B)⟩
    simp only [capChoiceBindings,vals,List.forall₂_cons]
    exact ⟨evalB_bin (op := .add) hM (evalB_lit (by omega)) (by change m+q<B; omega),
      evalB_lit (by omega),evalB_lit (by omega),evalB_lit (by omega),List.Forall₂.nil⟩
  have hSetup : Run B (capChoiceSetup q j) σ ρ 13 :=
    rD.seq (commands_run _ vals μ rfl he (capChoiceBindings_safe q))
  have hReg (r : String) (hr : r ∉ ["left","d","n","i","r"]) : ρ.vars r = σ.vars r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp [ρ,μ,install,capChoiceBindings,vals,vars_setVar,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2]
  have hPL : ρ.vars "left" = m+q := by simp [ρ,μ,install,capChoiceBindings,vals]
  have hPC : ρ.vars "d" = c := by simp [ρ,μ,install,capChoiceBindings,vals]
  have hPQ : ρ.vars "n" = q := by simp [ρ,μ,install,capChoiceBindings,vals]
  have hPI : ρ.vars "i" = 0 := by simp [ρ,μ,install,capChoiceBindings,vals]
  have hPV : ρ.vars "r" = 1 := by simp [ρ,μ,install,capChoiceBindings,vals]
  obtain ⟨η,hLoop,hV,_,hIn,hOut⟩ := capLoop_run B c q (m+q) ρ
    (by omega) hq (by omega) hB hPC hPQ hPL hPI hPV
  have hFrame (x : String) (hxI : x ≠ "i") (hxR : x ≠ "r") : η.vars x = ρ.vars x := by
    apply (run_frame hLoop).1
    simpa [capLoop,EvenTI.P10Words.capBody,scalarWrites,hxI,hxR]
  have hB' : η.vars cutChoiceBudget = budget :=
    (hFrame _ (by decide) (by decide)).trans ((hReg _ (by decide)).trans hBudget)
  let v := capPow (m+q) q c
  have hv : v < B := (capPow_le (m+q) q c).trans_lt hbPlus
  have ev : (Expr.var "r").evalB B η = some v :=
    evalB_var_iff.mpr ⟨hV.symm,hV ▸ hv⟩
  have ed : (Expr.var cutChoiceBudget).evalB B η = some budget :=
    evalB_var_iff.mpr ⟨hB'.symm,hB' ▸ (by omega : budget<B)⟩
  have eq : (Cond.lt (.var cutChoiceBudget) (.var "r")).evalB B η = some (decide (budget<v)) :=
    evalB_condLt ed ev
  have hVal : (if budget<v then 0 else v) = cappedCutChoiceCount q c budget := by
    have hbig : budget < m+q+1 := by omega
    unfold v capPow cappedCutChoiceCount
    by_cases h : q^c ≤ budget
    · simp [min_eq_left (show q^c ≤ m+q+1 by omega),h,not_lt.mpr h]
    · have hh : budget < min (q^c) (m+q+1) := lt_min (by omega) hbig
      simp [hh,h]
  let τ := η.setVar cutChoiceLength (if budget<v then 0 else v)
  have hFinal : Run B selectChoiceCount η τ 9 := by
    by_cases h : budget<v
    · have hh : (Cond.lt (.var cutChoiceBudget) (.var "r")).evalB B η = some true := by simpa only [h,decide_true] using eq
      simpa only [τ,if_pos h,selectChoiceCount] using
        (Run.ite_true (d := .assign cutChoiceLength (.var "r")) hh
          (Run.assign (x := cutChoiceLength) (evalB_lit (by omega : 0 < B)))).mono (by decide : _ ≤ 9)
    · have hh : (Cond.lt (.var cutChoiceBudget) (.var "r")).evalB B η = some false := by simpa only [h,decide_false] using eq
      simpa only [τ,if_neg h,selectChoiceCount] using
        (Run.ite_false (c := .assign cutChoiceLength (.lit 0)) hh
          (Run.assign (x := cutChoiceLength) ev)).mono (by decide : _ ≤ 9)
  refine ⟨τ,(hSetup.seq (hLoop.seq hFinal)).mono (by omega),by simp [τ,hVal],?_,?_,hIn,hOut⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    rw [show τ.vars r = η.vars r by simp [τ,hr.2.2.2.2.2], hFrame r hr.2.2.2.1 hr.2.2.2.2.1]
    apply hReg
    simp [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1]
  · funext a
    change η.arrs a = σ.arrs a
    rw [(run_frame hLoop).2.1 a (by simp [capLoop,EvenTI.P10Words.capBody,arrayWrites])]
    rfl

#print axioms capChoiceProgram_run
end EvenTI.P12ComparePrep
