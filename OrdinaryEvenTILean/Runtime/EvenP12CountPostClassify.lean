import EvenP12CountPostRow
import EvenP11OracleIntegration
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12CountPost

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open EvenTI.P10Oracle

set_option autoImplicit false
set_option maxHeartbeats 480000

def indicatorWords (w : List ℕ) : List ℕ := [if w = [1] then 1 else 0]

def indicatorProg : Com := .seq (.read "len")
  (.ite (.eq (.var "len") (.lit 1))
    (.seq (.read "value") (.write (oneBit (.var "value"))))
    (.write (.lit 0)))

def indicatorLayout : Layout := ⟨["len", "value"], [], 12⟩

theorem indicatorProg_ok : Com.Ok indicatorLayout indicatorProg := by
  simp [indicatorProg, indicatorLayout, oneBit, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

theorem indicatorProg_run {B : ℕ} (w : List ℕ) (h1 : 1 < B) (hlen : w.length < B)
    (hw : ∀ x ∈ w, x < B) :
    ∃ t, Run B indicatorProg (initEnv (fun _ => 0) (w.length :: w)) t 32 ∧
      t.out = indicatorWords w := by
  let s := initEnv (fun _ => 0) (w.length :: w)
  let s₁ := {s.setVar "len" w.length with inp := w}
  have hread : Run B (.read "len") s s₁ 1 := Run.read rfl
  have hl : (Expr.var "len").evalB B s₁ = some w.length := by
    have hev : s₁.vars "len" = w.length := by simp [s₁]
    rw [← hev]
    exact evalB_var (hev ▸ hlen)
  have htest := evalB_condEq hl (evalB_lit h1)
  by_cases hh : w.length = 1
  · obtain ⟨x, rfl⟩ : ∃ x, w = [x] := by
      cases w with
      | nil => simp at hh
      | cons x tail =>
        cases tail with
        | nil => exact ⟨x,rfl⟩
        | cons => simp at hh
    have ht : (Cond.eq (.var "len") (.lit 1)).evalB B s₁ = some true := by simpa using htest
    let s₂ := {s₁.setVar "value" x with inp := []}
    have hx : x < B := hw x (by simp)
    have hr : Run B (.read "value") s₁ s₂ 1 := Run.read rfl
    have hval : (Expr.var "value").evalB B s₂ = some x := by
      have he : s₂.vars "value" = x := by simp [s₂]
      rw [← he]; exact evalB_var (he ▸ hx)
    have hwrite := Run.write (oneBit_run hval h1 hx)
    refine ⟨_, (hread.seq (Run.ite_true ht (hr.seq hwrite))).mono ?_, ?_⟩
    · decide
    · simp [s₂,s₁,s,initEnv,indicatorWords]
  · have ht : (Cond.eq (.var "len") (.lit 1)).evalB B s₁ = some false := by
      simpa [hh] using htest
    have hwrite := Run.write (σ := s₁) (evalB_lit (by omega : 0 < B))
    refine ⟨_, (hread.seq (Run.ite_false ht hwrite)).mono ?_, ?_⟩
    · decide
    · have hn : w ≠ [1] := fun e => hh (e ▸ rfl)
      simp [s₁,s,initEnv,indicatorWords,hn]

theorem indicatorWords_turingPolytime : TuringPolytime indicatorWords := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp indicatorLayout indicatorProg indicatorWords
    (Polynomial.C 2) (Polynomial.C 32) indicatorProg_ok
  intro xs
  let B := 2 ^ (2 + bitSize xs + 1)
  have h1 : 1 < B := Nat.one_lt_two_pow (by omega)
  have hbase : 2^(bitSize xs+1) ≤ B :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hl := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hbase
  obtain ⟨t,hr,ho⟩ := indicatorProg_run xs h1 hl (fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hbase)
  exact ⟨fun _ => 0, t, by simpa only [B, Polynomial.eval_C] using hr, ho⟩

/-- Classification consumes all segments, even a final unterminated
segment. The output deliberately uses a canonical delimiter for every
answer and retains the original context unchanged. -/
theorem mapRest_packUnpacked (g : List ℕ → List ℕ) (xs : List ℕ) :
    mapRest (positiveCallback g) xs = packSegments ((unpackSegments xs).map g) := by
  cases xs with
  | nil => simp [mapRest,unpackSegments,packSegments]
  | cons a tail =>
    rw [mapRest, unpackSegments, List.map_cons,
      mapRest_packUnpacked g (cut (a::tail)).2]
    simp only [positiveCallback, Function.comp_apply, packSegments, List.flatMap_cons,
      List.append_assoc, List.singleton_append]
termination_by xs.length
decreasing_by exact cut_snd_lt a tail

theorem classifiedAnswers_turingPolytime : TuringPolytime (mapZ (positiveCallback indicatorWords)) :=
  turingPolytime_mapZ (positiveCallback_turingPolytime indicatorWords_turingPolytime)

theorem indicator_getD (xs : List (List ℕ)) (i : ℕ) :
    (xs.map indicatorWords).getD i [] = [1] ↔ xs.getD i [] = [1] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [indicatorWords]

#print axioms indicatorWords_turingPolytime
#print axioms mapRest_packUnpacked
#print axioms classifiedAnswers_turingPolytime
#print axioms indicator_getD
end EvenTI.P12CountPost
