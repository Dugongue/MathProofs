
import EvenP11OracleCodec
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001

namespace EvenTI.P12CountPre

open EvenTI.P10Oracle
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile

set_option autoImplicit false

/-- A word bank with one trailing zero. Every scan stops at the bank boundary
even when the corresponding input segment has no explicit delimiter. -/
def sentinelWords (z : List Nat) : List Nat := z ++ [0]

def segmentCond : Cond := .lt (.lit 0) (.get "data" (.var "cursor"))

def advanceCursor : Com :=
  .assign "cursor" (.add (.var "cursor") (.lit 1))

def segmentBody (copy : Bool) : Com :=
  if copy then .seq (.write (.get "data" (.var "cursor"))) advanceCursor
  else advanceCursor

def segmentLoop (copy : Bool) : Com := .while segmentCond (segmentBody copy)

private theorem getElem?_sentinel_words_lt {z : List Nat} {i : Nat} (hi : i < z.length) :
    (sentinelWords z)[i]? = z[i]? := by
  simp [sentinelWords, List.getElem?_append_left hi]

private theorem getElem?_sentinel_words_end (z : List Nat) :
    (sentinelWords z)[z.length]? = some 0 := by
  simp [sentinelWords, List.getElem?_append_right]

theorem cut_drop_poss (z : List Nat) :
    (cut z).1 ++ (if (cut z).1.length < z.length then [0] else []) ++ (cut z).2 = z := by
  induction z with
  | nil => rfl
  | cons a z ih =>
    cases a with
    | zero => simp [cut]
    | succ a =>
      have he : (a+1) :: (cut z).1 ++ (if (cut z).1.length < z.length then [0] else []) ++ (cut z).2 =
          (a+1) :: z := congrArg (List.cons (a+1)) ih
      simpa [cut] using he

/-- Search a segment in a physically installed bank. If asked to copy, the
actual output tape gains the complete segment. The same program handles missing delimiters. -/
theorem segmentLoop_run (copy : Bool) (z : List Nat) {start B : Nat} {σ : Env}
    (hStart : start ≤ z.length) (hσ : σ.vars "cursor" = start)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hv : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (segmentLoop copy) σ τ (17 * z.length + 8) ∧
      τ.vars "cursor" = start + (cut (z.drop start)).1.length ∧
      (τ.vars "cursor" = z.length ∨ (sentinelWords z)[τ.vars "cursor"]? = some 0) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ (if copy then (cut (z.drop start)).1 else []) := by
  let R := (cut (z.drop start)).1
  let I (t : Env) : Prop := t.vars "cursor" ≤ z.length ∧
    t.vars "cursor" + (cut (z.drop (t.vars "cursor"))).1.length = start + R.length ∧
    t.arrs = σ.arrs ∧ t.inp = σ.inp ∧
    t.out ++ (if copy then (cut (z.drop (t.vars "cursor"))).1 else []) =
      σ.out ++ (if copy then R else [])
  let V (t : Env) : Nat := z.length - t.vars "cursor"
  have eword (t : Env) (h : I t) :
      (Expr.get "data" (.var "cursor")).evalB B t =
        some ((z[t.vars "cursor"]?).getD 0) := by
    refine evalB_get (evalB_var (by have := h.1; omega)) ?_ ?_
    · rw [h.2.2.1, hBank]
      by_cases hi : t.vars "cursor" < z.length
      · rw [getElem?_sentinel_words_lt hi,List.getElem?_eq_getElem hi]
        rfl
      · have he := show t.vars "cursor" = z.length by have := h.1; omega
        rw [he, getElem?_sentinel_words_end, List.getElem?_eq_none (by simp)]
        rfl
    · by_cases hi : t.vars "cursor" < z.length
      · rw [List.getElem?_eq_getElem hi]
        exact hv _ (List.getElem_mem hi)
      · rw [List.getElem?_eq_none (by omega : z.length ≤ t.vars "cursor")]
        simp
        omega
  have econd (t : Env) (h : I t) :
      segmentCond.evalB B t = some (decide (0 < (z[t.vars "cursor"]?).getD 0)) := by
    exact evalB_condLt (evalB_lit (by omega)) (eword t h)
  have step (t : Env) (ht : I t) (hc : segmentCond.evalB B t = some true) :
      ∃ t', Run B (segmentBody copy) t t' 12 ∧ I t' ∧ V t' < V t := by
    rw [econd t ht] at hc
    have hp : 0 < (z[t.vars "cursor"]?).getD 0 := by simpa using hc
    have hi : t.vars "cursor" < z.length := by
      by_contra! he
      rw [List.getElem?_eq_none he] at hp
      simp at hp
    let j := t.vars "cursor"
    let a := z[j]
    have ha : 0 < a := by simpa only [j,List.getElem?_eq_getElem hi,Option.getD_some] using hp
    have he : t.vars "cursor" + 1 < B := by omega
    have hdrop : z.drop j = a :: z.drop (j+1) := List.drop_eq_getElem_cons hi
    have hcut : (cut (z.drop j)).1 = a :: (cut (z.drop (j+1))).1 := by
      rw [hdrop]
      have hsucc : a = (a-1)+1 := by omega
      rw [hsucc]
      rfl
    let t₁ := if copy then {t with out := t.out ++ [a]} else t
    let t₂ := t₁.setVar "cursor" (j + 1)
    have hcurs : t₁.vars "cursor" = j := by cases copy <;> rfl
    have ei : (Expr.add (.var "cursor") (.lit 1)).evalB B t₁ = some (j + 1) :=
      evalB_bin (by simpa only [hcurs, j] using
        (evalB_var (B := B) (σ := t₁) (x := "cursor") (by rw [hcurs]; omega)))
        (evalB_lit (by omega)) he
    have ra : Run B advanceCursor t₁ t₂ 4 := Run.assign ei
    have hr : Run B (segmentBody copy) t t₂ 12 := by
      cases copy
      · exact ra.mono (by decide)
      · have ew : (Expr.get "data" (.var "cursor")).evalB B t = some a := by
          rw [eword t ht, List.getElem?_eq_getElem hi]
          rfl
        exact ((Run.write ew).seq ra).mono (by decide)
    refine ⟨t₂,hr,⟨?_,?_,?_,?_,?_⟩,?_⟩
    · simp [t₂,j]
      omega
    · have hh := ht.2.1
      change j + (cut (z.drop j)).1.length = start + R.length at hh
      rw [hcut, List.length_cons] at hh
      simpa only [t₂,vars_setVar,if_true,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · cases copy <;> simpa [t₂,t₁] using ht.2.2.1
    · cases copy <;> simpa [t₂,t₁] using ht.2.2.2.1
    · have hh := ht.2.2.2.2
      change t.out ++ (if copy then (cut (z.drop j)).1 else []) =
        σ.out ++ (if copy then R else []) at hh
      rw [hcut] at hh
      cases copy <;> simpa [t₂,t₁,List.append_assoc] using hh
    · simp [t₂,V,j]
      omega
  obtain ⟨τ,hr,hi,hf⟩ := Run.while_count I V 12 (fun t h => ⟨_, econd t h⟩) step
    ⟨by rw [hσ]; exact hStart, by rw [hσ], rfl, rfl, by rw [hσ]⟩
  rw [econd τ hi] at hf
  have hzero : (z[τ.vars "cursor"]?).getD 0 = 0 := by
    have : ¬ 0 < (z[τ.vars "cursor"]?).getD 0 := by simpa using hf
    omega
  have hend : (cut (z.drop (τ.vars "cursor"))).1 = [] := by
    by_cases hb : τ.vars "cursor" < z.length
    · rw [List.drop_eq_getElem_cons hb]
      have hz := hzero
      rw [List.getElem?_eq_getElem hb] at hz
      exact show (cut (z[τ.vars "cursor"] :: _)).1 = [] by
        simp only [Option.getD_some] at hz
        rw [hz]
        rfl
    · simp [List.drop_eq_nil_of_le (by omega : z.length ≤ τ.vars "cursor"),cut]
  refine ⟨τ, hr.mono ?_, ?_, ?_, hi.2.2.1, hi.2.2.2.1, ?_⟩
  · simp [segmentCond,V,hσ]
    omega
  · have hh := hi.2.1
    simpa [hend] using hh
  · by_cases hb : τ.vars "cursor" < z.length
    · right
      rw [getElem?_sentinel_words_lt hb, List.getElem?_eq_getElem hb]
      rw [List.getElem?_eq_getElem hb] at hzero
      simpa using hzero
    · exact Or.inl (by have := hi.1; omega)
  · have hh := hi.2.2.2.2
    cases copy <;> simpa [hend] using hh

#print axioms segmentLoop_run
end EvenTI.P12CountPre

