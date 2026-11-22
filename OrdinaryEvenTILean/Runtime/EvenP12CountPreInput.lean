import EvenP12CountPreSegments

namespace EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
set_option autoImplicit false
private def natSucc (name : String) : Expr := .add (.var name) (.lit 1)

def inputBuffer (xs : List Nat) (i : Nat) : List Nat :=
  arrOf (xs.length + 1) (fun j => if j < i then xs.getD j 0 else 0)

private theorem inputBuffer_set (xs : List Nat) {i : Nat} (hi : i < xs.length) :
    (inputBuffer xs i).set i xs[i] = inputBuffer xs (i + 1) := by
  unfold inputBuffer
  rw [set_arrOf]
  apply arrOf_congr
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [List.getD_eq_getElem?_getD, hi]
  · by_cases hlt : k < i
    · simp [hki, hlt, show k < i + 1 by omega]
    · simp [hki, hlt, show ¬ k < i + 1 by omega]

private def belowLength : Cond := .lt (.var "i") (.var "length")

private def inputLoadBody : Com :=
  .seq (.read "word") (.seq (.store "data" (.var "i") (.var "word"))
    (.assign "i" (natSucc "i")))

def inputLoadLoop : Com := .while belowLength inputLoadBody

private theorem eval_succ {B : Nat} {σ : Env} {name : String}
    (h : σ.vars name + 1 < B) :
    (natSucc name).evalB B σ = some (σ.vars name + 1) :=
  evalB_bin (op := .add) (evalB_var (by omega)) (evalB_lit (by omega)) h

theorem inputLoad_run (xs : List Nat) {B : Nat} {σ : Env}
    (hl : σ.vars "length" = xs.length) (hi : σ.vars "i" = 0)
    (hInp : σ.inp = xs) (hArr : σ.arrs "data" = inputBuffer xs 0)
    (hlen : xs.length < B) (hB : 1 < B) (hv : ∀ v ∈ xs, v < B) :
    ∃ τ, Run B inputLoadLoop σ τ (13 * xs.length + 5) ∧
      τ.vars "length" = xs.length ∧ τ.arrs "data" = inputBuffer xs xs.length ∧
      τ.out = σ.out ∧ τ.inp = [] := by
  let I (t : Env) : Prop := t.vars "i" ≤ xs.length ∧ t.vars "length" = xs.length ∧
    t.inp = xs.drop (t.vars "i") ∧ t.arrs "data" = inputBuffer xs (t.vars "i") ∧
    t.out = σ.out
  let V (t : Env) : Nat := xs.length - t.vars "i"
  have hg (t : Env) (h : I t) :
      belowLength.evalB B t = some (decide (t.vars "i" < xs.length)) := by
    have e := evalB_condLt (B := B) (σ := t) (e := .var "i") (f := .var "length")
      (evalB_var (by have := h.1; omega)) (evalB_var (h.2.1 ▸ hlen))
    simpa only [belowLength, h.2.1] using e
  have hStep (t : Env) (ht : I t) (hk : belowLength.evalB B t = some true) :
      ∃ t', Run B inputLoadBody t t' 8 ∧ I t' ∧ V t' < V t := by
    rw [hg t ht] at hk
    have hj : t.vars "i" < xs.length := by simpa using hk
    let j := t.vars "i"
    let a := xs[j]
    have ha : a < B := hv a (List.getElem_mem hj)
    have hread : t.inp = a :: xs.drop (j + 1) := by
      rw [ht.2.2.1]
      exact List.drop_eq_getElem_cons hj
    let t₁ := {t.setVar "word" a with inp := xs.drop (j + 1)}
    let t₃ := t₁.setArr "data" j a
    let t₅ := t₃.setVar "i" (j + 1)
    have r₁ : Run B (.read "word") t t₁ 1 := Run.read hread
    have eᵢ : (Expr.var "i").evalB B t₁ = some j := by
      have h : t₁.vars "i" = j := by simp [t₁,j]
      simpa only [h] using evalB_var (B := B) (σ := t₁) (x := "i")
        (by rw [h]; omega)
    have eᵥ : (Expr.var "word").evalB B t₁ = some a := by
      have h : t₁.vars "word" = a := by simp [t₁]
      simpa only [h] using evalB_var (B := B) (σ := t₁) (x := "word")
        (by rw [h]; exact ha)
    have hind : j < (t₁.arrs "data").length := by
      simp [t₁, ht.2.2.2.1, inputBuffer]
      omega
    have r₃ := Run.store (a := "data") eᵢ eᵥ hind
    have e₅ : (natSucc "i").evalB B t₃ = some (j + 1) := by
      have h : t₃.vars "i" = j := by simp [t₃,t₁,j]
      simpa only [h] using eval_succ (σ := t₃) (name := "i") (by rw [h]; omega)
    have hrun : Run B inputLoadBody t t₅ (1 + (3 + 4)) :=
      r₁.seq (r₃.seq (Run.assign (x := "i") e₅))
    refine ⟨t₅, hrun, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [t₅]; omega
      · simp [t₅,t₃,t₁,ht.2.1]
      · simp [t₅,t₃,t₁]
      · simp only [t₅, arrs_setVar, t₃, arrs_setArr, if_true, t₁, ht.2.2.2.1]
        exact inputBuffer_set xs hj
      · simpa [t₅,t₃,t₁] using ht.2.2.2.2
    · simp [V,t₅,j]; omega
  have hInit : I σ := by simp [I, hl, hi, hInp, hArr]
  obtain ⟨τ, hrun, ht, hf⟩ := Run.while_count I V 8 (fun t h => ⟨_, hg t h⟩) hStep hInit
  rw [hg τ ht] at hf
  have hfinal : τ.vars "i" = xs.length := by
    have h := ht.1
    have : ¬ τ.vars "i" < xs.length := by simpa using hf
    omega
  have hnil : τ.inp = [] := by simp [ht.2.2.1, hfinal]
  refine ⟨τ, hrun.mono ?_, ht.2.1, ?_, ht.2.2.2.2, hnil⟩
  · simp [belowLength,V,hi]; omega
  · simpa [hfinal] using ht.2.2.2.1



theorem inputBuffer_zero (z : List Nat) :
    inputBuffer z 0 = List.replicate (z.length + 1) 0 := by
  simp [inputBuffer,replicate_eq_arrOf]

theorem inputBuffer_full (z : List Nat) :
    inputBuffer z z.length = sentinelWords z := by
  apply List.ext_get
  · simp [inputBuffer,sentinelWords]
  · intro j ha hb
    have hj : j < z.length + 1 := by simpa [inputBuffer] using ha
    simp only [inputBuffer, arrOf, List.getElem_map, List.getElem_range]
    by_cases h : j < z.length
    · simpa [h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,sentinelWords,List.getElem_append_left h]
    · have he : j = z.length := by omega
      subst j
      simp [sentinelWords]

#print axioms inputLoad_run
#print axioms inputBuffer_full
end EvenTI.P12CountPre