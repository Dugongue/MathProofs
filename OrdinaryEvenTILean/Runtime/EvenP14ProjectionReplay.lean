import EvenP12CountPreEmit

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace EvenTI.P14Projection

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.P12CountPre

private theorem slice_drop_cons {z : List Nat} {j stop : Nat}
    (hj : j < stop) (hs : stop ≤ z.length) :
    (z.take stop).drop j = z[j]'(hj.trans_le hs) :: (z.take stop).drop (j+1) := by
  have h : j < (z.take stop).length := by rw [List.length_take, min_eq_left hs]; exact hj
  rw [List.drop_eq_getElem_cons h, List.getElem_take]

/-- Replay a materialized interval through a checked one-word operation. The
program and bounds are uniform in the interval address and length. -/
theorem bankLoop_run_of_mem (z : List Nat) {start stop B c : Nat} {σ : Env} (writeWord : Com)
    (f : Nat → Nat) (hwrite : ∀ t : Env, t.vars "word" ∈ z →
      Run B writeWord t {t with out := t.out ++ [f (t.vars "word")]} c)
    (hstart : start ≤ stop) (hstop : stop ≤ z.length)
    (hc : σ.vars "cursor" = start) (hs : σ.vars "stop" = stop)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B) (hB : 1 < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (bankLoop writeWord) σ τ ((c+11)*(stop-start)+4) ∧
      (∀ v, v ≠ "cursor" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.vars "cursor" = stop ∧
      τ.out = σ.out ++ ((z.take stop).drop start).map f := by
  let I (t : Env) : Prop :=
    t.vars "cursor" ≤ stop ∧ (∀ v, v ≠ "cursor" → v ≠ "word" → t.vars v = σ.vars v) ∧
      t.arrs = σ.arrs ∧ t.inp = σ.inp ∧
      t.out ++ ((z.take stop).drop (t.vars "cursor")).map f =
        σ.out ++ ((z.take stop).drop start).map f
  let V (t : Env) : Nat := stop - t.vars "cursor"
  have g (t : Env) (ht : I t) :
      bankGuard.evalB B t = some (decide (t.vars "cursor" < stop)) := by
    have horig := ht.2.1 "stop" (by decide) (by decide)
    have g' := evalB_condLt (σ := t) (B := B) (e := .var "cursor") (f := .var "stop")
      (evalB_var (by have := ht.1; omega)) (evalB_var (by rw [horig,hs]; omega))
    simpa only [bankGuard,horig,hs] using g'
  have step (t : Env) (ht : I t) (hcond : bankGuard.evalB B t = some true) :
      ∃ t', Run B (bankBody writeWord) t t' (c+7) ∧ I t' ∧ V t' < V t := by
    rw [g t ht] at hcond
    have hcur : t.vars "cursor" < stop := by simpa using hcond
    let j := t.vars "cursor"
    have hj : j < z.length := hcur.trans_le hstop
    let a := z[j]
    have ha : a < B := hWords a (List.getElem_mem hj)
    have e : (Expr.get "data" (.var "cursor")).evalB B t = some a := by
      refine evalB_get (evalB_var (by omega)) ?_ ha
      rw [ht.2.2.1,hBank]
      unfold sentinelWords
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    let t₁ := t.setVar "word" a
    let t₂ := {t₁ with out := t₁.out ++ [f a]}
    let t₃ := t₂.setVar "cursor" (j+1)
    have r₁ : Run B (.assign "word" (.get "data" (.var "cursor"))) t t₁ 3 := Run.assign e
    have r₂ : Run B writeWord t₁ t₂ c := by simpa [t₁,t₂] using hwrite t₁ (by simpa [t₁,a] using List.getElem_mem hj)
    have ei : (Expr.add (.var "cursor") (.lit 1)).evalB B t₂ = some (j+1) := by
      have ee := evalB_bin (B := B) (σ := t₂) (op := .add)
        (evalB_var (x := "cursor") (by simp [t₂,t₁]; omega)) (evalB_lit (n := 1) hB)
        (by simp [t₂,t₁]; omega)
      simpa [t₂,t₁,j] using ee
    have r₃ : Run B advanceCursor t₂ t₃ 4 := Run.assign ei
    refine ⟨t₃,(r₁.seq (r₂.seq r₃)).mono (by omega),⟨?_,?_,?_,?_,?_⟩,?_⟩
    · simp [t₃,j]; omega
    · intro v hvc hvw
      simp [t₃,t₂,t₁,hvc,hvw,ht.2.1 _ hvc hvw]
    · simpa [t₃,t₂,t₁] using ht.2.2.1
    · simpa [t₃,t₂,t₁] using ht.2.2.2.1
    · have hh := ht.2.2.2.2
      change t.out ++ ((z.take stop).drop j).map f = _ at hh
      rw [slice_drop_cons hcur hstop] at hh
      simpa [t₃,t₂,t₁,List.append_assoc,a] using hh
    · simp [V,t₃,j]; omega
  obtain ⟨τ,hr,ht,hf⟩ := Run.while_count I V (c+7) (fun t h => ⟨_,g t h⟩) step
    ⟨by rw [hc]; exact hstart, fun _ _ _ => rfl, rfl, rfl, by rw [hc]⟩
  rw [g τ ht] at hf
  have hend : τ.vars "cursor" = stop := by
    have h₁ := ht.1
    have : ¬ τ.vars "cursor" < stop := by simpa using hf
    omega
  refine ⟨τ,hr.mono ?_,ht.2.1,ht.2.2.1,ht.2.2.2.1,hend,?_⟩
  · simp [bankGuard,V,hc,show 4 + (c + 7) = c + 11 by omega]
  · have hnil : (z.take stop).drop (τ.vars "cursor") = [] := by rw [hend]; simp
    simpa [hnil] using ht.2.2.2.2

#print axioms bankLoop_run_of_mem
end EvenTI.P14Projection
