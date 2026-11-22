import EvenP15RecoverResidueStore

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

def constantWordTable (key dest : String) : ℕ → List ℕ → Com
  | _, [] => .assign dest (.lit 0)
  | i, v::vs => .ite (.eq (.var key) (.lit i))
      (.assign dest (.lit v)) (constantWordTable key dest (i+1) vs)

private theorem lookup_cons_tail (xs : List ℕ) {k i v : ℕ} (h : k ≠ i) :
    (if i ≤ k then (v::xs).getD (k-i) 0 else 0) =
      if i+1 ≤ k then xs.getD (k-(i+1)) 0 else 0 := by
  by_cases hL : i ≤ k
  · have hN : i+1 ≤ k := by omega
    rw [if_pos hL,if_pos hN]
    rw [show k-i = (k-(i+1))+1 by omega] <;> rfl
  · have hN : ¬ i+1 ≤ k := by omega
    rw [if_neg hL,if_neg hN]

/-- Exact lookup for a fixed base-field table, by literal word comparisons. -/
theorem constantWordTable_run {W : ℕ} (key dest : String) (xs : List ℕ)
    {i k : ℕ} {s : Env} (hk : k < W) (hs : s.vars key = k)
    (hSize : i+xs.length < W) (hWords : ∀ v ∈ xs, v < W) :
    ∃ t, Run W (constantWordTable key dest i xs) s t (6*xs.length+2) ∧
      t.vars dest = (if i ≤ k then xs.getD (k-i) 0 else 0) ∧
      Frame (constantWordTable key dest i xs) s t := by
  induction xs generalizing i with
  | nil =>
    let t := s.setVar dest 0
    have r : Run W (constantWordTable key dest i []) s t 2 :=
      Run.assign (evalB_lit (by omega))
    exact ⟨t,r,by simp [t],Frame.of_run r⟩
  | cons v vs ih =>
    have hiW : i < W := by omega
    have hv : v < W := hWords v (by simp)
    have hGuard : (Cond.eq (.var key) (.lit i)).evalB W s = some (decide (k=i)) :=
      evalB_condEq (ev_var hs hk) (evalB_lit hiW)
    by_cases h : k = i
    · have ex : (Cond.eq (.var key) (.lit i)).evalB W s = some true := by simpa [h] using hGuard
      let t := s.setVar dest v
      have rb : Run W (.assign dest (.lit v)) s t 2 := Run.assign (evalB_lit hv)
      have rr : Run W (constantWordTable key dest i (v::vs)) s t (6*(v::vs).length+2) :=
        (Run.ite_true (d:=constantWordTable key dest (i+1) vs) ex rb).mono
          (by simp [Cond.size,Expr.size] <;> omega)
      exact ⟨t,rr,by simp [t,h],Frame.of_run rr⟩
    · have ex : (Cond.eq (.var key) (.lit i)).evalB W s = some false := by simpa [h] using hGuard
      obtain ⟨t,rt,ht,_⟩ := ih (i := i+1) (by simp at hSize; omega) (fun a ha =>
        hWords a (List.mem_cons_of_mem _ ha))
      have rr : Run W (constantWordTable key dest i (v::vs)) s t (6*(v::vs).length+2) :=
        (Run.ite_false (c:=.assign dest (.lit v)) ex rt).mono
          (by simp [Cond.size,Expr.size] <;> omega)
      exact ⟨t,rr,ht.trans (lookup_cons_tail vs h).symm,Frame.of_run rr⟩

#print axioms constantWordTable_run


theorem constantWordTable_preserves (key dest name : String) (i : ℕ) (xs : List ℕ)
    (h : name ≠ dest) :
    name ∉ Mathproof.Problem18IMPFieldLayout20261001.scalarWrites (constantWordTable key dest i xs) := by
  induction xs generalizing i with
  | nil => simp [constantWordTable,Mathproof.Problem18IMPFieldLayout20261001.scalarWrites,h]
  | cons x xs ih =>
    simp [constantWordTable,Mathproof.Problem18IMPFieldLayout20261001.scalarWrites,h,ih]

theorem constantWordTable_arrayFrame (key dest : String) (i : ℕ) (xs : List ℕ) (name : String) :
    name ∉ Mathproof.Problem18IMPFieldLayout20261001.arrayWrites (constantWordTable key dest i xs) := by
  induction xs generalizing i with
  | nil => simp [constantWordTable,Mathproof.Problem18IMPFieldLayout20261001.arrayWrites]
  | cons x xs ih =>
    simp [constantWordTable,Mathproof.Problem18IMPFieldLayout20261001.arrayWrites,ih]

end EvenTI.P15Recover
