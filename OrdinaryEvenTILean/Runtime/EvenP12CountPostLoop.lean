import EvenP12CountPostRow

namespace EvenTI.P12CountPost

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 625000

variable {G : Type} [CommGroup G] {q : ℕ}

def rowWords (rows : List (Fin q → ℕ)) : List ℕ :=
  rows.flatMap fun a => (List.finRange q).map a

def finishRows (enum : Fin q ≃ G) (old : Fin q → ℕ)
    (rows : List (Fin q → ℕ)) : Fin q → ℕ :=
  rows.foldl (fun old a => rowValue enum a old) old

def countCond : Cond := .lt (.lit 0) (.var "cd_count")
def decCount : Com := .assign "cd_count" (.sub (.var "cd_count") (.lit 1))
def countLoop (enum : Fin q ≃ G) : Com :=
  .while countCond (.seq (rowProg enum) decCount)

def loopCost (enum : Fin q ≃ G) (d : ℕ) : ℕ := (rowCost enum + 8) * d + 4

theorem rowValue_le (enum : Fin q ≃ G) (a old : Fin q → ℕ) (b : ℕ)
    (h : ∀ k, old k ≤ b) (j : Fin q) : rowValue enum a old j ≤ q * b := by
  calc
    _ ≤ ∑ _k : Fin q, b := Finset.sum_le_sum fun k _ => by
      by_cases hk : a k = 1 <;> simp [hk,h]
    _ = _ := by simp

private theorem whileCons {B c₁ c₂ : ℕ} {body : Com} {cond : Cond} {s t u : Env}
    (hc : cond.evalB B s = some true) (hr : Run B body s t c₁)
    (ht : Run B (.while cond body) t u c₂) :
    Run B (.while cond body) s u (1 + cond.size + c₁ + c₂) := by
  obtain ⟨a,ha,hr⟩ := hr
  obtain ⟨b,hb,ht⟩ := ht
  exact ⟨_, by omega, .while_true hc hr ht⟩

/-- Run the complete physical answer table on a framed sequence of rows.
The guard and every read, write and integer update are charged. -/
theorem countLoop_run {B : ℕ} (enum : Fin q ≃ G) (rows : List (Fin q → ℕ))
    (s : Env) (old : Fin q → ℕ) (spent : ℕ) (rest : List ℕ)
    (hcount : s.vars "cd_count" = rows.length) (hin : s.inp = rowWords rows ++ rest)
    (haF : q ≤ (s.arrs "cd_allow").length) (hoF : q ≤ (s.arrs "cd_old").length)
    (hnF : q ≤ (s.arrs "cd_new").length)
    (h1 : 1 < B) (hq : q ≤ B) (hq₁ : 1 ≤ q) (hd : rows.length < B)
    (ho : ∀ k, (s.arrs "cd_old").getD k.val 0 = old k)
    (hOld : ∀ k, old k ≤ q ^ spent) (hB : q ^ (spent + rows.length) < B)
    (hInBound : ∀ w ∈ rowWords rows, w < B) :
    ∃ t, Run B (countLoop enum) s t (loopCost enum rows.length) ∧
      (∀ j, (t.arrs "cd_old").getD j.val 0 = finishRows enum old rows j) ∧
      (∀ b, (t.arrs b).length = (s.arrs b).length) ∧ t.inp = rest ∧ t.out = s.out := by
  induction rows generalizing s old spent with
  | nil =>
    have h0 : (Expr.var "cd_count").evalB B s = some 0 := by
      have hh : s.vars "cd_count" = 0 := by simpa only [List.length_nil] using hcount
      rw [← hh]
      exact evalB_var (hh ▸ (by omega : 0 < B))
    have hg : countCond.evalB B s = some false := evalB_condLt (evalB_lit (by omega)) h0
    refine ⟨s, ?_, ho, fun _ => rfl, ?_, rfl⟩
    · simpa [countLoop, loopCost, countCond] using
        (Run.while_false (c := .seq (rowProg enum) decCount) hg)
    · simpa [rowWords] using hin
  | cons a rows ih =>
    have hc : s.vars "cd_count" = rows.length + 1 := hcount
    have hr : (Expr.var "cd_count").evalB B s = some (rows.length + 1) := by
      rw [← hc]
      exact evalB_var (by rw [hc]; exact hd)
    have hg : countCond.evalB B s = some true := by
      simpa [countCond] using
        (evalB_condLt (e := .lit 0) (evalB_lit (by omega)) hr)
    have hrow : s.inp = (List.finRange q).map a ++ (rowWords rows ++ rest) := by
      simpa [rowWords, List.append_assoc] using hin
    have ha : ∀ k, a k < B := by
      intro k
      apply hInBound (a k)
      change a k ∈ (List.finRange q).map a ++ rowWords rows
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩))
    have hpow : q ^ (spent + 1) < B :=
      (Nat.pow_le_pow_right hq₁ (by simp)).trans_lt hB
    have hpow0 : q ^ spent < B :=
      (Nat.pow_le_pow_right hq₁ (by simp)).trans_lt hB
    have hnew (j : Fin q) : rowValue enum a old j ≤ q ^ (spent + 1) := by
      rw [pow_succ', mul_comm q (q ^ spent)] <;> simpa [Nat.mul_comm] using
        rowValue_le enum a old (q ^ spent) hOld j
    obtain ⟨s₁,hu,hvals,hlens,hvars,hins,houts⟩ :=
      rowProg_run enum s a old _ hrow haF hoF hnF h1 hq ho ha
        (fun k => (hOld k).trans_lt hpow0) (fun k => (hnew k).trans_lt hpow)
    have hc₁ : s₁.vars "cd_count" = rows.length+1 := (hvars _ (by decide)).trans hc
    let s₂ := s₁.setVar "cd_count" rows.length
    have hE : (Expr.var "cd_count").evalB B s₁ = some (rows.length + 1) := by
      rw [← hc₁]
      exact evalB_var (by rw [hc₁]; exact hd)
    have hdec : (Expr.sub (.var "cd_count") (.lit 1)).evalB B s₁ = some rows.length := by
      simpa using evalB_bin (op := .sub) hE (evalB_lit h1) (by simp; omega)
    have hrun : Run B decCount s₁ s₂ 4 := Run.assign hdec
    obtain ⟨t,ht,htvals,htlen,htin,htout⟩ :=
      ih s₂ (rowValue enum a old) (spent + 1) (by simp [s₂]) hins
        (by simpa [s₂, hlens] using haF) (by simpa [s₂, hlens] using hoF)
        (by simpa [s₂, hlens] using hnF) (by omega) hvals hnew
        (by convert hB using 2; simp; omega)
        (fun w hw => hInBound w (List.mem_append.mpr (Or.inr hw)))
    refine ⟨t, ?_, htvals, ?_, htin, htout.trans houts⟩
    · have hstay := whileCons hg (hu.seq hrun) ht
      apply hstay.mono
      simp only [loopCost, countCond, size_condLt, size_lit, size_var, List.length_cons]
      ring_nf
      omega
    · intro b
      exact (htlen b).trans (hlens b)

#print axioms countLoop_run
end EvenTI.P12CountPost
