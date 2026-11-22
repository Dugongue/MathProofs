import EvenProductCount
import Mathproof.Meta.Problem18IMPFieldAddition20261001

namespace EvenTI.P12CountPost

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldAddition20261001 (getD_set_same getD_set_other)

set_option autoImplicit false

def install (a : String) {q : ℕ} (E : Fin q → Expr) : List (Fin q) → Com
  | [] => .skip
  | j :: js => .seq (.store a (.lit j.val) (E j)) (install a E js)

def installCost {q : ℕ} (E : Fin q → Expr) (js : List (Fin q)) : ℕ :=
  1 + (js.map fun j => 2 + (E j).size).sum

/-- Unroll a static set of slots. The expression values may depend on the
other arrays and scalar variables, which this code preserves. -/
theorem install_run {B q : ℕ} (a : String) (E : Fin q → Expr) (v : Fin q → ℕ)
    (js : List (Fin q)) (s : Env) (hB : q ≤ B) (hfit : q ≤ (s.arrs a).length)
    (he : ∀ t : Env, t.vars = s.vars → (∀ b, b ≠ a → t.arrs b = s.arrs b) →
      ∀ j ∈ js, (E j).evalB B t = some (v j)) :
    ∃ t, Run B (install a E js) s t (installCost E js) ∧
      t.vars = s.vars ∧ (∀ b, b ≠ a → t.arrs b = s.arrs b) ∧
      (t.arrs a).length = (s.arrs a).length ∧
      (∀ j ∈ js, (t.arrs a).getD j.val 0 = v j) ∧
      (∀ j : Fin q, j ∉ js → (t.arrs a).getD j.val 0 = (s.arrs a).getD j.val 0) ∧
      t.inp = s.inp ∧ t.out = s.out := by
  induction js generalizing s with
  | nil =>
    exact ⟨s, Run.skip, rfl, fun _ _ => rfl, rfl, by simp, fun _ _ => rfl, rfl, rfl⟩
  | cons j js ih =>
    let s' := s.setArr a j.val (v j)
    have hja := j.isLt.trans_le hfit
    have hs' : Run B (.store a (.lit j.val) (E j)) s s' (2 + (E j).size) :=
      Run.store (evalB_lit (j.isLt.trans_le hB)) (he s rfl (fun _ _ => rfl) j (by simp)) hja
    have hl : (s'.arrs a).length = (s.arrs a).length := by simp [s', Env.setArr]
    have hfr (b : String) (hb : b ≠ a) : s'.arrs b = s.arrs b := by
      simp [s', Env.setArr, hb]
    obtain ⟨t, ht, hvs, hAS, hlen, hmem, houtside, hIn, hOut⟩ :=
      ih s' (by rw [hl]; exact hfit)
        (fun t hv hA k hk => he t hv (fun b hb => (hA b hb).trans (hfr b hb)) k
          (List.mem_cons_of_mem _ hk))
    refine ⟨t, (hs'.seq ht).mono ?_, hvs, fun b hb => (hAS b hb).trans (hfr b hb),
      hlen.trans hl, ?_, ?_, hIn, hOut⟩
    · simp only [installCost, List.map_cons, List.sum_cons]; omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · by_cases h : k ∈ js
        · exact hmem k h
        · rw [houtside k h]
          simpa [s', Env.setArr] using getD_set_same (s.arrs a) k.val (v k) hja
      · exact hmem k hk
    · intro k hk
      rw [houtside k (fun hm => hk (List.mem_cons_of_mem _ hm))]
      have hd : j.val ≠ k.val := by
        intro hh
        exact hk (List.mem_cons.mpr (Or.inl (Fin.ext hh).symm))
      simpa [s', Env.setArr] using getD_set_other (s.arrs a) j.val k.val (v j)
        (k.isLt.trans_le hfit) hd

def readInstall (a : String) {q : ℕ} : List (Fin q) → Com
  | [] => .skip
  | j :: js => .seq (.read "cd_answer")
      (.seq (.store a (.lit j.val) (.var "cd_answer")) (readInstall a js))

/-- Read one word for each listed slot. The exact source length is part of
the precondition, so every read is paid and succeeds. -/
theorem readInstall_run {B q : ℕ} (a : String) (v : Fin q → ℕ)
    (js : List (Fin q)) (s : Env) (rest : List ℕ) (hin : s.inp = js.map v ++ rest)
    (hB : q ≤ B) (hfit : q ≤ (s.arrs a).length) (hv : ∀ j ∈ js, v j < B) :
    ∃ t, Run B (readInstall a js) s t (4 * js.length + 1) ∧
      (∀ x, x ≠ "cd_answer" → t.vars x = s.vars x) ∧
      (∀ b, b ≠ a → t.arrs b = s.arrs b) ∧
      (t.arrs a).length = (s.arrs a).length ∧
      (∀ j ∈ js, (t.arrs a).getD j.val 0 = v j) ∧
      (∀ j : Fin q, j ∉ js → (t.arrs a).getD j.val 0 = (s.arrs a).getD j.val 0) ∧
      t.inp = rest ∧ t.out = s.out := by
  induction js generalizing s with
  | nil =>
    exact ⟨s, Run.skip, fun _ _ => rfl, fun _ _ => rfl, rfl, by simp,
      fun _ _ => rfl, by simpa using hin, rfl⟩
  | cons j js ih =>
    let s₁ := { s.setVar "cd_answer" (v j) with inp := js.map v ++ rest }
    let s₂ := s₁.setArr a j.val (v j)
    have hr : Run B (.read "cd_answer") s s₁ 1 := Run.read (by simpa using hin)
    have hx : s₁.vars "cd_answer" = v j := by simp [s₁]
    have he : (Expr.var "cd_answer").evalB B s₁ = some (v j) := by
      rw [← hx]
      exact evalB_var (by rw [hx]; exact hv j (by simp))
    have hja := j.isLt.trans_le hfit
    have hs : Run B (.store a (.lit j.val) (.var "cd_answer")) s₁ s₂ 3 :=
      Run.store (evalB_lit (j.isLt.trans_le hB)) he hja
    have hl : (s₂.arrs a).length = (s.arrs a).length := by simp [s₂, s₁, Env.setArr]
    have hfr (b : String) (hb : b ≠ a) : s₂.arrs b = s.arrs b := by
      simp [s₂, s₁, Env.setArr, hb]
    obtain ⟨t, ht, hvs, hAS, hlen, hmem, houtside, hIn, hOut⟩ :=
      ih s₂ rfl (by rw [hl]; exact hfit) (fun k hk => hv k (List.mem_cons_of_mem _ hk))
    refine ⟨t, (hr.seq (hs.seq ht)).mono ?_, ?_, fun b hb => (hAS b hb).trans (hfr b hb),
      hlen.trans hl, ?_, ?_, hIn, hOut⟩
    · simp [List.length_cons]; omega
    · intro x hx
      rw [hvs x hx]
      simp [s₂, s₁, hx]
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · by_cases h : k ∈ js
        · exact hmem k h
        · rw [houtside k h]
          simpa [s₂, s₁, Env.setArr] using getD_set_same (s.arrs a) k.val (v k) hja
      · exact hmem k hk
    · intro k hk
      rw [houtside k (fun hm => hk (List.mem_cons_of_mem _ hm))]
      have hd : j.val ≠ k.val := by
        intro hh
        exact hk (List.mem_cons.mpr (Or.inl (Fin.ext hh).symm))
      simpa [s₂, s₁, Env.setArr] using getD_set_other (s.arrs a) j.val k.val (v j)
        (k.isLt.trans_le hfit) hd

#print axioms install_run
#print axioms readInstall_run
end EvenTI.P12CountPost
