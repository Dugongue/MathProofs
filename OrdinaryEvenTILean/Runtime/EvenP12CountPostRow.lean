import EvenP12CountPostBanks

namespace EvenTI.P12CountPost

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile

set_option autoImplicit false
set_option maxHeartbeats 525000
open scoped BigOperators

def sumExpr : List Expr → Expr
  | [] => .lit 0
  | e :: es => .add e (sumExpr es)

theorem sumExpr_run {B : ℕ} {I : Type} (s : Env) (xs : List I) (E : I → Expr)
    (v : I → ℕ) (h0 : 0 < B) (hb : (xs.map v).sum < B)
    (he : ∀ a ∈ xs, (E a).evalB B s = some (v a)) :
    (sumExpr (xs.map E)).evalB B s = some (xs.map v).sum := by
  induction xs with
  | nil => exact evalB_lit h0
  | cons a xs ih =>
    have ht : (xs.map v).sum < B := by simpa only [List.map_cons, List.sum_cons] using
      (show (xs.map v).sum < B from (Nat.le_add_left _ _).trans_lt hb)
    exact evalB_bin (he _ (by simp)) (ih ht (fun j hj => he j (by simp [hj]))) hb

theorem readBank {B : ℕ} (s : Env) (a : String) (i v : ℕ)
    (hi : i < (s.arrs a).length) (hiB : i < B) (h : (s.arrs a).getD i 0 = v)
    (hv : v < B) : (Expr.get a (.lit i)).evalB B s = some v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  exact evalB_get (evalB_lit hiB) (by rw [List.getElem?_eq_getElem hi, h]) hv

/-- The bounded subtraction expression equals 1 exactly at answer word 1. -/
def oneBit (e : Expr) : Expr := .sub (.sub (.lit 1) (.sub e (.lit 1))) (.sub (.lit 1) e)

theorem oneBit_run {B x : ℕ} {s : Env} {e : Expr} (h : e.evalB B s = some x)
    (h1 : 1 < B) (hx : x < B) :
    (oneBit e).evalB B s = some (if x = 1 then 1 else 0) := by
  have hL := evalB_bin (op := .sub) h (evalB_lit h1) (by simp; omega)
  have hR := evalB_bin (op := .sub) (evalB_lit h1) h (by simp; omega)
  have hO := evalB_bin (op := .sub) (evalB_lit h1) hL (by simp; omega)
  have hvals : 1 - (x - 1) - (1 - x) = if x = 1 then 1 else 0 := by split <;> omega
  have hFinal := evalB_bin (op := .sub) hO hR (by simp; omega)
  simpa only [oneBit, Bop.apply_sub, hvals] using hFinal

variable {G : Type} [CommGroup G] {q : ℕ}

def lookupIndex (enum : Fin q ≃ G) (j k : Fin q) : Fin q :=
  enum.symm ((enum k)⁻¹ * enum j)

def rowTerm (enum : Fin q ≃ G) (j k : Fin q) : Expr :=
  .mul (oneBit (.get "cd_allow" (.lit k.val)))
    (.get "cd_old" (.lit (lookupIndex enum j k).val))

def rowValue (enum : Fin q ≃ G) (a old : Fin q → ℕ) (j : Fin q) : ℕ :=
  ∑ k : Fin q, if a k = 1 then old (lookupIndex enum j k) else 0

def rowExpr (enum : Fin q ≃ G) (j : Fin q) : Expr :=
  sumExpr ((List.finRange q).map (rowTerm enum j))

def copyExpr (j : Fin q) : Expr := .get "cd_new" (.lit j.val)

def rowProg (enum : Fin q ≃ G) : Com :=
  .seq (readInstall "cd_allow" (List.finRange q))
    (.seq (install "cd_new" (rowExpr enum) (List.finRange q))
      (install "cd_old" copyExpr (List.finRange q)))

def rowCost (enum : Fin q ≃ G) : ℕ :=
  (4*q+1) + (installCost (rowExpr enum) (List.finRange q) +
    installCost copyExpr (List.finRange q))

theorem rowExpr_run {B : ℕ} (enum : Fin q ≃ G) (s : Env) (a old : Fin q → ℕ)
    (haF : q ≤ (s.arrs "cd_allow").length) (hoF : q ≤ (s.arrs "cd_old").length)
    (h1 : 1 < B) (hq : q ≤ B)
    (ha : ∀ k, (s.arrs "cd_allow").getD k.val 0 = a k)
    (ho : ∀ k, (s.arrs "cd_old").getD k.val 0 = old k)
    (hab : ∀ k, a k < B) (hob : ∀ k, old k < B)
    (j : Fin q) (hsum : rowValue enum a old j < B) :
    (rowExpr enum j).evalB B s = some (rowValue enum a old j) := by
  let v := fun k : Fin q => if a k = 1 then old (lookupIndex enum j k) else 0
  have hs : ((List.finRange q).map v).sum = rowValue enum a old j := by
    simp [List.finRange, List.sum_ofFn, rowValue, v]
  rw [← hs]
  apply sumExpr_run s (List.finRange q) (rowTerm enum j) v (by omega) (hs ▸ hsum)
  intro k _
  let i := lookupIndex enum j k
  have hA := readBank s "cd_allow" k.val (a k) (k.isLt.trans_le haF) (k.isLt.trans_le hq)
    (ha k) (hab k)
  have hO := readBank s "cd_old" i.val (old i) (i.isLt.trans_le hoF) (i.isLt.trans_le hq)
    (ho i) (hob i)
  have hbit := oneBit_run hA h1 (hab k)
  have hm : (if a k = 1 then 1 else 0) * old i = v k := by
    by_cases h : a k = 1 <;> simp [h, v, i]
  have hv : v k < B := by
    by_cases h : a k = 1
    · simpa only [v, h, if_true] using hob (lookupIndex enum j k)
    · simpa only [v, h, if_false] using (by omega : 0 < B)
  have hE := evalB_bin (op := .mul) hbit hO (by simpa only [Bop.apply_mul, hm] using hv)
  simpa only [rowTerm, Bop.apply_mul, hm, i] using hE

/-- The physical product-table update reads a complete row, computes into a
scratch bank, then commits all entries. Each control variable except the
answer reader is preserved. -/
theorem rowProg_run {B : ℕ} (enum : Fin q ≃ G) (s : Env) (a old : Fin q → ℕ) (rest : List ℕ)
    (hin : s.inp = (List.finRange q).map a ++ rest)
    (haF : q ≤ (s.arrs "cd_allow").length) (hoF : q ≤ (s.arrs "cd_old").length)
    (hnF : q ≤ (s.arrs "cd_new").length) (h1 : 1 < B) (hq : q ≤ B)
    (ho : ∀ k, (s.arrs "cd_old").getD k.val 0 = old k)
    (hab : ∀ k, a k < B) (hob : ∀ k, old k < B) (hsum : ∀ j, rowValue enum a old j < B) :
    ∃ t, Run B (rowProg enum) s t (rowCost enum) ∧
      (∀ j, (t.arrs "cd_old").getD j.val 0 = rowValue enum a old j) ∧
      (∀ b, (t.arrs b).length = (s.arrs b).length) ∧
      (∀ x, x ≠ "cd_answer" → t.vars x = s.vars x) ∧ t.inp = rest ∧ t.out = s.out := by
  obtain ⟨s₁,hr,hv₁,harr₁,hl₁,ha₁,_,hi₁,ho₁⟩ :=
    readInstall_run "cd_allow" a (List.finRange q) s rest hin hq haF (fun j _ => hab j)
  have hoF₁ : q ≤ (s₁.arrs "cd_old").length := by rw [harr₁ _ (by decide)]; exact hoF
  have hnF₁ : q ≤ (s₁.arrs "cd_new").length := by rw [harr₁ _ (by decide)]; exact hnF
  have haF₁ : q ≤ (s₁.arrs "cd_allow").length := hl₁ ▸ haF
  obtain ⟨s₂,hup,hv₂,harr₂,hl₂,hn₂,_,hi₂,ho₂⟩ :=
    install_run "cd_new" (rowExpr enum) (rowValue enum a old) (List.finRange q) s₁ hq hnF₁ (by
      intro t _ hA j _
      have haB := hA "cd_allow" (by decide)
      have hoB := hA "cd_old" (by decide)
      refine rowExpr_run enum t a old (by rw [haB]; exact haF₁) (by rw [hoB]; exact hoF₁) h1 hq
        (fun k => by rw [haB]; exact ha₁ k (by simp)) (fun k => by rw [hoB,harr₁ _ (by decide)]; exact ho k)
        hab hob j (hsum j))
  have hoF₂ : q ≤ (s₂.arrs "cd_old").length := by rw [harr₂ _ (by decide)]; exact hoF₁
  have hnF₂ : q ≤ (s₂.arrs "cd_new").length := hl₂ ▸ hnF₁
  obtain ⟨t,hcp,hv₃,harr₃,hl₃,hnew,_,hi₃,ho₃⟩ :=
    install_run "cd_old" copyExpr (rowValue enum a old) (List.finRange q) s₂ hq hoF₂ (by
      intro u _ hA j _
      have hb := hA "cd_new" (by decide)
      exact readBank u "cd_new" j.val _ (j.isLt.trans_le (by rw [hb]; exact hnF₂))
        (j.isLt.trans_le hq) (by rw [hb]; exact hn₂ j (by simp)) (hsum j))
  refine ⟨t, ?_, fun j => hnew j (by simp), ?_, ?_, hi₃.trans (hi₂.trans hi₁),
    ho₃.trans (ho₂.trans ho₁)⟩
  · simpa only [rowProg, rowCost, List.length_finRange] using hr.seq (hup.seq hcp)
  · intro b
    have f₁ : (s₁.arrs b).length = (s.arrs b).length := by
      by_cases h : b = "cd_allow"
      · simpa [h] using hl₁
      · rw [harr₁ _ h]
    have f₂ : (s₂.arrs b).length = (s₁.arrs b).length := by
      by_cases h : b = "cd_new"
      · simpa [h] using hl₂
      · rw [harr₂ _ h]
    by_cases h : b = "cd_old"
    · simpa only [h] using hl₃.trans ((show (s₂.arrs "cd_old").length = _ from h ▸ f₂).trans (h ▸ f₁))
    · rw [harr₃ _ h, f₂, f₁]
  · intro x hx
    rw [hv₃,hv₂,hv₁ _ hx]

#print axioms rowProg_run
end EvenTI.P12CountPost
