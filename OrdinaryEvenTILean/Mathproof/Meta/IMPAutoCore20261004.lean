import Mathproof.Meta.Problem18IMPFieldLayout20261001
import Mathproof.Meta.IMPAutoAttr20261004

/-!
# IMP automation, core: a weakest-precondition calculus with cost

This file is the logical core of the IMP proof-automation library.

* `nomv σ e` is the bound-free value of an expression (an array read is `getD … 0`).
  `Ok B σ e` says that every node of `e` is below `B` and every read is in range.
  `evalB_of_Ok` says that then `e.evalB B σ = some (nomv σ e)`, and `Ok_of_evalB` is
  the converse. Expression evaluation therefore becomes arithmetic, with no
  metavariables anywhere.
* `wp B c Q σ` (exact cost) is the weakest precondition.
  `vc B c Q σ` is the verification condition, computed by structural recursion on `c`
  (`while` is left as an annotation point).
  `vc_sound : vc → wp` is **the soundness theorem**; `vc_complete` is its converse.
* `Triple B P c Q t` is a Hoare triple with cost bound `t`, and `Triple.sound` turns it
  into a `Run` statement.
* `Frame c σ τ` bundles the five frame facts of `run_frame`. The loop rules carry it in
  their internal invariant and hand it to the user.
* Loop rules: `wp_while` (potential), `wp_while_count` (variant) and `wp_for` /
  `wp_for_var` (counted `idx < E` loops entered with `idx = 0`).
* Black-box calls: `vc_of_run`, `vc_spec`, `vc_triple`.
* `SegInv` is the standard invariant of a loop that writes an array segment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mathproof.IMPAuto20261004

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Problem18IMPFieldLayout20261001

/-! ## Nominal evaluation -/

/-- Bound-free value of an expression; an out-of-range read reads `0`. -/
def nomv (σ : Env) : Expr → ℕ
  | .lit n => n
  | .var x => σ.vars x
  | .get a i => (σ.arrs a).getD (nomv σ i) 0
  | .bin op e f => op.apply (nomv σ e) (nomv σ f)

/-- Every node of `e` evaluates below `B` and every array read is in range. -/
def Ok (B : ℕ) (σ : Env) : Expr → Prop
  | .lit n => n < B
  | .var x => σ.vars x < B
  | .get a i => Ok B σ i ∧ nomv σ i < (σ.arrs a).length ∧ (σ.arrs a).getD (nomv σ i) 0 < B
  | .bin op e f => Ok B σ e ∧ Ok B σ f ∧ op.apply (nomv σ e) (nomv σ f) < B

/-- Bound-free truth value of a condition. -/
def condv (σ : Env) : Cond → Bool
  | .eq e f => nomv σ e == nomv σ f
  | .lt e f => decide (nomv σ e < nomv σ f)

/-- Both operands of a condition are `Ok`. -/
def OkC (B : ℕ) (σ : Env) : Cond → Prop
  | .eq e f => Ok B σ e ∧ Ok B σ f
  | .lt e f => Ok B σ e ∧ Ok B σ f

@[simp, imp_simp] theorem nomv_lit (σ : Env) (n : ℕ) : nomv σ (.lit n) = n := rfl
@[simp, imp_simp] theorem nomv_var (σ : Env) (x : String) : nomv σ (.var x) = σ.vars x := rfl
@[simp, imp_simp] theorem nomv_get (σ : Env) (a : String) (i : Expr) :
    nomv σ (.get a i) = (σ.arrs a).getD (nomv σ i) 0 := rfl
@[simp, imp_simp] theorem nomv_bin (σ : Env) (op : Bop) (e f : Expr) :
    nomv σ (.bin op e f) = op.apply (nomv σ e) (nomv σ f) := rfl

@[simp, imp_simp] theorem Ok_lit {B : ℕ} {σ : Env} {n : ℕ} : Ok B σ (.lit n) ↔ n < B := Iff.rfl
@[simp, imp_simp] theorem Ok_var {B : ℕ} {σ : Env} {x : String} : Ok B σ (.var x) ↔ σ.vars x < B :=
  Iff.rfl
@[simp, imp_simp] theorem Ok_get {B : ℕ} {σ : Env} {a : String} {i : Expr} :
    Ok B σ (.get a i) ↔ Ok B σ i ∧ nomv σ i < (σ.arrs a).length ∧
      (σ.arrs a).getD (nomv σ i) 0 < B := Iff.rfl
@[simp, imp_simp] theorem Ok_bin {B : ℕ} {σ : Env} {op : Bop} {e f : Expr} :
    Ok B σ (.bin op e f) ↔ Ok B σ e ∧ Ok B σ f ∧ op.apply (nomv σ e) (nomv σ f) < B := Iff.rfl

@[simp, imp_simp] theorem condv_eq (σ : Env) (e f : Expr) :
    condv σ (.eq e f) = (nomv σ e == nomv σ f) := rfl
@[simp, imp_simp] theorem condv_lt (σ : Env) (e f : Expr) :
    condv σ (.lt e f) = decide (nomv σ e < nomv σ f) := rfl
@[simp, imp_simp] theorem OkC_eq {B : ℕ} {σ : Env} {e f : Expr} :
    OkC B σ (.eq e f) ↔ Ok B σ e ∧ Ok B σ f := Iff.rfl
@[simp, imp_simp] theorem OkC_lt {B : ℕ} {σ : Env} {e f : Expr} :
    OkC B σ (.lt e f) ↔ Ok B σ e ∧ Ok B σ f := Iff.rfl

theorem getElem?_of_lt {l : List ℕ} {k : ℕ} (h : k < l.length) : l[k]? = some (l.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `Ok` evaluates. -/
theorem evalB_of_Ok {B : ℕ} {σ : Env} {e : Expr} (h : Ok B σ e) :
    e.evalB B σ = some (nomv σ e) := by
  induction e with
  | lit n => exact fit_self (Ok_lit.1 h)
  | var x => exact fit_self (Ok_var.1 h)
  | get a i ih =>
      obtain ⟨hi, hlen, hv⟩ := Ok_get.1 h
      exact evalB_get (ih hi) (getElem?_of_lt hlen) hv
  | bin op e f ihe ihf =>
      obtain ⟨he, hf, hv⟩ := Ok_bin.1 h
      exact evalB_bin (ihe he) (ihf hf) hv

/-- Converse: a bounded evaluation is `Ok` and its value is the nominal one. -/
theorem Ok_of_evalB {B : ℕ} {σ : Env} {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) :
    Ok B σ e ∧ nomv σ e = v := by
  induction e generalizing v with
  | lit n => rw [evalB_lit_iff] at h; obtain ⟨rfl, h⟩ := h; exact ⟨h, rfl⟩
  | var x => rw [evalB_var_iff] at h; obtain ⟨rfl, h⟩ := h; exact ⟨h, rfl⟩
  | get a i ih =>
      rw [evalB_get_iff] at h
      obtain ⟨k, hk, hv, hB⟩ := h
      obtain ⟨hok, rfl⟩ := ih hk
      obtain ⟨hlen, hget⟩ := List.getElem?_eq_some_iff.1 hv
      have hd : (σ.arrs a).getD (nomv σ i) 0 = v := by
        rw [List.getD_eq_getElem?_getD, hv]; rfl
      exact ⟨Ok_get.2 ⟨hok, hlen, by rw [hd]; exact hB⟩, hd⟩
  | bin op e f ihe ihf =>
      rw [evalB_bin_iff] at h
      obtain ⟨m, n, hm, hn, rfl, hB⟩ := h
      obtain ⟨hoke, rfl⟩ := ihe hm
      obtain ⟨hokf, rfl⟩ := ihf hn
      exact ⟨Ok_bin.2 ⟨hoke, hokf, hB⟩, rfl⟩

theorem evalB_cond_of_Ok {B : ℕ} {σ : Env} {b : Cond} (h : OkC B σ b) :
    b.evalB B σ = some (condv σ b) := by
  cases b with
  | eq e f => exact evalB_condEq (evalB_of_Ok h.1) (evalB_of_Ok h.2)
  | lt e f => exact evalB_condLt (evalB_of_Ok h.1) (evalB_of_Ok h.2)

theorem OkC_of_evalB {B : ℕ} {σ : Env} {b : Cond} {r : Bool} (h : b.evalB B σ = some r) :
    OkC B σ b ∧ condv σ b = r := by
  cases b with
  | eq e f =>
      rw [evalB_condEq_iff] at h
      obtain ⟨m, n, hm, hn, rfl⟩ := h
      obtain ⟨h1, rfl⟩ := Ok_of_evalB hm
      obtain ⟨h2, rfl⟩ := Ok_of_evalB hn
      exact ⟨⟨h1, h2⟩, rfl⟩
  | lt e f =>
      rw [evalB_condLt_iff] at h
      obtain ⟨m, n, hm, hn, rfl⟩ := h
      obtain ⟨h1, rfl⟩ := Ok_of_evalB hm
      obtain ⟨h2, rfl⟩ := Ok_of_evalB hn
      exact ⟨⟨h1, h2⟩, rfl⟩

/-! ## Weakest precondition (exact cost) -/

/-- `wp B c Q σ`: running `c` from `σ` terminates in some `τ` at exact cost `k`,
every value below `B`, and `Q τ k`. -/
def wp (B : ℕ) (c : Com) (Q : Env → ℕ → Prop) (σ : Env) : Prop :=
  ∃ τ k, BigStepB B c σ τ k ∧ Q τ k

theorem wp_mono {B : ℕ} {c : Com} {Q Q' : Env → ℕ → Prop} {σ : Env} (h : wp B c Q σ)
    (hQ : ∀ τ k, Q τ k → Q' τ k) : wp B c Q' σ := by
  obtain ⟨τ, k, hr, hq⟩ := h; exact ⟨τ, k, hr, hQ τ k hq⟩

theorem wp_skip {B : ℕ} {Q : Env → ℕ → Prop} {σ : Env} (h : Q σ 1) : wp B .skip Q σ :=
  ⟨σ, 1, .skip, h⟩

theorem wp_assign {B : ℕ} {x : String} {e : Expr} {Q : Env → ℕ → Prop} {σ : Env}
    (he : Ok B σ e) (h : Q (σ.setVar x (nomv σ e)) (1 + e.size)) : wp B (.assign x e) Q σ :=
  ⟨_, _, .assign (evalB_of_Ok he), h⟩

theorem wp_store {B : ℕ} {a : String} {i e : Expr} {Q : Env → ℕ → Prop} {σ : Env}
    (hi : Ok B σ i) (he : Ok B σ e) (hl : nomv σ i < (σ.arrs a).length)
    (h : Q (σ.setArr a (nomv σ i) (nomv σ e)) (1 + i.size + e.size)) :
    wp B (.store a i e) Q σ :=
  ⟨_, _, .store (evalB_of_Ok hi) (evalB_of_Ok he) hl, h⟩

theorem wp_seq {B : ℕ} {c d : Com} {Q : Env → ℕ → Prop} {σ : Env}
    (h : wp B c (fun τ k => wp B d (fun ρ k' => Q ρ (k + k')) τ) σ) : wp B (.seq c d) Q σ := by
  obtain ⟨τ, k, hr, ρ, k', hr', hq⟩ := h
  exact ⟨ρ, k + k', .seq hr hr', hq⟩

theorem wp_ite {B : ℕ} {b : Cond} {c d : Com} {Q : Env → ℕ → Prop} {σ : Env}
    (hb : OkC B σ b)
    (ht : condv σ b = true → wp B c (fun τ k => Q τ (1 + b.size + k)) σ)
    (hf : condv σ b = false → wp B d (fun τ k => Q τ (1 + b.size + k)) σ) :
    wp B (.ite b c d) Q σ := by
  have hev := evalB_cond_of_Ok hb
  cases hc : condv σ b with
  | true =>
      obtain ⟨τ, k, hr, hq⟩ := ht hc
      exact ⟨τ, _, .ite_true (by rw [hev, hc]) hr, hq⟩
  | false =>
      obtain ⟨τ, k, hr, hq⟩ := hf hc
      exact ⟨τ, _, .ite_false (by rw [hev, hc]) hr, hq⟩

theorem wp_read {B : ℕ} {x : String} {Q : Env → ℕ → Prop} {σ : Env} {v : ℕ} {rest : List ℕ}
    (hin : σ.inp = v :: rest) (h : Q { σ.setVar x v with inp := rest } 1) :
    wp B (.read x) Q σ :=
  ⟨_, _, .read hin, h⟩

theorem wp_write {B : ℕ} {e : Expr} {Q : Env → ℕ → Prop} {σ : Env} (he : Ok B σ e)
    (h : Q { σ with out := σ.out ++ [nomv σ e] } (1 + e.size)) : wp B (.write e) Q σ :=
  ⟨_, _, .write (evalB_of_Ok he), h⟩

/-! ## The verification-condition generator -/

/-- The verification condition of `c` for the postcondition `Q` (exact cost), computed by
structural recursion. A loop is an annotation point: its VC is its `wp`, discharged by
one of the loop rules. -/
def vc (B : ℕ) : Com → (Env → ℕ → Prop) → Env → Prop
  | .skip, Q, σ => Q σ 1
  | .assign x e, Q, σ => Ok B σ e ∧ Q (σ.setVar x (nomv σ e)) (1 + e.size)
  | .store a i e, Q, σ => Ok B σ i ∧ Ok B σ e ∧ nomv σ i < (σ.arrs a).length ∧
      Q (σ.setArr a (nomv σ i) (nomv σ e)) (1 + i.size + e.size)
  | .seq c d, Q, σ => vc B c (fun τ k => vc B d (fun ρ k' => Q ρ (k + k')) τ) σ
  | .ite b c d, Q, σ => OkC B σ b ∧
      (condv σ b = true → vc B c (fun τ k => Q τ (1 + b.size + k)) σ) ∧
      (condv σ b = false → vc B d (fun τ k => Q τ (1 + b.size + k)) σ)
  | .while b c, Q, σ => wp B (.while b c) Q σ
  | .read x, Q, σ => ∃ v rest, σ.inp = v :: rest ∧ Q { σ.setVar x v with inp := rest } 1
  | .write e, Q, σ => Ok B σ e ∧ Q { σ with out := σ.out ++ [nomv σ e] } (1 + e.size)

/-- **Soundness of the VC generator.** -/
theorem vc_sound {B : ℕ} {c : Com} : ∀ {Q : Env → ℕ → Prop} {σ : Env}, vc B c Q σ → wp B c Q σ := by
  induction c with
  | skip => intro Q σ h; simp only [vc] at h; exact wp_skip h
  | assign x e => intro Q σ h; simp only [vc] at h; exact wp_assign h.1 h.2
  | store a i e =>
      intro Q σ h; simp only [vc] at h; exact wp_store h.1 h.2.1 h.2.2.1 h.2.2.2
  | seq c d ihc ihd =>
      intro Q σ h; simp only [vc] at h; exact wp_seq (wp_mono (ihc h) fun τ k hτ => ihd hτ)
  | ite b c d ihc ihd =>
      intro Q σ h; simp only [vc] at h
      exact wp_ite h.1 (fun hb => ihc (h.2.1 hb)) (fun hb => ihd (h.2.2 hb))
  | «while» b c _ => intro Q σ h; simp only [vc] at h; exact h
  | read x =>
      intro Q σ h; simp only [vc] at h; obtain ⟨v, rest, hin, hq⟩ := h; exact wp_read hin hq
  | write e => intro Q σ h; simp only [vc] at h; exact wp_write h.1 h.2

/-- **Completeness of the VC generator**: nothing is lost by generating VCs. -/
theorem vc_complete {B : ℕ} {c : Com} :
    ∀ {Q : Env → ℕ → Prop} {σ : Env}, wp B c Q σ → vc B c Q σ := by
  induction c with
  | skip => rintro Q σ ⟨τ, k, hbs, hq⟩; cases hbs; simp only [vc]; exact hq
  | assign x e =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | assign h => obtain ⟨hok, rfl⟩ := Ok_of_evalB h; simp only [vc]; exact ⟨hok, hq⟩
  | store a i e =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | store hi he hk =>
          obtain ⟨hoki, rfl⟩ := Ok_of_evalB hi
          obtain ⟨hoke, rfl⟩ := Ok_of_evalB he
          simp only [vc]; exact ⟨hoki, hoke, hk, hq⟩
  | seq c d ihc ihd =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | seq h1 h2 => simp only [vc]; exact ihc ⟨_, _, h1, ihd ⟨_, _, h2, hq⟩⟩
  | ite b c d ihc ihd =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | ite_true hb hc =>
          obtain ⟨hok, hcv⟩ := OkC_of_evalB hb
          simp only [vc]
          refine ⟨hok, fun _ => ihc ⟨_, _, hc, hq⟩, fun hf => ?_⟩
          rw [hcv] at hf; cases hf
      | ite_false hb hd =>
          obtain ⟨hok, hcv⟩ := OkC_of_evalB hb
          simp only [vc]
          refine ⟨hok, fun ht => ?_, fun _ => ihd ⟨_, _, hd, hq⟩⟩
          rw [hcv] at ht; cases ht
  | «while» b c _ => intro Q σ h; simp only [vc]; exact h
  | read x =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | read h => simp only [vc]; exact ⟨_, _, h, hq⟩
  | write e =>
      rintro Q σ ⟨τ, k, hbs, hq⟩
      cases hbs with
      | write h => obtain ⟨hok, rfl⟩ := Ok_of_evalB h; simp only [vc]; exact ⟨hok, hq⟩

theorem vc_iff {B : ℕ} {c : Com} {Q : Env → ℕ → Prop} {σ : Env} : vc B c Q σ ↔ wp B c Q σ :=
  ⟨vc_sound, vc_complete⟩

theorem vc_mono {B : ℕ} {c : Com} {Q Q' : Env → ℕ → Prop} {σ : Env} (h : vc B c Q σ)
    (hQ : ∀ τ k, Q τ k → Q' τ k) : vc B c Q' σ :=
  vc_complete (wp_mono (vc_sound h) hQ)

/-! ## Bridges to `Run` -/

theorem wp_of_run {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} {Q : Env → ℕ → Prop}
    (h : Run B c σ τ K) (hQ : ∀ k ≤ K, Q τ k) : wp B c Q σ := by
  obtain ⟨k, hk, hbs⟩ := h; exact ⟨τ, k, hbs, hQ k hk⟩

theorem wp.run {B : ℕ} {c : Com} {σ : Env} {T : ℕ} {Post : Env → Prop}
    (h : wp B c (fun τ k => k ≤ T ∧ Post τ) σ) : ∃ τ, Run B c σ τ T ∧ Post τ := by
  obtain ⟨τ, k, hbs, hk, hp⟩ := h; exact ⟨τ, ⟨k, hk, hbs⟩, hp⟩

/-! ## Frames -/

/-- The five frame facts of a run of `c` from `σ` to `τ`. -/
structure Frame (c : Com) (σ τ : Env) : Prop where
  vars : ∀ x, x ∉ scalarWrites c → τ.vars x = σ.vars x
  arrs : ∀ a, a ∉ arrayWrites c → τ.arrs a = σ.arrs a
  len : ∀ a, (τ.arrs a).length = (σ.arrs a).length
  inp : noRead c → τ.inp = σ.inp
  out : c.NoWrite → τ.out = σ.out

theorem Frame.of_run {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (h : Run B c σ τ K) : Frame c σ τ :=
  let ⟨h1, h2, h3, h4, h5⟩ := run_frame h; ⟨h1, h2, h3, h4, h5⟩

theorem Frame.of_bigStepB {B : ℕ} {c : Com} {σ τ : Env} {k : ℕ} (h : BigStepB B c σ τ k) :
    Frame c σ τ := Frame.of_run (Run.of_bigStepB h)

theorem Frame.refl (c : Com) (σ : Env) : Frame c σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Frames compose when the second command writes no more than the first. -/
theorem Frame.trans {c d : Com} {σ ρ τ : Env} (h1 : Frame c σ ρ) (h2 : Frame d ρ τ)
    (hs : scalarWrites d ⊆ scalarWrites c) (ha : arrayWrites d ⊆ arrayWrites c)
    (hr : noRead c → noRead d) (hw : c.NoWrite → d.NoWrite) : Frame c σ τ :=
  ⟨fun x hx => (h2.vars x (fun h => hx (hs h))).trans (h1.vars x hx),
   fun a ha' => (h2.arrs a (fun h => ha' (ha h))).trans (h1.arrs a ha'),
   fun a => (h2.len a).trans (h1.len a),
   fun h => (h2.inp (hr h)).trans (h1.inp h),
   fun h => (h2.out (hw h)).trans (h1.out h)⟩

/-- A loop body writes no more than its loop. -/
theorem Frame.loop {b : Cond} {c : Com} {σ ρ τ : Env} (h1 : Frame (.while b c) σ ρ)
    (h2 : Frame c ρ τ) : Frame (.while b c) σ τ :=
  h1.trans h2 (by intro x hx; exact hx) (by intro x hx; exact hx) (fun h => h) (fun h => h)

theorem wp_frame {B : ℕ} {c : Com} {Q : Env → ℕ → Prop} {σ : Env} (h : wp B c Q σ) :
    wp B c (fun τ k => Q τ k ∧ Frame c σ τ) σ := by
  obtain ⟨τ, k, hbs, hq⟩ := h; exact ⟨τ, k, hbs, hq, Frame.of_bigStepB hbs⟩

/-- The usual entry point: prove the VC of `c` for "cost at most `T`, and `Post` given the
frame", and get the stage statement `∃ τ, Run B c σ τ T ∧ Post τ`. -/
theorem run_of_vc {B : ℕ} {c : Com} {σ : Env} {T : ℕ} {Post : Env → Prop}
    (h : vc B c (fun τ k => k ≤ T ∧ (Frame c σ τ → Post τ)) σ) :
    ∃ τ, Run B c σ τ T ∧ Post τ := by
  obtain ⟨τ, k, hbs, hk, hp⟩ := vc_sound h
  exact ⟨τ, ⟨k, hk, hbs⟩, hp (Frame.of_bigStepB hbs)⟩

/-! ## Black-box calls -/

theorem vc_of_run {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} {Q : Env → ℕ → Prop}
    (h : Run B c σ τ K) (hQ : ∀ k ≤ K, Q τ k) : vc B c Q σ :=
  vc_complete (wp_of_run h hQ)

/-- Use a verified sub-program through its specification only. The caller gets an
arbitrary final state satisfying the spec, together with the frame of the call. -/
theorem vc_spec {B : ℕ} {c : Com} {σ : Env} {K : ℕ} {P : Env → Prop} {Q : Env → ℕ → Prop}
    (h : ∃ τ, Run B c σ τ K ∧ P τ) (hQ : ∀ τ k, P τ → Frame c σ τ → k ≤ K → Q τ k) :
    vc B c Q σ := by
  obtain ⟨τ, hr, hp⟩ := h
  exact vc_of_run hr fun k hk => hQ τ k hp (Frame.of_run hr) hk

/-! ## Hoare triples with cost -/

/-- `{P} c {Q}` with cost bound `t`: from every `σ` with `P σ`, `c` terminates in some
`τ` with `Q σ τ` at cost at most `t σ`, every value below `B`. -/
def Triple (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (t : Env → ℕ) : Prop :=
  ∀ σ, P σ → wp B c (fun τ k => k ≤ t σ ∧ Q σ τ) σ

/-- **Soundness of triples with respect to `Run`.** -/
theorem Triple.sound {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop}
    {t : Env → ℕ} (h : Triple B P c Q t) {σ : Env} (hP : P σ) :
    ∃ τ, Run B c σ τ (t σ) ∧ Q σ τ :=
  wp.run (h σ hP)

/-- A triple is proved by its verification conditions. -/
theorem Triple.of_vc {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop}
    {t : Env → ℕ} (h : ∀ σ, P σ → vc B c (fun τ k => k ≤ t σ ∧ Q σ τ) σ) : Triple B P c Q t :=
  fun σ hP => vc_sound (h σ hP)

/-- The end-to-end soundness theorem of the calculus: verification conditions of `c`
imply the `Run` statement. -/
theorem vcgen_sound {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop}
    {t : Env → ℕ} (h : ∀ σ, P σ → vc B c (fun τ k => k ≤ t σ ∧ Q σ τ) σ) {σ : Env}
    (hP : P σ) : ∃ τ, Run B c σ τ (t σ) ∧ Q σ τ :=
  (Triple.of_vc h).sound hP

theorem Triple.of_run {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop}
    {t : Env → ℕ} (h : ∀ σ, P σ → ∃ τ, Run B c σ τ (t σ) ∧ Q σ τ) : Triple B P c Q t := by
  intro σ hP
  obtain ⟨τ, hr, hq⟩ := h σ hP
  exact wp_of_run hr fun k hk => ⟨hk, hq⟩

/-- Use a triple as a black box inside a VC. -/
theorem vc_triple {B : ℕ} {P : Env → Prop} {c : Com} {R : Env → Env → Prop}
    {t : Env → ℕ} {Q : Env → ℕ → Prop} {σ : Env} (h : Triple B P c R t) (hP : P σ)
    (hQ : ∀ τ k, R σ τ → Frame c σ τ → k ≤ t σ → Q τ k) : vc B c Q σ :=
  vc_spec (h.sound hP) hQ

theorem Triple.conseq {B : ℕ} {P P' : Env → Prop} {c : Com} {Q Q' : Env → Env → Prop}
    {t t' : Env → ℕ} (h : Triple B P c Q t) (hP : ∀ σ, P' σ → P σ)
    (hQ : ∀ σ τ, P' σ → Q σ τ → Q' σ τ) (ht : ∀ σ, P' σ → t σ ≤ t' σ) :
    Triple B P' c Q' t' := by
  intro σ hσ
  exact wp_mono (h σ (hP σ hσ)) fun τ k ⟨hk, hq⟩ => ⟨hk.trans (ht σ hσ), hQ σ τ hσ hq⟩

/-- Sequential composition of triples; the cost of the second part may depend on the
intermediate state. -/
theorem Triple.seq {B : ℕ} {P : Env → Prop} {R : Env → Env → Prop} {c d : Com}
    {Q : Env → Env → Prop} {t u T : Env → ℕ}
    (h1 : Triple B P c R t) (h2 : ∀ σ, P σ → Triple B (R σ) d (fun _ ρ => Q σ ρ) u)
    (hT : ∀ σ τ, P σ → R σ τ → t σ + u τ ≤ T σ) : Triple B P (.seq c d) Q T := by
  intro σ hσ
  obtain ⟨τ, k, hbs, hk, hr⟩ := h1 σ hσ
  obtain ⟨ρ, k', hbs', hk', hq⟩ := h2 σ hσ τ hr
  exact ⟨ρ, k + k', .seq hbs hbs', by have := hT σ τ hσ hr; omega, hq⟩

/-! ## Loop rules -/

/-- Amortised loop rule: invariant `I`, potential `Φ` paying for each iteration. -/
theorem wp_while {B : ℕ} {b : Cond} {c : Com} {Q : Env → ℕ → Prop} {σ : Env}
    (I : Env → Prop) (Φ : Env → ℕ) (hI : I σ)
    (hdef : ∀ ρ, I ρ → Frame (.while b c) σ ρ → OkC B ρ b)
    (hstep : ∀ ρ, I ρ → Frame (.while b c) σ ρ → condv ρ b = true →
      vc B c (fun ρ' k => I ρ' ∧ 1 + b.size + k + Φ ρ' ≤ Φ ρ) ρ)
    (hexit : ∀ ρ k, I ρ → Frame (.while b c) σ ρ → condv ρ b = false →
      k + Φ ρ ≤ Φ σ + 1 + b.size → Q ρ k) :
    wp B (.while b c) Q σ := by
  obtain ⟨τ, K, hrun, ⟨hIτ, hfr⟩, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := b) (c := c)
      (fun ρ => I ρ ∧ Frame (.while b c) σ ρ) Φ
      (fun ρ h => ⟨_, evalB_cond_of_Ok (hdef ρ h.1 h.2)⟩)
      (fun ρ h ht => by
        have hc : condv ρ b = true := by
          have := evalB_cond_of_Ok (hdef ρ h.1 h.2); rw [ht] at this
          exact (Option.some.inj this).symm
        obtain ⟨ρ', k, hbs, hI', hpay⟩ := vc_sound (hstep ρ h.1 h.2 hc)
        exact ⟨ρ', k, Run.of_bigStepB hbs, ⟨hI', h.2.loop (Frame.of_bigStepB hbs)⟩, hpay⟩)
      ⟨hI, Frame.refl _ _⟩
  have hc : condv τ b = false := by
    have := evalB_cond_of_Ok (hdef τ hIτ hfr); rw [hfalse] at this
    exact (Option.some.inj this).symm
  obtain ⟨k, hk, hbs⟩ := hrun
  exact ⟨τ, k, hbs, hexit τ k hIτ hfr hc (by omega)⟩

/-- Counted loop rule: invariant `I`, variant `V`, per-iteration cost `P`. -/
theorem wp_while_count {B : ℕ} {b : Cond} {c : Com} {Q : Env → ℕ → Prop} {σ : Env}
    (I : Env → Prop) (V : Env → ℕ) (P : ℕ) (hI : I σ)
    (hdef : ∀ ρ, I ρ → Frame (.while b c) σ ρ → OkC B ρ b)
    (hstep : ∀ ρ, I ρ → Frame (.while b c) σ ρ → condv ρ b = true →
      vc B c (fun ρ' k => I ρ' ∧ V ρ' < V ρ ∧ k ≤ P) ρ)
    (hexit : ∀ ρ k, I ρ → Frame (.while b c) σ ρ → condv ρ b = false →
      k ≤ (1 + b.size + P) * V σ + 1 + b.size → Q ρ k) :
    wp B (.while b c) Q σ := by
  obtain ⟨τ, hrun, ⟨hIτ, hfr⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := b) (c := c)
      (fun ρ => I ρ ∧ Frame (.while b c) σ ρ) V P
      (fun ρ h => ⟨_, evalB_cond_of_Ok (hdef ρ h.1 h.2)⟩)
      (fun ρ h ht => by
        have hc : condv ρ b = true := by
          have := evalB_cond_of_Ok (hdef ρ h.1 h.2); rw [ht] at this
          exact (Option.some.inj this).symm
        obtain ⟨ρ', k, hbs, hI', hV, hk⟩ := vc_sound (hstep ρ h.1 h.2 hc)
        exact ⟨ρ', ⟨k, hk, hbs⟩, ⟨hI', h.2.loop (Frame.of_bigStepB hbs)⟩, hV⟩)
      ⟨hI, Frame.refl _ _⟩
  have hc : condv τ b = false := by
    have := evalB_cond_of_Ok (hdef τ hIτ hfr); rw [hfalse] at this
    exact (Option.some.inj this).symm
  obtain ⟨k, hk, hbs⟩ := hrun
  exact ⟨τ, k, hbs, hexit τ k hIτ hfr hc hk⟩

/-- The cost bound of a counted loop `while idx < E do body` with `n` iterations of
cost at most `P` each. -/
def forCost (E : Expr) (P n : ℕ) : ℕ := (3 + E.size + P) * n + 3 + E.size

/-- **Counted loop rule.** The loop `while idx < E do body` is entered with `idx = 0`;
`E` evaluates to `n` throughout; the body moves the invariant from `i` to `i + 1` and
increments `idx`. The rule tracks `idx` and the frame itself. -/
theorem wp_for {B : ℕ} {idx : String} {E : Expr} {body : Com} {Q : Env → ℕ → Prop}
    {σ : Env} (n P : ℕ) (Inv : ℕ → Env → Prop)
    (hn : n < B) (hσ : σ.vars idx = 0) (h0 : Inv 0 σ)
    (hE : ∀ i ≤ n, ∀ ρ, Inv i ρ → ρ.vars idx = i →
      Frame (.while (.lt (.var idx) E) body) σ ρ → Ok B ρ E ∧ nomv ρ E = n)
    (hstep : ∀ i < n, ∀ ρ, Inv i ρ → ρ.vars idx = i →
      Frame (.while (.lt (.var idx) E) body) σ ρ →
      vc B body (fun ρ' k => Inv (i + 1) ρ' ∧ ρ'.vars idx = i + 1 ∧ k ≤ P) ρ)
    (hexit : ∀ ρ k, Inv n ρ → ρ.vars idx = n →
      Frame (.while (.lt (.var idx) E) body) σ ρ → k ≤ forCost E P n → Q ρ k) :
    wp B (.while (.lt (.var idx) E) body) Q σ := by
  refine wp_while_count (fun ρ => ∃ i ≤ n, Inv i ρ ∧ ρ.vars idx = i)
    (fun ρ => n - ρ.vars idx) P ⟨0, Nat.zero_le _, h0, hσ⟩ ?_ ?_ ?_
  · rintro ρ ⟨i, hi, hInv, hidx⟩ hfr
    exact OkC_lt.2 ⟨Ok_var.2 (by omega), (hE i hi ρ hInv hidx hfr).1⟩
  · rintro ρ ⟨i, hi, hInv, hidx⟩ hfr hc
    have hval := (hE i hi ρ hInv hidx hfr).2
    have hlt : i < n := by
      simp only [condv_lt, nomv_var, hidx, hval, decide_eq_true_eq] at hc; exact hc
    exact vc_mono (hstep i hlt ρ hInv hidx hfr) fun ρ' k ⟨h1, h2, h3⟩ =>
      ⟨⟨i + 1, hlt, h1, h2⟩, by show n - ρ'.vars idx < n - ρ.vars idx; omega, h3⟩
  · rintro ρ k ⟨i, hi, hInv, hidx⟩ hfr hc hk
    have hval := (hE i hi ρ hInv hidx hfr).2
    have hge : ¬ i < n := by
      simp only [condv_lt, nomv_var, hidx, hval, decide_eq_false_iff_not] at hc; exact hc
    obtain rfl : i = n := by omega
    refine hexit ρ k hInv hidx hfr (le_trans hk (le_of_eq ?_))
    simp only [hσ, Nat.sub_zero, size_condLt, size_var, forCost]
    ring

/-- `wp_for` for the common bound `idx < cnt` with `cnt` a register the loop never
writes. -/
theorem wp_for_var {B : ℕ} {idx cnt : String} {body : Com} {Q : Env → ℕ → Prop}
    {σ : Env} (n P : ℕ) (Inv : ℕ → Env → Prop)
    (hn : n < B) (hσ : σ.vars idx = 0) (hcnt : σ.vars cnt = n)
    (hw : cnt ∉ scalarWrites body) (h0 : Inv 0 σ)
    (hstep : ∀ i < n, ∀ ρ, Inv i ρ → ρ.vars idx = i →
      Frame (.while (.lt (.var idx) (.var cnt)) body) σ ρ →
      vc B body (fun ρ' k => Inv (i + 1) ρ' ∧ ρ'.vars idx = i + 1 ∧ k ≤ P) ρ)
    (hexit : ∀ ρ k, Inv n ρ → ρ.vars idx = n →
      Frame (.while (.lt (.var idx) (.var cnt)) body) σ ρ → k ≤ (P + 4) * n + 4 → Q ρ k) :
    wp B (.while (.lt (.var idx) (.var cnt)) body) Q σ := by
  refine wp_for n P Inv hn hσ h0 ?_ hstep ?_
  · intro i _ ρ _ _ hfr
    have hc : ρ.vars cnt = n := (hfr.vars cnt hw).trans hcnt
    exact ⟨Ok_var.2 (by omega), by simp [hc]⟩
  · intro ρ k h1 h2 h3 hk
    refine hexit ρ k h1 h2 h3 (le_trans hk (le_of_eq ?_))
    simp only [forCost, size_var]; ring

/-! ## Array segments -/

theorem getD_set_self' {l : List ℕ} {i v : ℕ} (h : i < l.length) : (l.set i v).getD i 0 = v := by
  simp [List.getD, List.getElem?_set_self h]

theorem getD_set_ne' {l : List ℕ} {i j v : ℕ} (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD, List.getElem?_set_ne h]

/-- `cur` holds `f k` at `base + k` for `k < i` and agrees with `orig` outside
`[base, base + i)`. A structure, so that `and_intros` does not split it. -/
structure SegInv (orig cur : List ℕ) (base i : ℕ) (f : ℕ → ℕ) : Prop where
  inside : ∀ k < i, cur.getD (base + k) 0 = f k
  outside : ∀ k, (k < base ∨ base + i ≤ k) → cur.getD k 0 = orig.getD k 0

theorem SegInv.zero (l : List ℕ) (base : ℕ) (f : ℕ → ℕ) : SegInv l l base 0 f :=
  ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- One store at `base + i` extends the segment. -/
theorem SegInv.step {orig cur : List ℕ} {base i : ℕ} {f : ℕ → ℕ}
    (h : SegInv orig cur base i f) (hlen : base + i < cur.length) {v : ℕ} (hv : v = f i) :
    SegInv orig (cur.set (base + i) v) base (i + 1) f := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hki : k = i
    · subst hki; rw [getD_set_self' hlen, hv]
    · rw [getD_set_ne' (by omega)]; exact h.inside k (by omega)
  · rw [getD_set_ne' (by omega)]; exact h.outside k (by omega)

end Mathproof.IMPAuto20261004
