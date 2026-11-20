import Mathproof.Meta.IMPAutoCore20261004

/-!
# IMP automation: tactics

* `imp_vcgen [defs, facts]` turns a goal of one of these forms into arithmetic
  verification conditions:
  - `∃ τ, Run B c σ τ T ∧ Post τ` (via `run_of_vc`; the frame of `c` is then available
    inside `Post`);
  - `wp B c Q σ`;
  - `vc B c Q σ`.

  It unfolds the program (`defs`), computes the VC, evaluates every expression
  nominally, splits the conjunction, and closes what `omega` can. Left over are loops
  (`wp B (.while …) …`, for a loop rule), calls to opaque sub-programs (`vc B prog …`,
  for `vc_spec`/`vc_of_run`), branch implications, invariants, and arithmetic `omega`
  cannot see.
* `imp_eval [facts]` closes `e.evalB B σ = some v`, `b.evalB B σ = some r` and `Ok`
  goals on concrete syntax.
* `imp_frame [defs, facts]` closes `x ∉ scalarWrites c`, `a ∉ arrayWrites c`,
  `noRead c` and `c.NoWrite`:
  - first by a reflective Boolean checker decided by the kernel (concrete names; no
    `simp` on list or `Finset` membership, hence no elaborator blow-up);
  - then, for symbolic names, by unfolding and the `≠` hypotheses in context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mathproof.IMPAuto20261004

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Problem18IMPFieldLayout20261001

attribute [imp_simp] vars_setVar arrs_setVar inp_setVar out_setVar vars_setArr arrs_setArr
  inp_setArr out_setArr length_arrs_setArr size_lit size_var size_get size_bin size_add
  size_sub size_mul size_div size_and size_or size_xor size_shiftl size_shiftr size_condEq
  size_condLt Bop.apply_add Bop.apply_sub Bop.apply_mul Bop.apply_div Bop.apply_and
  Bop.apply_or Bop.apply_xor Bop.apply_shiftl Bop.apply_shiftr
  decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq beq_eq_false_iff_ne ne_eq
  if_true if_false eq_self_iff_true ite_true ite_false true_and and_true
  forall_const true_implies not_true_eq_false not_false_eq_true
  Expr.add_def Expr.sub_def Expr.mul_def Expr.div_def Expr.and_def Expr.or_def Expr.xor_def
  Expr.shiftl_def Expr.shiftr_def

/-! ## Reflective frame checkers -/

/-- Does `c` syntactically assign the scalar `x`? -/
def writesVar (x : String) : Com → Bool
  | .assign y _ => x == y
  | .read y => x == y
  | .seq c d => writesVar x c || writesVar x d
  | .ite _ c d => writesVar x c || writesVar x d
  | .while _ c => writesVar x c
  | .skip => false
  | .store _ _ _ => false
  | .write _ => false

/-- Does `c` syntactically store into the array `a`? -/
def writesArr (a : String) : Com → Bool
  | .store b _ _ => a == b
  | .seq c d => writesArr a c || writesArr a d
  | .ite _ c d => writesArr a c || writesArr a d
  | .while _ c => writesArr a c
  | .skip => false
  | .assign _ _ => false
  | .read _ => false
  | .write _ => false

/-- Does `c` contain a `read`? -/
def readsInp : Com → Bool
  | .read _ => true
  | .seq c d => readsInp c || readsInp d
  | .ite _ c d => readsInp c || readsInp d
  | .while _ c => readsInp c
  | .skip => false
  | .assign _ _ => false
  | .store _ _ _ => false
  | .write _ => false

/-- Does `c` contain a `write`? -/
def writesOut : Com → Bool
  | .write _ => true
  | .seq c d => writesOut c || writesOut d
  | .ite _ c d => writesOut c || writesOut d
  | .while _ c => writesOut c
  | .skip => false
  | .assign _ _ => false
  | .store _ _ _ => false
  | .read _ => false

theorem mem_scalarWrites_iff (x : String) (c : Com) :
    x ∈ scalarWrites c ↔ writesVar x c = true := by
  induction c with
  | skip => simp [scalarWrites, writesVar]
  | assign y e => simp [scalarWrites, writesVar]
  | store a i e => simp [scalarWrites, writesVar]
  | seq c d ihc ihd => simp [scalarWrites, writesVar, ihc, ihd]
  | ite b c d ihc ihd => simp [scalarWrites, writesVar, ihc, ihd]
  | «while» b c ih => simp [scalarWrites, writesVar, ih]
  | read y => simp [scalarWrites, writesVar]
  | write e => simp [scalarWrites, writesVar]

theorem mem_arrayWrites_iff (a : String) (c : Com) :
    a ∈ arrayWrites c ↔ writesArr a c = true := by
  induction c with
  | skip => simp [arrayWrites, writesArr]
  | assign y e => simp [arrayWrites, writesArr]
  | store b i e => simp [arrayWrites, writesArr]
  | seq c d ihc ihd => simp [arrayWrites, writesArr, ihc, ihd]
  | ite b c d ihc ihd => simp [arrayWrites, writesArr, ihc, ihd]
  | «while» b c ih => simp [arrayWrites, writesArr, ih]
  | read y => simp [arrayWrites, writesArr]
  | write e => simp [arrayWrites, writesArr]

theorem not_mem_scalarWrites {x : String} {c : Com} (h : writesVar x c = false) :
    x ∉ scalarWrites c := by
  rw [mem_scalarWrites_iff, h]; exact Bool.false_ne_true

theorem not_mem_arrayWrites {a : String} {c : Com} (h : writesArr a c = false) :
    a ∉ arrayWrites c := by
  rw [mem_arrayWrites_iff, h]; exact Bool.false_ne_true

theorem noRead_of_check {c : Com} (h : readsInp c = false) : noRead c := by
  induction c with
  | read y => simp [readsInp] at h
  | seq c d ihc ihd =>
      simp only [readsInp, Bool.or_eq_false_iff] at h; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd =>
      simp only [readsInp, Bool.or_eq_false_iff] at h; exact ⟨ihc h.1, ihd h.2⟩
  | «while» b c ih => simp only [readsInp] at h; exact ih h
  | skip => trivial
  | assign _ _ => trivial
  | store _ _ _ => trivial
  | write _ => trivial

theorem noWrite_of_check {c : Com} (h : writesOut c = false) : c.NoWrite := by
  induction c with
  | write e => simp [writesOut] at h
  | seq c d ihc ihd =>
      simp only [writesOut, Bool.or_eq_false_iff] at h; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd =>
      simp only [writesOut, Bool.or_eq_false_iff] at h; exact ⟨ihc h.1, ihd h.2⟩
  | «while» b c ih => simp only [writesOut] at h; exact ih h
  | skip => trivial
  | assign _ _ => trivial
  | store _ _ _ => trivial
  | read _ => trivial

/-- A register the program never writes keeps its value: the frame in one step. -/
theorem Frame.var_eq {c : Com} {σ ρ : Env} (hfr : Frame c σ ρ) {x : String}
    (hx : x ∉ scalarWrites c) {v : ℕ} (h : σ.vars x = v) : ρ.vars x = v :=
  (hfr.vars x hx).trans h

theorem Frame.arr_eq {c : Com} {σ ρ : Env} (hfr : Frame c σ ρ) {a : String}
    (ha : a ∉ arrayWrites c) : ρ.arrs a = σ.arrs a := hfr.arrs a ha

/-! ## Evaluation helpers -/

theorem evalB_eq_of {B : ℕ} {σ : Env} {e : Expr} {v : ℕ} (h : Ok B σ e) (hv : nomv σ e = v) :
    e.evalB B σ = some v := hv ▸ evalB_of_Ok h

theorem evalB_cond_eq_of {B : ℕ} {σ : Env} {b : Cond} {r : Bool} (h : OkC B σ b)
    (hv : condv σ b = r) : b.evalB B σ = some r := hv ▸ evalB_cond_of_Ok h

/-! ## Deciding equality of register names -/

open Lean Meta Simp in
/-- Decide `x = y` for *closed* string terms, such as register names given as
definitions (`fj`, `canonical.mem`): unfold both to literals and compare. The
disequality proof is the core literal-disequality certificate, which the kernel checks
by unfolding the names. Terms with free variables are left alone, so symbolic names are
handled by `≠` hypotheses instead. -/
simproc_decl impStrEq ((_ : String) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let a := e.appFn!.appArg!
  let b := e.appArg!
  if a.hasFVar || b.hasFVar || a.hasMVar || b.hasMVar then return .continue
  let some n := getStringValue? (← whnfD a) | return .continue
  let some m := getStringValue? (← whnfD b) | return .continue
  if n == m then
    let pf ← mkExpectedTypeHint (← mkEqRefl a) e
    return .done { expr := mkConst ``True, proof? := mkApp2 (mkConst ``eq_true) e pf }
  else
    let ne ← mkStringLitNeProof n m
    return .done { expr := mkConst ``False, proof? := mkApp2 (mkConst ``eq_false) e ne }

/-! ## Tactics -/

/-- Split conjunctions syntactically (reducible transparency only), so that defined
predicates and opaque `vc B prog Q σ` goals are never unfolded and split. -/
macro "imp_split" : tactic => `(tactic| repeat' (with_reducible refine And.intro ?_ ?_))

/-- Close what is left after unfolding: trivial goals, `≠` facts from hypotheses,
decidable closed facts. -/
macro "imp_close" : tactic => `(tactic| first
  | done | trivial | assumption | (exact Ne.symm (by assumption)) | omega | decide)

syntax (name := impFrame) "imp_frame" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| imp_frame) => `(tactic| imp_frame [Bool.false_or])
  | `(tactic| imp_frame [$ls,*]) => `(tactic| first
      | (apply not_mem_scalarWrites; decide +kernel)
      | (apply not_mem_arrayWrites; decide +kernel)
      | (apply noRead_of_check; decide +kernel)
      | (apply noWrite_of_check; decide +kernel)
      | (apply not_mem_scalarWrites; simp only [writesVar, Bool.or_false, Bool.false_or, Bool.or_eq_false_iff,
           beq_eq_false_iff_ne, ne_eq, and_self, impStrEq, $ls,*] <;> (try imp_split) <;>
           imp_close)
      | (apply not_mem_arrayWrites; simp only [writesArr, Bool.or_false, Bool.false_or, Bool.or_eq_false_iff,
           beq_eq_false_iff_ne, ne_eq, and_self, impStrEq, $ls,*] <;> (try imp_split) <;>
           imp_close)
      | (apply noRead_of_check; simp only [readsInp, Bool.or_false, Bool.false_or, $ls,*])
      | (apply noWrite_of_check; simp only [writesOut, Bool.or_false, Bool.false_or, $ls,*]))

syntax (name := impEval) "imp_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| imp_eval) => `(tactic| (
      (first | apply evalB_eq_of | apply evalB_cond_eq_of | skip) <;>
      (try simp only [imp_simp, impStrEq]) <;> (try imp_split) <;> (try omega)))
  | `(tactic| imp_eval [$ls,*]) => `(tactic| (
      (first | apply evalB_eq_of | apply evalB_cond_eq_of | skip) <;>
      (try simp only [imp_simp, impStrEq, $ls,*]) <;> (try imp_split) <;> (try omega)))

syntax (name := impVcgen) "imp_vcgen" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| imp_vcgen) => `(tactic| (
      (first | apply run_of_vc | apply vc_sound | skip) <;>
      (simp only [vc, imp_simp, impStrEq]) <;> (try imp_split) <;> (try omega)))
  | `(tactic| imp_vcgen [$ls,*]) => `(tactic| (
      (first | apply run_of_vc | apply vc_sound | skip) <;>
      (simp only [vc, imp_simp, impStrEq, $ls,*]) <;> (try imp_split) <;> (try omega)))

/-- Normalise update chains, nominal values and names in the goal (no splitting). -/
syntax (name := impNorm) "imp_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| imp_norm) => `(tactic| simp only [imp_simp, impStrEq])
  | `(tactic| imp_norm [$ls,*]) => `(tactic| simp only [imp_simp, impStrEq, $ls,*])

end Mathproof.IMPAuto20261004
