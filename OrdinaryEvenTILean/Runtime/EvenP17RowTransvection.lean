import EvenP16InvertCutBank
import Mathproof.Meta.P15RecogIMPRank20261007
import Mathlib.LinearAlgebra.Matrix.Transvection

set_option autoImplicit false

namespace EvenTI.P17Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15RecogIMPRank20261007 (qN_valid)

variable {K : Type} [Field K] [Fintype K]

noncomputable def rowTransvection (F : FieldPresentation K) : Com :=
  axpyLoop (fieldMacros F) qN (.var qN.u) (.var qN.w)

noncomputable def rowTransvectionCost (F : FieldPresentation K) (n : ℕ) : ℕ :=
  axpyCost (fieldMacros F) (.var qN.u) (.var qN.w) n

private theorem rowEnd_le {m n : ℕ} (a : Fin m) :
    a.val*n+n ≤ m*n := by
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right n (show a.val+1 ≤ m from a.isLt)

private theorem rowSep {m n : ℕ} {a b : Fin m} (h : a.val < b.val) :
    a.val*n+n ≤ b.val*n := by
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right n (show a.val+1 ≤ b.val from h)

/-- The live row update implements the exact elementary multiplication in
order-four diagonalization. Field slot 2 holds the negated coefficient. -/
theorem rowTransvection_run (F : FieldPresentation K)
    {B Sn m n base : ℕ} {s : Env} (A : Matrix (Fin m) (Fin n) K)
    (i j : Fin m) (hij : i ≠ j) (c : K) (hSlots : Slots F canonical qN.WS Sn B s)
    (hbase : 5 ≤ base) (hfit : base+m*n ≤ Sn)
    (hN : s.vars qN.N=n) (hI : s.vars qN.u=base+i.val*n) (hJ : s.vars qN.w=base+j.val*n)
    (hCoeff : val F canonical qN.WS s 2 = -c)
    (hRead : ∀ a b, val F canonical qN.WS s (base+a.val*n+b.val)=A a b) :
    ∃ t, Run B (rowTransvection F) s t (rowTransvectionCost F n) ∧
      Slots F canonical qN.WS Sn B t ∧
      (∀ a b, val F canonical qN.WS t (base+a.val*n+b.val) =
        (Matrix.transvection i j c * A) a b) ∧
      (∀ x < Sn, (x < base+i.val*n ∨ base+i.val*n+n ≤ x) → x ≠ 3 → x ≠ 4 →
        val F canonical qN.WS t x = val F canonical qN.WS s x) ∧
      (∀ x, x ∉ regNames canonical → x ≠ qN.j → t.vars x=s.vars x) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hWord := hSlots.slots_word
  have hi := rowEnd_le (n:=n) i
  have hj := rowEnd_le (n:=n) j
  have el (name : String) (v : ℕ) (h : s.vars name=v) (hv : v<B) :
      (Expr.var name).evalB B s=some v := by
    rw [←h]
    exact evalB_var (h ▸ hv)
  have hSep : base+i.val*n+n ≤ base+j.val*n ∨ base+j.val*n+n ≤ base+i.val*n := by
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h|h
    · have hb := rowSep (n:=n) h
      omega
    · have hb := rowSep (n:=n) h
      omega
  obtain ⟨t,r,hS,hAt,hOff,hVars,_,_,hIn,hOut⟩ := axpy_run (fieldMacros F) qN qN_valid
    (.var qN.u) (.var qN.w) (by change qN.u ∈ qN.fixed; decide) (by change qN.w ∈ qN.fixed; decide) hSlots (el _ _ hI (by omega))
    (el _ _ hJ (by omega)) hN (by omega) (by omega) (by omega) (by omega) hSep
  refine ⟨t,r,hS,?_,hOff,hVars,hIn,hOut⟩
  intro a b
  by_cases ha : a=i
  · subst a
    rw [Matrix.transvection_mul_apply_same,hAt _ b.isLt,hCoeff,hRead,hRead]
    ring
  · rw [Matrix.transvection_mul_apply_of_ne i j a b ha c A]
    have hb := b.isLt
    apply (hOff _ (by have h := rowEnd_le (n:=n) a; omega) ?_ (by omega) (by omega)).trans (hRead _ _)
    rcases lt_or_gt_of_ne (show a.val ≠ i.val from fun h => ha (Fin.ext h)) with h|h
    · have hh := rowSep (n:=n) h
      omega
    · have hh := rowSep (n:=n) h
      omega

#print axioms rowTransvection_run
end EvenTI.P17Execution
