import Mathproof.Meta.Problem18PrimaryTraceBoundary20260930
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace Mathproof.Problem18PrimaryTraceCount20260930
open Classical
open Mathproof.Problem18PrimaryTraceBoundary20260930
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

noncomputable def scalarTraceForm (c : E) : LinearMap.BilinForm K E :=
  (Algebra.traceForm K E).comp (LinearMap.mulLeft K c) LinearMap.id

@[simp] theorem scalarTraceForm_apply (c x y : E) :
    scalarTraceForm (K := K) c x y = Algebra.trace K E (c*x*y) := rfl

theorem scalarTraceForm_balanced (c : E) : Balanced (scalarTraceForm (K := K) c) := by
  intro t x y
  simp only [scalarTraceForm_apply]
  congr 1
  ring

theorem scalarTraceForm_symmetric (c : E) : (scalarTraceForm (K := K) c).IsSymm := by
  constructor
  intro x y
  simp only [scalarTraceForm_apply]
  congr 1
  ring

theorem scalarTraceForm_nondegenerate (c : E) (hc : c ≠ 0) :
    (scalarTraceForm (K := K) c).Nondegenerate := by
  constructor
  · intro x hx
    have hcx : c*x=0 := (traceForm_nondegenerate K E).1 _ (by
      intro y
      exact hx y)
    exact (mul_eq_zero.mp hcx).resolve_left hc
  · intro y hy
    have hcy : c*y=0 := (traceForm_nondegenerate K E).2 _ (by
      intro x
      change Algebra.trace K E (x*(c*y))=0
      convert hy x using 1 <;> rw [scalarTraceForm_apply] <;> congr 1 <;> ring)
    exact (mul_eq_zero.mp hcy).resolve_left hc

@[simp] theorem scalarTraceForm_coefficient (c : E) :
    traceCoefficient (scalarTraceForm (K := K) c)=c := by
  apply trace_coefficient_ext (K := K)
  intro x
  rw [traceCoefficient_spec,scalarTraceForm_apply,mul_one]

abbrev BalancedNondegenerateForms :=
  {B : LinearMap.BilinForm K E // Balanced B ∧ B.Nondegenerate}

/-- A bijection of actual forms, not merely a classification up to isometry. -/
noncomputable def balancedNondegenerateEquiv :
    BalancedNondegenerateForms (K := K) (E := E) ≃ {c : E // c ≠ 0} where
  toFun B := ⟨traceCoefficient B.val, traceCoefficient_ne_zero B.val B.property.1 B.property.2⟩
  invFun c := ⟨scalarTraceForm c.val,scalarTraceForm_balanced c.val,
    scalarTraceForm_nondegenerate c.val c.property⟩
  left_inv B := by
    apply Subtype.ext
    ext x y
    exact (balanced_trace_representation B.val B.property.1 x y).symm
  right_inv c := by
    apply Subtype.ext
    exact scalarTraceForm_coefficient c.val

/-- Exact local form count for each simple ordinary symmetric primary block. -/
theorem balancedNondegenerate_card [Fintype E] :
    Nat.card (BalancedNondegenerateForms (K := K) (E := E)) = Fintype.card E-1 := by
  rw [Nat.card_congr (balancedNondegenerateEquiv (K := K) (E := E)),
    ← Nat.card_congr (unitsEquivNeZero (G₀ := E)),Nat.card_eq_fintype_card,Fintype.card_units]

end Mathproof.Problem18PrimaryTraceCount20260930
