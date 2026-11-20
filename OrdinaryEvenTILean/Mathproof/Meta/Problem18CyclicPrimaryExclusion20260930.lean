import Mathproof.Meta.Problem18CyclicIsotropy20260930
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! Structural bridge for the simple-primary classification in the explicit
Pfaffian handoff. No elementary-divisor or counting assertion is assumed here. -/
namespace Mathproof.Problem18CyclicPrimaryExclusion20260930

open scoped Polynomial
open Mathproof.Problem18CyclicIsotropy20260930

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Polynomial iterates belong to the actual span of the power iterates. -/
theorem aeval_mem_cyclic_span (S : Module.End K V) (v : V) (p : K[X]) :
    (Polynomial.aeval S p) v ∈
      Submodule.span K (Set.range fun i : ℕ => (S ^ i) v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.aeval_add, LinearMap.add_apply] using
        Submodule.add_mem _ hp hq
  | monomial i a =>
      have hi : (S ^ i) v ∈
          Submodule.span K (Set.range fun j : ℕ => (S ^ j) v) :=
        Submodule.subset_span ⟨i, rfl⟩
      simpa only [Polynomial.aeval_monomial, ← Algebra.smul_def,
        LinearMap.smul_apply] using Submodule.smul_mem _ a hi

/-- Polynomial cyclic vectors pair to zero. This supplies B(a u,u)=0
when the extension-field action is represented by polynomials in S. -/
theorem selfAdjoint_cyclic_polynomials_zero
    (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hB : B.IsAlt) (hS : B.IsSelfAdjoint S)
    (hBS : ∀ v : V, B v (S v) = 0) (v : V) (p q : K[X]) :
    B ((Polynomial.aeval S p) v) ((Polynomial.aeval S q) v) = 0 := by
  exact selfAdjoint_cyclic_span_isotropic B S hB hS hBS v _ _
    (aeval_mem_cyclic_span S v p) (aeval_mem_cyclic_span S v q)

/-- A nonzero nonsingular alternating block cannot be cyclic when both B
and B(-,S-) are alternating. Applied to a primary restriction, this excludes
an elementary divisor h² occupying the entire block. -/
theorem nondegenerate_cyclic_span_ne_top [Nontrivial V]
    (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hB : B.IsAlt) (hNondeg : B.Nondegenerate) (hS : B.IsSelfAdjoint S)
    (hBS : ∀ v : V, B v (S v) = 0) (v : V) :
    Submodule.span K (Set.range fun i : ℕ => (S ^ i) v) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply hNondeg.1 x
  intro y
  apply selfAdjoint_cyclic_span_isotropic B S hB hS hBS v x y
  · rw [htop]
    exact Submodule.mem_top
  · rw [htop]
    exact Submodule.mem_top

end Mathproof.Problem18CyclicPrimaryExclusion20260930
