import Mathproof.Meta.Problem18PfaffianSimplePrimary20260930
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-!
# The extension-field structure on a simple Pfaffian primary block

The quotient `E = K[X]/(h)` acts by polynomial evaluation at `S` once
`h(S)=0`. The scalar-tower dimension formula and
`charpoly S = h^2` then give `dim_E V = 2`.

A falsifier would be either failure of the quotient action to respect the
original K-action, or an E-dimension other than two under the displayed
characteristic-polynomial hypothesis.
-/

namespace Mathproof.Problem18PfaffianSimplePrimaryModule20260930

open scoped Polynomial
open Module

variable {K V : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Polynomial evaluation at S as a ring homomorphism into the endomorphism
ring; scalar endomorphisms commute with S. -/
noncomputable def simplePrimaryEvalRingHom (S : Module.End K V) :
    K[X] →+* Module.End K V :=
  Polynomial.eval₂RingHom' (algebraMap K (Module.End K V)) S
    (fun a => Algebra.commutes a S)

@[simp]
theorem simplePrimaryEvalRingHom_apply
    (S : Module.End K V) (p : K[X]) :
    simplePrimaryEvalRingHom S p =
      Polynomial.eval₂ (algebraMap K (Module.End K V)) S p := rfl

theorem simplePrimaryEvalRingHom_vanishes
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0) :
    ∀ p ∈ Ideal.span ({h} : Set K[X]), simplePrimaryEvalRingHom S p = 0 := by
  intro p hp
  rcases Ideal.mem_span_singleton.mp hp with ⟨q, rfl⟩
  rw [map_mul]
  have heval : simplePrimaryEvalRingHom S h = 0 := by
    change Polynomial.eval₂ (algebraMap K (Module.End K V)) S h = 0
    simpa only [Polynomial.aeval_def] using hzero
  rw [heval, zero_mul]

/-- Polynomial evaluation at S, descended through K[X]/(h) into the
(noncommutative) endomorphism ring. -/
noncomputable def simplePrimaryRingHom
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0) :
    AdjoinRoot h →+* Module.End K V :=
  Ideal.Quotient.lift (Ideal.span ({h} : Set K[X]))
    (simplePrimaryEvalRingHom S)
    (simplePrimaryEvalRingHom_vanishes S h hzero)

@[simp]
theorem simplePrimaryRingHom_mk
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0)
    (p : K[X]) :
    simplePrimaryRingHom S h hzero (AdjoinRoot.mk h p) =
      simplePrimaryEvalRingHom S p := rfl

@[simp]
theorem simplePrimaryRingHom_algebraMap
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0)
    (a : K) :
    simplePrimaryRingHom S h hzero (algebraMap K (AdjoinRoot h) a) =
      algebraMap K (Module.End K V) a := by
  rw [AdjoinRoot.algebraMap_eq]
  change simplePrimaryRingHom S h hzero
    (AdjoinRoot.mk h (Polynomial.C a)) = algebraMap K (Module.End K V) a
  rw [simplePrimaryRingHom_mk]
  change Polynomial.eval₂ (algebraMap K (Module.End K V)) S
    (Polynomial.C a) = algebraMap K (Module.End K V) a
  rw [Polynomial.eval₂_C]

@[simp]
theorem simplePrimaryRingHom_root
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0) :
    simplePrimaryRingHom S h hzero (AdjoinRoot.root h) = S := by
  change simplePrimaryRingHom S h hzero
    (AdjoinRoot.mk h Polynomial.X) = S
  rw [simplePrimaryRingHom_mk]
  change Polynomial.eval₂ (algebraMap K (Module.End K V)) S
    Polynomial.X = S
  rw [Polynomial.eval₂_X]
/-- The actual extension-field module structure supplied by `h(S)=0`. -/
noncomputable def simplePrimaryModule
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0) :
    Module (AdjoinRoot h) V :=
  Module.compHom V (simplePrimaryRingHom S h hzero)

/-- The induced extension action restricts to the original K-action. -/
noncomputable def simplePrimaryScalarTower
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0) :
    letI := simplePrimaryModule S h hzero
    IsScalarTower K (AdjoinRoot h) V := by
  letI := simplePrimaryModule S h hzero
  apply IsScalarTower.of_algebraMap_smul
  intro a v
  change (simplePrimaryRingHom S h hzero
    (algebraMap K (AdjoinRoot h) a)) v = a • v
  rw [simplePrimaryRingHom_algebraMap]
  rfl

/-- On the induced E-module, the residue class of X acts exactly as S. -/
theorem root_smul_eq
    (S : Module.End K V) (h : K[X]) (hzero : Polynomial.aeval S h = 0)
    (v : V) :
    letI := simplePrimaryModule S h hzero
    AdjoinRoot.root h • v = S v := by
  letI := simplePrimaryModule S h hzero
  change simplePrimaryRingHom S h hzero (AdjoinRoot.root h) v = S v
  rw [simplePrimaryRingHom_root]

/-- The simple-primary block has dimension exactly two over
`E = K[X]/(h)`. -/
theorem simplePrimary_finrank_eq_two
    (S : Module.End K V) (h : K[X]) (hirr : Irreducible h)
    (hzero : Polynomial.aeval S h = 0)
    (hchar : S.charpoly = h ^ 2) :
    letI : Fact (Irreducible h) := ⟨hirr⟩
    letI := simplePrimaryModule S h hzero
    Module.finrank (AdjoinRoot h) V = 2 := by
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI := simplePrimaryModule S h hzero
  letI : IsScalarTower K (AdjoinRoot h) V :=
    simplePrimaryScalarTower S h hzero
  have hE : Module.finrank K (AdjoinRoot h) = h.natDegree :=
    finrank_quotient_span_eq_natDegree
  have hV : Module.finrank K V = 2 * h.natDegree := by
    calc
      Module.finrank K V = S.charpoly.natDegree := S.charpoly_natDegree.symm
      _ = (h ^ 2).natDegree := by rw [hchar]
      _ = 2 * h.natDegree := by
        rw [Polynomial.natDegree_pow h 2]
  have htower := Module.finrank_mul_finrank K (AdjoinRoot h) V
  rw [hE, hV] at htower
  exact Nat.eq_of_mul_eq_mul_right hirr.natDegree_pos
    (by simpa [mul_comm] using htower)

end Mathproof.Problem18PfaffianSimplePrimaryModule20260930





