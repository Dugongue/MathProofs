import Mathproof.Meta.Problem18CyclicPrimaryExclusion20260930
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/-!
# The actual simple-primary bridge for the Pfaffian spectral count

If the characteristic polynomial of a nonsingular alternating self-adjoint
block is `h^2`, cyclic isotropy rules out minimal polynomial `h^2`.
Irreducibility then forces the minimal polynomial to be `h`, so the block is
a two-dimensional module over `K[X]/(h)`.

The falsifier for this leaf is a block satisfying the displayed hypotheses
with `h(S) ≠ 0`. The proof constructs the resulting cyclic vector explicitly
through the PID module theorem and contradicts the audited cyclic-span
exclusion.
-/

namespace Mathproof.Problem18PfaffianSimplePrimary20260930

open scoped Polynomial
open Module
open Mathproof.Problem18CyclicPrimaryExclusion20260930

variable {K V : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- Evaluation on a vector, restricted to polynomials of degree below `n`. -/
noncomputable def cyclicEvalMap (S : Module.End K V) (v : V) (n : ℕ) :
    Polynomial.degreeLT K n →ₗ[K] V where
  toFun p := (Polynomial.aeval S p.1) v
  map_add' p q := by simp
  map_smul' c p := by simp

/-- A nonzero `h(S)` under `charpoly S = h^2` forces the full square to be
the minimal polynomial. -/
theorem minpoly_eq_sq_of_charpoly_eq_sq
    (S : Module.End K V) (h : K[X]) (hh : h.Monic)
    (hirr : Irreducible h) (hchar : S.charpoly = h ^ 2)
    (hne : Polynomial.aeval S h ≠ 0) :
    minpoly K S = h ^ 2 := by
  have hm_dvd : minpoly K S ∣ h ^ 2 := by
    rw [← hchar]
    exact LinearMap.minpoly_dvd_charpoly S
  have hnot : ¬minpoly K S ∣ h := by
    intro hdvd
    obtain ⟨a, ha⟩ := hdvd
    apply hne
    rw [ha, Polynomial.aeval_mul]
    simp
  obtain ⟨a, ha⟩ := hm_dvd
  have hh_dvd_m : h ∣ minpoly K S := by
    have hd : h ∣ minpoly K S * a := by
      rw [← ha]
      simpa only [pow_two] using dvd_mul_right h h
    rcases hirr.prime.dvd_mul.mp hd with hm | ha'
    · exact hm
    · obtain ⟨b, hb⟩ := ha'
      exfalso
      apply hnot
      refine ⟨b, ?_⟩
      apply mul_right_cancel₀ hirr.ne_zero
      calc
        h * h = h ^ 2 := by rw [pow_two]
        _ = minpoly K S * a := ha
        _ = minpoly K S * (h * b) := by rw [hb]
        _ = minpoly K S * b * h := by ac_rfl
  obtain ⟨c, hc⟩ := hh_dvd_m
  have hc_dvd_h : c ∣ h := by
    refine ⟨a, ?_⟩
    apply mul_left_cancel₀ hirr.ne_zero
    calc
      h * h = h ^ 2 := by rw [pow_two]
      _ = minpoly K S * a := ha
      _ = (h * c) * a := by rw [← hc]
      _ = h * (c * a) := by ac_rfl
  rcases (hirr.dvd_iff.mp hc_dvd_h) with hcu | hca
  · exfalso
    apply hnot
    rw [hc]
    exact hcu.mul_right_dvd.mpr (dvd_refl h)
  · apply Polynomial.eq_of_monic_of_associated (minpoly.monic (LinearMap.isIntegral S)) (hh.pow 2)
    rw [hc, pow_two]
    exact Associated.mul_left h hca.symm

/-- If the minimal polynomial equals the characteristic polynomial, the PID
cyclic-vector theorem produces a vector whose actual power span is all of
`V`. -/
theorem exists_cyclic_span_eq_top_of_minpoly_eq_charpoly
    (S : Module.End K V) (hmc : minpoly K S = S.charpoly) :
    ∃ v : V, Submodule.span K (Set.range fun i : ℕ => (S ^ i) v) = ⊤ := by
  letI : Module K[X] (Module.AEval' S) := inferInstance
  obtain ⟨x, hx⟩ :=
    Module.exists_ker_toSpanSingleton_eq_annihilator K[X] (Module.AEval' S)
  let v : V := (Module.AEval'.of S).symm x
  have hvx : Module.AEval'.of S v = x := (Module.AEval'.of S).apply_symm_apply x
  let L := cyclicEvalMap S v (minpoly K S).natDegree
  have hLinj : Function.Injective L := by
    intro p q hpq
    apply sub_eq_zero.mp
    apply Subtype.ext
    have hpzero : L (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hker :
        ((p - q : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X]) ∈
          LinearMap.ker
            (LinearMap.toSpanSingleton K[X] (Module.AEval' S) x) := by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      rw [← hvx]
      change ((p - q : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X]) •
          Module.AEval'.of S v = 0
      have hz := congrArg (Module.AEval'.of S) hpzero
      change ((p : K[X]) - (q : K[X])) • Module.AEval'.of S v = 0
      rw [sub_smul, ← Module.AEval.of_aeval_smul,
        ← Module.AEval.of_aeval_smul]
      simpa [L, cyclicEvalMap] using hz
    have hmem :
        ((p - q : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X]) ∈
          Ideal.span ({minpoly K S} : Set K[X]) := by
      rw [Polynomial.span_minpoly_eq_annihilator, ← hx]
      exact hker
    have hdvd : minpoly K S ∣
        ((p - q : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X]) := by
      simpa only [Ideal.mem_span_singleton] using hmem
    have hdeg :
        ((p - q : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X]).degree <
          (minpoly K S).degree := by
      have hpdeg := (p - q : Polynomial.degreeLT K (minpoly K S).natDegree).property
      rw [Polynomial.mem_degreeLT] at hpdeg
      simpa [Polynomial.degree_eq_natDegree (minpoly.monic (LinearMap.isIntegral S)).ne_zero] using hpdeg
    exact Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have hdim :
      Module.finrank K (Polynomial.degreeLT K (minpoly K S).natDegree) =
        Module.finrank K V := by
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis K (minpoly K S).natDegree), Fintype.card_fin,
      hmc, S.charpoly_natDegree]
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLinj
  refine ⟨v, eq_top_iff.mpr fun y _ => ?_⟩
  obtain ⟨p, hp⟩ := hLsurj y
  rw [← hp]
  change (Polynomial.aeval S
    ((p : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X])) v ∈
      Submodule.span K (Set.range fun i : ℕ => (S ^ i) v)
  exact aeval_mem_cyclic_span S v
    ((p : Polynomial.degreeLT K (minpoly K S).natDegree) : K[X])

/-- The simple Pfaffian primary block is annihilated by `h`, without an
assumed rational-canonical-form classification. -/
theorem aeval_irreducible_eq_zero_of_charpoly_eq_sq
    (B : LinearMap.BilinForm K V) (S : Module.End K V) (h : K[X])
    (hh : h.Monic) (hirr : Irreducible h)
    (hchar : S.charpoly = h ^ 2)
    (hB : B.IsAlt) (hNondeg : B.Nondegenerate)
    (hS : B.IsSelfAdjoint S) (hBS : ∀ v : V, B v (S v) = 0) :
    Polynomial.aeval S h = 0 := by
  by_contra hne
  have hmin := minpoly_eq_sq_of_charpoly_eq_sq S h hh hirr hchar hne
  obtain ⟨v, hv⟩ :=
    exists_cyclic_span_eq_top_of_minpoly_eq_charpoly S (hmin.trans hchar.symm)
  exact nondegenerate_cyclic_span_ne_top B S hB hNondeg hS hBS v hv

end Mathproof.Problem18PfaffianSimplePrimary20260930




