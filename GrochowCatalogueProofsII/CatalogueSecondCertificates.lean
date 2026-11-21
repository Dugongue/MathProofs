import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic

open scoped BigOperators

namespace GrochowCatalogueSecond

theorem support_card_monomial_sum {I X R : Type*} [CommSemiring R]
    (s : Finset I) (e : I → X →₀ ℕ) (c : I → R) :
    (∑ i ∈ s, MvPolynomial.monomial (e i) (c i)).support.card ≤ s.card := by
  classical
  have h := MvPolynomial.support_sum
    (s := s) (f := fun i => MvPolynomial.monomial (e i) (c i))
  refine (Finset.card_le_card (t := s.image e) ?_).trans Finset.card_image_le
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (h hd)
  have equal : d = e i := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hdi)
  exact Finset.mem_image.mpr ⟨i, hi, equal.symm⟩

/-- A substitution whose monomial images are monomials cannot increase the
    number of terms of an expanded polynomial. Zero coefficients are allowed. -/
theorem sparse_substitution {X Y R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : MvPolynomial X R →+* MvPolynomial Y S)
    (h : ∀ (e : X →₀ ℕ) (c : R), ∃ (e' : Y →₀ ℕ) (c' : S),
      φ (MvPolynomial.monomial e c) = MvPolynomial.monomial e' c')
    (f : MvPolynomial X R) :
    (φ f).support.card ≤ f.support.card := by
  classical
  choose e c he using fun d : X →₀ ℕ => h d (MvPolynomial.coeff d f)
  conv_lhs =>
    rw [← MvPolynomial.support_sum_monomial_coeff f, map_sum]
  simp_rw [he]
  exact support_card_monomial_sum f.support e c

theorem relative_average_constant {I F : Type*} [Fintype I] [Field F]
    (v : I → F) (a : F) (h : ∀ i, v i = a)
    (hd : (Fintype.card I : F) ≠ 0) :
    (Fintype.card I : F)⁻¹ * (∑ i, v i) = a := by
  classical
  simp [h, hd]

theorem geometric_sum_double {R : Type*} [CommSemiring R] (h : R) (m : ℕ) :
    (∑ i ∈ Finset.range (m + m), h ^ i) =
      (∑ i ∈ Finset.range m, h ^ i) * (1 + h ^ m) := by
  rw [Finset.sum_range_add (fun i : ℕ => h ^ i) m m]
  simp only [pow_add, mul_add, mul_one, Finset.sum_mul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end GrochowCatalogueSecond

#print axioms GrochowCatalogueSecond.support_card_monomial_sum
#print axioms GrochowCatalogueSecond.sparse_substitution
#print axioms GrochowCatalogueSecond.relative_average_constant
#print axioms GrochowCatalogueSecond.geometric_sum_double
