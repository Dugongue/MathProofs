import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Expand

open scoped BigOperators

namespace FrobeniusDescent

/-- Homogeneous substitution acts by entrywise Frobenius on the pure-power space. -/
theorem linearForm_pow {ι R : Type*} [Fintype ι] [CommSemiring R] (p : ℕ)
    [ExpChar R p] (a : ι → R) :
    (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) ^ p =
      ∑ j, MvPolynomial.C (a j ^ p) * MvPolynomial.X j ^ p := by
  rw [sum_pow_char]
  simp_rw [mul_pow, ← MvPolynomial.C_pow]

/-- Composing the local linking identities around a complete chain. -/
theorem chain_pow {R : Type*} [Monoid R] (p : ℕ) (a : ℕ) (g : ℕ → R)
    (step : ∀ i < a, g (i + 1) = g i ^ p) : g a = g 0 ^ (p ^ a) := by
  induction a with
  | zero => simp
  | succ i ih =>
    rw [step i (Nat.lt_succ_self i), ih (fun j hj => step j (Nat.lt_succ_of_lt hj)),
      ← pow_mul, pow_succ]

/-- Over any extension of a finite field the fixed coordinates are exactly base scalars. -/
theorem finiteField_fixed {K L : Type*} [Field K] [Fintype K] [Field L]
    (f : K →+* L) (x : L) : x ^ Fintype.card K = x ↔ ∃ y : K, f y = x := by
  let q := Fintype.card K
  let P : Polynomial K := Polynomial.X ^ q - Polynomial.X
  have hq : 1 < q := Fintype.one_lt_card
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hroots : P.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X K
  have hcard : P.roots.card = P.natDegree := by rw [hroots, hdeg]; rfl
  have hm : P.map f = (Polynomial.X ^ q - Polynomial.X : Polynomial L) := by simp [P]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree f.injective hcard
  have hmap_ne : P.map f ≠ 0 := Polynomial.map_ne_zero hP
  calc
    x ^ q = x ↔ Polynomial.IsRoot (P.map f) x := by
      simp [Polynomial.IsRoot, hm, sub_eq_zero]
    _ ↔ ∃ y : K, f y = x := by
      rw [← Polynomial.mem_roots hmap_ne, ← hmap, Multiset.mem_map, hroots]
      simp

end FrobeniusDescent
