import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Finite.Basic

/-! The projector identities from the MathProof P15 field-frame proof and
the scalar-emission routine from Problem 1.7, with narrow imports. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace EvenTI.CellProducer

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {A : Type*} [CommRing A] [Algebra K A]


theorem prod_univ_X_sub_C : ∏ a : K, (X - C a) = (X ^ Fintype.card K - X : K[X]) := by
  have hm : (X ^ Fintype.card K - X : K[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast Fintype.one_lt_card
  have hcard : Multiset.card (X ^ Fintype.card K - X : K[X]).roots =
      (X ^ Fintype.card K - X : K[X]).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq K
      Fintype.one_lt_card]
    rfl
  have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  rw [FiniteField.roots_X_pow_card_sub_X] at this
  exact this

theorem aeval_eq_of_eval_eq (s : A) (Rt : Finset K) (hR : aeval s (∏ μ ∈ Rt, (X - C μ)) = 0)
    (q1 q2 : K[X]) (h : ∀ μ ∈ Rt, eval μ q1 = eval μ q2) : aeval s q1 = aeval s q2 := by
  classical
  have hdvd : (∏ μ ∈ Rt, (X - C μ)) ∣ q1 - q2 := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact pairwise_coprime_X_sub_C (K := K) (s := (id : K → K)) Function.injective_id hab
    · intro μ hμ
      rw [dvd_iff_isRoot, IsRoot.def, eval_sub, h μ hμ, sub_self]
  obtain ⟨t, ht⟩ := hdvd
  rw [← sub_eq_zero, ← map_sub, ht, map_mul, hR, zero_mul]

theorem lagrange_split (s : A) (Rt : Finset K) (hR : aeval s (∏ μ ∈ Rt, (X - C μ)) = 0)
    (e : A) (he : e * e = e) :
    (∑ l ∈ Rt, e * aeval s (Lagrange.basis Rt id l) = e) ∧
    (∀ l ∈ Rt, ∀ l' ∈ Rt, l ≠ l' →
      (e * aeval s (Lagrange.basis Rt id l)) * (e * aeval s (Lagrange.basis Rt id l')) = 0) ∧
    (∀ l ∈ Rt, (e * aeval s (Lagrange.basis Rt id l)) * (e * aeval s (Lagrange.basis Rt id l)) =
      e * aeval s (Lagrange.basis Rt id l)) ∧
    (∀ l ∈ Rt, s * (e * aeval s (Lagrange.basis Rt id l)) =
      algebraMap K A l * (e * aeval s (Lagrange.basis Rt id l))) := by
  classical
  have hinj : Set.InjOn (id : K → K) Rt := Function.injective_id.injOn
  have heval : ∀ l ∈ Rt, ∀ μ ∈ Rt, eval μ (Lagrange.basis Rt id l) = if μ = l then 1 else 0 := by
    intro l hl μ hμ
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hinj hl
    · exact Lagrange.eval_basis_of_ne (v := (id : K → K)) (s := Rt) (Ne.symm h) hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases Rt.eq_empty_or_nonempty with h0 | hne
    · subst h0
      simp only [Finset.prod_empty, map_one] at hR
      have : Subsingleton A := subsingleton_of_zero_eq_one hR.symm
      exact Subsingleton.elim _ _
    · rw [← Finset.mul_sum, ← map_sum, Lagrange.sum_basis hinj hne, map_one, mul_one]
  · intro l hl l' hl' hll
    have : aeval s (Lagrange.basis Rt id l * Lagrange.basis Rt id l') = aeval s (0 : K[X]) := by
      apply aeval_eq_of_eval_eq s Rt hR
      intro μ hμ
      rw [eval_mul, heval l hl μ hμ, heval l' hl' μ hμ, eval_zero]
      split_ifs with h1 h2 <;> simp_all
    rw [map_mul, map_zero] at this
    calc e * aeval s (Lagrange.basis Rt id l) * (e * aeval s (Lagrange.basis Rt id l'))
        = (e * e) * (aeval s (Lagrange.basis Rt id l) * aeval s (Lagrange.basis Rt id l')) := by ring
      _ = 0 := by rw [this, mul_zero]
  · intro l hl
    have : aeval s (Lagrange.basis Rt id l * Lagrange.basis Rt id l) =
        aeval s (Lagrange.basis Rt id l) := by
      apply aeval_eq_of_eval_eq s Rt hR
      intro μ hμ
      rw [eval_mul, heval l hl μ hμ]
      split_ifs <;> simp
    rw [map_mul] at this
    calc e * aeval s (Lagrange.basis Rt id l) * (e * aeval s (Lagrange.basis Rt id l))
        = (e * e) * (aeval s (Lagrange.basis Rt id l) * aeval s (Lagrange.basis Rt id l)) := by ring
      _ = e * aeval s (Lagrange.basis Rt id l) := by rw [he, this]
  · intro l hl
    have : aeval s (X * Lagrange.basis Rt id l) = aeval s (C l * Lagrange.basis Rt id l) := by
      apply aeval_eq_of_eval_eq s Rt hR
      intro μ hμ
      rw [eval_mul, eval_mul, eval_X, eval_C, heval l hl μ hμ]
      split_ifs with h <;> simp [h]
    rw [map_mul, map_mul, aeval_X, aeval_C] at this
    calc s * (e * aeval s (Lagrange.basis Rt id l)) = e * (s * aeval s (Lagrange.basis Rt id l)) := by
          ring
      _ = algebraMap K A l * (e * aeval s (Lagrange.basis Rt id l)) := by rw [this]; ring

noncomputable def selector (c : K) : K[X] := 1 - (X - C c) ^ (Fintype.card K - 1)

theorem selector_eval (c x : K) : (selector c).eval x = if x = c then 1 else 0 := by
  have hq : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  unfold selector
  rw [eval_sub, eval_one, eval_pow, eval_sub, eval_X, eval_C]
  by_cases h : x = c
  · simp [h, Nat.ne_of_gt hq]
  · rw [if_neg h, FiniteField.pow_card_sub_one_eq_one (x-c) (sub_ne_zero.mpr h), sub_self]

def projector (x : A) (c : K) : A :=
  1 - (x - algebraMap K A c) ^ (Fintype.card K - 1)

theorem projector_eq_aeval (x : A) (c : K) :
    projector x c = aeval x (selector c) := by
  simp [projector, selector]

theorem projector_lagrange (x : A) (R : Finset K)
    (hR : aeval x (∏ c ∈ R, (X - C c)) = 0)
    (c : K) (hc : c ∈ R) : projector x c = aeval x (Lagrange.basis R id c) := by
  rw [projector_eq_aeval]
  apply aeval_eq_of_eval_eq x R hR
  intro d hd
  rw [selector_eval]
  by_cases h : d = c
  · subst d
    rw [if_pos rfl]
    exact (Lagrange.eval_basis_self (Function.injective_id.injOn) hc).symm
  · rw [if_neg h]
    exact (Lagrange.eval_basis_of_ne (v := id) (Ne.symm h) hd).symm

theorem projector_partition (x : A) (hx : x ^ Fintype.card K = x) (e : A)
    (he : e*e=e) :
    (∑ c : K, e * projector x c) = e ∧
    (∀ c d : K, c ≠ d → (e*projector x c)*(e*projector x d)=0) ∧
    (∀ c : K, (e*projector x c)*(e*projector x c)=e*projector x c) ∧
    (∀ c : K, x*(e*projector x c)=algebraMap K A c*(e*projector x c)) := by
  have hR : aeval x (∏ c : K, (X - C c)) = 0 := by
    rw [prod_univ_X_sub_C]
    simp [hx]
  obtain ⟨hsum, hortho, hidem, hscalar⟩ := lagrange_split x Finset.univ hR e he
  have h (c : K) : projector x c = aeval x (Lagrange.basis Finset.univ id c) :=
    projector_lagrange x Finset.univ hR c (Finset.mem_univ _)
  simp_rw [h]
  exact ⟨hsum, fun c d hn => hortho c (Finset.mem_univ _) d (Finset.mem_univ _) hn,
    fun c => hidem c (Finset.mem_univ _), fun c => hscalar c (Finset.mem_univ _)⟩

#print axioms projector_partition

end EvenTI.CellProducer