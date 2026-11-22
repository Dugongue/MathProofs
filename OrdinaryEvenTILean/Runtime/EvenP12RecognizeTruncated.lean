import EvenP12RecognizeSchur
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option autoImplicit false

namespace EvenTI.LiveSpectral

open Polynomial Matrix

variable (K : Type) [Field K]

noncomputable def truncationIdeal (n : Nat) : Ideal K[X] :=
  Ideal.span { (X : K[X])^(n+1) }

abbrev Truncation (n : Nat) := K[X] ⧸ truncationIdeal K n

noncomputable def truncationResidue (n : Nat) : Truncation K n →+* K :=
  Ideal.Quotient.lift (truncationIdeal K n) (evalRingHom 0) fun p hp => by
    obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp

@[simp] theorem truncationResidue_mk (n : Nat) (p : K[X]) :
    truncationResidue K n (Ideal.Quotient.mk (truncationIdeal K n) p) = p.eval 0 := rfl

theorem truncationResidue_nilpotent (n : Nat) (v : Truncation K n)
    (h : truncationResidue K n v = 0) : v^(n+1) = 0 := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective v
  have hEval : p.eval 0 = 0 := h
  have hp : X ∣ p := Polynomial.X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
  obtain ⟨q,rfl⟩ := hp
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ⟨q^(n+1),mul_pow _ _ _⟩

/-- The determinant recursion over truncated coefficients computes the entire
reversed characteristic polynomial, even for repeated or inseparable spectra. -/
theorem nearOneDet_charpolyRev {n : Nat} (A : Matrix (Fin n) (Fin n) K) :
    nearOneDet (n+1)
      ((1 - (X : K[X]) • A.map C).map (Ideal.Quotient.mk (truncationIdeal K n))) =
      Ideal.Quotient.mk (truncationIdeal K n) A.charpoly.reverse := by
  have hres :
      (((1 - (X : K[X]) • A.map C).map (Ideal.Quotient.mk (truncationIdeal K n))).map
        (truncationResidue K n)) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [nearOneDet_eq (truncationResidue K n) (truncationResidue_nilpotent K n) _ hres]
  let m := Ideal.Quotient.mk (truncationIdeal K n)
  change (m.mapMatrix (1 - (X : K[X]) • A.map C)).det = m A.charpoly.reverse
  rw [← RingHom.map_det, Matrix.reverse_charpoly, Matrix.charpolyRev]

theorem truncationRepresentative_unique (n : Nat) (p q : K[X])
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : Ideal.Quotient.mk (truncationIdeal K n) p =
      Ideal.Quotient.mk (truncationIdeal K n) q) : p = q := by
  have hzero : Ideal.Quotient.mk (truncationIdeal K n) (p-q) = 0 := by rw [map_sub,h,sub_self]
  have hd : (X : K[X])^(n+1) ∣ p-q :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hm : ((X : K[X])^(n+1)).Monic := monic_X.pow _
  have hmod : p %ₘ (X : K[X])^(n+1) = q %ₘ (X : K[X])^(n+1) :=
    modByMonic_eq_of_dvd_sub hm hd
  have hlt {r : K[X]} (hr : r.natDegree ≤ n) :
      r.degree < ((X : K[X])^(n+1)).degree := by
    calc
      _ ≤ (n : WithBot Nat) := natDegree_le_iff_degree_le.mp hr
      _ < _ := by simp; exact_mod_cast Nat.lt_succ_self n
  simpa only [(modByMonic_eq_self_iff hm).2 (hlt hp), (modByMonic_eq_self_iff hm).2 (hlt hq)] using hmod

/-- A coefficient buffer of length at most the matrix size plus one is a
complete representation of the reversed characteristic polynomial. -/
theorem nearOneDet_coefficients {n : Nat} (A : Matrix (Fin n) (Fin n) K) (p : K[X])
    (hp : p.natDegree ≤ n)
    (h : Ideal.Quotient.mk (truncationIdeal K n) p =
      nearOneDet (n+1)
        ((1 - (X : K[X]) • A.map C).map (Ideal.Quotient.mk (truncationIdeal K n)))) :
    ∀ i ≤ n, p.coeff (n-i) = A.charpoly.coeff i := by
  have hd : A.charpoly.natDegree = n := by simp
  have ha : A.charpoly.reverse.natDegree ≤ n := A.charpoly.reverse_natDegree_le.trans hd.le
  have hEq := truncationRepresentative_unique K n p A.charpoly.reverse hp ha
    (h.trans (nearOneDet_charpolyRev K A))
  intro i hi
  rw [hEq,coeff_reverse,hd,revAt_le (Nat.sub_le _ _),Nat.sub_sub_self hi]

#print axioms nearOneDet_charpolyRev
#print axioms nearOneDet_coefficients

end EvenTI.LiveSpectral
