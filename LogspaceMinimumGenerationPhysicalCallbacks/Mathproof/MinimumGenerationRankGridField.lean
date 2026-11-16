import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-!
Finite prime-field extensions large enough for the weighted-rank test.
The requested threshold determines the extension degree exactly.
-/

noncomputable section

namespace Mathproof.MinimumGeneration.RankGridField

/-- The least positive degree whose field order strictly exceeds the threshold. -/
def degree (p threshold : Nat) : Nat := (Nat.log p threshold).succ

theorem degree_pos (p threshold : Nat) : 0 < degree p threshold :=
  Nat.succ_pos _

variable (p : Nat) [Fact p.Prime] (threshold : Nat)

/-- Use Mathlib's checked construction from the splitting field of the
corresponding Frobenius polynomial. -/
abbrev Extension : Type := GaloisField p (degree p threshold)

def baseEmbedding : ZMod p →+* Extension p threshold :=
  algebraMap (ZMod p) (Extension p threshold)

theorem baseEmbedding_injective : Function.Injective (baseEmbedding p threshold) :=
  (baseEmbedding p threshold).injective

theorem card_extension : Nat.card (Extension p threshold) = p ^ degree p threshold :=
  GaloisField.card p _ (degree_pos p threshold).ne'

theorem finrank_extension : Module.finrank (ZMod p) (Extension p threshold) = degree p threshold :=
  GaloisField.finrank p (degree_pos p threshold).ne'

theorem threshold_lt_card : threshold < Nat.card (Extension p threshold) := by
  rw [card_extension]
  exact Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt threshold

theorem card_le_mul_succ_threshold : Nat.card (Extension p threshold) ≤ p * (threshold + 1) := by
  rw [card_extension, degree, pow_succ']
  exact Nat.mul_le_mul_left p (Nat.pow_log_le_add_one p threshold)

/-- The extension has a monic irreducible polynomial of its chosen degree.
This existence theorem supplies a correctness target for finite searches. -/
theorem exists_monic_irreducible_of_degree :
    ∃ f : Polynomial (ZMod p), f.Monic ∧ Irreducible f ∧ f.natDegree = degree p threshold := by
  obtain ⟨a, ha⟩ :=
    Field.exists_primitive_element_of_finite_top (ZMod p) (Extension p threshold)
  have hIntegral := IsIntegral.of_finite (ZMod p) a
  refine ⟨minpoly (ZMod p) a, minpoly.monic hIntegral, minpoly.irreducible hIntegral, ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) a).mp ha).trans
    (finrank_extension p threshold)

/-- The base-field coefficients below the leading one describe a candidate for
the extension modulus. There are exactly as many candidates as field elements. -/
def monicCandidate (coefficients : Fin (degree p threshold) → ZMod p) :
    Polynomial (ZMod p) :=
  Polynomial.X ^ degree p threshold + Polynomial.ofFn (degree p threshold) coefficients

theorem monicCandidate_of_coeffs {f : Polynomial (ZMod p)}
    (hMonic : f.Monic) (hDegree : f.natDegree = degree p threshold) :
    monicCandidate p threshold (fun i => f.coeff i.val) = f := by
  ext i
  rw [monicCandidate, Polynomial.coeff_add, Polynomial.coeff_X_pow]
  by_cases hSmall : i < degree p threshold
  · simp [hSmall, hSmall.ne]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hSmall), add_zero]
    split
    · rename_i hTop
      rw [← hDegree] at hTop
      rw [hTop, hMonic.coeff_natDegree]
    · rename_i hNotTop
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem exists_irreducible_candidate :
    ∃ coefficients : Fin (degree p threshold) → ZMod p,
      Irreducible (monicCandidate p threshold coefficients) := by
  obtain ⟨f, hMonic, hIrreducible, hDegree⟩ := exists_monic_irreducible_of_degree p threshold
  refine ⟨fun i => f.coeff i.val, ?_⟩
  rw [monicCandidate_of_coeffs p threshold hMonic hDegree]
  exact hIrreducible

theorem card_candidate_codes :
    Fintype.card (Fin (degree p threshold) → ZMod p) = Nat.card (Extension p threshold) := by
  rw [card_extension, Fintype.card_fun, Fintype.card_fin, ZMod.card]


end Mathproof.MinimumGeneration.RankGridField
