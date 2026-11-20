import Mathlib

/-! # P15 FACTOR: distinct-degree splitting over a finite field (campaign p15-lean-20261007)

`L` finite field, `Q = |L|`.  For irreducible `g`: `g ∣ X^(Q^d) - X ↔ deg g ∣ d` (Mathlib:
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`).  Consequently, for squarefree `f`,
the normalized factors of `gcd(f, X^(Q^d) - X)` are exactly the normalized factors of `f` of degree
dividing `d`, the gcd is the (normalized) product of them, and the cofactor keeps the others; so
peeling `d = 1, 2, …` isolates the degree-`d` factors at step `d`. -/

namespace Mathproof.P15Factor20261007

open Polynomial UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

noncomputable section

variable {L : Type*} [Field L] [Fintype L] [DecidableEq L]

/-- The distinct-degree test polynomial `X^(Q^d) - X`. -/
def ddfPoly (L : Type*) [Field L] [Fintype L] (d : ℕ) : L[X] := X ^ (Fintype.card L) ^ d - X

theorem irreducible_dvd_ddfPoly_iff {g : L[X]} (hg : Irreducible g) (d : ℕ) :
    g ∣ ddfPoly L d ↔ g.natDegree ∣ d := by
  rw [ddfPoly, ← Nat.card_eq_fintype_card]
  exact hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.symm

theorem irreducible_dvd_gcd_iff (f : L[X]) {g : L[X]} (hg : Irreducible g) (d : ℕ) :
    g ∣ gcd f (ddfPoly L d) ↔ g ∣ f ∧ g.natDegree ∣ d := by
  rw [dvd_gcd_iff, irreducible_dvd_ddfPoly_iff hg]

theorem gcd_ne_zero_of_left {f h : L[X]} (hf : f ≠ 0) : gcd f h ≠ 0 := by
  intro h0; exact hf ((gcd_eq_zero_iff f h).mp h0).1

/-- **Distinct-degree splitting.** -/
theorem ddf_normalizedFactors {f : L[X]} (hf : f ≠ 0) (hsq : Squarefree f) (d : ℕ) :
    normalizedFactors (gcd f (ddfPoly L d)) =
      (normalizedFactors f).filter (fun g => g.natDegree ∣ d) := by
  have hg0 := gcd_ne_zero_of_left (h := ddfPoly L d) hf
  have hsq' : Squarefree (gcd f (ddfPoly L d)) := hsq.squarefree_of_dvd (gcd_dvd_left _ _)
  have hn1 := (squarefree_iff_nodup_normalizedFactors hg0).mp hsq'
  have hn2 := ((squarefree_iff_nodup_normalizedFactors hf).mp hsq).filter
    (fun g : L[X] => g.natDegree ∣ d)
  rw [Multiset.Nodup.ext hn1 hn2]
  intro g
  rw [mem_normalizedFactors_iff' hg0, Multiset.mem_filter, mem_normalizedFactors_iff' hf]
  constructor
  · rintro ⟨hi, hn, hdvd⟩
    exact ⟨⟨hi, hn, ((irreducible_dvd_gcd_iff f hi d).mp hdvd).1⟩,
      ((irreducible_dvd_gcd_iff f hi d).mp hdvd).2⟩
  · rintro ⟨⟨hi, hn, hdvd⟩, hd⟩
    exact ⟨hi, hn, (irreducible_dvd_gcd_iff f hi d).mpr ⟨hdvd, hd⟩⟩

/-- The gcd is the (normalized) product of the factors of degree dividing `d`. -/
theorem ddf_gcd_eq_prod {f : L[X]} (hf : f ≠ 0) (hsq : Squarefree f) (d : ℕ) :
    gcd f (ddfPoly L d) =
      normalize ((normalizedFactors f).filter (fun g => g.natDegree ∣ d)).prod := by
  have hg0 := gcd_ne_zero_of_left (h := ddfPoly L d) hf
  rw [← ddf_normalizedFactors hf hsq d]
  have ha := prod_normalizedFactors hg0
  rw [normalize_eq_normalize ha.dvd ha.symm.dvd, normalize_gcd]

/-- The cofactor keeps exactly the factors of degree not dividing `d`. -/
theorem ddf_cofactor {f : L[X]} (hf : f ≠ 0) (hsq : Squarefree f) (d : ℕ) :
    normalizedFactors (f / gcd f (ddfPoly L d)) =
      (normalizedFactors f).filter (fun g => ¬ g.natDegree ∣ d) := by
  have hg0 := gcd_ne_zero_of_left (h := ddfPoly L d) hf
  have hmul : gcd f (ddfPoly L d) * (f / gcd f (ddfPoly L d)) = f :=
    EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have hq0 : f / gcd f (ddfPoly L d) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hf hmul.symm
  have := normalizedFactors_mul hg0 hq0
  rw [hmul, ddf_normalizedFactors hf hsq d] at this
  have hsplit := (Multiset.filter_add_not (fun g : L[X] => g.natDegree ∣ d)
    (normalizedFactors f)).trans this
  exact (add_left_cancel hsplit).symm

/-- **Peeling.** If all factors of `f` have degree `≥ d` (`d ≥ 1`), step `d` isolates exactly the
factors of degree `d`, and the cofactor has only factors of degree `≥ d + 1`. -/
theorem ddf_peel {f : L[X]} (hf : f ≠ 0) (hsq : Squarefree f) {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ g ∈ normalizedFactors f, d ≤ g.natDegree) :
    normalizedFactors (gcd f (ddfPoly L d)) =
        (normalizedFactors f).filter (fun g => g.natDegree = d) ∧
      ∀ g ∈ normalizedFactors (f / gcd f (ddfPoly L d)), d + 1 ≤ g.natDegree := by
  constructor
  · rw [ddf_normalizedFactors hf hsq d]
    apply Multiset.filter_congr
    intro g hg
    have := hdeg g hg
    constructor
    · intro h; exact le_antisymm (Nat.le_of_dvd hd h) this
    · intro h; rw [h]
  · intro g hg
    rw [ddf_cofactor hf hsq d, Multiset.mem_filter] at hg
    have h1 := hdeg g hg.1
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · exact absurd (h ▸ dvd_refl d) hg.2
    · exact h

end

end Mathproof.P15Factor20261007
