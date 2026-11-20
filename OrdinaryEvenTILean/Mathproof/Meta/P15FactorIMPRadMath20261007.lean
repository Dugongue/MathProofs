import Mathproof.Meta.P15FactorDDF20261007
import Mathproof.Meta.P15FactorRefPoly20261007

/-! # P15 FACTOR IMP: the radical pre-pass, mathematics (campaign p15-lean-20261007)

`radCall` computes `R := lcm_{d ≤ N} gcd(f, X^{q^d} − X)` as `R ← R · (P / gcd(R, P))`.
* `lcm_step`: squarefree `R`, `P` ⇒ `R · (P / gcd R P)` is squarefree and its prime divisors are
  those of `R` or `P`.
* `round_props`: `f ∣ XQ − X^{q^d}` (`d ≥ 1`) ⇒ `P = gcd f (XQ − X)` is monic, squarefree, divides `f`,
  and its irreducible divisors are those of `f` of degree dividing `d`.
* `RInv f R d`: `R` monic squarefree, `R ∣ f`, irreducible divisors = those of `f` of degree `≤ d`.
* `radP f := (normalizedFactors f).dedup.prod`; `rinv_eq_radP`: `RInv f R d` with `d ≥ deg f` ⇒ `R = radP f`.
* `radP_props`: `radP f` is monic, squarefree, divides `f`, and has the irreducible divisors of `f`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mathproof.P15FactorIMP20261007

open Polynomial UniqueFactorizationMonoid Mathproof.P15Factor20261007 Mathproof.P15FactorRef20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem gcd_monic' {a b : K[X]} (ha : a ≠ 0) : (gcd a b).Monic := by
  have h0 : gcd a b ≠ 0 := fun h => ha ((gcd_eq_zero_iff a b).mp h).1
  rw [← normalize_gcd]; exact monic_normalize h0

omit [Fintype K] in
theorem lcm_step {R P : K[X]} (hR : Squarefree R) (hP : Squarefree P) (hP0 : P ≠ 0) :
    Squarefree (R * (P / gcd R P)) ∧ IsRelPrime R (P / gcd R P) ∧ P / gcd R P ∣ P ∧
      ∀ p : K[X], Prime p → (p ∣ R * (P / gcd R P) ↔ p ∣ R ∨ p ∣ P) := by
  have hG0 : gcd R P ≠ 0 := fun h => hP0 ((gcd_eq_zero_iff R P).mp h).2
  have hGQ : gcd R P * (P / gcd R P) = P := EuclideanDomain.mul_div_cancel' hG0 (gcd_dvd_right R P)
  have hQP : P / gcd R P ∣ P := ⟨gcd R P, by rw [mul_comm]; exact hGQ.symm⟩
  have hrel : IsRelPrime R (P / gcd R P) := by
    intro d hdR hdQ
    have hdG : d ∣ gcd R P := dvd_gcd hdR (hdQ.trans hQP)
    have : d * d ∣ P := hGQ ▸ mul_dvd_mul hdG hdQ
    exact hP d this
  refine ⟨squarefree_mul_iff.mpr ⟨hrel, hR, Squarefree.squarefree_of_dvd hQP hP⟩, hrel, hQP, fun p hp => ?_⟩
  rw [hp.dvd_mul]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (h.trans hQP)
  · intro h
    by_cases hr : p ∣ R
    · exact Or.inl hr
    · rcases h with h | h
      · exact absurd h hr
      · right
        rw [← hGQ] at h
        rcases hp.dvd_mul.mp h with h' | h'
        · exact absurd (h'.trans (gcd_dvd_left R P)) hr
        · exact h'

theorem ddfPoly_squarefree {d : ℕ} (hd : 1 ≤ d) : Squarefree (ddfPoly K d) := by
  obtain ⟨n, hp, hq⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hdiv : ringChar K ∣ Fintype.card K ^ d := by
    rw [hq]; exact dvd_pow (dvd_pow_self _ (PNat.ne_zero n)) (by omega)
  exact (galois_poly_separable (K := K) (ringChar K) _ hdiv).squarefree

/-- **One round.** -/
theorem round_props {f XQ : K[X]} (hf : f ≠ 0) {d : ℕ} (hd : 1 ≤ d)
    (hX : f ∣ XQ - X ^ (Fintype.card K ^ d)) :
    gcd f (XQ - X) ≠ 0 ∧ (gcd f (XQ - X)).Monic ∧ Squarefree (gcd f (XQ - X)) ∧ gcd f (XQ - X) ∣ f ∧
      ∀ p : K[X], Irreducible p → (p ∣ gcd f (XQ - X) ↔ p ∣ f ∧ p.natDegree ∣ d) := by
  have h0 : gcd f (XQ - X) ≠ 0 := fun h => hf ((gcd_eq_zero_iff _ _).mp h).1
  have hsplit : XQ - X = (XQ - X ^ (Fintype.card K ^ d)) + ddfPoly K d := by unfold ddfPoly; ring
  have hdd : gcd f (XQ - X) ∣ ddfPoly K d := by
    have h1 := gcd_dvd_right f (XQ - X)
    have h2 := (gcd_dvd_left f (XQ - X)).trans hX
    exact (dvd_add_right h2).mp (by rw [← hsplit]; exact h1)
  refine ⟨h0, gcd_monic' hf, Squarefree.squarefree_of_dvd hdd (ddfPoly_squarefree hd), gcd_dvd_left _ _,
    fun p hp => ?_⟩
  rw [dvd_gcd_iff, ← irreducible_dvd_ddfPoly_iff hp d]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [hsplit] at h2
    exact (dvd_add_right (h1.trans hX)).mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [hsplit]
    exact dvd_add (h1.trans hX) h2

/-- The loop invariant after `d` rounds. -/
def RInv (f R : K[X]) (d : ℕ) : Prop :=
  R.Monic ∧ Squarefree R ∧ R ∣ f ∧ ∀ p : K[X], Irreducible p → (p ∣ R ↔ p ∣ f ∧ p.natDegree ≤ d)

theorem rinv_zero (f : K[X]) : RInv f 1 0 := by
  refine ⟨monic_one, squarefree_one, one_dvd _, fun p hp => ?_⟩
  have hdeg : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hp)
  constructor
  · intro h; exact absurd (isUnit_of_dvd_one h) hp.not_isUnit
  · rintro ⟨-, h⟩; omega

/-- **The lcm update keeps the invariant.** -/
theorem rinv_step {f R XQ : K[X]} (hf : f ≠ 0) {d : ℕ} (hI : RInv f R d)
    (hX : f ∣ XQ - X ^ (Fintype.card K ^ (d + 1))) :
    RInv f (R * (gcd f (XQ - X) / gcd R (gcd f (XQ - X)))) (d + 1) := by
  obtain ⟨hm, hsq, hdv, hirr⟩ := hI
  obtain ⟨hP0, hPm, hPsq, hPf, hPirr⟩ := round_props hf (by omega) hX
  set P := gcd f (XQ - X)
  obtain ⟨hsq', hrel, hQP, hdiv⟩ := lcm_step hsq hPsq hP0
  have hG0 : gcd R P ≠ 0 := fun h => hP0 ((gcd_eq_zero_iff R P).mp h).2
  have hGm : (gcd R P).Monic := gcd_monic' hm.ne_zero
  have hGQ : gcd R P * (P / gcd R P) = P := EuclideanDomain.mul_div_cancel' hG0 (gcd_dvd_right R P)
  have hQm : (P / gcd R P).Monic := Monic.of_mul_monic_left hGm (by rw [hGQ]; exact hPm)
  refine ⟨hm.mul hQm, hsq', hrel.mul_dvd hdv (hQP.trans hPf), fun p hp => ?_⟩
  rw [hdiv p hp.prime, hirr p hp, hPirr p hp]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by omega⟩
    · exact ⟨h1, Nat.le_of_dvd (by omega) h2⟩
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_or_ge p.natDegree (d + 1) with h | h
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by rw [show p.natDegree = d + 1 by omega]⟩

/-- The canonical radical. -/
noncomputable def radP (f : K[X]) : K[X] := ((normalizedFactors f).dedup).prod

omit [Fintype K] in
theorem nf_monic {f q : K[X]} (hq : q ∈ normalizedFactors f) : q.Monic := by
  rw [← normalize_normalized_factor q hq]; exact monic_normalize (ne_zero_of_mem_normalizedFactors hq)

omit [Fintype K] in
/-- **Uniqueness**: a monic squarefree `R` with the irreducible divisors of `f` is `radP f`. -/
theorem eq_radP {f R : K[X]} (hf : f ≠ 0) (hm : R.Monic) (hsq : Squarefree R)
    (hirr : ∀ p : K[X], Irreducible p → (p ∣ R ↔ p ∣ f)) : R = radP f := by
  have hR0 : R ≠ 0 := hm.ne_zero
  have hnf : normalizedFactors R = (normalizedFactors f).dedup := by
    rw [Multiset.Nodup.ext ((squarefree_iff_nodup_normalizedFactors hR0).mp hsq) (Multiset.nodup_dedup _)]
    intro q
    rw [Multiset.mem_dedup, mem_normalizedFactors_iff' hR0, mem_normalizedFactors_iff' hf]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hirr q h1).mp h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hirr q h1).mpr h3⟩
  have hpm : (normalizedFactors R).prod.Monic := by
    have := monic_multiset_prod_of_monic (normalizedFactors R) id (fun q hq => nf_monic hq)
    rwa [Multiset.map_id] at this
  unfold radP
  rw [← hnf]
  exact (eq_of_monic_of_associated hpm hm (prod_normalizedFactors hR0)).symm

theorem rinv_eq_radP {f R : K[X]} (hf : f ≠ 0) {d : ℕ} (hI : RInv f R d) (hd : f.natDegree ≤ d) :
    R = radP f := by
  obtain ⟨hm, hsq, hdv, hirr⟩ := hI
  refine eq_radP hf hm hsq (fun p hp => ?_)
  rw [hirr p hp]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, (natDegree_le_of_dvd h hf).trans hd⟩

theorem rinv_exists {f : K[X]} (hf : f ≠ 0) (d : ℕ) : ∃ R, RInv f R d := by
  induction d with
  | zero => exact ⟨1, rinv_zero f⟩
  | succ d ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨_, rinv_step hf hR (XQ := X ^ (Fintype.card K ^ (d + 1))) (by simp)⟩

/-- **Properties of the radical.** -/
theorem radP_props {f : K[X]} (hf : f ≠ 0) :
    (radP f).Monic ∧ Squarefree (radP f) ∧ radP f ∣ f ∧
      ∀ p : K[X], Irreducible p → (p ∣ radP f ↔ p ∣ f) := by
  obtain ⟨R, hR⟩ := rinv_exists hf f.natDegree
  have he := rinv_eq_radP hf hR le_rfl
  obtain ⟨hm, hsq, hdv, hirr⟩ := hR
  subst he
  refine ⟨hm, hsq, hdv, fun p hp => ?_⟩
  rw [hirr p hp]
  exact ⟨fun h => h.1, fun h => ⟨h, natDegree_le_of_dvd h hf⟩⟩

theorem radP_natDegree_le {f : K[X]} (hf : f ≠ 0) : (radP f).natDegree ≤ f.natDegree :=
  natDegree_le_of_dvd (radP_props hf).2.2.1 hf

/-- The normalized factors of the radical: those of `f`, once each. -/
theorem nf_radP {f : K[X]} (hf : f ≠ 0) : normalizedFactors (radP f) = (normalizedFactors f).dedup := by
  obtain ⟨hm, hsq, -, hirr⟩ := radP_props hf
  have hR0 := hm.ne_zero
  rw [Multiset.Nodup.ext ((squarefree_iff_nodup_normalizedFactors hR0).mp hsq) (Multiset.nodup_dedup _)]
  intro q
  rw [Multiset.mem_dedup, mem_normalizedFactors_iff' hR0, mem_normalizedFactors_iff' hf]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hirr q h1).mp h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hirr q h1).mpr h3⟩

/-- The coefficient list of length `N` (little-endian). -/
noncomputable def coeffsL (N : ℕ) (P : K[X]) : List K := List.ofFn (fun i : Fin N => P.coeff i)

theorem toPoly_coeffsL {N : ℕ} {P : K[X]} (hP : P.degree < N) : toPoly (coeffsL N P) = P := by
  ext i
  rw [coeff_toPoly, coeffsL]
  by_cases hi : i < N
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hP (by exact_mod_cast (not_lt.mp hi)))).symm

theorem coeffsL_length (N : ℕ) (P : K[X]) : (coeffsL N P).length = N := by simp [coeffsL]

end Mathproof.P15FactorIMP20261007
