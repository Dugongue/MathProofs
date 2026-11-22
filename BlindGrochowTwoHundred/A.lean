import Mathlib

namespace GrochowTwoHundred.WeightedCycles

section Integral
variable {I : Type*} [Fintype I] [DecidableEq I]

def cost (w z : I → ℤ) : ℤ := ∑ i, w i * |z i|
def signal (c z : I → ℤ) : ℤ := ∑ i, c i * z i

private def pulse (i : I) (v : ℤ) (j : I) : ℤ := if j = i then v else 0

private theorem sum_pulse (i : I) (v : ℤ) : (∑ j, pulse i v j) = v := by
  simp [pulse]

private theorem signal_pulse (c : I → ℤ) (i : I) (v : ℤ) :
    signal c (pulse i v) = c i * v := by
  simp [signal, pulse, mul_ite]

private theorem signal_add (c z z' : I → ℤ) :
    signal c (fun i => z i + z' i) = signal c z + signal c z' := by
  simp [signal, mul_add, Finset.sum_add_distrib]

private theorem abs_at_least_one {z : ℤ} (h : z ≠ 0) : 1 ≤ |z| := by
  have hz := abs_pos.mpr h
  omega

private theorem abs_subsum (s : Finset I) (w c z : I → ℤ) (hw : ∀ i, |c i| ≤ w i) :
    |∑ i ∈ s, c i * z i| ≤ ∑ i ∈ s, w i * |z i| := by
  apply le_trans (Finset.abs_sum_le_sum_abs (fun i => c i * z i) s)
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)

private theorem abs_dvd_lower {m x : ℤ} (hm : 0 < m) (hd : m ∣ x) (hx : x ≠ 0) :
    m ≤ |x| := by
  obtain ⟨q, rfl⟩ := hd
  have hq : q ≠ 0 := right_ne_zero_of_mul hx
  rw [abs_mul, abs_of_pos hm]
  simpa using (mul_le_mul_of_nonneg_left (abs_at_least_one hq) (le_of_lt hm))

/-- A modular signal determines the exact signal in a signed weighted ball. -/
theorem exact_signal_below_modulus {w c z : I → ℤ} (m : ℤ) (hm : 0 < m)
    (hw : ∀ i, |c i| ≤ w i) (h : m ∣ signal c z) (hcost : cost w z < m) :
    signal c z = 0 := by
  by_contra hn
  exact (not_le_of_gt hcost) ((abs_dvd_lower hm h hn).trans (abs_subsum Finset.univ w c z hw))

/-- If an exact signal cancels, one occupied coordinate forces compensating weight elsewhere. -/
theorem opposing_mass_bound {w c z : I → ℤ} (i : I) (hw : ∀ j, |c j| ≤ w j)
    (h0 : signal c z = 0) :
    (w i + |c i|) * |z i| ≤ cost w z := by
  have he := Finset.sum_erase_add Finset.univ (fun j => c j * z j) (Finset.mem_univ i)
  have he' : (∑ j ∈ Finset.univ.erase i, c j * z j) = -(c i * z i) := by
    change (∑ j ∈ Finset.univ.erase i, c j * z j) + c i * z i = signal c z at he
    rw [h0] at he
    omega
  have hb := abs_subsum (Finset.univ.erase i) w c z hw
  rw [he', abs_neg, abs_mul] at hb
  have hsum := Finset.sum_erase_add Finset.univ (fun j => w j * |z j|) (Finset.mem_univ i)
  change (∑ j ∈ Finset.univ.erase i, w j * |z j|) + w i * |z i| = cost w z at hsum
  rw [add_mul, ← hsum]
  linarith

/-- A nonzero off-anchor perturbation costs at least its own weight plus its signal. -/
theorem off_anchor_perturbation_bound {w c z : I → ℤ} (i : I) (hw : ∀ j, |c j| ≤ w j)
    (h0 : signal c z = 0) (hi : z i ≠ 0) :
    w i + |c i| ≤ cost w z := by
  have hnonneg : 0 ≤ w i + |c i| := by have := hw i; have := abs_nonneg (c i); linarith
  have hscaled : w i + |c i| ≤ (w i + |c i|) * |z i| := by
    simpa using (mul_le_mul_of_nonneg_left (abs_at_least_one hi) hnonneg)
  exact hscaled.trans (opposing_mass_bound i hw h0)

/-- A distinguished unit-cost, unit-signal coordinate gives a sharp injectivity
criterion for modular observations on signed weighted perturbations. -/
theorem recover_below_balanced_or_residue_cost {w c z : I → ℤ} (a : I) (m L : ℤ)
    (hw : ∀ i, |c i| ≤ w i) (ha : c a = 1) (hL : 0 < L) (hm : L ≤ m)
    (hother : ∀ i, i ≠ a → L ≤ w i + |c i|)
    (hmod : m ∣ signal c z) (hbudget : cost w z < L) :
    z = 0 := by
  have h0 := exact_signal_below_modulus m (hL.trans_le hm) hw hmod (hbudget.trans_le hm)
  have hOff : ∀ i, i ≠ a → z i = 0 := by
    intro i hi
    by_contra hn
    exact (not_le_of_gt hbudget) ((hother i hi).trans (off_anchor_perturbation_bound i hw h0 hn))
  have hsignal : signal c z = z a := by
    unfold signal
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a), ha, one_mul]
    intro i hi hia
    simp [hOff i hia]
  funext i
  by_cases hi : i = a
  · subst i
    exact hsignal.symm.trans h0
  · exact hOff i hi

/-- The residue threshold is attained by a perturbation on the reference coordinate. -/
theorem residue_endpoint_witness {w c : I → ℤ} (a : I) (m : ℤ)
    (hm : 0 < m) (hw : w a = 1) (hc : c a = 1) :
    ∃ z : I → ℤ, z ≠ 0 ∧ m ∣ signal c z ∧ cost w z = m := by
  refine ⟨pulse a m, ?_, ?_, ?_⟩
  · intro h
    have hh := congrFun h a
    simp [pulse, hm.ne'] at hh
  · rw [signal_pulse, hc, one_mul]
  · simp [cost, pulse, abs_ite, mul_ite, hw, abs_of_pos hm]

/-- A prescribed off-anchor coordinate realizes its lower bound by a compensating anchor. -/
theorem balanced_endpoint_witness {w c : I → ℤ} (a i : I) (hia : i ≠ a)
    (hw : w a = 1) (hc : c a = 1) :
    ∃ z : I → ℤ, z i = 1 ∧ signal c z = 0 ∧ cost w z = w i + |c i| := by
  let z := fun j => pulse i 1 j + pulse a (-(c i)) j
  refine ⟨z, by simp [z, pulse, hia], ?_, ?_⟩
  · dsimp [z]
    rw [signal_add, signal_pulse, signal_pulse, hc]
    ring
  · have hpoint (j : I) : w j * |z j| = pulse i (w i) j + pulse a |c i| j := by
      by_cases hj : j = i
      · subst j
        simp [z, pulse, hia]
      · by_cases hja : j = a
        · subst j
          simp [z, pulse, Ne.symm hia, hw]
        · simp [z, pulse, hj, hja]
    unfold cost
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, sum_pulse, sum_pulse]

/-- In the budget range where every non-anchor direction is excluded, the only
possible nonzero collision at the residue endpoint is the anchor pulse up to sign. -/
theorem residue_endpoint_support {w c z : I → ℤ} (a : I) (m : ℤ)
    (hw : ∀ i, |c i| ≤ w i) (ha : w a = 1) (hc : c a = 1) (hm : 0 < m)
    (hgap : ∀ i, i ≠ a → m < w i)
    (hd : m ∣ signal c z) (hn : z ≠ 0) (hcost : cost w z ≤ m) :
    |z a| = m ∧ ∀ i, i ≠ a → z i = 0 := by
  have hOff : ∀ i, i ≠ a → z i = 0 := by
    intro i hi
    by_contra hzi
    have hm' : w i ≤ w i * |z i| := by
      have hwi := (abs_nonneg (c i)).trans (hw i)
      simpa using (mul_le_mul_of_nonneg_left (abs_at_least_one hzi) hwi)
    have hs : w i * |z i| ≤ cost w z := by
      exact Finset.single_le_sum (fun j _ => mul_nonneg ((abs_nonneg _).trans (hw j)) (abs_nonneg _))
        (Finset.mem_univ i)
    exact (not_le_of_gt (hgap i hi)) (hm'.trans (hs.trans hcost))
  have hza : z a ≠ 0 := by
    intro h
    apply hn
    funext i
    by_cases hi : i = a
    · simpa [hi] using h
    · exact hOff i hi
  have hsignal : signal c z = z a := by
    unfold signal
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a), hc, one_mul]
    intro i hi hia
    simp [hOff i hia]
  have hcost' : cost w z = |z a| := by
    unfold cost
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a), ha, one_mul]
    intro i hi hia
    simp [hOff i hia]
  rw [hsignal] at hd
  rw [hcost'] at hcost
  exact ⟨le_antisymm hcost (abs_dvd_lower hm hd hza), hOff⟩

/-- Independently observed residues of one signal combine into the product period
when the moduli are coprime. -/
theorem merge_coprime_signal_residues {c z : I → ℤ} {m n : ℤ} (h : IsCoprime m n)
    (hm : m ∣ signal c z) (hn : n ∣ signal c z) :
    m * n ∣ signal c z :=
  h.mul_dvd hm hn

/-- A large combination of individually weak exact-divisibility observations
recovers the actual weighted signal without access to the signed perturbation. -/
theorem coprime_panel_forces_exact_signal {w c z : I → ℤ} {m n : ℤ}
    (h : IsCoprime m n) (hm : 0 < m) (hn : 0 < n) (hw : ∀ i, |c i| ≤ w i)
    (hmz : m ∣ signal c z) (hnz : n ∣ signal c z) (hcost : cost w z < m * n) :
    signal c z = 0 :=
  exact_signal_below_modulus (m * n) (mul_pos hm hn) hw
    (merge_coprime_signal_residues h hmz hnz) hcost

end Integral

section Tomography
variable {I V K : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

def fibre (label : I → V) (z : I → ℤ) (v : V) : ℤ :=
  ∑ i, if label i = v then z i else 0

private theorem fibre_eq_coordinate {label : I → V} {z : I → ℤ} (i : I)
    (h : ∀ j, j ≠ i → label j = label i → z j = 0) :
    fibre label z (label i) = z i := by
  unfold fibre
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j hj hji
    by_cases hji' : label j = label i
    · simp [hji', h j hji hji']
    · simp [hji']

/-- The difference of two profiles is zero if an intact panel can isolate every
nonzero disagreement and each isolated reading lies below its integral granularity. -/
theorem modular_sparse_tomography {z : I → ℤ} (label : K → I → V)
    (allowed : Set K) (m granularity : I → ℤ)
    (hgran : ∀ i, 0 < granularity i ∧ granularity i ∣ z i)
    (hmod : ∀ k ∈ allowed, ∀ i, m i ∣ fibre (label k) z (label k i))
    (hsep : z ≠ 0 → ∃ k ∈ allowed, ∃ i, z i ≠ 0 ∧
       (∀ j, j ≠ i → label k j = label k i → z j = 0) ∧
       0 < m i ∧ IsCoprime (granularity i) (m i) ∧
       |fibre (label k) z (label k i)| < granularity i * m i) :
    z = 0 := by
  by_contra hn
  obtain ⟨k, hk, i, hi, hf, hm, hcop, hlt⟩ := hsep hn
  rw [fibre_eq_coordinate i hf] at hlt
  have hd := hmod k hk i
  rw [fibre_eq_coordinate i hf] at hd
  exact (not_le_of_gt hlt) (abs_dvd_lower (mul_pos (hgran i).1 hm)
    (hcop.mul_dvd (hgran i).2 hd) hi)

/-- A family of tests with possible erasures recovers signed deviations if every
disagreement set contains a singleton fibre of one retained test with sufficient precision. -/
theorem noisy_erasure_tomography {z : I → ℤ} (label : K → I → V) (retained : Set K)
    (granularity : I → ℤ)
    (hweight : ∀ i, 0 < granularity i ∧ granularity i ∣ z i)
    (hnoise : ∀ k ∈ retained, ∀ i, |fibre (label k) z (label k i)| < granularity i)
    (hsep : ∀ s : Finset I, s.Nonempty → ∃ k ∈ retained, ∃ i ∈ s,
      ∀ j ∈ s, label k j = label k i → j = i) :
    z = 0 := by
  classical
  by_contra hn
  have hz : ∃ i, z i ≠ 0 := by
    by_contra! hz
    exact hn (funext hz)
  let s := Finset.univ.filter (fun i => z i ≠ 0)
  obtain ⟨q, hq⟩ := hz
  obtain ⟨k, hk, i, hi, hsing⟩ :=
    hsep s ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
  have hz' := (Finset.mem_filter.mp hi).2
  have hzero : ∀ j, j ≠ i → label k j = label k i → z j = 0 := by
    intro j hji hlj
    by_contra hnon
    exact hji (hsing j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon⟩) hlj)
  have hlt := hnoise k hk i
  rw [fibre_eq_coordinate i hzero] at hlt
  exact (not_le_of_gt hlt) (abs_dvd_lower (hweight i).1 (hweight i).2 hz')

/-- Balanced signs can be certified by a label-preserving matching rather than
enumerating any of the fibres. -/
theorem fibre_cancels_under_matching (e : I ≃ I) (label : I → V) (z : I → ℤ)
    (hp : ∀ i, label (e i) = label i) (hz : ∀ i, z (e i) = -z i) :
    ∀ v, fibre label z v = 0 := by
  intro v
  let f : I → ℤ := fun i => if label i = v then z i else 0
  have h : (∑ i, f (e i)) = ∑ i, f i := e.sum_comp f
  have hf (i : I) : f (e i) = -f i := by
    dsimp [f]
    rw [hp i, hz i]
    split <;> simp_all
  simp_rw [hf, Finset.sum_neg_distrib] at h
  unfold fibre
  change (∑ i, f i) = 0
  omega

/-- A sufficiently precise signed fibre cannot report a nonzero residue equal
to a strict lower-dimensional amount supported outside it. -/
theorem fibre_lifts_exact_value {label : I → V} {z : I → ℤ} {v : V} (m x : ℤ)
    (hm : 0 < m) (hd : m ∣ (fibre label z v - x))
    (herror : |fibre label z v - x| < m) :
    fibre label z v = x := by
  by_contra hn
  exact (not_le_of_gt herror) (abs_dvd_lower hm hd (sub_ne_zero.mpr hn))

/-- A unimodularly weighted two-channel kernel restricts all possible arrays on a
rectangle to one alternating circulation. -/
theorem rectangle_balance_iff (x y z w : ℤ) :
    (x + y = 0 ∧ z + w = 0 ∧ x + z = 0 ∧ y + w = 0) ↔
      (y = -x ∧ z = -x ∧ w = x) := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Integer edge divisibility makes the first rectangle ambiguity a common
multiple, hence certifies exact recovery below the circulating bound. -/
theorem rectangle_moduli_rigid_below {x y z w a b c d m : ℤ}
    (hm : 0 < m) (hcommon : ∀ v : ℤ, a ∣ v → b ∣ v → c ∣ v → d ∣ v → m ∣ v)
    (ha : a ∣ x) (hb : b ∣ y) (hc : c ∣ z) (hd : d ∣ w)
    (hcirc : x + y = 0 ∧ z + w = 0 ∧ x + z = 0 ∧ y + w = 0)
    (hbound : |x| + |y| + |z| + |w| < 4 * m) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨hy, hz, hw⟩ := (rectangle_balance_iff x y z w).mp hcirc
  subst y
  subst z
  subst w
  have hx : x = 0 := by
    by_contra hn
    have hg := abs_dvd_lower hm (hcommon x ha (dvd_neg.mp hb) (dvd_neg.mp hc) hd) hn
    rw [abs_neg] at hbound
    omega
  simp [hx]

/-- Two disjoint observations joined with one signed diagonal determine every
entry in a rectangle over the integers. -/
theorem rectangle_diagonal_recovers {x y z w : ℤ}
    (h : x + y = 0 ∧ z + w = 0 ∧ x + z = 0 ∧ y + w = 0)
    (hdiag : x + w = 0) : x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨hy, hz, hw⟩ := (rectangle_balance_iff x y z w).mp h
  subst y
  subst z
  subst w
  have hx : x = 0 := by omega
  simp [hx]

theorem rectangle_diagonal_robust_recovers {x y z w m : ℤ}
    (h : x + y = 0 ∧ z + w = 0 ∧ x + z = 0 ∧ y + w = 0)
    (hm : 0 < m) (hd : m ∣ x) (herr : |x + w| < 2 * m) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨hy, hz, hw⟩ := (rectangle_balance_iff x y z w).mp h
  subst y
  subst z
  subst w
  have hx : x = 0 := by
    by_contra hn
    have hh := abs_dvd_lower hm hd hn
    rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)] at herr
    omega
  simp [hx]

end Tomography
end GrochowTwoHundred.WeightedCycles

namespace GrochowTwoHundred.DeterminantalPanels

section Domains
variable {I J K R : Type*} [CommRing R] [IsDomain R]

def rankOne (M : I → J → R) : Prop :=
  ∀ i k j l, M i j * M k l = M i l * M k j

/-- A row and column meeting at a nonzero pivot certify equality within the
entire determinantal rank-one locus. -/
theorem pivot_panel_recovers {M N : I → J → R} (i₀ : I) (j₀ : J)
    (hM : rankOne M) (hN : rankOne N) (hPivot : M i₀ j₀ ≠ 0)
    (hrow : ∀ j, M i₀ j = N i₀ j) (hcol : ∀ i, M i j₀ = N i j₀) :
    M = N := by
  funext i j
  apply mul_right_cancel₀ hPivot
  rw [hM i i₀ j j₀, hcol i, hrow j, ← hN i i₀ j j₀, ← hrow j₀]

/-- Arbitrary row and column data over a field with a common nonzero entry
have a unique completion satisfying every two-by-two minor equation. -/
theorem pivot_panel_unique_completion [Field K] {r : J → K} {c : I → K}
    (i₀ : I) (j₀ : J) (h : r j₀ = c i₀) (hn : r j₀ ≠ 0) :
    ∃! M : I → J → K, rankOne M ∧ (∀ j, M i₀ j = r j) ∧ (∀ i, M i j₀ = c i) := by
  let M := fun i j => c i * r j / r j₀
  have hM : rankOne M := by
    intro i k j l
    dsimp [M]
    ring
  have hrow : ∀ j, M i₀ j = r j := by
    intro j
    dsimp [M]
    rw [← h]
    field_simp
  have hcol : ∀ i, M i j₀ = c i := by
    intro i
    dsimp [M]
    field_simp
  refine ⟨M, ⟨hM, hrow, hcol⟩, ?_⟩
  rintro N ⟨hN, hrow', hcol'⟩
  apply pivot_panel_recovers i₀ j₀ hN hM
  · rwa [hrow' j₀]
  · intro j
    rw [hrow' j, hrow j]
  · intro i
    rw [hcol' i, hcol i]

/-- If the pivot is a unit, the determinantal equations produce an exact
outer-product factorization over the base ring. -/
theorem unit_pivot_exact_factorization {M : I → J → R}
    (i₀ : I) (j₀ : J) (h : rankOne M) (hunit : IsUnit (M i₀ j₀)) :
    ∃ u : I → R, ∃ v : J → R, v j₀ = 1 ∧ (∀ i j, M i j = u i * v j) := by
  obtain ⟨unit, hunit⟩ := hunit
  let v := fun j => M i₀ j * (↑unit⁻¹ : R)
  refine ⟨fun i => M i j₀, v, ?_, ?_⟩
  · simp [v, ← hunit]
  · intro i j
    dsimp [v]
    rw [← mul_assoc, ← h i i₀ j j₀, ← hunit, mul_assoc]
    simp

/-- A nonzero entry in an omitted row and column certifies that their
intersection can serve as a pivot. -/
theorem rank_one_support_rectangle {M : I → J → R} (h : rankOne M)
    (i k : I) (j l : J) (hi : M i l ≠ 0) (hj : M k j ≠ 0) :
    M i j ≠ 0 ∧ M k l ≠ 0 := by
  have hp : M i j * M k l ≠ 0 := by rw [h i k j l]; exact mul_ne_zero hi hj
  exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

/-- If every entry of a rank-one matrix lies in the kernel of one fixed row
or column test, a nonzero pivot forces the corresponding entire row or column
factor to vanish on that test. -/
theorem rank_one_row_test_factor [Fintype J] {M : I → J → R}
    (h : rankOne M) (i₀ : I) (j₀ : J) (hp : M i₀ j₀ ≠ 0) (b : J → R)
    (hrow : ∑ j, b j * M i₀ j = 0) :
    ∀ i, ∑ j, b j * M i j = 0 := by
  intro i
  apply mul_right_cancel₀ hp
  rw [zero_mul, Finset.sum_mul]
  trans ∑ j, b j * (M i j₀ * M i₀ j)
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, h i i₀ j j₀]
  · have he : (∑ j, b j * (M i j₀ * M i₀ j)) = M i j₀ * (∑ j, b j * M i₀ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, hrow, mul_zero]

/-- Independent row and column weights can be chosen adversarially. Their
common contraction times an entry still equals the product of the two marginals. -/
theorem weighted_contraction_identity [Fintype I] [Fintype J] {M : I → J → R}
    (h : rankOne M) (a : I → R) (b : J → R) (i : I) (j : J) :
    (∑ k, a k * (∑ l, b l * M k l)) * M i j =
      (∑ l, b l * M i l) * (∑ k, a k * M k j) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  calc
    a k * (b l * M k l) * M i j = a k * b l * (M i j * M k l) := by ring
    _ = a k * b l * (M i l * M k j) := by rw [h i k j l]
    _ = b l * M i l * (a k * M k j) := by ring

/-- Two weighted marginals with one shared nonzero contraction give an exact
reconstruction theorem even when the ordinary total of all entries is zero. -/
theorem weighted_panel_recovers [Fintype I] [Fintype J] {M N : I → J → R}
    (hM : rankOne M) (hN : rankOne N) (a : I → R) (b : J → R)
    (hNZ : (∑ i, a i * (∑ j, b j * M i j)) ≠ 0)
    (hrow : ∀ i, (∑ j, b j * M i j) = ∑ j, b j * N i j)
    (hcol : ∀ j, (∑ i, a i * M i j) = ∑ i, a i * N i j) :
    M = N := by
  have ht : (∑ i, a i * (∑ j, b j * M i j)) = ∑ i, a i * (∑ j, b j * N i j) := by
    simp_rw [hrow]
  funext i j
  apply mul_left_cancel₀ hNZ
  rw [weighted_contraction_identity hM a b, hrow i, hcol j, ht,
    weighted_contraction_identity hN a b]

/-- Nonzero weighted marginals in both directions certify a valid pivot
denominator for the rank-one reconstruction formula. -/
theorem weighted_marginals_certify_nonzero_contraction [Fintype I] [Fintype J]
    {M : I → J → R} (hM : rankOne M) (a : I → R) (b : J → R) (i : I) (j : J)
    (hrow : (∑ l, b l * M i l) ≠ 0) (hcol : (∑ k, a k * M k j) ≠ 0) :
    (∑ k, a k * (∑ l, b l * M k l)) ≠ 0 := by
  have hp := mul_ne_zero hrow hcol
  rw [← weighted_contraction_identity hM a b i j] at hp
  exact left_ne_zero_of_mul hp

/-- Linear transformation of the rows preserves determinantal rank one when a
nonzero unit pivot supplies a factorization. -/
theorem rank_one_survives_row_probes [Fintype I] {M : I → J → R} (i₀ : I) (j₀ : J)
    (h : rankOne M) (hunit : IsUnit (M i₀ j₀)) (probe : K → I → R) :
    rankOne (fun k j => ∑ i, probe k i * M i j) := by
  obtain ⟨u, v, hv, hu⟩ := unit_pivot_exact_factorization i₀ j₀ h hunit
  have hc (k : K) (j : J) :
      (∑ i, probe k i * M i j) = (∑ i, probe k i * u i) * v j := by
    simp_rw [hu, ← mul_assoc, Finset.sum_mul]
  intro i k j l
  simp_rw [hc]
  ring

end Domains
end GrochowTwoHundred.DeterminantalPanels

namespace GrochowTwoHundred.ExtensionPanels

def period (k d : ℕ) : ℕ := d / d.gcd k

private theorem period_pos {k d : ℕ} (hd : 0 < d) : 0 < period k d :=
  Nat.div_pos (Nat.gcd_le_left k hd) (Nat.gcd_pos_of_pos_left k hd)

private theorem period_dvd_iff {k d n : ℕ} (hd : 0 < d) :
    period k d ∣ n ↔ d ∣ k * n := by
  have hc : d.gcd k * period k d = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d k)
  have h := Nat.mul_dvd_mul_iff_left (b := period k d) (c := n) (Nat.gcd_pos_of_pos_left k hd)
  rw [hc] at h
  exact h.symm.trans Nat.dvd_gcd_mul_iff_dvd_mul

private theorem eq_multiples {d e : ℕ} (h : ∀ n, d ∣ n ↔ e ∣ n) : d = e :=
  Nat.dvd_antisymm ((h e).2 dvd_rfl) ((h d).1 dvd_rfl)

private theorem period_compose {d : ℕ} (hd : 0 < d) (k l : ℕ) :
    period l (period k d) = period (k * l) d := by
  apply eq_multiples
  intro n
  rw [period_dvd_iff (period_pos (k := k) hd), period_dvd_iff hd, period_dvd_iff hd,
    Nat.mul_assoc]

/-- The lcm of an arbitrary finite suite of paired power-cycle lengths
recovers the cycle after its gcd exponent. -/
theorem joint_period_gcd {d : ℕ} (hd : 0 < d) (s : Finset ℕ) :
    s.lcm (fun k => period k d) = period (s.gcd id) d := by
  apply eq_multiples
  intro n
  rw [Finset.lcm_dvd_iff, period_dvd_iff hd]
  have hg : (s.gcd fun k => k * n) = s.gcd id * n := by
    simpa using (Finset.gcd_mul_right (s := s) (f := id) (a := n))
  rw [← hg, Finset.dvd_gcd_iff]
  exact forall_congr' fun k => forall_congr' fun _ => period_dvd_iff hd

/-- The gcd-profile is a sufficient statistic for every paired observation:
a decoder recovers each listed period via a further power. -/
theorem recover_power_from_gcd {d k : ℕ} (hd : 0 < d) (s : Finset ℕ) (hk : k ∈ s) :
    period (k / s.gcd id) (period (s.gcd id) d) = period k d := by
  have hg : s.gcd id ∣ k := Finset.gcd_dvd (f := id) hk
  rw [period_compose hd, Nat.mul_div_cancel' hg]

/-- Pairing data on each original cycle is exactly as discriminating as a single
gcd-power test, even when a different subset of primes is lost by each exponent. -/
theorem joint_power_equivalence {d e : ℕ} (hd : 0 < d) (he : 0 < e) (s : Finset ℕ) :
    (∀ k ∈ s, period k d = period k e) ↔ period (s.gcd id) d = period (s.gcd id) e := by
  constructor
  · intro h
    rw [← joint_period_gcd hd, ← joint_period_gcd he]
    exact Finset.lcm_congr rfl h
  · intro h k hk
    rw [← recover_power_from_gcd hd s hk, ← recover_power_from_gcd he s hk, h]

/-- Knowing a common period bound permits unique recovery even if the tested
degrees share primes, provided those primes are disjoint from the bound. -/
theorem joint_period_recovers_bounded_lengths {d e bound : ℕ}
    (hd : 0 < d) (he : 0 < e) (hdb : d ∣ bound) (heb : e ∣ bound) (s : Finset ℕ)
    (hc : bound.Coprime (s.gcd id)) (h : ∀ k ∈ s, period k d = period k e) :
    d = e := by
  have hde := (joint_power_equivalence hd he s).mp h
  have hcd := hc.coprime_dvd_left hdb
  have hce := hc.coprime_dvd_left heb
  simpa [period, hcd.gcd_eq_one, hce.gcd_eq_one] using hde

/-- On all positive divisors of a nonzero period bound, the condition for paired
recovery is exact. If it fails, the common gcd divisor is a second hidden length. -/
theorem joint_period_injective_iff_coprime_bound (s : Finset ℕ) {bound : ℕ}
    (hb : 0 < bound) :
    (∀ d e : ℕ, 0 < d → 0 < e → d ∣ bound → e ∣ bound →
      (∀ k ∈ s, period k d = period k e) → d = e) ↔
    bound.Coprime (s.gcd id) := by
  constructor
  · intro h
    let d := bound.gcd (s.gcd id)
    have hd : 0 < d := Nat.gcd_pos_of_pos_left _ hb
    have hdiv : d ∣ bound := Nat.gcd_dvd_left _ _
    have hdiv' : d ∣ s.gcd id := Nat.gcd_dvd_right _ _
    have hlabel : ∀ k ∈ s, period k d = period k 1 := by
      intro k hk
      have hk' : d ∣ k := hdiv'.trans (Finset.gcd_dvd hk)
      have heq : d.gcd k = d := Nat.gcd_eq_left hk'
      rw [period, heq, Nat.div_self hd]
      simp [period]
    have hd₁ := h d 1 hd (by omega) hdiv (one_dvd _) hlabel
    exact hd₁
  · intro h d e hd he hdB heB
    exact joint_period_recovers_bounded_lengths hd he hdB heB s h

/-- A deleted panel retains all paired distinguishing power if its gcd stays the same. -/
theorem gcd_preserving_erasures_keep_all_labels (s t : Finset ℕ)
    (h : s.gcd id = t.gcd id) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (∀ k ∈ s, period k d = period k e) ↔ (∀ k ∈ t, period k d = period k e) := by
  rw [joint_power_equivalence hd he, joint_power_equivalence hd he, h]

/-- Inserting one auxiliary extension restores full paired recovery whenever
its exponent is coprime to the gcd of the existing suite. -/
theorem auxiliary_power_restores_recovery (s : Finset ℕ) (k : ℕ)
    (hcop : k.Coprime (s.gcd id)) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (h : ∀ l ∈ insert k s, period l d = period l e) :
    d = e := by
  have hg : (insert k s).gcd id = 1 := by
    rw [Finset.gcd_insert]
    exact hcop.gcd_eq_one
  have hh := (joint_power_equivalence hd he (insert k s)).mp h
  simpa [hg, period] using hh

/-- Simultaneously applying a common initial extension multiplies the
consolidated gcd exponent. -/
theorem common_preextension_consolidates (s : Finset ℕ) (b : ℕ) {d : ℕ}
    (hd : 0 < d) :
    s.lcm (fun k => period k (period b d)) = period (b * s.gcd id) d := by
  rw [joint_period_gcd (period_pos hd), period_compose hd]

/-- Paired data from two suites can be consolidated before or after joining
them, which permits lossless aggregation across independent computations. -/
theorem merge_extension_suites (s t : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    (s.lcm (fun k => period k d)).lcm (t.lcm (fun k => period k d)) =
      period ((s ∪ t).gcd id) d := by
  rw [← joint_period_gcd hd]
  apply eq_multiples
  intro n
  rw [Nat.lcm_dvd_iff]
  simp only [Finset.lcm_dvd_iff, Finset.mem_union]
  exact ⟨fun h k hk => hk.elim (h.1 k) (h.2 k),
    fun h => ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩⟩

end GrochowTwoHundred.ExtensionPanels

namespace GrochowTwoHundred.LinearPanels

section General
variable {I J K R : Type*} [Fintype I] [Fintype J] [CommRing R]

def read (A : J → I → R) (x : I → R) (j : J) : R := ∑ i, A j i * x i

def combine (D : K → J → R) (A : J → I → R) (k : K) (i : I) :=
  ∑ j, D k j * A j i

private theorem composed_read (D : K → J → R) (A : J → I → R) (x : I → R) (k : K) :
    read D (read A x) k = read (combine D A) x k := by
  unfold read combine
  simp_rw [Finset.mul_sum, ← mul_assoc, Finset.sum_mul]
  exact Finset.sum_comm

private theorem diagonal_decodes [DecidableEq I] {D : I → J → R} {A : J → I → R}
    {d : I → R} (h : ∀ i k, combine D A i k = if i = k then d i else 0)
    (x : I → R) (i : I) :
    read D (read A x) i = d i * x i := by
  rw [composed_read]
  unfold read
  simp_rw [h, ite_mul, zero_mul]
  simp

/-- A diagonal decoder with possibly zero gains still recovers a vector
on a known support where each gain is nonzero. -/
theorem certified_support_recovery [IsDomain R] [DecidableEq I]
    (D : I → J → R) (A : J → I → R) (d : I → R) (S : Set I) {x y : I → R}
    (h : ∀ i k, combine D A i k = if i = k then d i else 0)
    (hgain : ∀ i ∈ S, d i ≠ 0) (hoff : ∀ i ∉ S, x i = y i)
    (heq : read A x = read A y) : x = y := by
  funext i
  by_cases hi : i ∈ S
  · apply mul_left_cancel₀ (hgain i hi)
    rw [← diagonal_decodes h, ← diagonal_decodes h, heq]
  · exact hoff i hi

/-- A weighted Gram matrix certifies an injective observation map using only
inner products of the measurement columns. -/
theorem orthogonal_observations_recover [IsDomain R] [DecidableEq I]
    (A : J → I → R) (r : J → R) (d : I → R)
    (hGram : ∀ i k, (∑ j, r j * A j i * A j k) = if i = k then d i else 0)
    (hDiag : ∀ i, d i ≠ 0) : Function.Injective (read A) := by
  intro x y h
  let D := fun i j => r j * A j i
  exact certified_support_recovery D A d Set.univ (by simpa [D, combine] using hGram)
    (fun i _ => hDiag i) (fun i hi => (hi (Set.mem_univ i)).elim) h

/-- Weighted energy is exactly diagonal when the measured columns are
orthogonal, allowing the norm of a hidden profile to be read from the probes. -/
theorem orthogonal_panel_preserves_energy [DecidableEq I]
    (A : J → I → R) (r : J → R) (d : I → R) (x y : I → R)
    (hGram : ∀ i k, (∑ j, r j * A j i * A j k) = if i = k then d i else 0) :
    (∑ j, r j * read A x j * read A y j) = ∑ i, d i * x i * y i := by
  let D : I → J → R := fun i j => r j * A j i
  have hD : ∀ i k, combine D A i k = if i = k then d i else 0 := by
    simpa [D, combine] using hGram
  calc
    (∑ j, r j * read A x j * read A y j) =
        ∑ i, read D (read A x) i * y i := by
      unfold read
      rw [show (∑ j, r j * (∑ i, A j i * x i) * (∑ i, A j i * y i)) =
        ∑ j, (r j * (∑ i, A j i * x i)) * (∑ i, A j i * y i) by rfl]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      dsimp [D]
      ring
    _ = ∑ i, d i * x i * y i := by simp_rw [diagonal_decodes hD]

/-- Reversible per-channel scalings and added offsets do not compromise a
certified recovery panel. -/
theorem affine_channel_calibration_recovers [IsDomain R]
    (A : J → I → R) (scale offset : J → R)
    (hA : Function.Injective (read A)) (hs : ∀ j, scale j ≠ 0) :
    Function.Injective (fun x j => scale j * read A x j + offset j) := by
  intro x y h
  apply hA
  funext j
  exact mul_left_cancel₀ (hs j) (add_right_cancel (congrFun h j))

/-- A pair of complete tensor marginal panels determines every entry of an
arbitrary array when each axis measurement has a left inverse. -/
theorem independent_axis_panels_recover {L : Type*} [Fintype L]
    (A : J → I → R) (B : K → L → R)
    (hA : Function.Injective (read A)) (hB : Function.Injective (read B))
    {x y : I → L → R}
    (h : ∀ j k, read B (fun l => read A (fun i => x i l) j) k =
      read B (fun l => read A (fun i => y i l) j) k) :
    x = y := by
  have hAcross (j : J) := hB (funext (h j))
  have hin (l : L) : (fun i => x i l) = (fun i => y i l) :=
    hA (funext fun j => congrFun (hAcross j) l)
  funext i l
  exact congrFun (hin l) i

/-- Measuring an arbitrary array along a recovered axis determines its product
against any coefficient vector in the remaining direction. -/
theorem axis_probe_readouts_transfer {L : Type*} [Fintype L]
    (A : J → I → R) (b : L → R) {x y : I → L → R}
    (hA : Function.Injective (read A))
    (h : ∀ j, (∑ l, b l * read A (fun i => x i l) j) =
      ∑ l, b l * read A (fun i => y i l) j) :
    ∀ i, (∑ l, b l * x i l) = ∑ l, b l * y i l := by
  have he (z : I → L → R) (j : J) :
      (∑ l, b l * read A (fun i => z i l) j) =
      read A (fun i => ∑ l, b l * z i l) j := by
    unfold read
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hf := hA (funext fun j => (he x j).symm.trans ((h j).trans (he y j)))
  exact congrFun hf

end General

section Integral
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

/-- If a diagonal integer decoder's worst possible noise at every coordinate
is smaller than its nonzero gain, the recovered integral profile is unique. -/
theorem integer_panel_stable_under_noise {D : I → J → ℤ} {A : J → I → ℤ}
    {d : I → ℤ} {x y : I → ℤ} (ε : J → ℤ)
    (h : ∀ i k, combine D A i k = if i = k then d i else 0)
    (hobs : ∀ j, |read A x j - read A y j| ≤ ε j)
    (hgain : ∀ i, (∑ j, |D i j| * ε j) < |d i|) :
    x = y := by
  let z := fun i => x i - y i
  have hr (j : J) : read A z j = read A x j - read A y j := by
    simp [read, z, mul_sub, Finset.sum_sub_distrib]
  funext i
  by_contra hn
  have hzn : z i ≠ 0 := sub_ne_zero.mpr hn
  have hone : 1 ≤ |z i| := by have := abs_pos.mpr hzn; omega
  have hbase : |d i| ≤ |d i| * |z i| := by
    simpa using (mul_le_mul_of_nonneg_left hone (abs_nonneg (d i)))
  have hbound : |read D (read A z) i| ≤ ∑ j, |D i j| * ε j := by
    change |∑ j, D i j * read A z j| ≤ ∑ j, |D i j| * ε j
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [← hr j] using hobs j) (abs_nonneg _)
  rw [diagonal_decodes h, abs_mul] at hbound
  exact (not_le_of_gt (hgain i)) (hbase.trans hbound)

/-- Coefficient errors may vary by measurement channel and candidate. A
triangle inequality converts independent observation intervals into stability. -/
theorem independent_error_budgets_recover {D : I → J → ℤ} {A : J → I → ℤ}
    {d : I → ℤ} {x y : I → ℤ} (measured e₁ e₂ : J → ℤ)
    (h : ∀ i k, combine D A i k = if i = k then d i else 0)
    (h₁ : ∀ j, |read A x j - measured j| ≤ e₁ j)
    (h₂ : ∀ j, |read A y j - measured j| ≤ e₂ j)
    (hgain : ∀ i, (∑ j, |D i j| * (e₁ j + e₂ j)) < |d i|) :
    x = y := by
  apply integer_panel_stable_under_noise (fun j => e₁ j + e₂ j) h _ hgain
  intro j
  calc
    |read A x j - read A y j| =
      |(read A x j - measured j) + (-(read A y j - measured j))| := by congr 1 <;> ring
    _ ≤ |read A x j - measured j| + |-(read A y j - measured j)| := by
      exact abs_add_le ..
    _ ≤ e₁ j + e₂ j := by rw [abs_neg]; exact add_le_add (h₁ j) (h₂ j)

end Integral
end GrochowTwoHundred.LinearPanels

namespace GrochowTwoHundred.TriangularPanels

variable {R : Type*} [CommRing R]

def probe (s : Finset ℕ) (M : ℕ → ℕ → R) (z : ℕ → R) (i : ℕ) : R :=
  ∑ j ∈ s, M i j * z j

/-- Local pivot injectivity suffices for recovering a finite profile from any
collection of upper-zero rows with arbitrary lower terms. -/
theorem triangular_local_recovery (s : Finset ℕ) (M : ℕ → ℕ → R) (z : ℕ → R)
    (condition : ℕ → R → Prop)
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hObs : ∀ i ∈ s, condition i (probe s M z i))
    (hPivot : ∀ i ∈ s, condition i (M i i * z i) → z i = 0) :
    ∀ i ∈ s, z i = 0 := by
  classical
  by_contra! h
  let S := s.filter (fun i => z i ≠ 0)
  obtain ⟨k, hks, hkz⟩ := h
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S id
    ⟨k, Finset.mem_filter.mpr ⟨hks, hkz⟩⟩
  obtain ⟨his, hzi⟩ := Finset.mem_filter.mp hi
  have hp : probe s M z i = M i i * z i := by
    unfold probe
    apply Finset.sum_eq_single_of_mem i his
    intro j hjs hji
    by_cases hzj : z j = 0
    · simp [hzj]
    · have hij : i ≤ j := hmin j (Finset.mem_filter.mpr ⟨hjs, hzj⟩)
      simp [hUpper i his j hjs (lt_of_le_of_ne hij (Ne.symm hji))]
  exact hzi (hPivot i his (hp ▸ hObs i his))

/-- On a triangular panel over a domain, equal readings force equality on the
entire finite support, even for nonunit pivots. -/
theorem triangular_exact_recovers [IsDomain R] (s : Finset ℕ) (M : ℕ → ℕ → R) {x y : ℕ → R}
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hDiag : ∀ i ∈ s, M i i ≠ 0)
    (hObs : ∀ i ∈ s, probe s M x i = probe s M y i) : ∀ i ∈ s, x i = y i := by
  have h := triangular_local_recovery s M (fun i => x i - y i) (fun _ v => v = 0) hUpper
    (fun i hi => by simpa [probe, mul_sub, Finset.sum_sub_distrib] using sub_eq_zero.mpr (hObs i hi))
    (fun i hi h => (mul_eq_zero.mp h).resolve_left (hDiag i hi))
  exact fun i hi => sub_eq_zero.mp (h i hi)

/-- Nonunit diagonal coefficients admit a precise effective residue modulus.
One can remove a common divisor before testing coprimality and the size bound. -/
theorem triangular_nonunit_modular_recovery (s : Finset ℕ) (M : ℕ → ℕ → ℤ) (z : ℕ → ℤ)
    (common reduced diagonal : ℕ → ℤ)
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hFactor : ∀ i ∈ s, common i ≠ 0 ∧ M i i = common i * diagonal i)
    (hReduced : ∀ i ∈ s, 0 < reduced i ∧ IsCoprime (reduced i) (diagonal i))
    (hsize : ∀ i ∈ s, |z i| < reduced i)
    (hObs : ∀ i ∈ s, common i * reduced i ∣ probe s M z i) :
    ∀ i ∈ s, z i = 0 := by
  apply triangular_local_recovery s M z (fun i v => common i * reduced i ∣ v) hUpper hObs
  intro i hi h
  rw [(hFactor i hi).2, mul_assoc] at h
  have hred := Int.dvd_of_mul_dvd_mul_left (hFactor i hi).1 h
  have hd := (hReduced i hi).2.dvd_of_dvd_mul_left hred
  by_contra hn
  have hge := WeightedCycles.abs_dvd_lower (hReduced i hi).1 hd hn
  exact (not_le_of_gt (hsize i hi)) hge

/-- Different channels may supply independently coprime residues for each row.
Their product is the effective range for a triangular reconstruction. -/
theorem triangular_coprime_panel_recovery (s : Finset ℕ) (M : ℕ → ℕ → ℤ) (z : ℕ → ℤ)
    (m n : ℕ → ℤ)
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hmod : ∀ i ∈ s, IsCoprime (m i) (n i))
    (hunit : ∀ i ∈ s, IsCoprime (m i * n i) (M i i))
    (hpos : ∀ i ∈ s, 0 < m i * n i) (hsize : ∀ i ∈ s, |z i| < m i * n i)
    (hObs₁ : ∀ i ∈ s, m i ∣ probe s M z i)
    (hObs₂ : ∀ i ∈ s, n i ∣ probe s M z i) :
    ∀ i ∈ s, z i = 0 := by
  refine triangular_nonunit_modular_recovery s M z (fun _ => 1) (fun i => m i * n i)
    (fun i => M i i) hUpper (fun _ _ => by simp) (fun i hi => ⟨hpos i hi, hunit i hi⟩)
    hsize ?_
  intro i hi
  simpa using (hmod i hi).mul_dvd (hObs₁ i hi) (hObs₂ i hi)

/-- An absolute error smaller than each pivot magnitude uniquely determines
the integral profile from a triangular panel. -/
theorem triangular_stable_under_noise (s : Finset ℕ) (M : ℕ → ℕ → ℤ) (z : ℕ → ℤ)
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hObs : ∀ i ∈ s, |probe s M z i| < |M i i|) :
    ∀ i ∈ s, z i = 0 := by
  apply triangular_local_recovery s M z (fun i v => |v| < |M i i|) hUpper hObs
  intro i _ h
  by_contra hn
  have hz := WeightedCycles.abs_at_least_one hn
  rw [abs_mul] at h
  have hm := mul_le_mul_of_nonneg_left hz (abs_nonneg (M i i))
  exact (not_le_of_gt h) (by simpa using hm)

/-- Distinct interval centres are harmless after taking the observed differences:
two integer profiles obeying shared intervals narrower than their pivot gains
must be equal. -/
theorem triangular_shared_intervals_recover (s : Finset ℕ) (M : ℕ → ℕ → ℤ)
    {x y : ℕ → ℤ} (centre leftErr rightErr : ℕ → ℤ)
    (hUpper : ∀ i ∈ s, ∀ j ∈ s, i < j → M i j = 0)
    (hX : ∀ i ∈ s, |probe s M x i - centre i| ≤ leftErr i)
    (hY : ∀ i ∈ s, |probe s M y i - centre i| ≤ rightErr i)
    (hErr : ∀ i ∈ s, leftErr i + rightErr i < |M i i|) :
    ∀ i ∈ s, x i = y i := by
  have h := triangular_stable_under_noise s M (fun i => x i - y i) hUpper ?_
  · exact fun i hi => sub_eq_zero.mp (h i hi)
  intro i hi
  rw [show probe s M (fun i => x i - y i) i = (probe s M x i - centre i) +
    (-(probe s M y i - centre i)) by
      simp only [probe, mul_sub, Finset.sum_sub_distrib] <;> ring]
  have htriangle := abs_add_le (probe s M x i - centre i) (-(probe s M y i - centre i))
  rw [abs_neg] at htriangle
  exact (htriangle.trans (add_le_add (hX i hi) (hY i hi))).trans_lt (hErr i hi)

/-- A column whose coefficients are all divisible by their row moduli yields an
explicit invisible unit perturbation, with no triangularity requirement. -/
theorem invisible_column_modular_witness (s : Finset ℕ) (M : ℕ → ℕ → ℤ)
    (m : ℕ → ℤ) (j : ℕ) (hj : j ∈ s)
    (hmod : ∀ i ∈ s, m i ∣ M i j) :
    ∃ z : ℕ → ℤ, z j = 1 ∧ ∀ i ∈ s, m i ∣ probe s M z i := by
  let z : ℕ → ℤ := fun i => if i = j then 1 else 0
  refine ⟨z, by simp [z], ?_⟩
  intro i hi
  have hread : probe s M z i = M i j := by
    simp [probe, z, mul_ite, hj]
  rw [hread]
  exact hmod i hi

end GrochowTwoHundred.TriangularPanels

