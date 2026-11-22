import Mathlib

namespace BlindGrochowHundred.CycleRecovery

/-- Length of a constituent cycle after taking the k-th power. -/
def period (k d : ℕ) : ℕ := d / d.gcd k

private theorem eq_of_same_multiples {d e : ℕ} (h : ∀ n, d ∣ n ↔ e ∣ n) : d = e :=
  Nat.dvd_antisymm ((h e).2 (dvd_refl e)) ((h d).1 (dvd_refl d))

private theorem powered_period_positive {k d : ℕ} (hd : 0 < d) : 0 < period k d := by
  unfold period
  exact Nat.div_pos (Nat.gcd_le_left k hd) (Nat.gcd_pos_of_pos_left k hd)

/-- An old length returns at the powered time exactly when its new period divides the time. -/
theorem powered_period_schedule {k d n : ℕ} (hd : 0 < d) :
    period k d ∣ n ↔ d ∣ k * n := by
  have hg := Nat.gcd_pos_of_pos_left k hd
  have hc : d.gcd k * period k d = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d k)
  have h := Nat.mul_dvd_mul_iff_left (b := period k d) (c := n) hg
  rw [hc] at h
  exact h.symm.trans Nat.dvd_gcd_mul_iff_dvd_mul

theorem successive_extensions {d : ℕ} (hd : 0 < d) (k l : ℕ) :
    period l (period k d) = period (k * l) d := by
  apply eq_of_same_multiples
  intro n
  rw [powered_period_schedule (powered_period_positive (k := k) hd),
    powered_period_schedule hd, powered_period_schedule hd, Nat.mul_assoc]

theorem period_of_disjoint_union {d e : ℕ} (hd : 0 < d) (he : 0 < e) (k : ℕ) :
    period k (d.lcm e) = (period k d).lcm (period k e) := by
  apply eq_of_same_multiples
  intro n
  rw [powered_period_schedule (Nat.lcm_pos hd he), Nat.lcm_dvd_iff, Nat.lcm_dvd_iff,
    powered_period_schedule hd, powered_period_schedule he]

/-- Simultaneous knowledge of the powered periods recovers the period at the gcd exponent. -/
theorem matching_two_periods_recovers_gcd {d : ℕ} (hd : 0 < d) (k l : ℕ) :
    (period k d).lcm (period l d) = period (k.gcd l) d := by
  apply eq_of_same_multiples
  intro n
  rw [Nat.lcm_dvd_iff, powered_period_schedule hd, powered_period_schedule hd,
    powered_period_schedule hd, ← Nat.gcd_mul_right]
  exact Nat.dvd_gcd_iff.symm

theorem matching_coprime_periods_injective {k l : ℕ} (hkl : k.Coprime l) :
    Function.Injective (fun d : ℕ+ => (period k d.val, period l d.val)) := by
  intro a b h
  have ha := matching_two_periods_recovers_gcd a.property k l
  have hb := matching_two_periods_recovers_gcd b.property k l
  rw [hkl.gcd_eq_one] at ha hb
  have hone (d : ℕ) : period 1 d = d := by simp [period]
  rw [hone] at ha hb
  apply Subtype.ext
  exact ha.symm.trans ((congrArg (fun z : ℕ × ℕ => z.1.lcm z.2) h).trans hb)

/-- For bounded period, the power schedule factors through the divisors of the period bound. -/
theorem period_modulo_bound {d bound : ℕ} (hd : 0 < d) (hdb : d ∣ bound) (k : ℕ) :
    period (k.gcd bound) d = period k d := by
  apply eq_of_same_multiples
  intro n
  rw [powered_period_schedule hd, powered_period_schedule hd, ← Nat.gcd_mul_right,
    Nat.dvd_gcd_iff]
  exact and_iff_left (dvd_trans hdb (Nat.dvd_mul_right bound n))

theorem period_monotone_in_cycle_length {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hde : d ∣ e) (k : ℕ) :
    period k d ∣ period k e :=
  (powered_period_schedule hd).2
    (dvd_trans hde ((powered_period_schedule he).1 (dvd_refl (period k e))))

theorem period_antitone_in_extension {d k l : ℕ} (hd : 0 < d) (hkl : k ∣ l) :
    period l d ∣ period k d :=
  (powered_period_schedule hd).2
    (dvd_trans ((powered_period_schedule hd).1 (dvd_refl (period k d)))
      (Nat.mul_dvd_mul_right hkl (period k d)))

/-- Characterization of all original lengths yielding the same powered period. -/
theorem powered_period_fibre {k d r : ℕ} (hd : 0 < d) :
    period k d = r ↔ ∃ g, g ∣ k ∧ d = r * g ∧ r.Coprime (k / g) := by
  constructor
  · intro h
    refine ⟨d.gcd k, Nat.gcd_dvd_right d k, ?_, ?_⟩
    · rw [← h]
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left d k)).symm
    · rw [← h]
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left k hd)
  · rintro ⟨g, hg, hprod, hcop⟩
    have hgpos : 0 < g := by
      by_contra! h
      have hg0 : g = 0 := by omega
      simp [hg0] at hprod
      omega
    have hk : k / g * g = k := Nat.div_mul_cancel hg
    have hgd : d.gcd k = g := by
      rw [← hk, hprod, Nat.gcd_mul_right, hcop.gcd_eq_one, Nat.one_mul]
    unfold period
    rw [hgd, hprod, Nat.mul_div_cancel _ hgpos]


/-- The mass of weighted cycle counts in a known subset. -/
def totalMass (s : Finset ℕ) (a : ℕ → ℕ) := ∑ d ∈ s, d * a d

/-- Fixed point count of a permutation power in cycle notation. -/
def mark (s : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) :=
  ∑ d ∈ s, if d ∣ n then d * a d else 0

theorem bounded_period_mark_factors {s : Finset ℕ} (a : ℕ → ℕ) {N : ℕ}
    (hs : ∀ d ∈ s, d ∣ N) (n : ℕ) : mark s a (n.gcd N) = mark s a n := by
  unfold mark
  apply Finset.sum_congr rfl
  intro d hd
  have h : d ∣ n.gcd N ↔ d ∣ n := by
    rw [Nat.dvd_gcd_iff]
    exact and_iff_left (hs d hd)
  simp only [h]

/-- Powering followed by a fixed-point test uses the same counts as multiplying times. -/
theorem fixed_point_count_after_extension {s : Finset ℕ} (a : ℕ → ℕ)
    (hs : ∀ d ∈ s, 0 < d) (k n : ℕ) :
    (∑ d ∈ s, if period k d ∣ n then d * a d else 0) = mark s a (k * n) := by
  unfold mark
  apply Finset.sum_congr rfl
  intro d hd
  simp only [powered_period_schedule (hs d hd)]

theorem period_bound_saturates_mark {s : Finset ℕ} {a : ℕ → ℕ} {bound : ℕ}
    (hs : ∀ d ∈ s, d ∣ bound) (n : ℕ) :
    mark s a (bound * n) = totalMass s a := by
  unfold mark totalMass
  apply Finset.sum_congr rfl
  intro d hd
  simp [dvd_trans (hs d hd) (Nat.dvd_mul_right bound n)]

theorem support_bound_from_single_mark {s : Finset ℕ} {a : ℕ → ℕ} {bound : ℕ}
    (h : mark s a bound = totalMass s a) :
    ∀ d ∈ s, 0 < d → 0 < a d → d ∣ bound := by
  intro d hd hdpos hapos
  by_contra hn
  have hm (u : ℕ) : (if u ∣ bound then u * a u else 0) ≤ u * a u := by split <;> omega
  have hl : (if d ∣ bound then d * a d else 0) < d * a d := by
    simpa [hn] using (Nat.mul_pos hdpos hapos)
  apply (not_lt_of_ge (le_of_eq h.symm))
  unfold mark totalMass
  rw [← Finset.sum_erase_add s (fun u => if u ∣ bound then u * a u else 0) hd,
    ← Finset.sum_erase_add s (fun u => u * a u) hd]
  exact add_lt_add_of_le_of_lt (Finset.sum_le_sum fun i _ => hm i) hl

theorem lcm_schedule_preserves_full_return {s : Finset ℕ} {a : ℕ → ℕ} {L M : ℕ}
    (ha : mark s a L = totalMass s a) :
    mark s a (L.lcm M) = totalMass s a := by
  unfold mark totalMass
  apply Finset.sum_congr rfl
  intro d hd
  rcases Nat.eq_zero_or_pos d with hz | hdpos
  · simp [hz]
  rcases Nat.eq_zero_or_pos (a d) with hz | hapos
  · simp [hz]
  simp [dvd_trans (support_bound_from_single_mark ha d hd hdpos hapos) (Nat.dvd_lcm_left L M)]

/-- A complete mark gives a sharp bound on each weight unseen by partial return. -/
theorem undetected_cycle_weight_bound {s : Finset ℕ} {a : ℕ → ℕ} (d n : ℕ)
    (hd : d ∈ s) (hmiss : ¬ d ∣ n) :
    mark s a n + d * a d ≤ totalMass s a := by
  unfold mark totalMass
  rw [← Finset.sum_erase_add s (fun u => if u ∣ n then u * a u else 0) hd,
    ← Finset.sum_erase_add s (fun u => u * a u) hd]
  simp only [if_neg hmiss, add_zero]
  exact Nat.add_le_add_right (Finset.sum_le_sum fun i _ => by split <;> omega) _

end BlindGrochowHundred.CycleRecovery


namespace BlindGrochowHundred.Tomography

def deck {I V R : Type*} [DecidableEq V] [AddCommMonoid R]
    (s : Finset I) (p : I → V) (w : I → R) (u : V) : R :=
  ∑ i ∈ s, if p i = u then w i else 0

theorem deck_conserves_total {I V R : Type*} [DecidableEq V] [AddCommMonoid R]
    (s : Finset I) (p : I → V) (w : I → R) :
    (∑ u ∈ s.image p, deck s p w u) = ∑ i ∈ s, w i := by
  classical
  unfold deck
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem (p i) (Finset.mem_image_of_mem p hi)]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]

theorem coarsening_preserves_deck {I U V R : Type*} [DecidableEq U] [DecidableEq V]
    [AddCommMonoid R] (s : Finset I) (p : I → U) (q : U → V) (w : I → R) :
    deck (s.image p) q (deck s p w) = deck s (q ∘ p) w := by
  classical
  ext z
  unfold deck
  simp only [← Finset.sum_filter (s := s.image p)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : q (p i) = z
  · have hm : p i ∈ (s.image p).filter (fun u => q u = z) :=
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem p hi, hz⟩
    rw [Finset.sum_eq_single_of_mem (p i) hm]
    · simp [hz]
    · intro u hu hne
      simp [Ne.symm hne]
  · have hzero : ∀ u ∈ (s.image p).filter (fun u => q u = z), p i ≠ u := by
      intro u hu h
      exact hz (h.symm ▸ (Finset.mem_filter.mp hu).2)
    rw [Finset.sum_eq_zero]
    · simp [hz]
    · intro u hu
      simp [hzero u hu]

theorem injective_labels_recover_mass {I V R : Type*} [DecidableEq V] [AddCommMonoid R]
    {s : Finset I} {p : I → V} {w w' : I → R}
    (hinj : Set.InjOn p (↑s : Set I)) (hobs : deck s p w = deck s p w') :
    ∀ i ∈ s, w i = w' i := by
  intro i hi
  have h₁ := congrFun hobs (p i)
  unfold deck at h₁
  have h₂ (a : I → R) : (∑ j ∈ s, if p j = p i then a j else 0) = a i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp
    · intro j hj hne
      simp [show p j ≠ p i from fun h => hne (hinj hj hi h)]
  rw [h₂, h₂] at h₁
  exact h₁

theorem paired_coprime_extension_recovers_weights {R : Type*} [AddCommMonoid R]
    {s : Finset ℕ+} {k l : ℕ} {w w' : ℕ+ → R}
    (hkl : k.Coprime l)
    (h : deck s (fun d : ℕ+ => (CycleRecovery.period k d.val, CycleRecovery.period l d.val)) w =
         deck s (fun d : ℕ+ => (CycleRecovery.period k d.val, CycleRecovery.period l d.val)) w') :
    ∀ d ∈ s, w d = w' d :=
  injective_labels_recover_mass (CycleRecovery.matching_coprime_periods_injective hkl).injOn h

/-- Signed weights are uniquely determined by multiple overlapping decks when each
disagreement set exposes a singleton fibre in one of the available decks. -/
theorem singleton_fibre_panel_recovers_weights {I V R : Type*} [DecidableEq V]
    [AddCommGroup R] (s : Finset I) {w w' : I → R} (p : ℕ → I → V)
    (hrows : ∀ t ⊆ s, t.Nonempty → ∃ i ∈ t, ∃ k,
      ∀ j ∈ t, p k j = p k i → j = i)
    (hsums : ∀ k, deck s (p k) w = deck s (p k) w') :
    ∀ i ∈ s, w i = w' i := by
  classical
  by_contra! h
  obtain ⟨e, he, hne⟩ := h
  let t := s.filter (fun i => w i ≠ w' i)
  have ht : t.Nonempty := ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩⟩
  obtain ⟨i, hi, k, hk⟩ := hrows t (Finset.filter_subset _ _) ht
  obtain ⟨his, hni⟩ := Finset.mem_filter.mp hi
  have hsum := congrFun (hsums k) (p k i)
  unfold deck at hsum
  rw [← Finset.sum_erase_add s (fun j => if p k j = p k i then w j else 0) his,
    ← Finset.sum_erase_add s (fun j => if p k j = p k i then w' j else 0) his] at hsum
  have off : (∑ j ∈ s.erase i, if p k j = p k i then w j else 0) =
      ∑ j ∈ s.erase i, if p k j = p k i then w' j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    by_cases hp : p k j = p k i
    · by_cases hw : w j = w' j
      · simp [hp, hw]
      · exact (hji (hk j (Finset.mem_filter.mpr ⟨hjs, hw⟩) hp)).elim
    · simp [hp]
  rw [off] at hsum
  simp only [if_pos rfl] at hsum
  exact hni (add_left_cancel hsum)

/-- A collection of sound test indices can be kept while replacing all other decks arbitrarily. -/
theorem recovery_after_declared_erasures {I V R : Type*} [DecidableEq V]
    [AddCommGroup R] (s : Finset I) {w w' : I → R} (p : ℕ → I → V) (sound : Set ℕ)
    (hrows : ∀ t ⊆ s, t.Nonempty → ∃ i ∈ t, ∃ k ∈ sound,
      ∀ j ∈ t, p k j = p k i → j = i)
    (hsums : ∀ k ∈ sound, deck s (p k) w = deck s (p k) w') :
    ∀ i ∈ s, w i = w' i := by
  classical
  have hnonempty (hs : s.Nonempty) : sound.Nonempty := by
    obtain ⟨_, _, k, hk, _⟩ := hrows s (fun _ h => h) hs
    exact ⟨k, hk⟩
  by_cases hs : s.Nonempty
  · let fallback := (hnonempty hs).choose
    have hfall : fallback ∈ sound := (hnonempty hs).choose_spec
    let panel := fun k => if k ∈ sound then p k else p fallback
    apply singleton_fibre_panel_recovers_weights s panel
    · intro t ht hne
      obtain ⟨i, hi, k, hks, hk⟩ := hrows t ht hne
      exact ⟨i, hi, k, by simpa [panel, hks] using hk⟩
    · intro k
      by_cases hk : k ∈ sound
      · simpa [panel, hk] using hsums k hk
      · simpa [panel, hk] using hsums fallback hfall
  · intro i hi
    exact (hs ⟨i, hi⟩).elim

section OuterProducts
variable {I J R : Type*} [Fintype I] [Fintype J]

/-- Two marginals reconstruct a rank-one table up to the single total-mass scalar. -/
private theorem outer_product_marginal_identity [CommSemiring R] (u : I → R) (v : J → R)
    (i : I) (j : J) :
    ((∑ x, u x) * (∑ y, v y)) * (u i * v j) =
      (∑ y, u i * v y) * (∑ x, u x * v j) := by
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem nonzero_mass_marginals_recover_rank_one [CommRing R] [IsDomain R]
    (u u' : I → R) (v v' : J → R)
    (ht : (∑ i, u i) * (∑ j, v j) = (∑ i, u' i) * (∑ j, v' j))
    (hnz : (∑ i, u i) * (∑ j, v j) ≠ 0)
    (hrow : ∀ i, (∑ j, u i * v j) = ∑ j, u' i * v' j)
    (hcol : ∀ j, (∑ i, u i * v j) = ∑ i, u' i * v' j) :
    ∀ i j, u i * v j = u' i * v' j := by
  intro i j
  have h₁ := outer_product_marginal_identity u v i j
  have h₂ := outer_product_marginal_identity u' v' i j
  rw [← ht, ← hrow i, ← hcol j] at h₂
  exact mul_left_cancel₀ hnz (h₁.trans h₂.symm)

omit [Fintype I] in
theorem product_with_known_factor_recovers_first [CommRing R] [IsDomain R]
    (u u' : I → R) (v : J → R)
    (hnz : ∑ j, v j ≠ 0)
    (h : ∀ i, (∑ j, u i * v j) = ∑ j, u' i * v j) :
    u = u' := by
  funext i
  apply mul_right_cancel₀ hnz
  simpa only [Finset.mul_sum] using h i

end OuterProducts

/-- An explicit weighted rectangle collision respecting all four divisibility requirements. -/
theorem weighted_rectangle_collision (a b c d L : ℤ)
    (hL : L ≠ 0) (ha : a ∣ L) (hb : b ∣ L) (hc : c ∣ L) (hd : d ∣ L) :
    ∃ x y z w : ℤ, x ≠ 0 ∧ a ∣ x ∧ b ∣ y ∧ c ∣ z ∧ d ∣ w ∧
      x + y = 0 ∧ z + w = 0 ∧ x + z = 0 ∧ y + w = 0 := by
  exact ⟨L, -L, -L, L, hL, ha, dvd_neg.mpr hb, dvd_neg.mpr hc, hd, by simp,
    by simp, by simp, by simp⟩

theorem weighted_rectangle_minimum_mass (x y z w L : ℤ)
    (hL : 0 < L) (hdiv : L ∣ x) (hnz : x ≠ 0)
    (hr : x + y = 0) (hc : x + z = 0) (hrest : z + w = 0) :
    4 * L ≤ |x| + |y| + |z| + |w| := by
  have hy : y = -x := by omega
  have hz : z = -x := by omega
  have hw : w = x := by omega
  rw [hy, hz, hw, abs_neg]
  obtain ⟨k, hk⟩ := hdiv
  have hknz : k ≠ 0 := by
    intro h
    apply hnz
    simp [hk, h]
  have hab : 1 ≤ |k| := by
    have := abs_pos.mpr hknz
    omega
  have hlx : L ≤ |x| := by
    rw [hk, abs_mul, abs_of_pos hL]
    simpa using (mul_le_mul_of_nonneg_left hab (le_of_lt hL))
  omega

end BlindGrochowHundred.Tomography
