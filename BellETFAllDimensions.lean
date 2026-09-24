/- For every integer d >= 2, constructs a normalized maximally entangled
equiangular tight frame of d^2+1 vectors in C^d tensor C^d.
Answers the existence question in Section IX of Wei, Cobucci and Tavakoli,
Nonprojective Bell-state measurements, Phys. Rev. A 110, 042206 (2024). -/
import Mathlib


open scoped BigOperators

namespace HarmonicFrame

theorem root_exists {N : ℕ} (hN : 0 < N) : ∃ w : ℂ, IsPrimitiveRoot w N :=
  ⟨_, Complex.isPrimitiveRoot_exp N (Nat.ne_of_gt hN)⟩

theorem root_unit {N : ℕ} (hN : 0 < N) (w : ℂ) (hw : IsPrimitiveRoot w N) (r : ℕ) :
    w^r * star (w^r) = 1 := by
  have hn := hw.norm'_eq_one (Nat.ne_of_gt hN)
  change w^r * (starRingEnd ℂ) (w^r) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hn]
  norm_num

theorem root_unit' {N : ℕ} (hN : 0 < N) (w : ℂ) (hw : IsPrimitiveRoot w N) (r : ℕ) :
    star (w^r) * w^r = 1 := by
  rw [mul_comm]
  exact root_unit hN w hw r

theorem finite_geometric_zero {N : ℕ} (q : ℂ) (hq : q^N = 1) (hne : q ≠ 1) :
    (∑ j : Fin N, q^j.val) = 0 := by
  have h := geom_sum_mul q N
  rw [hq, sub_self] at h
  have hs := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  simpa only [Fin.sum_univ_eq_sum_range] using hs

theorem full_orthogonality {N : ℕ} (hN : 0 < N) (w : ℂ)
    (hw : IsPrimitiveRoot w N) (r s : Fin N) :
    (∑ j : Fin N, w^(r.val*j.val) * star (w^(s.val*j.val))) =
      if r = s then (N : ℂ) else 0 := by
  by_cases hrs : r = s
  · subst s
    simp only [root_unit hN w hw]
    simp
  · rw [if_neg hrs]
    let q := w^r.val * star (w^s.val)
    have hq : q^N = 1 := by
      change (w^r.val * star (w^s.val))^N = 1
      rw [mul_pow, ← star_pow, ← pow_mul, ← pow_mul,
        Nat.mul_comm r.val N, Nat.mul_comm s.val N, pow_mul, pow_mul, hw.pow_eq_one]
      simp
    have hne : q ≠ 1 := by
      intro he
      have heq : w^r.val = w^s.val := by
        have hx := congrArg (fun x : ℂ => x * w^s.val) he
        change (w^r.val * star (w^s.val)) * w^s.val = 1 * w^s.val at hx
        rw [mul_assoc, root_unit' hN w hw s.val, mul_one, one_mul] at hx
        exact hx
      exact hrs (Fin.ext (hw.pow_inj r.isLt s.isLt heq))
    convert finite_geometric_zero q hq hne using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [q, mul_pow, pow_mul, star_pow]

theorem truncated_gram {n : ℕ} (w : ℂ) (hw : IsPrimitiveRoot w (n+1))
    (j k : Fin (n+1)) (hjk : j ≠ k) :
    (∑ r : Fin n, star (w^(r.val*j.val)) * w^(r.val*k.val)) =
      -(star (w^(n*j.val)) * w^(n*k.val)) := by
  have h := full_orthogonality (Nat.succ_pos n) w hw k j
  rw [if_neg (Ne.symm hjk), Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last] at h
  have h' : (∑ r : Fin n, star (w^(r.val*j.val)) * w^(r.val*k.val)) +
      star (w^(n*j.val)) * w^(n*k.val) = 0 := by
    simpa only [Nat.mul_comm, mul_comm] using h
  exact eq_neg_of_add_eq_zero_left h'

theorem weighted_gram {n : ℕ} (w : ℂ) (c : Fin n → ℂ)
    (hc : ∀ i, star (c i)*c i = 1) (j k : Fin (n+1)) :
    (∑ i : Fin n, star (c i*w^(i.val*j.val)) * (c i*w^(i.val*k.val))) =
      ∑ i : Fin n, star (w^(i.val*j.val)) * w^(i.val*k.val) := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (star (c i)*c i) * (star (w^(i.val*j.val))*w^(i.val*k.val)) := by
      rw [star_mul]; ring
    _ = _ := by rw [hc, one_mul]

theorem weighted_norm {n : ℕ} (w : ℂ) (hw : IsPrimitiveRoot w (n+1))
    (c : Fin n → ℂ) (hc : ∀ i, star (c i)*c i = 1) (j : Fin (n+1)) :
    (∑ i : Fin n, star (c i*w^(i.val*j.val)) * (c i*w^(i.val*j.val))) = (n:ℂ) := by
  rw [weighted_gram w c hc j j]
  simp_rw [root_unit' (Nat.succ_pos n) w hw]
  simp

theorem weighted_equiangular {n : ℕ} (w : ℂ) (hw : IsPrimitiveRoot w (n+1))
    (c : Fin n → ℂ) (hc : ∀ i, star (c i)*c i = 1)
    (j k : Fin (n+1)) (hjk : j ≠ k) :
    Complex.normSq (∑ i : Fin n,
      star (c i*w^(i.val*j.val)) * (c i*w^(i.val*k.val))) = 1 := by
  rw [weighted_gram w c hc j k, truncated_gram w hw j k hjk]
  have hn := hw.norm'_eq_one (Nat.succ_ne_zero n)
  simp [Complex.normSq_eq_norm_sq, norm_pow, hn]

theorem weighted_tight {n : ℕ} (w : ℂ) (hw : IsPrimitiveRoot w (n+1))
    (c : Fin n → ℂ) (hc : ∀ i, star (c i)*c i = 1) (r s : Fin n) :
    (∑ j : Fin (n+1), (c r*w^(r.val*j.val)) * star (c s*w^(s.val*j.val))) =
      if r = s then ((n+1:ℕ):ℂ) else 0 := by
  have hterm (j : Fin (n+1)) :
      (c r*w^(r.val*j.val)) * star (c s*w^(s.val*j.val)) =
      (c r*star (c s)) * (w^(r.val*j.val)*star (w^(s.val*j.val))) := by
    rw [star_mul]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have ho := full_orthogonality (Nat.succ_pos n) w hw r.castSucc s.castSucc
  simp only [Fin.val_castSucc, Fin.castSucc_inj] at ho
  rw [ho]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl]
    have hr : c r*star (c r) = 1 := by rw [mul_comm]; exact hc r
    rw [hr, one_mul]
  · simp only [if_neg hrs, mul_zero]

end HarmonicFrame


open scoped BigOperators

namespace BellETF

def pairEquiv (d : ℕ) : Fin d × Fin d ≃ Fin (d^2) :=
  (finProdFinEquiv : Fin d × Fin d ≃ Fin (d*d)).trans
    (finCongr (by rw [pow_two]))

def pairIndex (d : ℕ) (a b : Fin d) : Fin (d^2) := pairEquiv d (a,b)

@[simp] theorem pairIndex_val (d : ℕ) (a b : Fin d) :
    (pairIndex d a b).val = d*a.val+b.val := by
  simp [pairIndex, pairEquiv, finProdFinEquiv, Nat.add_comm]

@[simp] theorem pairIndex_eq_iff (d : ℕ) (a b c e : Fin d) :
    pairIndex d a b = pairIndex d c e ↔ a=c ∧ b=e := by
  change pairEquiv d (a,b) = pairEquiv d (c,e) ↔ _
  rw [(pairEquiv d).injective.eq_iff]
  simp only [Prod.mk.injEq]

theorem sum_pairIndex (d : ℕ) (f : Fin (d^2) → ℂ) :
    (∑ a, ∑ b, f (pairIndex d a b)) = ∑ i, f i := by
  simpa only [Fintype.sum_prod_type, pairIndex] using (Equiv.sum_comp (pairEquiv d) f)

noncomputable def seedWeights (d : ℕ) (u : ℂ) (i : Fin (d^2)) : ℂ :=
  u^(((pairEquiv d).symm i).1.val * ((pairEquiv d).symm i).2.val)

@[simp] theorem seedWeights_pairIndex (d : ℕ) (u : ℂ) (a b : Fin d) :
    seedWeights d u (pairIndex d a b) = u^(a.val*b.val) := by
  simp [seedWeights, pairIndex]

end BellETF

#print axioms BellETF.sum_pairIndex


open scoped BigOperators

namespace BellReduction

theorem phased_scaled_rowGram {d : ℕ} (hd : d ≠ 0)
    (F : Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a c, (∑ b, F a b * star (F c b)) = if a = c then (d : ℂ) else 0)
    (r c : Fin d → ℂ)
    (hr : ∀ a, r a * star (r a) = 1) (hc : ∀ b, c b * star (c b) = 1) :
    let V : Matrix (Fin d) (Fin d) ℂ := fun a b => r a * F a b * c b / (d : ℂ)
    V * V.conjTranspose = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  dsimp only
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  apply Matrix.ext
  intro a k
  change (∑ b, (r a * F a b * c b / (d : ℂ)) *
    star (r k * F k b * c b / (d : ℂ))) =
    (d : ℂ)⁻¹ * (if a = k then 1 else 0)
  have hterm (b : Fin d) :
      (r a * F a b * c b / (d : ℂ)) * star (r k * F k b * c b / (d : ℂ)) =
      (r a * star (r k) / (d : ℂ)^2) * (F a b * star (F k b)) := by
    simp only [star_div₀, star_mul, star_natCast]
    calc
      _ = (r a * star (r k) / (d : ℂ)^2) *
        (F a b * star (F k b)) * (c b * star (c b)) := by ring
      _ = _ := by rw [hc]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hF]
  by_cases h : a = k
  · subst k
    rw [if_pos rfl, hr]
    field_simp <;> simp
  · simp [h]

/-- Equality of the two normalized reductions for a square coefficient matrix. -/
theorem columnGram_of_rowGram {d : ℕ} (hd : d ≠ 0)
    (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V * V.conjTranspose = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    V.conjTranspose * V = (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hleft : ((d : ℂ) • V) * V.conjTranspose = 1 := by
    rw [Matrix.smul_mul, hV, smul_smul]
    simp [hd']
  have hright : V.conjTranspose * ((d : ℂ) • V) = 1 :=
    mul_eq_one_comm.mp hleft
  rw [Matrix.mul_smul] at hright
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (d : ℂ)⁻¹ • A) hright
  simpa [smul_smul, hd'] using h

noncomputable def bellSeed (d : ℕ) (u w : ℂ) (j : Fin (d^2+1)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => u^(a.val*b.val) * w^((d*a.val+b.val)*j.val) / (d : ℂ)

theorem bellSeed_factor (d : ℕ) (u w : ℂ) (j : Fin (d^2+1)) :
    bellSeed d u w j = fun a b =>
      w^(d*a.val*j.val) * u^(a.val*b.val) * w^(b.val*j.val) / (d : ℂ) := by
  apply Matrix.ext
  intro a b
  simp only [bellSeed, Nat.add_mul, pow_add]
  ring

theorem bellSeed_rowGram {d : ℕ} (hd : 0 < d) (u w : ℂ)
    (hu : IsPrimitiveRoot u d) (hw : IsPrimitiveRoot w (d^2+1))
    (j : Fin (d^2+1)) :
    bellSeed d u w j * (bellSeed d u w j).conjTranspose =
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [bellSeed_factor]
  exact phased_scaled_rowGram (Nat.ne_of_gt hd)
    (fun a b => u^(a.val*b.val))
    (fun a c => HarmonicFrame.full_orthogonality hd u hu a c)
    (fun a => w^(d*a.val*j.val)) (fun b => w^(b.val*j.val))
    (fun a => HarmonicFrame.root_unit (by omega : 0 < d^2+1) w hw (d*a.val*j.val))
    (fun b => HarmonicFrame.root_unit (by omega : 0 < d^2+1) w hw (b.val*j.val))

theorem bellSeed_columnGram {d : ℕ} (hd : 0 < d) (u w : ℂ)
    (hu : IsPrimitiveRoot u d) (hw : IsPrimitiveRoot w (d^2+1))
    (j : Fin (d^2+1)) :
    (bellSeed d u w j).conjTranspose * bellSeed d u w j =
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  columnGram_of_rowGram (Nat.ne_of_gt hd) _ (bellSeed_rowGram hd u w hu hw j)

#print axioms bellSeed_rowGram
#print axioms bellSeed_columnGram

end BellReduction


open scoped BigOperators

namespace BellETF

theorem seedWeights_unit {d : ℕ} (hd : 0 < d) (u : ℂ) (hu : IsPrimitiveRoot u d) :
    ∀ i, star (seedWeights d u i) * seedWeights d u i = 1 := by
  intro i
  exact HarmonicFrame.root_unit' hd u hu _

theorem seed_eq_weighted (d : ℕ) (u w : ℂ) (j : Fin (d^2+1)) (a b : Fin d) :
    BellReduction.bellSeed d u w j a b =
      seedWeights d u (pairIndex d a b) *
        w^((pairIndex d a b).val*j.val) / (d : ℂ) := by
  simp [BellReduction.bellSeed]

theorem scaled_inner_term (x y : ℂ) (d : ℕ) :
    star (x/(d : ℂ)) * (y/(d : ℂ)) = (star x*y)/(d : ℂ)^2 := by
  simp only [star_div₀, star_natCast]
  ring

theorem seed_inner (d : ℕ) (u w : ℂ) (j k : Fin (d^2+1)) :
    (∑ a, ∑ b, star (BellReduction.bellSeed d u w j a b) *
      BellReduction.bellSeed d u w k a b) =
    (∑ i : Fin (d^2), star (seedWeights d u i*w^(i.val*j.val)) *
      (seedWeights d u i*w^(i.val*k.val))) / (d : ℂ)^2 := by
  simp_rw [seed_eq_weighted, scaled_inner_term, ← Finset.sum_div]
  congr 1
  exact sum_pairIndex d (fun i => star (seedWeights d u i*w^(i.val*j.val)) *
    (seedWeights d u i*w^(i.val*k.val)))

theorem seed_norm {d : ℕ} (hd : 0 < d) (u w : ℂ)
    (hu : IsPrimitiveRoot u d) (hw : IsPrimitiveRoot w (d^2+1)) (j : Fin (d^2+1)) :
    (∑ a, ∑ b, star (BellReduction.bellSeed d u w j a b) *
      BellReduction.bellSeed d u w j a b) = 1 := by
  rw [seed_inner, HarmonicFrame.weighted_norm w hw (seedWeights d u) (seedWeights_unit hd u hu)]
  simp [Nat.cast_pow, Nat.ne_of_gt hd]

theorem seed_equiangular {d : ℕ} (hd : 0 < d) (u w : ℂ)
    (hu : IsPrimitiveRoot u d) (hw : IsPrimitiveRoot w (d^2+1))
    (norm_scaled : ∀ (x : ℂ) (m : ℕ), Complex.normSq x = 1 →
      Complex.normSq (x/(m : ℂ)^2) = 1/(m : ℝ)^4)
    (j k : Fin (d^2+1)) (hjk : j ≠ k) :
    Complex.normSq (∑ a, ∑ b, star (BellReduction.bellSeed d u w j a b) *
      BellReduction.bellSeed d u w k a b) = 1/(d : ℝ)^4 := by
  rw [seed_inner]
  exact norm_scaled _ d (HarmonicFrame.weighted_equiangular w hw
    (seedWeights d u) (seedWeights_unit hd u hu) j k hjk)

theorem seed_tight {d : ℕ} (hd : 0 < d) (u w : ℂ)
    (hu : IsPrimitiveRoot u d) (hw : IsPrimitiveRoot w (d^2+1))
    (a b c e : Fin d) :
    (∑ j, BellReduction.bellSeed d u w j a b * star (BellReduction.bellSeed d u w j c e)) =
      if a=c ∧ b=e then ((d : ℂ)^2+1)/(d : ℂ)^2 else 0 := by
  have hterm (x y : ℂ) : x/(d : ℂ)*star (y/(d : ℂ)) = (x*star y)/(d : ℂ)^2 := by
    simp only [star_div₀, star_natCast]
    ring
  simp_rw [seed_eq_weighted, hterm]
  rw [← Finset.sum_div, HarmonicFrame.weighted_tight w hw
    (seedWeights d u) (seedWeights_unit hd u hu)]
  simp only [pairIndex_eq_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  split_ifs <;> simp

end BellETF



theorem bell_normSq_scaled (x : ℂ) (d : ℕ) (hx : Complex.normSq x = 1) : Complex.normSq (x / (d : ℂ)^2) = 1 / (d : ℝ)^4 := by
  exact (by
    simp_all <;> ring
  )
theorem maximally_entangled_equiangular_tight_frame_all_dimensions (d : ℕ) (hd : 2 ≤ d) :
    ∃ v : Fin (d^2+1) → Matrix (Fin d) (Fin d) ℂ,
      (∀ j, (∑ a, ∑ b, star (v j a b) * v j a b) = 1) ∧
      (∀ j k, j ≠ k → Complex.normSq (∑ a, ∑ b,
        star (v j a b) * v k a b) = 1 / (d : ℝ)^4) ∧
      (∀ a b c e, (∑ j, v j a b * star (v j c e)) =
        if a = c ∧ b = e then ((d : ℂ)^2+1)/(d : ℂ)^2 else 0) ∧
      (∀ j, (v j) * (v j).conjTranspose = (d : ℂ)⁻¹ • 1) ∧
      (∀ j, (v j).conjTranspose * (v j) = (d : ℂ)⁻¹ • 1) := by
  have hdpos : 0 < d := by omega
  obtain ⟨u,hu⟩ := HarmonicFrame.root_exists hdpos
  obtain ⟨w,hw⟩ := HarmonicFrame.root_exists (Nat.succ_pos (d^2))
  refine ⟨BellReduction.bellSeed d u w,
    BellETF.seed_norm hdpos u w hu hw,
    BellETF.seed_equiangular hdpos u w hu hw bell_normSq_scaled,
    BellETF.seed_tight hdpos u w hu hw,
    BellReduction.bellSeed_rowGram hdpos u w hu hw,
    BellReduction.bellSeed_columnGram hdpos u w hu hw⟩

#print axioms maximally_entangled_equiangular_tight_frame_all_dimensions
