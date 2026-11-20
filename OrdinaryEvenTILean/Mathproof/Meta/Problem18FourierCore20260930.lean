import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.GaussSum
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathproof.Meta.Problem18ProbabilityAssembly20260930

/-! Exact declaration-body lifts from the historical tensor Fourier development
and Hermitian second-moment module. Only imports, namespace, and the ambient
classical scope change. Provenance is in github-reuse-20260930/fourier-lift.json.
These are reused results, not additional discoveries. -/
namespace Mathproof.Problem18FourierCore20260930
open scoped BigOperators Matrix
open Matrix Finset Classical
variable {K : Type*} [Field K]

theorem quadratic_character_polarization
    {G F : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup F]
    (ψ : AddChar F ℂ) (Q : G → F) (B : G → G → F)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B x h) :
    (∑ x, ψ (Q x)) * (∑ x, ψ (-Q x)) =
      ∑ h, ψ (Q h) * ∑ x, ψ (B x h) := by
  have he (x : G) : ∑ h, ψ (Q (x + h)) = ∑ y, ψ (Q y) :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  calc
    (∑ x, ψ (Q x)) * (∑ x, ψ (-Q x)) =
        ∑ x, (∑ h, ψ (Q (x + h))) * ψ (-Q x) := by
          simp_rw [he]; rw [Finset.mul_sum]
    _ = ∑ h, ∑ x, ψ (Q (x + h)) * ψ (-Q x) := by
      simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    _ = ∑ h, ψ (Q h) * ∑ x, ψ (B x h) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hQ]
      congr 1
      abel

theorem quadratic_character_radical_count
    {G F : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup F]
    (ψ : AddChar F ℂ) (Q : G → F) (B : G → G → F)
    (β : G → AddChar G ℂ)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B x h)
    (hβ : ∀ h x, β h x = ψ (B x h))
    (hrad : ∀ h, β h = 1 → Q h = 0) :
    (∑ x, ψ (Q x)) * (∑ x, ψ (-Q x)) =
      (Fintype.card G : ℂ) * (Finset.univ.filter (fun h => β h = 1)).card := by
  rw [quadratic_character_polarization ψ Q B hQ]
  have hi (h : G) : ∑ x, ψ (B x h) =
      if β h = 1 then (Fintype.card G : ℂ) else 0 := by
    simp_rw [← hβ]
    by_cases hh : β h = 1
    · simp [hh]
    · rw [AddChar.sum_eq_zero_of_ne_one hh]
      simp [hh]
  simp_rw [hi]
  calc
    (∑ h, ψ (Q h) * (if β h = 1 then (Fintype.card G : ℂ) else 0)) =
        ∑ h, if β h = 1 then (Fintype.card G : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro h _
          by_cases hh : β h = 1
          · simp [hh, hrad h hh, AddChar.map_zero_eq_one]
          · simp [hh]
    _ = _ := by simp [Finset.sum_ite, mul_comm]

theorem quadratic_character_norm_sq
    {G F : Type*} [AddCommGroup G] [Fintype G] [CommRing F]
    (hp : 0 < ringChar F) (ψ : AddChar F ℂ) (Q : G → F) (B : G → G → F)
    (β : G → AddChar G ℂ)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B x h)
    (hβ : ∀ h x, β h x = ψ (B x h))
    (hrad : ∀ h, β h = 1 → Q h = 0) :
    ‖∑ x, ψ (Q x)‖ ^ 2 =
      (Fintype.card G : ℝ) * (Finset.univ.filter (fun h => β h = 1)).card := by
  have hn (a : F) : ψ (-a) = star (ψ a) := by
    simpa [AddChar.inv_apply] using (AddChar.starComp_apply hp (φ := ψ) a).symm
  have hs : ∑ x, ψ (-Q x) = star (∑ x, ψ (Q x)) := by
    simp_rw [hn]
    exact (map_sum (starRingEnd ℂ) (fun x => ψ (Q x)) Finset.univ).symm
  have he := quadratic_character_radical_count ψ Q B β hQ hβ hrad
  rw [hs] at he
  change (∑ x, ψ (Q x)) * (starRingEnd ℂ) (∑ x, ψ (Q x)) = _ at he
  rw [Complex.mul_conj] at he
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hr
  simpa only [Complex.normSq_eq_norm_sq] using hr

theorem quadratic_character_mean_norm_sq
    {G F : Type*} [AddCommGroup G] [Fintype G] [CommRing F]
    (hp : 0 < ringChar F) (ψ : AddChar F ℂ) (Q : G → F) (B : G → G → F)
    (β : G → AddChar G ℂ)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + B x h)
    (hβ : ∀ h x, β h x = ψ (B x h))
    (hrad : ∀ h, β h = 1 → Q h = 0) :
    ‖(∑ x, ψ (Q x)) / (Fintype.card G : ℂ)‖ ^ 2 =
      (Finset.univ.filter (fun h => β h = 1)).card / (Fintype.card G : ℝ) := by
  rw [norm_div, div_pow, quadratic_character_norm_sq hp ψ Q B β hQ hβ hrad]
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Complex.norm_natCast]
  field_simp

theorem character_detects_linear_map
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (L : V →ₗ[F] F) :
    (∀ x, ψ (L x) = 1) ↔ L = 0 := by
  constructor
  · intro h
    ext x
    change L x = 0
    by_contra hx
    apply hψ
    ext a
    change ψ a = 1
    have he := h ((a / L x) • x)
    simpa [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx] using he
  · rintro rfl
    simp [AddChar.map_zero_eq_one]

theorem trace_character_nondegenerate
    {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : K) :
    (∀ x, ψ (Algebra.trace F K (a * x)) = 1) ↔ a = 0 := by
  constructor
  · intro h
    have hz : Algebra.traceForm F K a = 0 :=
      (character_detects_linear_map ψ hψ (Algebra.traceForm F K a)).mp h
    exact (traceForm_nondegenerate F K).1 a (by simp [hz])
  · rintro rfl
    simp [AddChar.map_zero_eq_one]

theorem trace_vector_character_nondegenerate
    {F i : Type*} [Field F] [Fintype i] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (z : i → K) :
    (∀ x : i → K, ψ (Algebra.trace F K (∑ j, x j * z j)) = 1) ↔ z = 0 := by
  constructor
  · intro h
    ext j
    apply (trace_character_nondegenerate ψ hψ (z j)).mp
    intro a
    have he := h (Pi.single j a)
    simpa [Pi.single_apply, ite_mul, mul_comm] using he
  · rintro rfl
    simp [AddChar.map_zero_eq_one]

theorem trace_matrix_character_radical
    {F i j : Type*} [Field F] [Fintype i] [Fintype j]
    [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (A : Matrix i j K) (y : j → K) :
    (∀ x : i → K, ψ (Algebra.trace F K (∑ k, x k * (A.mulVec y) k)) = 1) ↔
      A.mulVec y = 0 :=
  trace_vector_character_nondegenerate ψ hψ (A.mulVec y)

theorem linear_kernel_fraction
    {F V W : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [Module F V]
    [AddCommGroup W] [Module F W] (L : V →ₗ[F] W) :
    (Fintype.card (LinearMap.ker L) : ℝ) / (Fintype.card V : ℝ) =
      ((Fintype.card F : ℝ) ^ Module.finrank F (LinearMap.range L))⁻¹ := by
  rw [Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker L),
    Module.card_eq_pow_finrank (K := F) (V := V), ← L.finrank_range_add_finrank_ker]
  simp only [Nat.cast_pow, pow_add, Nat.cast_mul]
  have hc : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem trace_matrix_quadratic_fourier
    {F i : Type*} [Field F] [Fintype F] [Fintype K] [Fintype i] [StarRing K]
    [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (hp : 0 < ringChar F) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (A : Matrix i i K) (Q : (i → K) → F)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h +
      Algebra.trace F K (∑ j, star (x j) * (A.mulVec h) j))
    (hrad : ∀ h, A.mulVec h = 0 → Q h = 0) :
    ‖(∑ x, ψ (Q x)) / (Fintype.card (i → K) : ℂ)‖ ^ 2 =
      ((Fintype.card K : ℝ) ^ A.rank)⁻¹ := by
  let L (h : i → K) : (i → K) →+ F := {
    toFun := fun x => Algebra.trace F K (∑ j, star (x j) * (A.mulVec h) j)
    map_zero' := by simp
    map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib] }
  let β (h : i → K) : AddChar (i → K) ℂ := ψ.compAddMonoidHom (L h)
  have hb (h : i → K) : β h = 1 ↔ A.mulVec h = 0 := by
    constructor
    · intro he
      apply (trace_matrix_character_radical ψ hψ A h).mp
      intro x
      have hx := congrArg (fun χ : AddChar (i → K) ℂ => χ (star x)) he
      simpa [β, L] using hx
    · intro he
      ext x
      simp [β, L, he, AddChar.map_zero_eq_one]
  have he := quadratic_character_mean_norm_sq hp ψ Q
    (fun x h => Algebra.trace F K (∑ j, star (x j) * (A.mulVec h) j)) β
    hQ (fun _ _ => rfl) (fun h hh => hrad h ((hb h).mp hh))
  simp only [hb] at he
  rw [he]
  have hk : (Finset.univ.filter (fun h => A.mulVec h = 0)).card =
      Fintype.card (LinearMap.ker A.mulVecLin) := by
    symm
    exact Fintype.card_of_subtype _ (by intro x; simp)
  rw [hk]
  simpa only [Matrix.rank] using linear_kernel_fraction A.mulVecLin

theorem independent_quadratic_character_sum
    {F V : Type*} [AddCommGroup F] [Fintype V]
    (ψ : AddChar F ℂ) (Q : V → F) (m : ℕ) :
    (∑ x : Fin m → V, ψ (∑ j, Q (x j))) = (∑ x : V, ψ (Q x)) ^ m := by
  have hs (s : Finset (Fin m)) (x : Fin m → V) :
      ψ (∑ j ∈ s, Q (x j)) = ∏ j ∈ s, ψ (Q (x j)) := by
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert j s hj ih => simp [hj, AddChar.map_add_eq_mul, ih]
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (x : V) => ψ (Q x))]
  simp

theorem finite_fourier_pairing
    {G : Type*} [AddCommGroup G] [Fintype G] (f g : G → ℂ) :
    (∑ χ : AddChar G ℂ, (∑ x, f x * χ x) * (∑ y, g y * χ (-y))) =
      (Fintype.card G : ℂ) * ∑ x, f x * g x := by
  have he (χ : AddChar G ℂ) :
      (∑ x, f x * χ x) * (∑ y, g y * χ (-y)) =
        ∑ x, ∑ y, (f x * g y) * χ (x - y) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [he]
  calc
    (∑ χ : AddChar G ℂ, ∑ x, ∑ y, (f x * g y) * χ (x - y)) =
        ∑ x, ∑ y, ∑ χ : AddChar G ℂ, (f x * g y) * χ (x - y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
      simp [sub_eq_zero, mul_ite, Finset.mul_sum, mul_comm]

theorem finite_fourier_parseval
    {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, ‖∑ x, f x * χ x‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  have hc (χ : AddChar G ℂ) :
      (∑ y, (starRingEnd ℂ) (f y) * χ (-y)) =
        (starRingEnd ℂ) (∑ y, f y * χ y) := by
    simp only [map_sum, map_mul, AddChar.map_neg_eq_conj]
  have he := finite_fourier_pairing f (fun x => (starRingEnd ℂ) (f x))
  simp_rw [hc, Complex.mul_conj] at he
  have hr : (∑ χ : AddChar G ℂ, Complex.normSq (∑ x, f x * χ x)) =
      (Fintype.card G : ℝ) * ∑ x, Complex.normSq (f x) := by
    exact_mod_cast he
  simpa only [Complex.normSq_eq_norm_sq] using hr

noncomputable def uniformImageWeight
    {V G : Type*} [Fintype V] (P : V → G) (y : G) : ℂ :=
  (Finset.univ.filter (fun x => P x = y)).card / (Fintype.card V : ℂ)

theorem uniform_image_average
    {V G : Type*} [Fintype V] [Fintype G] (P : V → G) (g : G → ℂ) :
    (∑ y, uniformImageWeight P y * g y) = (∑ x, g (P x)) / (Fintype.card V : ℂ) := by
  unfold uniformImageWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_fiberwise' Finset.univ P g]
  simp [nsmul_eq_mul]

def gramHermitian
    {i j : Type*} [Fintype j] [StarRing K] (N : Matrix i j K) :
    selfAdjoint (Matrix i i K) :=
  ⟨N * Nᴴ, by
    change (N * Nᴴ)ᴴ = N * Nᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]⟩

def rankOneHermitian
    {i : Type*} [StarRing K] (x : i → K) :
    selfAdjoint (Matrix i i K) :=
  ⟨fun a b => x a * star (x b), Matrix.IsHermitian.ext (by
    intro a b
    simp [star_mul])⟩

theorem sum_rankOneHermitian_eq_gram
    {i j : Type*} [Fintype j] [StarRing K] (x : j → (i → K)) :
    (∑ b, rankOneHermitian (x b)) = gramHermitian (fun a b => x b a) := by
  apply Subtype.ext
  change (selfAdjoint (Matrix i i K)).subtype (∑ b, rankOneHermitian (x b)) = _
  rw [map_sum]
  ext a c
  change (∑ b, (fun a c => x b a * star (x b c) : Matrix i i K)) a c =
    ∑ b, x b a * star (x b c)
  exact Matrix.sum_apply a c Finset.univ _

theorem uniform_image_event_mass
    {V G : Type*} [Fintype V] [Fintype G] (P : V → G) (A : Finset G) :
    (∑ y ∈ A, uniformImageWeight P y) =
      ((Finset.univ.filter (fun x => P x ∈ A)).card : ℂ) / Fintype.card V := by
  have h := uniform_image_average P (fun y => if y ∈ A then 1 else 0)
  simpa [mul_ite, Finset.sum_ite] using h

theorem uniform_image_density_second_moment
    {V G : Type*} [Fintype V] [Nonempty V] [AddCommGroup G] [Fintype G]
    (P : V → G) :
    (Fintype.card G : ℝ) * ∑ y, ‖uniformImageWeight P y‖ ^ 2 =
      ∑ χ : AddChar G ℂ,
        ‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖ ^ 2 := by
  simpa only [uniform_image_average] using
    (finite_fourier_parseval (uniformImageWeight P)).symm

theorem uniform_sum_density_second_moment
    {V G : Type*} [Fintype V] [Nonempty V] [AddCommGroup G] [Fintype G]
    (P : V → G) (m : ℕ) :
    (Fintype.card G : ℝ) *
        ∑ y, ‖uniformImageWeight (fun x : Fin m → V => ∑ j, P (x j)) y‖ ^ 2 =
      ∑ χ : AddChar G ℂ,
        (‖(∑ x, χ (P x)) / (Fintype.card V : ℂ)‖ ^ 2) ^ m := by
  rw [uniform_image_density_second_moment]
  apply Finset.sum_congr rfl
  intro χ _
  simp only [independent_quadratic_character_sum, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]
  rw [← div_pow, norm_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul]

theorem image_event_probability_le_sqrt
    {V G : Type*} [Fintype V] [Nonempty V] [AddCommGroup G] [Fintype G]
    (P : V → G) (E : Finset G) (C : ℝ)
    (hC : 0 ≤ C)
    (hsecond :
      (Fintype.card G : ℝ) * ∑ y, ‖uniformImageWeight P y‖ ^ 2 ≤ C) :
    ((Finset.univ.filter (fun x => P x ∈ E)).card : ℝ) / Fintype.card V ≤
      Real.sqrt (C * ((E.card : ℝ) / Fintype.card G)) := by
  let ρ : G → ℝ := fun y => (Fintype.card G : ℝ) * ‖uniformImageWeight P y‖
  have hρ : ∀ y, 0 ≤ ρ y := by
    intro y
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hρ2 : ∑ y, (ρ y) ^ 2 ≤ C * Fintype.card G := by
    have hm := mul_le_mul_of_nonneg_left hsecond
      (show (0 : ℝ) ≤ Fintype.card G by positivity)
    dsimp only [ρ]
    simp only [mul_pow, ← Finset.mul_sum]
    nlinarith
  have ht :=
    Problem18ProbabilityAssembly20260930.weighted_event_probability_le_sqrt
      ρ E C hρ hC hρ2
  have hmassC := uniform_image_event_mass P E
  have htriangle := norm_sum_le E (uniformImageWeight P)
  rw [hmassC] at htriangle
  have hmass :
      ((Finset.univ.filter (fun x => P x ∈ E)).card : ℝ) /
          Fintype.card V ≤
        ∑ y ∈ E, ‖uniformImageWeight P y‖ := by
    simpa [norm_div, Complex.norm_natCast] using htriangle
  have hcard : (0 : ℝ) < Fintype.card G := by positivity
  dsimp only [ρ] at ht
  rw [← Finset.mul_sum] at ht
  have hcancel :
      ((Fintype.card G : ℝ) *
        ∑ y ∈ E, ‖uniformImageWeight P y‖) / Fintype.card G =
        ∑ y ∈ E, ‖uniformImageWeight P y‖ := by
    field_simp [hcard.ne']
  rw [hcancel] at ht
  exact hmass.trans ht

end Mathproof.Problem18FourierCore20260930
