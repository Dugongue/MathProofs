import Mathproof.Meta.Problem18SpectralBlocks20260930

open scoped Polynomial

namespace Mathproof.Meta.Problem18HermitianSpectral20260930

universe u v
open Mathproof.Meta.Problem18SpectralBlocks20260930

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

/-- All coefficients lie in the fixed field of the semilinearity. -/
def CoefficientsFixed (sigma : K ≃+* K) (p : K[X]) : Prop :=
  p.map sigma.toRingHom = p

/-- Self-adjointness relative to a Hermitian/sesquilinear form. -/
def IsSelfAdjointFor (sigma : K ≃+* K)
    (B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K) (S : Module.End K V) : Prop :=
  ∀ x y, B (S x) y = B x (S y)

theorem isSelfAdjointFor_pow {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K} {S : Module.End K V}
    (hS : IsSelfAdjointFor sigma B S) (n : ℕ) :
    IsSelfAdjointFor sigma B (S ^ n) := by
  induction n with
  | zero =>
      intro x y
      simp
  | succ n ih =>
      intro x y
      simp only [pow_succ, Module.End.mul_apply]
      rw [ih, hS]
      congr 1
      simpa only [Module.End.mul_apply] using
        congrArg (fun T : Module.End K V => T y) ((Commute.refl S).pow_right n).eq

/-- The adjoint of polynomial evaluation is evaluation of the coefficientwise
conjugate polynomial. This is the safe statement for arbitrary coefficients. -/
theorem pairing_polyEval_eq_map {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K} {S : Module.End K V}
    (hS : IsSelfAdjointFor sigma B S) (p : K[X]) (x y : V) :
    B (polyEval S p x) y =
      B x (polyEval S (p.map sigma.toRingHom) y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [polyEval, Polynomial.aeval_add, LinearMap.add_apply,
        map_add, Polynomial.map_add]
      simpa only [polyEval] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      simp only [polyEval, Polynomial.aeval_monomial, ← Algebra.smul_def,
        LinearMap.smul_apply, map_smulₛₗ, map_smul, smul_eq_mul,
        Polynomial.map_monomial]
      rw [isSelfAdjointFor_pow hS n]
      rfl

/-- Fixed-coefficient polynomial functions of a self-adjoint operator remain
self-adjoint. Arbitrary extension-field coefficients are intentionally excluded. -/
theorem isSelfAdjointFor_polyEval_fixed {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K} {S : Module.End K V}
    (hS : IsSelfAdjointFor sigma B S) {p : K[X]}
    (hp : CoefficientsFixed sigma p) :
    IsSelfAdjointFor sigma B (polyEval S p) := by
  intro x y
  rw [pairing_polyEval_eq_map hS, hp]

theorem coefficientsFixed_pow {sigma : K ≃+* K} {p : K[X]}
    (hp : CoefficientsFixed sigma p) (n : ℕ) :
    CoefficientsFixed sigma (p ^ n) := by
  unfold CoefficientsFixed at hp ⊢
  rw [Polynomial.map_pow, hp]

/-- Hermitian Bézout orthogonality for fixed-coefficient coprime kernels.
The Bézout coefficients themselves need not be fixed: conjugating the
projector preserves the fixed right factor that kills the second vector. -/
theorem coprime_kernels_pairing_eq_zero
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor sigma B S)
    (hp : CoefficientsFixed sigma p) (hq : CoefficientsFixed sigma q)
    (hpq : IsCoprime p q)
    {x y : V} (hx : x ∈ primarySpace S p) (hy : y ∈ primarySpace S q) :
    B x y = 0 := by
  rcases hpq with ⟨a, b, hab⟩
  have hpx : polyEval S p x = 0 := LinearMap.mem_ker.mp hx
  have hqy : polyEval S q y = 0 := LinearMap.mem_ker.mp hy
  change (Polynomial.aeval S p) x = 0 at hpx
  change (Polynomial.aeval S q) y = 0 at hqy
  have hxproject : x = polyEval S (b * q) x := by
    calc
      x = polyEval S 1 x := by simp [polyEval]
      _ = polyEval S (a * p + b * q) x := by rw [hab]
      _ = polyEval S (a * p) x + polyEval S (b * q) x := by
        simp only [polyEval, Polynomial.aeval_add, LinearMap.add_apply]
      _ = polyEval S (b * q) x := by
        simp only [polyEval, Polynomial.aeval_mul, Module.End.mul_apply]
        simp [hpx]
  rw [hxproject, pairing_polyEval_eq_map hS]
  simp only [Polynomial.map_mul, hq, polyEval, Polynomial.aeval_mul,
    Module.End.mul_apply]
  rw [show q.map sigma.toRingHom = q from hq, hqy, map_zero, map_zero]

theorem coprime_primarySpaces_pairing_eq_zero
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor sigma B S)
    (hp : CoefficientsFixed sigma p) (hq : CoefficientsFixed sigma q)
    (hpq : IsCoprime p q) (m n : ℕ)
    {x y : V} (hx : x ∈ primarySpace S (p ^ m))
    (hy : y ∈ primarySpace S (q ^ n)) :
    B x y = 0 :=
  coprime_kernels_pairing_eq_zero hS (coefficientsFixed_pow hp m)
    (coefficientsFixed_pow hq n) hpq.pow hx hy

theorem primarySpace_le_orthogonal
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor sigma B S)
    (hp : CoefficientsFixed sigma p) (hq : CoefficientsFixed sigma q)
    (hpq : IsCoprime p q) :
    primarySpace S q ≤ (primarySpace S p).orthogonalBilin B := by
  intro y hy x hx
  exact coprime_kernels_pairing_eq_zero hS hp hq hpq hx hy

/-- CRT projector action on the two Hermitian spectral blocks. -/
theorem exists_crt_projector_polynomial
    {S : Module.End K V} {p q : K[X]} (hpq : IsCoprime p q) :
    ∃ e : K[X],
      (∀ x ∈ primarySpace S p, polyEval S e x = x) ∧
      (∀ y ∈ primarySpace S q, polyEval S e y = 0) :=
  Problem18SpectralBlocks20260930.exists_crt_projector_polynomial hpq

theorem nondegenerate_restrict_of_orthogonal_complement
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    (hB : B.IsRefl) (hNondeg : B.Nondegenerate)
    {U W : Submodule K V} (hsum : U ⊔ W = ⊤)
    (horth : W ≤ U.orthogonalBilin B) :
    (B.domRestrict₁₂ U U).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply hNondeg.1 x.val
    intro y
    have hy : y ∈ U ⊔ W := by rw [hsum]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    have hxu : B x.val u = 0 := by
      simpa only [LinearMap.domRestrict₁₂_apply] using hx ⟨u, hu⟩
    have hxw : B x.val w = 0 := horth hw x.val x.property
    rw [hxu, hxw, add_zero]
  · intro y hy
    apply Subtype.ext
    apply hNondeg.2 y.val
    intro x
    have hx : x ∈ U ⊔ W := by rw [hsum]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    have huy : B u y.val = 0 := by
      simpa only [LinearMap.domRestrict₁₂_apply] using hy ⟨u, hu⟩
    have hwy : B w y.val = 0 := hB.eq_zero (horth hw y.val y.property)
    rw [LinearMap.add_apply, huy, hwy, add_zero]

/-- Complementary coprime Hermitian primary blocks inherit nondegenerate
restrictions from the ambient nondegenerate Hermitian form. -/
theorem coprime_primarySpaces_nondegenerate
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    (hB : B.IsSymm) (hNondeg : B.Nondegenerate)
    {S : Module.End K V} (hS : IsSelfAdjointFor sigma B S)
    {p q : K[X]} (hp : CoefficientsFixed sigma p)
    (hq : CoefficientsFixed sigma q) (hpq : IsCoprime p q) (m n : ℕ)
    (hsum : primarySpace S (p ^ m) ⊔ primarySpace S (q ^ n) = ⊤) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate := by
  constructor
  · exact nondegenerate_restrict_of_orthogonal_complement hB.isRefl hNondeg hsum
      (primarySpace_le_orthogonal hS (coefficientsFixed_pow hp m)
        (coefficientsFixed_pow hq n) hpq.pow)
  · exact nondegenerate_restrict_of_orthogonal_complement hB.isRefl hNondeg
      (by simpa only [sup_comm] using hsum)
      (primarySpace_le_orthogonal hS (coefficientsFixed_pow hq n)
        (coefficientsFixed_pow hp m) hpq.symm.pow)

end Mathproof.Meta.Problem18HermitianSpectral20260930
