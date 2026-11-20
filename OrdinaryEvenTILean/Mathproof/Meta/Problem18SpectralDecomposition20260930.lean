import Mathproof.Meta.Problem18HermitianSpectral20260930

open scoped Polynomial

namespace Mathproof.Meta.Problem18SpectralDecomposition20260930

universe u v

open Mathproof.Meta.Problem18SpectralBlocks20260930

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

/-- Coprime polynomial kernels are complementary whenever their product
annihilates the operator. -/
theorem isCompl_primarySpaces_of_mul_eq_zero
    {S : Module.End K V} {p q : K[X]} (hpq : IsCoprime p q)
    (hann : polyEval S (p * q) = 0) :
    IsCompl (primarySpace S p) (primarySpace S q) := by
  refine ⟨?_, ?_⟩
  · simpa only [primarySpace, polyEval] using
      Polynomial.disjoint_ker_aeval_of_isCoprime S hpq
  · show Codisjoint (primarySpace S p) (primarySpace S q)
    rw [codisjoint_iff]
    rw [show primarySpace S p ⊔ primarySpace S q =
        primarySpace S (p * q) by
      simpa only [primarySpace, polyEval] using
        Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime S hpq]
    unfold primarySpace
    rw [LinearMap.ker_eq_top]
    exact hann

/-- Powered primary spaces are complementary under the corresponding product
annihilator. -/
theorem isCompl_primarySpaces_pow_of_mul_eq_zero
    {S : Module.End K V} {p q : K[X]} (hpq : IsCoprime p q)
    (m n : ℕ) (hann : polyEval S (p ^ m * q ^ n) = 0) :
    IsCompl (primarySpace S (p ^ m)) (primarySpace S (q ^ n)) :=
  isCompl_primarySpaces_of_mul_eq_zero hpq.pow hann

/-- A coprime factorization of the characteristic polynomial gives the actual
complementary kernel decomposition, by Cayley--Hamilton. -/
theorem isCompl_primarySpaces_of_charpoly_eq_mul
    [FiniteDimensional K V] {S : Module.End K V} {p q : K[X]}
    (hpq : IsCoprime p q) (hfactor : S.charpoly = p * q) :
    IsCompl (primarySpace S p) (primarySpace S q) := by
  apply isCompl_primarySpaces_of_mul_eq_zero hpq
  rw [← hfactor]
  simpa only [polyEval] using S.aeval_self_charpoly

/-- Powered form of the characteristic-polynomial decomposition. -/
theorem isCompl_primarySpaces_pow_of_charpoly_eq_mul
    [FiniteDimensional K V] {S : Module.End K V} {p q : K[X]}
    (hpq : IsCoprime p q) (m n : ℕ)
    (hfactor : S.charpoly = p ^ m * q ^ n) :
    IsCompl (primarySpace S (p ^ m)) (primarySpace S (q ^ n)) :=
  isCompl_primarySpaces_of_charpoly_eq_mul hpq.pow hfactor

/-- Coprime primary restrictions of a nondegenerate reflexive bilinear form
are nondegenerate as soon as their product annihilates the self-adjoint
operator. -/
theorem bilinear_primarySpaces_nondegenerate_of_mul_eq_zero
    {B : LinearMap.BilinForm K V} (hB : B.IsRefl)
    (hNondeg : B.Nondegenerate) {S : Module.End K V}
    (hS : Problem18SpectralBlocks20260930.IsSelfAdjointFor B S)
    {p q : K[X]} (hpq : IsCoprime p q) (m n : ℕ)
    (hann : polyEval S (p ^ m * q ^ n) = 0) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate :=
  Problem18SpectralBlocks20260930.coprime_primarySpaces_nondegenerate
    hB hNondeg hS hpq m n
      (isCompl_primarySpaces_pow_of_mul_eq_zero hpq m n hann).sup_eq_top

/-- Cayley--Hamilton supplies the annihilator needed by the bilinear primary
nondegeneracy theorem. -/
theorem bilinear_primarySpaces_nondegenerate_of_charpoly_eq_mul
    [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsRefl)
    (hNondeg : B.Nondegenerate) {S : Module.End K V}
    (hS : Problem18SpectralBlocks20260930.IsSelfAdjointFor B S)
    {p q : K[X]} (hpq : IsCoprime p q) (m n : ℕ)
    (hfactor : S.charpoly = p ^ m * q ^ n) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate :=
  Problem18SpectralBlocks20260930.coprime_primarySpaces_nondegenerate
    hB hNondeg hS hpq m n
      (isCompl_primarySpaces_pow_of_charpoly_eq_mul hpq m n hfactor).sup_eq_top

/-- Hermitian primary restrictions inherit nondegeneracy from a product
annihilator, with fixed-coefficient hypotheses kept explicit. -/
theorem hermitian_primarySpaces_nondegenerate_of_mul_eq_zero
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    (hB : B.IsSymm) (hNondeg : B.Nondegenerate)
    {S : Module.End K V}
    (hS : Problem18HermitianSpectral20260930.IsSelfAdjointFor sigma B S)
    {p q : K[X]}
    (hp : Problem18HermitianSpectral20260930.CoefficientsFixed sigma p)
    (hq : Problem18HermitianSpectral20260930.CoefficientsFixed sigma q)
    (hpq : IsCoprime p q) (m n : ℕ)
    (hann : polyEval S (p ^ m * q ^ n) = 0) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate :=
  Problem18HermitianSpectral20260930.coprime_primarySpaces_nondegenerate
    hB hNondeg hS hp hq hpq m n
      (isCompl_primarySpaces_pow_of_mul_eq_zero hpq m n hann).sup_eq_top

/-- Cayley--Hamilton form of Hermitian primary nondegeneracy. -/
theorem hermitian_primarySpaces_nondegenerate_of_charpoly_eq_mul
    [FiniteDimensional K V]
    {sigma : K ≃+* K}
    {B : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K}
    (hB : B.IsSymm) (hNondeg : B.Nondegenerate)
    {S : Module.End K V}
    (hS : Problem18HermitianSpectral20260930.IsSelfAdjointFor sigma B S)
    {p q : K[X]}
    (hp : Problem18HermitianSpectral20260930.CoefficientsFixed sigma p)
    (hq : Problem18HermitianSpectral20260930.CoefficientsFixed sigma q)
    (hpq : IsCoprime p q) (m n : ℕ)
    (hfactor : S.charpoly = p ^ m * q ^ n) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate :=
  Problem18HermitianSpectral20260930.coprime_primarySpaces_nondegenerate
    hB hNondeg hS hp hq hpq m n
      (isCompl_primarySpaces_pow_of_charpoly_eq_mul hpq m n hfactor).sup_eq_top

end Mathproof.Meta.Problem18SpectralDecomposition20260930
