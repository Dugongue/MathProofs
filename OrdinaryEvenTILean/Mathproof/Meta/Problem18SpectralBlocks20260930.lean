import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.RingTheory.Coprime.Lemmas

open scoped Polynomial

namespace Mathproof.Meta.Problem18SpectralBlocks20260930

universe u v

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

/-- Self-adjointness relative to an arbitrary bilinear form. -/
def IsSelfAdjointFor (B : LinearMap.BilinForm K V) (S : Module.End K V) : Prop :=
  ∀ x y, B (S x) y = B x (S y)

/-- Polynomial functional calculus for an endomorphism. -/
noncomputable def polyEval (S : Module.End K V) (p : K[X]) : Module.End K V :=
  Polynomial.aeval S p

theorem isSelfAdjointFor_add {B : LinearMap.BilinForm K V} {S T : Module.End K V}
    (hS : IsSelfAdjointFor B S) (hT : IsSelfAdjointFor B T) :
    IsSelfAdjointFor B (S + T) := by
  intro x y
  simp only [LinearMap.add_apply, map_add]
  rw [hS, hT]

theorem isSelfAdjointFor_smul {B : LinearMap.BilinForm K V} {S : Module.End K V}
    (hS : IsSelfAdjointFor B S) (c : K) :
    IsSelfAdjointFor B (c • S) := by
  intro x y
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hS]

theorem isSelfAdjointFor_pow {B : LinearMap.BilinForm K V} {S : Module.End K V}
    (hS : IsSelfAdjointFor B S) (n : ℕ) :
    IsSelfAdjointFor B (S ^ n) := by
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

theorem isSelfAdjointFor_polyEval {B : LinearMap.BilinForm K V} {S : Module.End K V}
    (hS : IsSelfAdjointFor B S) (p : K[X]) :
    IsSelfAdjointFor B (polyEval S p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [polyEval, Polynomial.aeval_add] using isSelfAdjointFor_add hp hq
  | monomial n a =>
      simpa only [polyEval, Polynomial.aeval_monomial, ← Algebra.smul_def] using
        isSelfAdjointFor_smul (isSelfAdjointFor_pow hS n) a

/-- The kernel cut out by a polynomial in an endomorphism.  Powers of an
irreducible polynomial give the usual primary spaces. -/
noncomputable def primarySpace (S : Module.End K V) (p : K[X]) : Submodule K V :=
  LinearMap.ker (polyEval S p)

/-- Bézout orthogonality: kernels of coprime polynomials in a self-adjoint
operator pair to zero.  No characteristic assumption is used. -/
theorem coprime_kernels_pairing_eq_zero
    {B : LinearMap.BilinForm K V} {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor B S) (hpq : IsCoprime p q)
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
  rw [hxproject, isSelfAdjointFor_polyEval hS]
  simp [polyEval, Polynomial.aeval_mul, Module.End.mul_apply, hqy]

/-- Primary spaces belonging to coprime base polynomials are orthogonal, for
arbitrary positive or zero exponents as encoded by the powered kernels. -/
theorem coprime_primarySpaces_pairing_eq_zero
    {B : LinearMap.BilinForm K V} {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor B S) (hpq : IsCoprime p q) (m n : ℕ)
    {x y : V} (hx : x ∈ primarySpace S (p ^ m))
    (hy : y ∈ primarySpace S (q ^ n)) : B x y = 0 :=
  coprime_kernels_pairing_eq_zero hS hpq.pow hx hy

/-- Submodule form of coprime primary orthogonality. -/
theorem primarySpace_le_orthogonalBilin
    {B : LinearMap.BilinForm K V} {S : Module.End K V} {p q : K[X]}
    (hS : IsSelfAdjointFor B S) (hpq : IsCoprime p q) :
    primarySpace S q ≤ (primarySpace S p).orthogonalBilin B := by
  intro y hy x hx
  exact coprime_kernels_pairing_eq_zero hS hpq hx hy

/-- Binary CRT supplies a polynomial operator which is the identity on the
`p`-kernel and zero on the `q`-kernel. -/
theorem exists_crt_projector_polynomial
    {S : Module.End K V} {p q : K[X]} (hpq : IsCoprime p q) :
    ∃ e : K[X],
      (∀ x ∈ primarySpace S p, polyEval S e x = x) ∧
      (∀ y ∈ primarySpace S q, polyEval S e y = 0) := by
  rcases hpq with ⟨a, b, hab⟩
  refine ⟨b * q, ?_, ?_⟩
  · intro x hx
    have hpx : polyEval S p x = 0 := LinearMap.mem_ker.mp hx
    change (Polynomial.aeval S p) x = 0 at hpx
    calc
      polyEval S (b * q) x = polyEval S (a * p) x + polyEval S (b * q) x := by
        simp only [polyEval, Polynomial.aeval_mul, Module.End.mul_apply]
        simp [hpx]
      _ = polyEval S (a * p + b * q) x := by
        simp only [polyEval, Polynomial.aeval_add, LinearMap.add_apply]
      _ = x := by rw [hab]; simp [polyEval]
  · intro y hy
    have hqy : polyEval S q y = 0 := LinearMap.mem_ker.mp hy
    change (Polynomial.aeval S q) y = 0 at hqy
    simp [polyEval, Polynomial.aeval_mul, Module.End.mul_apply, hqy]

/-- A polynomial operator may be reduced modulo any monic annihilator without
changing the induced endomorphism, with the standard strict degree bound. -/
theorem reduce_polyEval_mod_annihilator
    {S : Module.End K V} {e χ : K[X]} (hχ : χ.Monic)
    (hann : polyEval S χ = 0) :
    polyEval S (e %ₘ χ) = polyEval S e ∧ (e %ₘ χ).degree < χ.degree := by
  constructor
  · exact Polynomial.aeval_modByMonic_eq_self_of_root hann
  · exact Polynomial.degree_modByMonic_lt e hχ

/-- Powered version of the CRT projector, directly matching primary kernels. -/
theorem exists_primary_crt_projector_polynomial
    {S : Module.End K V} {p q : K[X]} (hpq : IsCoprime p q) (m n : ℕ) :
    ∃ e : K[X],
      (∀ x ∈ primarySpace S (p ^ m), polyEval S e x = x) ∧
      (∀ y ∈ primarySpace S (q ^ n), polyEval S e y = 0) :=
  exists_crt_projector_polynomial hpq.pow

/-- A CRT projector can be chosen below the degree of any monic ambient
annihilator.  Taking the characteristic polynomial gives the usual bound by
the ambient dimension. -/
theorem exists_degree_bounded_crt_projector_polynomial
    {S : Module.End K V} {p q χ : K[X]} (hpq : IsCoprime p q)
    (hχ : χ.Monic) (hann : polyEval S χ = 0) :
    ∃ e : K[X],
      e.degree < χ.degree ∧
      (∀ x ∈ primarySpace S p, polyEval S e x = x) ∧
      (∀ y ∈ primarySpace S q, polyEval S e y = 0) := by
  obtain ⟨e, hep, heq⟩ := exists_crt_projector_polynomial (S := S) hpq
  refine ⟨e %ₘ χ, Polynomial.degree_modByMonic_lt e hχ, ?_, ?_⟩
  · intro x hx
    rw [(reduce_polyEval_mod_annihilator hχ hann).1]
    exact hep x hx
  · intro y hy
    rw [(reduce_polyEval_mod_annihilator hχ hann).1]
    exact heq y hy

/-- If an ambient nondegenerate reflexive bilinear space is the sum of a
submodule and a submodule orthogonal to it, then the first block is
nondegenerate.  Directness is not needed: it follows for the relevant radical
element from ambient nondegeneracy. -/
theorem nondegenerate_restrict_of_orthogonal_complement
    {B : LinearMap.BilinForm K V} (hB : B.IsRefl) (hNondeg : B.Nondegenerate)
    {U W : Submodule K V} (hsum : U ⊔ W = ⊤)
    (horth : W ≤ U.orthogonalBilin B) :
    (B.domRestrict₁₂ U U).Nondegenerate := by
  apply LinearMap.nondegenerate_restrict_of_disjoint_orthogonal hB
  refine Submodule.disjoint_def.mpr fun x hxU hxUorth => ?_
  apply hNondeg.1 x
  intro y
  have hy : y ∈ U ⊔ W := by rw [hsum]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  have hxu : B x u = 0 := hB.eq_zero (hxUorth u hu)
  have hxw : B x w = 0 := horth hw x hxU
  rw [hxu, hxw, add_zero]

/-- Two coprime primary spaces which exhaust the ambient space are both
regular blocks of a nondegenerate reflexive bilinear form. -/
theorem coprime_primarySpaces_nondegenerate
    {B : LinearMap.BilinForm K V} (hB : B.IsRefl) (hNondeg : B.Nondegenerate)
    {S : Module.End K V} (hS : IsSelfAdjointFor B S)
    {p q : K[X]} (hpq : IsCoprime p q) (m n : ℕ)
    (hsum : primarySpace S (p ^ m) ⊔ primarySpace S (q ^ n) = ⊤) :
    (B.domRestrict₁₂ (primarySpace S (p ^ m))
      (primarySpace S (p ^ m))).Nondegenerate ∧
    (B.domRestrict₁₂ (primarySpace S (q ^ n))
      (primarySpace S (q ^ n))).Nondegenerate := by
  constructor
  · exact nondegenerate_restrict_of_orthogonal_complement hB hNondeg hsum
      (primarySpace_le_orthogonalBilin hS hpq.pow)
  · exact nondegenerate_restrict_of_orthogonal_complement hB hNondeg
      (by simpa only [sup_comm] using hsum)
      (primarySpace_le_orthogonalBilin hS hpq.symm.pow)

/-- Cayley--Hamilton specializes the degree-bounded CRT construction to a
projector polynomial of degree strictly below the ambient dimension. -/
theorem exists_finrank_bounded_crt_projector_polynomial
    [FiniteDimensional K V] {S : Module.End K V} {p q : K[X]}
    (hpq : IsCoprime p q) :
    ∃ e : K[X],
      e.degree < (Module.finrank K V : WithBot ℕ) ∧
      (∀ x ∈ primarySpace S p, polyEval S e x = x) ∧
      (∀ y ∈ primarySpace S q, polyEval S e y = 0) := by
  obtain ⟨e, hedeg, hep, heq⟩ :=
    exists_degree_bounded_crt_projector_polynomial (S := S) hpq
      S.charpoly_monic (by simpa only [polyEval] using S.aeval_self_charpoly)
  refine ⟨e, ?_, hep, heq⟩
  rw [Polynomial.degree_eq_natDegree S.charpoly_monic.ne_zero,
    S.charpoly_natDegree] at hedeg
  exact hedeg

end Mathproof.Meta.Problem18SpectralBlocks20260930
