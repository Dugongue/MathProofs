/- Clean-room rewrite (2026-10-04); no third-party code. -/
import Mathproof.Meta.Problem18PfaffianSimplePrimaryModule20260930
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

namespace Mathproof.Problem18PrimaryScalarCharpolyBoundary20260930
open Polynomial Module
open Mathproof.Problem18PfaffianSimplePrimaryModule20260930

/-- A block-diagonal matrix with every block equal to `M` has characteristic polynomial
`M.charpoly ^ (number of blocks)`. -/
theorem charpoly_blockDiagonal_const {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
    (M : Matrix n n R) :
    (Matrix.blockDiagonal (fun _ : m => M)).charpoly=M.charpoly^Fintype.card m := by
  have hc : (Matrix.blockDiagonal (fun _ : m => M)).charmatrix =
      Matrix.blockDiagonal (fun _ : m => M.charmatrix) := by
    ext ⟨i,k⟩ ⟨j,l⟩
    by_cases hkl : k=l
    · subst hkl
      by_cases hij : i=j
      · subst hij
        simp [Matrix.blockDiagonal_apply]
      · simp [Matrix.blockDiagonal_apply, hij]
    · simp [Matrix.blockDiagonal_apply, hkl]
  rw [Matrix.charpoly, hc, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ,
    Matrix.charpoly]

variable {K E V : Type*} [Field K] [Field E] [Algebra K E]
  [AddCommGroup V] [Module K V] [Module E V] [IsScalarTower K E V]

/-- A scalar operator in a scalar-tower basis is an actual constant block matrix. -/
theorem scalar_toMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K E) (c : Basis κ E V)
    (S : Module.End K V) (t : E) (hS : ∀ v, S v=t • v) :
    LinearMap.toMatrix (b.smulTower c) (b.smulTower c) S =
      Matrix.blockDiagonal (fun _ : κ => Algebra.leftMulMatrix b t) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [LinearMap.toMatrix_apply,Basis.smulTower_apply,hS,← mul_smul,
    Basis.smulTower_repr,map_smul,Basis.repr_self,Finsupp.smul_apply,smul_eq_mul,
    Matrix.blockDiagonal_apply,Algebra.leftMulMatrix_apply]
  by_cases h : k=l
  · subst l
    simp
  · simp [h,Ne.symm h]

/-- The quotient-field action proves the full characteristic-polynomial power formula. -/
theorem simplePrimary_charpoly_pow {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Module.End K V) (h : K[X]) (hm : h.Monic) (hirr : Irreducible h)
    (hzero : Polynomial.aeval S h=0) :
    letI : Fact (Irreducible h) := ⟨hirr⟩
    letI := simplePrimaryModule S h hzero
    S.charpoly=h^Module.finrank (AdjoinRoot h) V := by
  classical
  letI : Fact (Irreducible h) := ⟨hirr⟩
  letI := simplePrimaryModule S h hzero
  letI : IsScalarTower K (AdjoinRoot h) V := simplePrimaryScalarTower S h hzero
  letI : FiniteDimensional (AdjoinRoot h) V := FiniteDimensional.right K (AdjoinRoot h) V
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  let c := Module.finBasis (AdjoinRoot h) V
  rw [← LinearMap.charpoly_toMatrix S (pb.basis.smulTower c),
    scalar_toMatrix pb.basis c S (AdjoinRoot.root h) (fun v => (root_smul_eq S h hzero v).symm),
    charpoly_blockDiagonal_const,Fintype.card_fin]
  change (Algebra.leftMulMatrix pb.basis pb.gen).charpoly ^ _ = _
  rw [charpoly_leftMulMatrix,AdjoinRoot.minpoly_powerBasis_gen_of_monic hm]

end Mathproof.Problem18PrimaryScalarCharpolyBoundary20260930
