import ComparatorPrimarySplit
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Pi

/-! Complete primary coordinates and exact transport of a common factor
partition, without choosing a rational canonical form. -/
namespace Mathproof.Problem17Comparator46Primary
open scoped DirectSum BigOperators
open Algebra Module Polynomial
open Mathproof.Problem17ComparatorPrimarySplit

noncomputable section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

abbrev part (T : End K V) (p : K[X]) := LinearMap.ker (aeval T p)

theorem map_eval (S : End K V) (T : End K W) (L : V →ₗ[K] W)
    (h : ∀ x, L (S x) = T (L x)) (p : K[X]) (x : V) :
    L (aeval S p x) = aeval T p (L x) := by
  have hp (k : ℕ) (v : V) : L ((S^k) v) = (T^k) (L v) := by
    induction k generalizing v with
    | zero => simp
    | succ j ih =>
      simp only [pow_succ, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply]
    change L (a • (S^k) x) = a • (T^k) (L x)
    rw [LinearMap.map_smul, hp]

theorem coprime_intertwiner_zero (S : End K V) (T : End K W)
    (L : V →ₗ[K] W) (h : ∀ x, L (S x) = T (L x)) {p q : K[X]}
    (hp : aeval S p = 0) (hq : aeval T q = 0) (hc : IsCoprime p q) : L = 0 := by
  obtain ⟨a,b,hab⟩ := hc
  have ht : aeval T (a*p) + aeval T (b*q) = 1 := by rw [← map_add, hab, map_one]
  ext x
  have hz : aeval T p (L x) = 0 := by rw [← map_eval S T L h p x, hp]; simp
  have h := LinearMap.congr_fun ht (L x)
  simpa [map_mul, Module.End.mul_apply, hz, hq] using h.symm

theorem primary_internal {I : Type*} [Fintype I] [DecidableEq I]
    (S : End K V) (p : I → K[X])
    (hc : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hp : aeval S (∏ i, p i) = 0) :
    DirectSum.IsInternal (fun i => part S (p i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have h (i : I) (_ : i ∈ Finset.univ) (j : I) (_ : j ∈ Finset.univ)
      (hij : i ≠ j) : IsCoprime (p i) (p j) := hc hij
  constructor
  · rw [iSupIndep_def]
    intro i
    apply (disjoint_factor_remainder S Finset.univ p h (Finset.mem_univ i)).mono_right
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact Finset.le_sup (f := fun k => part S (p k))
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
  · apply top_unique
    calc
      ⊤ = LinearMap.ker (aeval S (∏ i, p i)) := by rw [hp, LinearMap.ker_zero]
      _ = Finset.univ.sup (fun i => part S (p i)) := ker_coprime_product S Finset.univ p h
      _ ≤ _ := Finset.sup_le fun i _ => le_iSup (fun j => part S (p j)) i

noncomputable def coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (S : End K V) (p : I → K[X])
    (hc : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hp : aeval S (∏ i, p i) = 0) : V ≃ₗ[K] ((i : I) → part S (p i)) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => part S (p i)))
    (primary_internal S p hc hp)).symm.trans (DirectSum.linearEquivFunOnFintype K I _)

theorem coordinates_symm_single {I : Type*} [Fintype I] [DecidableEq I]
    (S : End K V) (p : I → K[X])
    (hc : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hp : aeval S (∏ i, p i) = 0) (i : I) (v : part S (p i)) :
    (coordinates S p hc hp).symm (Pi.single i v) = v.val := by
  simp [coordinates, DirectSum.coeLinearMap]

def partMap (S : End K V) (T : End K W) (L : V →ₗ[K] W)
    (h : ∀ x, L (S x) = T (L x)) (p : K[X]) :
    part S p →ₗ[K] part T p :=
  (L.comp (part S p).subtype).codRestrict (part T p) (fun x => by
    change aeval T p (L x) = 0
    rw [← map_eval S T L h p x, show aeval S p x = 0 from x.property, map_zero])

theorem map_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (S : End K V) (T : End K W) (p : I → K[X])
    (hc : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hs : aeval S (∏ i, p i) = 0) (ht : aeval T (∏ i, p i) = 0)
    (L : V →ₗ[K] W) (h : ∀ x, L (S x) = T (L x)) (v : V) :
    coordinates T p hc ht (L v) = fun i => partMap S T L h (p i) (coordinates S p hc hs v i) := by
  classical
  let cs := coordinates S p hc hs
  let ct := coordinates T p hc ht
  let y := cs v
  have hsingle (i : I) :
      ct (L (cs.symm (Pi.single i (y i)))) =
        Pi.single i (partMap S T L h (p i) (y i)) := by
    apply ct.symm.injective
    rw [LinearEquiv.symm_apply_apply, coordinates_symm_single, coordinates_symm_single]
    rfl
  have hsum : (∑ i, Pi.single i (y i)) = y := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact Pi.single_eq_of_ne (Ne.symm hij) _
    · simp
  change ct (L v) = _
  calc
    _ = ct (L (cs.symm (∑ i, Pi.single i (y i)))) := by rw [hsum]; simp [y]
    _ = ∑ i, ct (L (cs.symm (Pi.single i (y i)))) := by simp only [map_sum]
    _ = ∑ i, Pi.single i (partMap S T L h (p i) (y i)) := Finset.sum_congr rfl (fun i _ => hsingle i)
    _ = _ := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [y,cs]
      · intro i _ hij
        exact Pi.single_eq_of_ne (Ne.symm hij) _
      · simp

end
end Mathproof.Problem17Comparator46Primary

#print axioms Mathproof.Problem17Comparator46Primary.primary_internal
#print axioms Mathproof.Problem17Comparator46Primary.map_coordinates
