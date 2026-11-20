import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Ring

/-! Primary subspaces from the literal kernels of powers of pairwise coprime
factors. Bézout polynomials split every input vector. -/
namespace Mathproof.Problem17ComparatorPrimarySplit
open Algebra Module Polynomial
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem bezout_eval (T : End K V) {a b f g : K[X]}
    (hab : a*f+b*g=1) :
    aeval T (a*f) + aeval T (b*g) = 1 := by
  rw [← map_add, hab, map_one]

theorem ker_coprime_disjoint (T : End K V) {f g : K[X]} (hcop : IsCoprime f g) :
    Disjoint (LinearMap.ker (aeval T f)) (LinearMap.ker (aeval T g)) := by
  obtain ⟨a,b,hab⟩ := hcop
  rw [Submodule.disjoint_def]
  intro x hf hg
  change aeval T f x = 0 at hf
  change aeval T g x = 0 at hg
  have h := LinearMap.congr_fun (bezout_eval T hab) x
  simpa [map_mul, Module.End.mul_apply, hf, hg] using h.symm

theorem ker_coprime_mul (T : End K V) {f g : K[X]} (hcop : IsCoprime f g) :
    LinearMap.ker (aeval T (f*g)) =
      LinearMap.ker (aeval T f) ⊔ LinearMap.ker (aeval T g) := by
  obtain ⟨a,b,hab⟩ := hcop
  apply le_antisymm
  · intro x hx
    change aeval T (f*g) x = 0 at hx
    apply Submodule.mem_sup.mpr
    refine ⟨aeval T (b*g) x, ?_, aeval T (a*f) x, ?_, ?_⟩
    · change aeval T f (aeval T (b*g) x) = 0
      rw [← Module.End.mul_apply, ← map_mul, show f*(b*g)=b*(f*g) by ring,
        map_mul, Module.End.mul_apply, hx, LinearMap.map_zero]
    · change aeval T g (aeval T (a*f) x) = 0
      rw [← Module.End.mul_apply, ← map_mul, show g*(a*f)=a*(f*g) by ring,
        map_mul, Module.End.mul_apply, hx, LinearMap.map_zero]
    · have h := LinearMap.congr_fun (bezout_eval T hab) x
      simpa only [LinearMap.add_apply, Module.End.one_apply, add_comm] using h
  · apply sup_le
    · intro x hx
      change aeval T f x = 0 at hx
      change aeval T (f*g) x = 0
      rw [mul_comm f g, map_mul, Module.End.mul_apply, hx, LinearMap.map_zero]
    · intro x hx
      change aeval T g x = 0 at hx
      change aeval T (f*g) x = 0
      rw [map_mul, Module.End.mul_apply, hx, LinearMap.map_zero]

theorem ker_coprime_product {I : Type*} [DecidableEq I] (T : End K V) (S : Finset I)
    (f : I → K[X]) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (f i) (f j)) :
    LinearMap.ker (aeval T (∏ i ∈ S, f i)) =
      S.sup (fun i => LinearMap.ker (aeval T (f i))) := by
  induction S using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | @insert i S hi ih =>
    have hcop : IsCoprime (f i) (∏ j ∈ S, f j) := IsCoprime.prod_right (fun j hj =>
      h i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun he => hi (he.symm ▸ hj)))
    rw [Finset.prod_insert hi, ker_coprime_mul T hcop, Finset.sup_insert]
    rw [ih (fun a ha b hb hab =>
      h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)]

theorem disjoint_factor_remainder {I : Type*} [DecidableEq I] (T : End K V) (S : Finset I)
    (f : I → K[X]) (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (f i) (f j))
    {i : I} (hi : i ∈ S) :
    Disjoint (LinearMap.ker (aeval T (f i)))
      ((S.erase i).sup (fun j => LinearMap.ker (aeval T (f j)))) := by
  rw [← ker_coprime_product T (S.erase i) f (fun a ha b hb hab =>
    h a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)]
  apply ker_coprime_disjoint T
  apply IsCoprime.prod_right
  intro j hj
  exact h i hi j (Finset.mem_of_mem_erase hj) (Ne.symm (Finset.ne_of_mem_erase hj))

end Mathproof.Problem17ComparatorPrimarySplit

#print axioms Mathproof.Problem17ComparatorPrimarySplit.ker_coprime_product
#print axioms Mathproof.Problem17ComparatorPrimarySplit.disjoint_factor_remainder