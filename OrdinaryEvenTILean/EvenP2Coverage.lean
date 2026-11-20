import EvenP2Source
import EvenP2Corank

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Action EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Forms

noncomputable section

private theorem event_or_le {A : Type*} [Fintype A] (p q : A → Prop) :
    event (fun x => p x ∨ q x) ≤ event p + event q := by
  let f (a : A) : ℝ := if p a then 1 else 0
  let g (a : A) : ℝ := if q a then 1 else 0
  have h (x : A) :
      (@ite ℝ (p x ∨ q x) (Classical.propDecidable _) 1 0) ≤ f x + g x := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [f,g,hp,hq]
  change mean (fun x => @ite ℝ (p x ∨ q x) (Classical.propDecidable _) 1 0) ≤ _
  refine (mean_mono h).trans_eq ?_
  simp only [event, mean, f, g, Finset.sum_add_distrib, add_div]

variable {K : Type*} [Field K] [Fintype K] {l n : ℕ}

private theorem exceptionalKernels_mass (hl : 2 ≤ l) (hn : 64 ≤ n) :
    event (fun T : Source K l n => exceptionalKernels (exactKernels T)) ≤
      2 / n + 2 / (Fintype.card K : ℝ)^n := by
  let high (T : Source K l n) : Prop := n < Fintype.card K ^ finrank K (rightCutKernel T).ker
  have himp (T : Source K l n) (h : exceptionalKernels (exactKernels T)) :
      high T ∨ BadRightForm T ∨ BadLeftForm T := by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ((badRightForm_iff_fiber (withExactKernels T)).mpr h))
    · exact Or.inr (Or.inr ((badLeftForm_iff_fiber (withExactKernels T)).mpr h))
  have hmono : event (fun T : Source K l n => exceptionalKernels (exactKernels T)) ≤
      event (fun T : Source K l n => high T ∨ BadRightForm T ∨ BadLeftForm T) := by
    apply mean_mono
    intro T
    by_cases h : exceptionalKernels (exactKernels T)
    · simp [h, himp T h]
    · simp only [if_neg h]
      split <;> norm_num
  have h1 : event high ≤ 2 / n := square_cut_large_corank (by omega)
  have hR := badRightForm_fraction_uniform (K := K) (l := l) (n := n) (by omega) hl
  have hL := badLeftForm_fraction_uniform (K := K) (l := l) (n := n) (by omega) hl
  rw [← event_as_fraction] at hR hL
  refine hmono.trans ((event_or_le high _).trans ?_)
  calc
    _ ≤ 2 / (n : ℝ) + (1 / (Fintype.card K : ℝ)^n + 1 / (Fintype.card K : ℝ)^n) :=
      add_le_add h1 ((event_or_le BadRightForm BadLeftForm).trans (add_le_add hR hL))
    _ = _ := by ring

private theorem finite_kernelPair : Finite (KernelPair K l n) := by
  haveI : Finite (Submodule K (CutSide K l n)) :=
    Finite.of_injective (fun U : Submodule K (CutSide K l n) => (U : Set (CutSide K l n)))
      SetLike.coe_injective
  infer_instance

set_option maxHeartbeats 500000 in
private theorem kernelFiber_combination (hl : 2 ≤ l) (hn : 64 ≤ n) :
    event (singularShapeBad : Source K l n → Prop) ≤
      event (fun T : Source K l n => exceptionalKernels (exactKernels T)) +
        spectralFailureBound K n := by
  letI : Finite (KernelPair K l n) := finite_kernelPair
  letI : Fintype (KernelPair K l n) := Fintype.ofFinite _
  exact event_le_of_fibers (exactKernels : Source K l n → KernelPair K l n)
    singularShapeBad exceptionalKernels (spectralFailureBound K n)
    (spectralFailureBound_nonneg (K := K) (by omega : 2 ≤ n))
    (fun k hk => nonexceptionalFiber_bad k hl hn hk)

/-- The large-order singular coverage estimate on raw dense sources.
The spectral budget is tested on one suitable pair over the exact kernels. -/
theorem higherOrder_singular_coverage (hl : 2 ≤ l) (hn : 64 ≤ n) :
    event (singularShapeBad : Source K l n → Prop) ≤
      2 / n + 2 / (Fintype.card K : ℝ)^n + spectralFailureBound K n :=
  (kernelFiber_combination hl hn).trans
    (add_le_add (exceptionalKernels_mass hl hn) (le_refl _))

#print axioms higherOrder_singular_coverage

end
end Mathproof.EvenTI.Singular.Coverage
