import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Full automorphism groups of cubic bent support codes and designs

For every integer t ≥ 1 and s ≥ 0, let d = 3t and
  f(x,y,u,v) = x · y + ∑ j, y(j,0)y(j,1)y(j,2) + u · v
on F₂^d × F₂^d × F₂^s × F₂^s.

This file computes the full automorphism groups of the restricted affine
support code and the dual-Walsh support design, including every affine
symmetry mixing cubic and quadratic coordinates. Both groups are isomorphic to
  U_(d,s) ⋊ ((GL(3,2)^t ⋊ Sym(t)) × Sp(2s,2)),
where U consists of all pairs (E,B) with B+Bᵀ=EᵀJE and multiplication
  (E,B)(E',B') = (E+E', B+B'+EᵀJE').
The Levi action is (E,B) ↦ (F E D⁻¹, D⁻ᵀ B D⁻¹). Their common order is
  2^(d(d+1)/2 + 2sd + s²) · 168^t · t! · ∏ i=1..s (2^(2i)-1).

This supplies an explicit family-level answer to Open Problem 6 of
Hyun–Kwon–Wang–Wu, “Designs, linear codes, plateaued functions, and their
interconnections” (2026), arXiv:2605.24355v1. Their Theorem 8 gives the abstract
affine-stabilizer identification; here the transfer is proved and the full
stabilizer is explicitly determined. The objects are precisely the restricted
affine evaluation code and Theorem 6's support design, not its complement.

The proof includes the exact Walsh spectrum, affine support spanning, code
reconstruction, distinct design blocks, the point/block-permutation convention,
the pair-kernel laws, and the general-linear wreath-product identification.
Main results in CubicBentAutomorphisms:
  complete_code_design_result; explicit_code_design_groups;
  explicit_incidence_group; card_supportCodeAut; card_supportDesignAut;
  card_supportIncidenceAut.

Only Mathlib is imported. This is a special-family classification, not a
classification of all bent functions, a publication-priority certification,
or a nonexistence theorem for MUBs in complex dimension six. Ancillary
center, commutator, and point-orbit classifications are not claimed here.
-/

/-! ## Intrinsic cubic invariants -/

section
open scoped BigOperators

namespace CubicBentAutomorphisms

abbrev F₂ := ZMod 2
abbrev Y (t : ℕ) := Fin t × Fin 3 → F₂
abbrev Z (s : ℕ) := (Fin s → F₂) × (Fin s → F₂)
abbrev V (t s : ℕ) := (Y t × Y t) × Z s

def dot {ι : Type*} [Fintype ι] (a b : ι → F₂) : F₂ := ∑ i, a i * b i

def cubic (t : ℕ) (y : Y t) : F₂ :=
  ∑ j : Fin t, y (j, 0) * y (j, 1) * y (j, 2)

def hyperbolic (s : ℕ) (z : Z s) : F₂ := dot z.1 z.2

def quad (t s : ℕ) (w : V t s) : F₂ :=
  dot w.1.1 w.1.2 + hyperbolic s w.2

def bentFamily (t s : ℕ) (w : V t s) : F₂ :=
  quad t s w + cubic t w.1.2

@[simp] theorem add_self_F₂ (a : F₂) : a + a = 0 := by
  fin_cases a <;> decide

@[simp] theorem two_F₂ : (2 : F₂) = 0 := rfl

@[simp] theorem three_F₂ : (3 : F₂) = 1 := by decide

@[simp] theorem four_F₂ : (4 : F₂) = 0 := rfl

@[simp] theorem eight_F₂ : (8 : F₂) = 0 := rfl

def gradient (t : ℕ) (y : Y t) : Y t := fun i =>
  if i.2 = 0 then y (i.1, 1) * y (i.1, 2)
  else if i.2 = 1 then y (i.1, 0) * y (i.1, 2)
  else y (i.1, 0) * y (i.1, 1)

theorem block_euler (t : ℕ) (y : Y t) (j : Fin t) :
    (∑ k : Fin 3, y (j, k) * gradient t y (j, k)) =
      y (j, 0) * y (j, 1) * y (j, 2) := by
  rw [Fin.sum_univ_three]
  simp [gradient]
  ring_nf
  simp

theorem dot_gradient (t : ℕ) (y : Y t) :
    dot y (gradient t y) = cubic t y := by
  classical
  rw [dot, cubic, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  exact block_euler t y j

def shear (t s : ℕ) (w : V t s) : V t s :=
  ((w.1.1 + gradient t w.1.2, w.1.2), w.2)

@[simp] theorem gradient_zero (t : ℕ) : gradient t (0 : Y t) = 0 := by
  ext i
  simp [gradient]

theorem gradient_add_self (t : ℕ) (y : Y t) :
    gradient t y + gradient t y = 0 := by
  ext i
  exact add_self_F₂ _

theorem shear_involutive (t s : ℕ) : Function.Involutive (shear t s) := by
  intro w
  ext i <;> simp [shear, gradient_add_self, add_assoc]

def shearEquiv (t s : ℕ) : V t s ≃ V t s where
  toFun := shear t s
  invFun := shear t s
  left_inv := shear_involutive t s
  right_inv := shear_involutive t s

theorem bentFamily_eq_quad_shear (t s : ℕ) (w : V t s) :
    bentFamily t s w = quad t s (shear t s w) := by
  have hg : (∑ i, gradient t w.1.2 i * w.1.2 i) = cubic t w.1.2 := by
    simpa only [dot, mul_comm] using dot_gradient t w.1.2
  simp only [bentFamily, quad, shear, dot, hyperbolic, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]
  rw [hg]
  abel

theorem quad_shear (t s : ℕ) (w : V t s) :
    quad t s (shear t s w) = bentFamily t s w :=
  (bentFamily_eq_quad_shear t s w).symm

section AffineCoordinates

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

/-- The affine equivalence with linear part `L` and translation `c`. -/
def affineOfLinearTranslation (L : W ≃ₗ[F₂] W) (c : W) : W ≃ᵃ[F₂] W where
  toFun w := L w + c
  invFun w := L.symm (w - c)
  left_inv w := by simp
  right_inv w := by simp
  linear := L
  map_vadd' p v := by simp [add_assoc, add_left_comm, add_comm]

@[simp] theorem affineOfLinearTranslation_apply
    (L : W ≃ₗ[F₂] W) (c w : W) :
    affineOfLinearTranslation L c w = L w + c := rfl

@[simp] theorem affineOfLinearTranslation_linear
    (L : W ≃ₗ[F₂] W) (c : W) :
    (affineOfLinearTranslation L c).linear = L := rfl

@[simp] theorem affineOfLinearTranslation_zero
    (L : W ≃ₗ[F₂] W) (c : W) :
    affineOfLinearTranslation L c 0 = c := by simp

/-- An affine self-equivalence is uniquely its linear part and its value at zero. -/
def affineEquivLinearTranslationEquiv :
    (W ≃ᵃ[F₂] W) ≃ ((W ≃ₗ[F₂] W) × W) where
  toFun e := (e.linear, e 0)
  invFun p := affineOfLinearTranslation p.1 p.2
  left_inv e := by
    apply AffineEquiv.ext
    intro w
    simpa only [affineOfLinearTranslation_apply, vadd_eq_add, add_zero] using
      (e.map_vadd (0 : W) w).symm
  right_inv p := by
    rcases p with ⟨L, c⟩
    simp

theorem affine_apply_eq_linear_add (e : W ≃ᵃ[F₂] W) (w : W) :
    e w = e.linear w + e 0 := by
  simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : W) w

end AffineCoordinates

/-- The full affine stabilizer whose cardinality is computed below. -/
abbrev AffineStabilizer (t s : ℕ) :=
  {e : V t s ≃ᵃ[F₂] V t s // ∀ w, bentFamily t s (e w) = bentFamily t s w}

section IntrinsicDerivatives

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

/-- The characteristic-two third finite difference. -/
def thirdDifference (g : W → F₂) (a b c x : W) : F₂ :=
  g x + g (x + a) + g (x + b) + g (x + c) +
  g (x + a + b) + g (x + a + c) + g (x + b + c) +
  g (x + a + b + c)

theorem affine_add (e : W ≃ᵃ[F₂] W) (x a : W) :
    e (x + a) = e x + e.linear a := by
  simpa only [add_comm, vadd_eq_add] using e.map_vadd x a

theorem thirdDifference_affine (g : W → F₂) (e : W ≃ᵃ[F₂] W)
    (a b c x : W) :
    thirdDifference (fun w => g (e w)) a b c x =
      thirdDifference g (e.linear a) (e.linear b) (e.linear c) (e x) := by
  simp only [thirdDifference, affine_add]

theorem thirdDifference_congr {g h : W → F₂}
    (heq : ∀ w, g w = h w) (a b c x : W) :
    thirdDifference g a b c x = thirdDifference h a b c x := by
  simp only [thirdDifference, heq]

theorem thirdDifference_add (g h : W → F₂) (a b c x : W) :
    thirdDifference (fun w => g w + h w) a b c x =
      thirdDifference g a b c x + thirdDifference h a b c x := by
  simp only [thirdDifference]
  abel

end IntrinsicDerivatives

def volumeBlock (t : ℕ) (a b c : Y t) (j : Fin t) : F₂ :=
    a (j, 0) * b (j, 1) * c (j, 2) +
    a (j, 0) * c (j, 1) * b (j, 2) +
    b (j, 0) * a (j, 1) * c (j, 2) +
    b (j, 0) * c (j, 1) * a (j, 2) +
    c (j, 0) * a (j, 1) * b (j, 2) +
    c (j, 0) * b (j, 1) * a (j, 2)

def cubicTensor (t : ℕ) (a b c : Y t) : F₂ :=
  ∑ j, volumeBlock t a b c j

def unitY (t : ℕ) (j : Fin t) (k : Fin 3) : Y t := fun i =>
  if i = (j, k) then 1 else 0

theorem cubicTensor_unit_one_two (t : ℕ) (a : Y t) (j : Fin t) :
    cubicTensor t a (unitY t j 1) (unitY t j 2) = a (j, 0) := by
  classical
  simp [cubicTensor, volumeBlock, unitY]

theorem cubicTensor_unit_zero_two (t : ℕ) (a : Y t) (j : Fin t) :
    cubicTensor t a (unitY t j 0) (unitY t j 2) = a (j, 1) := by
  classical
  simp [cubicTensor, volumeBlock, unitY]

theorem cubicTensor_unit_zero_one (t : ℕ) (a : Y t) (j : Fin t) :
    cubicTensor t a (unitY t j 0) (unitY t j 1) = a (j, 2) := by
  classical
  simp [cubicTensor, volumeBlock, unitY]

theorem cubicTensor_radical_iff (t : ℕ) (a : Y t) :
    (∀ b c, cubicTensor t a b c = 0) ↔ a = 0 := by
  constructor
  · intro h
    ext i
    rcases i with ⟨j, k⟩
    fin_cases k
    · have hi := h (unitY t j 1) (unitY t j 2)
      rwa [cubicTensor_unit_one_two] at hi
    · have hi := h (unitY t j 0) (unitY t j 2)
      rwa [cubicTensor_unit_zero_two] at hi
    · have hi := h (unitY t j 0) (unitY t j 1)
      rwa [cubicTensor_unit_zero_one] at hi
  · rintro rfl b c
    simp [cubicTensor, volumeBlock]

theorem thirdDifference_block_cubic (t : ℕ) (a b c x : Y t) (j : Fin t) :
    thirdDifference
        (fun y => y (j, 0) * y (j, 1) * y (j, 2)) a b c x =
      volumeBlock t a b c j := by
  simp only [thirdDifference, volumeBlock, Pi.add_apply]
  ring_nf
  simp

theorem thirdDifference_cubic (t : ℕ) (a b c x : Y t) :
    thirdDifference (cubic t) a b c x = cubicTensor t a b c := by
  classical
  simp only [thirdDifference, cubic, cubicTensor, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact thirdDifference_block_cubic t a b c x j

theorem thirdDifference_dot_pair {ι : Type*} [Fintype ι]
    (a b c x : (ι → F₂) × (ι → F₂)) :
    thirdDifference (fun p => dot p.1 p.2) a b c x = 0 := by
  classical
  simp only [thirdDifference, dot, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring_nf
  simp

theorem thirdDifference_hyperbolic (s : ℕ) (a b c x : Z s) :
    thirdDifference (hyperbolic s) a b c x = 0 :=
  thirdDifference_dot_pair a b c x

theorem thirdDifference_quad (t s : ℕ) (a b c x : V t s) :
    thirdDifference (quad t s) a b c x = 0 := by
  rw [show quad t s = fun w => dot w.1.1 w.1.2 + hyperbolic s w.2 from rfl]
  rw [thirdDifference_add]
  change thirdDifference (fun p => dot p.1 p.2) a.1 b.1 c.1 x.1 +
      thirdDifference (hyperbolic s) a.2 b.2 c.2 x.2 = 0
  rw [thirdDifference_dot_pair, thirdDifference_hyperbolic, zero_add]

theorem thirdDifference_bentFamily (t s : ℕ) (a b c x : V t s) :
    thirdDifference (bentFamily t s) a b c x =
      cubicTensor t a.1.2 b.1.2 c.1.2 := by
  rw [show bentFamily t s = fun w => quad t s w + cubic t w.1.2 from rfl]
  rw [thirdDifference_add, thirdDifference_quad, zero_add]
  simpa only [thirdDifference, Prod.fst_add, Prod.snd_add] using
    thirdDifference_cubic t a.1.2 b.1.2 c.1.2 x.1.2

theorem affine_stabilizer_preserves_thirdDifference
    {t s : ℕ} (e : AffineStabilizer t s) (a b c x : V t s) :
    thirdDifference (bentFamily t s) (e.1.linear a) (e.1.linear b)
        (e.1.linear c) (e.1 x) =
      thirdDifference (bentFamily t s) a b c x := by
  rw [← thirdDifference_affine]
  exact thirdDifference_congr e.2 a b c x

theorem affine_stabilizer_preserves_cubicTensor
    {t s : ℕ} (e : AffineStabilizer t s) (a b c : V t s) :
    cubicTensor t (e.1.linear a).1.2 (e.1.linear b).1.2
        (e.1.linear c).1.2 = cubicTensor t a.1.2 b.1.2 c.1.2 := by
  simpa only [thirdDifference_bentFamily] using
    affine_stabilizer_preserves_thirdDifference e a b c 0

def InCubicRadical (t s : ℕ) (a : V t s) : Prop :=
  ∀ b c : V t s, cubicTensor t a.1.2 b.1.2 c.1.2 = 0

theorem inCubicRadical_iff (t s : ℕ) (a : V t s) :
    InCubicRadical t s a ↔ a.1.2 = 0 := by
  constructor
  · intro h
    rw [← cubicTensor_radical_iff]
    intro b c
    simpa using h ((0, b), 0) ((0, c), 0)
  · intro ha b c
    rw [ha]
    simp [cubicTensor, volumeBlock]

theorem affine_stabilizer_preserves_cubic_radical
    {t s : ℕ} (e : AffineStabilizer t s) {a : V t s}
    (ha : a.1.2 = 0) : (e.1.linear a).1.2 = 0 := by
  rw [← inCubicRadical_iff] at ha ⊢
  intro p q
  obtain ⟨b, rfl⟩ := e.1.linear.surjective p
  obtain ⟨c, rfl⟩ := e.1.linear.surjective q
  rw [affine_stabilizer_preserves_cubicTensor]
  exact ha b c

/-- The characteristic-two second finite difference. -/
def secondDifference {W : Type*} [Add W] (g : W → F₂) (a b x : W) : F₂ :=
  g x + g (x + a) + g (x + b) + g (x + a + b)

theorem secondDifference_affine {W : Type*} [AddCommGroup W] [Module F₂ W]
    (g : W → F₂) (e : W ≃ᵃ[F₂] W) (a b x : W) :
    secondDifference (fun w => g (e w)) a b x =
      secondDifference g (e.linear a) (e.linear b) (e x) := by
  simp only [secondDifference, affine_add]

theorem secondDifference_congr {W : Type*} [Add W] {g h : W → F₂}
    (heq : ∀ w, g w = h w) (a b x : W) :
    secondDifference g a b x = secondDifference h a b x := by
  simp only [secondDifference, heq]

theorem secondDifference_add {W : Type*} [Add W]
    (g h : W → F₂) (a b x : W) :
    secondDifference (fun w => g w + h w) a b x =
      secondDifference g a b x + secondDifference h a b x := by
  simp only [secondDifference]
  abel

def polarZ (s : ℕ) (a b : Z s) : F₂ :=
  dot a.1 b.2 + dot b.1 a.2

theorem secondDifference_dot_pair {ι : Type*} [Fintype ι]
    (a b x : (ι → F₂) × (ι → F₂)) :
    secondDifference (fun p => dot p.1 p.2) a b x =
      dot a.1 b.2 + dot b.1 a.2 := by
  classical
  simp only [secondDifference, dot, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  simp

theorem secondDifference_hyperbolic (s : ℕ) (a b x : Z s) :
    secondDifference (hyperbolic s) a b x = polarZ s a b :=
  secondDifference_dot_pair a b x

theorem secondDifference_cubic_zero_of_y_zero (t : ℕ) (a b : Y t)
    (ha : a = 0) (hb : b = 0) (x : Y t) :
    secondDifference (cubic t) a b x = 0 := by
  subst a
  subst b
  simp [secondDifference]

theorem secondDifference_quad_on_cubicRadical (t s : ℕ) (a b x : V t s)
    (ha : a.1.2 = 0) (hb : b.1.2 = 0) :
    secondDifference (quad t s) a b x = polarZ s a.2 b.2 := by
  rw [show quad t s = fun w => dot w.1.1 w.1.2 + hyperbolic s w.2 from rfl]
  rw [show secondDifference
      (fun w : V t s => dot w.1.1 w.1.2 + hyperbolic s w.2) a b x =
      secondDifference (fun p => dot p.1 p.2) a.1 b.1 x.1 +
        secondDifference (hyperbolic s) a.2 b.2 x.2 by
    rw [secondDifference_add]
    rfl]
  rw [secondDifference_dot_pair, secondDifference_hyperbolic]
  rw [ha, hb]
  simp [dot]

theorem secondDifference_bent_on_cubicRadical (t s : ℕ) (a b x : V t s)
    (ha : a.1.2 = 0) (hb : b.1.2 = 0) :
    secondDifference (bentFamily t s) a b x = polarZ s a.2 b.2 := by
  rw [show bentFamily t s = fun w => quad t s w + cubic t w.1.2 from rfl]
  rw [show secondDifference
      (fun w : V t s => quad t s w + cubic t w.1.2) a b x =
      secondDifference (quad t s) a b x +
        secondDifference (cubic t) a.1.2 b.1.2 x.1.2 by
    rw [secondDifference_add]
    rfl]
  rw [secondDifference_quad_on_cubicRadical t s a b x ha hb,
    secondDifference_cubic_zero_of_y_zero t a.1.2 b.1.2 ha hb, add_zero]

def unitFin (s : ℕ) (i : Fin s) : Fin s → F₂ := fun j => if j = i then 1 else 0

@[simp] theorem dot_zero_left {ι : Type*} [Fintype ι] (a : ι → F₂) :
    dot 0 a = 0 := by simp [dot]

@[simp] theorem dot_zero_right {ι : Type*} [Fintype ι] (a : ι → F₂) :
    dot a 0 = 0 := by simp [dot]

theorem dot_unit_right (s : ℕ) (a : Fin s → F₂) (i : Fin s) :
    dot a (unitFin s i) = a i := by
  classical
  simp [dot, unitFin]

theorem dot_unit_left (s : ℕ) (a : Fin s → F₂) (i : Fin s) :
    dot (unitFin s i) a = a i := by
  simpa only [dot, mul_comm] using dot_unit_right s a i

theorem polarZ_nondegenerate (s : ℕ) (a : Z s) :
    (∀ b, polarZ s a b = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · funext i
      change a.1 i = 0
      have hi := h (0, unitFin s i)
      simpa only [polarZ, dot_unit_right, dot_zero_left, add_zero] using hi
    · funext i
      change a.2 i = 0
      have hi := h (unitFin s i, 0)
      simpa only [polarZ, dot_unit_left, dot_zero_right, zero_add] using hi
  · rintro rfl b
    simp [polarZ, dot]

def InSecondRadicalWithinCubic (t s : ℕ) (a : V t s) : Prop :=
  a.1.2 = 0 ∧ ∀ b : V t s, b.1.2 = 0 →
    secondDifference (bentFamily t s) a b 0 = 0

theorem inSecondRadicalWithinCubic_iff (t s : ℕ) (a : V t s) :
    InSecondRadicalWithinCubic t s a ↔ a.1.2 = 0 ∧ a.2 = 0 := by
  constructor
  · rintro ⟨hay, h⟩
    refine ⟨hay, (polarZ_nondegenerate s a.2).mp ?_⟩
    intro z
    have hz := h ((0, 0), z) rfl
    rwa [secondDifference_bent_on_cubicRadical t s a ((0, 0), z) 0 hay rfl] at hz
  · rintro ⟨hay, haz⟩
    refine ⟨hay, ?_⟩
    intro b hby
    rw [secondDifference_bent_on_cubicRadical t s a b 0 hay hby, haz]
    simp [polarZ, dot]

def stabilizerSymm {t s : ℕ} (e : AffineStabilizer t s) : AffineStabilizer t s :=
  ⟨e.1.symm, fun w => by
    have h := e.2 (e.1.symm w)
    simpa using h.symm⟩

theorem affine_stabilizer_preserves_secondDifference
    {t s : ℕ} (e : AffineStabilizer t s) (a b x : V t s) :
    secondDifference (bentFamily t s) (e.1.linear a) (e.1.linear b) (e.1 x) =
      secondDifference (bentFamily t s) a b x := by
  rw [← secondDifference_affine]
  exact secondDifference_congr e.2 a b x

theorem affine_stabilizer_preserves_intrinsic_x_space
    {t s : ℕ} (e : AffineStabilizer t s) {a : V t s}
    (hay : a.1.2 = 0) (haz : a.2 = 0) :
    (e.1.linear a).1.2 = 0 ∧ (e.1.linear a).2 = 0 := by
  rw [← inSecondRadicalWithinCubic_iff]
  refine ⟨affine_stabilizer_preserves_cubic_radical e hay, ?_⟩
  intro p hpy
  let b := e.1.linear.symm p
  have hby : b.1.2 = 0 := by
    have h := affine_stabilizer_preserves_cubic_radical (stabilizerSymm e) hpy
    simpa only [stabilizerSymm, AffineEquiv.linear_symm] using h
  have hsecond := affine_stabilizer_preserves_secondDifference e a b 0
  rw [e.1.linear.apply_symm_apply] at hsecond
  have hlay := affine_stabilizer_preserves_cubic_radical e hay
  rw [secondDifference_bent_on_cubicRadical t s (e.1.linear a) p (e.1 0) hlay hpy,
    secondDifference_bent_on_cubicRadical t s a b 0 hay hby] at hsecond
  rw [secondDifference_bent_on_cubicRadical t s (e.1.linear a) p 0 hlay hpy,
    hsecond]
  have hz := ((inSecondRadicalWithinCubic_iff t s a).mpr ⟨hay, haz⟩).2 b hby
  rwa [secondDifference_bent_on_cubicRadical t s a b 0 hay hby] at hz

section GradientPolarization

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

@[simp] theorem module_add_self (w : W) : w + w = 0 := by
  rw [← two_smul F₂ w, two_F₂, zero_smul]

end GradientPolarization

theorem dot_comm {ι : Type*} [Fintype ι] (a b : ι → F₂) : dot a b = dot b a := by
  simp only [dot, mul_comm]

theorem dot_add_left {ι : Type*} [Fintype ι]
    (a b c : ι → F₂) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {ι : Type*} [Fintype ι]
    (a b c : ι → F₂) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_unitY_left (t : ℕ) (a : Y t) (j : Fin t) (k : Fin 3) :
    dot (unitY t j k) a = a (j, k) := by
  classical
  simp [dot, unitY]

theorem dot_nondegenerate (t : ℕ) (a : Y t) :
    (∀ c, dot c a = 0) ↔ a = 0 := by
  constructor
  · intro h
    funext i
    rcases i with ⟨j, k⟩
    change a (j, k) = 0
    simpa only [dot_unitY_left] using h (unitY t j k)
  · rintro rfl c
    exact dot_zero_right c

theorem gradient_polar_block (t : ℕ) (a b c : Y t) (j : Fin t) :
    (∑ k : Fin 3, c (j, k) *
      (gradient t (a + b) (j, k) + gradient t a (j, k) +
        gradient t b (j, k))) = volumeBlock t c a b j := by
  rw [Fin.sum_univ_three]
  simp [gradient]
  ring_nf
  simp
  unfold volumeBlock
  ring

theorem gradient_polar (t : ℕ) (a b c : Y t) :
    dot c (gradient t (a + b) + gradient t a + gradient t b) =
      cubicTensor t c a b := by
  classical
  rw [dot, cubicTensor, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Pi.add_apply] using gradient_polar_block t a b c j

def gradientCorrection {t : ℕ} (P D : Y t ≃ₗ[F₂] Y t) (y : Y t) : Y t :=
  P (gradient t y) + gradient t (D y)

theorem gradientCorrection_additive {t : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (hpair : ∀ x y, dot (P x) (D y) = dot x y)
    (htensor : ∀ a b c,
      cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (a b : Y t) :
    gradientCorrection P D (a + b) =
      gradientCorrection P D a + gradientCorrection P D b := by
  have hz : gradientCorrection P D (a + b) + gradientCorrection P D a +
      gradientCorrection P D b = 0 := by
    rw [← dot_nondegenerate]
    intro z
    obtain ⟨c, rfl⟩ := D.surjective z
    have hpair' (x y : Y t) : dot (D y) (P x) = dot x y := by
      rw [dot_comm, hpair]
    have hp : dot (D c) (P (gradient t (a + b))) +
        dot (D c) (P (gradient t a)) + dot (D c) (P (gradient t b)) =
        cubicTensor t c a b := by
      rw [hpair', hpair', hpair']
      simpa only [dot_add_right, dot_comm] using gradient_polar t a b c
    have hpD : dot (D c) (gradient t (D a + D b)) +
        dot (D c) (gradient t (D a)) + dot (D c) (gradient t (D b)) =
        cubicTensor t c a b := by
      have h := gradient_polar t (D a) (D b) (D c)
      rw [htensor] at h
      simpa only [dot_add_right] using h
    calc
      dot (D c) (gradientCorrection P D (a + b) +
          gradientCorrection P D a + gradientCorrection P D b) =
          (dot (D c) (P (gradient t (a + b))) +
              dot (D c) (P (gradient t a)) + dot (D c) (P (gradient t b))) +
            (dot (D c) (gradient t (D a + D b)) +
              dot (D c) (gradient t (D a)) + dot (D c) (gradient t (D b))) := by
        simp only [gradientCorrection, dot_add_right, map_add]
        abel
      _ = cubicTensor t c a b + cubicTensor t c a b := by rw [hp, hpD]
      _ = 0 := add_self_F₂ _
  calc
    gradientCorrection P D (a + b) =
        gradientCorrection P D (a + b) + 0 := by simp
    _ = gradientCorrection P D (a + b) +
        (gradientCorrection P D (a + b) + gradientCorrection P D a +
          gradientCorrection P D b) := by rw [hz]
    _ = gradientCorrection P D a + gradientCorrection P D b := by
      calc
        gradientCorrection P D (a + b) +
              (gradientCorrection P D (a + b) + gradientCorrection P D a +
                gradientCorrection P D b) =
            (gradientCorrection P D (a + b) + gradientCorrection P D (a + b)) +
              (gradientCorrection P D a + gradientCorrection P D b) := by abel
        _ = gradientCorrection P D a + gradientCorrection P D b := by
          rw [module_add_self, zero_add]

def gradientCorrectionLinear {t : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (hpair : ∀ x y, dot (P x) (D y) = dot x y)
    (htensor : ∀ a b c,
      cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c) :
    Y t →ₗ[F₂] Y t where
  toFun := gradientCorrection P D
  map_add' := gradientCorrection_additive P D hpair htensor
  map_smul' r y := by
    have hr : r = 0 ∨ r = 1 := (by decide : ∀ q : F₂, q = 0 ∨ q = 1) r
    rcases hr with rfl | rfl <;> simp [gradientCorrection]

theorem card_GL_three_F₂ : Nat.card (GL (Fin 3) F₂) = 168 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  change Nat.card (GL (Fin 3) (ZMod 2)) = 168
  rw [Matrix.card_GL_field (𝔽 := ZMod 2)]
  norm_num [Fin.prod_univ_three, ZMod.card]

theorem card_block_permutations (t : ℕ) :
    Nat.card (Equiv.Perm (Fin t)) = Nat.factorial t := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem card_binary_coordinates (n : ℕ) :
    Nat.card (Fin n → F₂) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

section ExplicitCubicTensorSymmetries

abbrev Block₃ := Fin 3 → F₂

def blockSlice {t : ℕ} (y : Y t) (j : Fin t) : Block₃ := fun k => y (j, k)

@[simp] theorem blockSlice_apply {t : ℕ} (y : Y t) (j : Fin t) (k : Fin 3) :
    blockSlice y j k = y (j, k) := rfl

@[simp] theorem blockSlice_add {t : ℕ} (a b : Y t) (j : Fin t) :
    blockSlice (a + b) j = blockSlice a j + blockSlice b j := rfl

@[simp] theorem blockSlice_smul {t : ℕ} (r : F₂) (a : Y t) (j : Fin t) :
    blockSlice (r • a) j = r • blockSlice a j := rfl

def volume₃ (a b c : Block₃) : F₂ :=
  a 0 * b 1 * c 2 + a 0 * c 1 * b 2 +
  b 0 * a 1 * c 2 + b 0 * c 1 * a 2 +
  c 0 * a 1 * b 2 + c 0 * b 1 * a 2

theorem volumeBlock_eq_volume₃ {t : ℕ} (a b c : Y t) (j : Fin t) :
    volumeBlock t a b c j =
      volume₃ (blockSlice a j) (blockSlice b j) (blockSlice c j) := rfl

def threeColumns (a b c : Block₃) : Matrix (Fin 3) (Fin 3) F₂ := fun i j =>
  if j = 0 then a i else if j = 1 then b i else c i

theorem det_threeColumns (a b c : Block₃) :
    (threeColumns a b c).det = volume₃ a b c := by
  rw [Matrix.det_fin_three]
  simp [threeColumns, volume₃]
  have hneg (x : F₂) : -x = x := by
    exact (eq_neg_of_add_eq_zero_left (add_self_F₂ x)).symm
  simp only [sub_eq_add_neg, hneg]

theorem toMatrix_mul_threeColumns (D : Block₃ ≃ₗ[F₂] Block₃) (a b c : Block₃) :
    LinearMap.toMatrix' D.toLinearMap * threeColumns a b c =
      threeColumns (D a) (D b) (D c) := by
  ext i j
  fin_cases j
  · simpa [threeColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (LinearMap.toMatrix'_mulVec D.toLinearMap a) i
  · simpa [threeColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (LinearMap.toMatrix'_mulVec D.toLinearMap b) i
  · simpa [threeColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (LinearMap.toMatrix'_mulVec D.toLinearMap c) i

theorem nonzero_F₂_eq_one (a : F₂) (ha : a ≠ 0) : a = 1 := by
  apply ZMod.val_injective
  rw [ZMod.val_one]
  have hpos : 0 < a.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).2 ha)
  have hlt : a.val < 2 := ZMod.val_lt a
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hpos

/-- Every invertible binary three-dimensional linear map preserves the volume form.
Over `F₂` its determinant is the unique nonzero scalar. -/
theorem volume₃_linearEquiv_invariant :
    ∀ D : Block₃ ≃ₗ[F₂] Block₃, ∀ a b c : Block₃,
      volume₃ (D a) (D b) (D c) = volume₃ a b c := by
  intro D a b c
  have hdet : (LinearMap.toMatrix' D.toLinearMap).det = 1 := by
    apply nonzero_F₂_eq_one
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' D).ne_zero
  rw [← det_threeColumns, ← toMatrix_mul_threeColumns, Matrix.det_mul, hdet,
    one_mul, det_threeColumns]

/-- The evident wreath-product action on the `t` cubic blocks. -/
def blockTransform {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (y : Y t) : Y t := fun i => A i.1 (blockSlice y (π.symm i.1)) i.2

theorem blockSlice_blockTransform {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (y : Y t) (j : Fin t) :
    blockSlice (blockTransform A π y) j = A j (blockSlice y (π.symm j)) := by
  rfl

def blockTransformInv {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (y : Y t) : Y t := fun i =>
  (A (π i.1)).symm (blockSlice y (π i.1)) i.2

theorem blockSlice_blockTransformInv {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (y : Y t) (j : Fin t) :
    blockSlice (blockTransformInv A π y) j =
      (A (π j)).symm (blockSlice y (π j)) := by
  rfl

/-- The block formula is an actual linear equivalence, not merely a tensor-preserving
function. -/
def blockTransformLinearEquiv {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t)) :
    Y t ≃ₗ[F₂] Y t where
  toFun := blockTransform A π
  invFun := blockTransformInv A π
  left_inv y := by
    funext i
    rcases i with ⟨j, k⟩
    simp [blockTransformInv, blockSlice_blockTransform]
  right_inv y := by
    funext i
    rcases i with ⟨j, k⟩
    simp [blockTransform, blockSlice_blockTransformInv]
  map_add' a b := by
    funext i
    rcases i with ⟨j, k⟩
    simp [blockTransform]
  map_smul' r a := by
    funext i
    rcases i with ⟨j, k⟩
    simp [blockTransform]

theorem cubicTensor_blockTransform {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (a b c : Y t) :
    cubicTensor t (blockTransform A π a) (blockTransform A π b)
        (blockTransform A π c) = cubicTensor t a b c := by
  classical
  simp only [cubicTensor, volumeBlock_eq_volume₃, blockSlice_blockTransform,
    volume₃_linearEquiv_invariant]
  exact Equiv.sum_comp π.symm
    (fun j => volume₃ (blockSlice a j) (blockSlice b j) (blockSlice c j))

theorem cubicTensor_blockTransformLinearEquiv {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (a b c : Y t) :
    cubicTensor t (blockTransformLinearEquiv A π a)
        (blockTransformLinearEquiv A π b) (blockTransformLinearEquiv A π c) =
      cubicTensor t a b c :=
  cubicTensor_blockTransform A π a b c

/-- Matrix and linear-equivalence presentations of the binary three-dimensional
general linear group are equivalent. -/
noncomputable def blockLinearEquivGL :
    GL (Fin 3) F₂ ≃ (Block₃ ≃ₗ[F₂] Block₃) :=
  Matrix.GeneralLinearGroup.toLin.toEquiv.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F₂ Block₃).toEquiv

theorem card_block_linearEquiv :
    Nat.card (Block₃ ≃ₗ[F₂] Block₃) = 168 := by
  calc
    Nat.card (Block₃ ≃ₗ[F₂] Block₃) = Nat.card (GL (Fin 3) F₂) :=
      (Nat.card_congr blockLinearEquivGL).symm
    _ = 168 := card_GL_three_F₂

/-- Parameters for the explicit blockwise cubic-tensor stabilizers. -/
abbrev CubicBlockDatum (t : ℕ) :=
  ((Fin t → (Block₃ ≃ₗ[F₂] Block₃)) × Equiv.Perm (Fin t))

theorem card_cubicBlockDatum (t : ℕ) :
    Nat.card (CubicBlockDatum t) = 168 ^ t * Nat.factorial t := by
  rw [Nat.card_prod, Nat.card_fun, card_block_linearEquiv, Nat.card_fin,
    card_block_permutations]

section IntrinsicBlockRecovery

def blockEmbed (t : ℕ) (j : Fin t) (a : Block₃) : Y t := fun i =>
  if i.1 = j then a i.2 else 0

@[simp] theorem blockEmbed_add (t : ℕ) (j : Fin t) (a b : Block₃) :
    blockEmbed t j (a + b) = blockEmbed t j a + blockEmbed t j b := by
  funext i
  by_cases hi : i.1 = j <;> simp [blockEmbed, hi]

@[simp] theorem blockEmbed_smul (t : ℕ) (j : Fin t) (r : F₂) (a : Block₃) :
    blockEmbed t j (r • a) = r • blockEmbed t j a := by
  funext i
  simp [blockEmbed]

@[simp] theorem blockSlice_blockEmbed_same (t : ℕ) (j : Fin t) (a : Block₃) :
    blockSlice (blockEmbed t j a) j = a := by
  funext k
  simp [blockEmbed]

@[simp] theorem blockSlice_blockEmbed_of_ne (t : ℕ) {j k : Fin t} (h : k ≠ j)
    (a : Block₃) : blockSlice (blockEmbed t j a) k = 0 := by
  funext q
  simp [blockEmbed, h]

theorem volume₃_contraction_square_zero (a b c d e : Block₃) :
    volume₃ a b c * volume₃ a d e +
      volume₃ a b d * volume₃ a e c +
      volume₃ a b e * volume₃ a c d = 0 := by
  simp only [volume₃]
  ring_nf
  simp

theorem cubicTensor_blockEmbed_pair (t : ℕ) (a : Y t) (j : Fin t) (b c : Block₃) :
    cubicTensor t a (blockEmbed t j b) (blockEmbed t j c) =
      volume₃ (blockSlice a j) b c := by
  classical
  rw [cubicTensor, Finset.sum_eq_single j]
  · simp [volumeBlock_eq_volume₃, volume₃, blockEmbed]
  · intro k _ hkj
    simp [volumeBlock_eq_volume₃, volume₃, blockEmbed, hkj]
  · simp

theorem cubicTensor_blockEmbed_mixed (t : ℕ) (a : Y t) {j k : Fin t} (h : j ≠ k)
    (b c : Block₃) :
    cubicTensor t a (blockEmbed t j b) (blockEmbed t k c) = 0 := by
  classical
  rw [cubicTensor]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q = j
  · subst q
    simp [volumeBlock_eq_volume₃, volume₃, blockEmbed, h]
  · simp [volumeBlock_eq_volume₃, volume₃, blockEmbed, hq]

/-- The square of the two-form obtained by contracting the cubic tensor with `a`. -/
def contractionSquare (t : ℕ) (a b c d e : Y t) : F₂ :=
  cubicTensor t a b c * cubicTensor t a d e +
  cubicTensor t a b d * cubicTensor t a e c +
  cubicTensor t a b e * cubicTensor t a c d

def LowContraction (t : ℕ) (a : Y t) : Prop :=
  ∀ b c d e, contractionSquare t a b c d e = 0

def AtMostOneActiveBlock (t : ℕ) (a : Y t) : Prop :=
  ∀ j k : Fin t, j ≠ k → blockSlice a j = 0 ∨ blockSlice a k = 0

theorem volume₃_exists_pair_of_ne_zero (a : Block₃) (ha : a ≠ 0) :
    ∃ b c : Block₃, volume₃ a b c = 1 := by
  by_cases h0 : a 0 = 0
  · by_cases h1 : a 1 = 0
    · have h2 : a 2 ≠ 0 := by
        intro h2
        apply ha
        funext i
        fin_cases i <;> simp_all
      have h2' := nonzero_F₂_eq_one (a 2) h2
      refine ⟨unitFin 3 0, unitFin 3 1, ?_⟩
      simp [volume₃, unitFin, h0, h1, h2']
    · have h1' := nonzero_F₂_eq_one (a 1) h1
      refine ⟨unitFin 3 0, unitFin 3 2, ?_⟩
      simp [volume₃, unitFin, h0, h1']
  · have h0' := nonzero_F₂_eq_one (a 0) h0
    refine ⟨unitFin 3 1, unitFin 3 2, ?_⟩
    simp [volume₃, unitFin, h0']

theorem cubicTensor_eq_single_block (t : ℕ) (a b c : Y t) (j : Fin t)
    (hother : ∀ k : Fin t, k ≠ j → blockSlice a k = 0) :
    cubicTensor t a b c =
      volume₃ (blockSlice a j) (blockSlice b j) (blockSlice c j) := by
  classical
  rw [cubicTensor, Finset.sum_eq_single j]
  · rfl
  · intro k _ hkj
    rw [volumeBlock_eq_volume₃, hother k hkj]
    simp [volume₃]
  · simp

theorem lowContraction_of_atMostOneActiveBlock {t : ℕ} {a : Y t}
    (ha : AtMostOneActiveBlock t a) : LowContraction t a := by
  intro b c d e
  by_cases haz : a = 0
  · subst a
    simp [contractionSquare, cubicTensor, volumeBlock]
  · have hex : ∃ j : Fin t, blockSlice a j ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      apply haz
      funext i
      rcases i with ⟨j, k⟩
      have hj := congrFun (h j) k
      simpa using hj
    obtain ⟨j, hj⟩ := hex
    have hother : ∀ k : Fin t, k ≠ j → blockSlice a k = 0 := by
      intro k hkj
      rcases ha j k hkj.symm with hzero | hzero
      · exact (hj hzero).elim
      · exact hzero
    simp only [contractionSquare, cubicTensor_eq_single_block t a b c j hother,
      cubicTensor_eq_single_block t a d e j hother,
      cubicTensor_eq_single_block t a b d j hother,
      cubicTensor_eq_single_block t a e c j hother,
      cubicTensor_eq_single_block t a b e j hother,
      cubicTensor_eq_single_block t a c d j hother]
    exact volume₃_contraction_square_zero (blockSlice a j) (blockSlice b j)
      (blockSlice c j) (blockSlice d j) (blockSlice e j)

theorem atMostOneActiveBlock_of_lowContraction {t : ℕ} {a : Y t}
    (ha : LowContraction t a) : AtMostOneActiveBlock t a := by
  intro j k hjk
  by_contra hboth
  simp only [not_or] at hboth
  obtain ⟨b, c, hbc⟩ := volume₃_exists_pair_of_ne_zero (blockSlice a j) hboth.1
  obtain ⟨d, e, hde⟩ := volume₃_exists_pair_of_ne_zero (blockSlice a k) hboth.2
  have hs := ha (blockEmbed t j b) (blockEmbed t j c)
    (blockEmbed t k d) (blockEmbed t k e)
  rw [contractionSquare,
    cubicTensor_blockEmbed_pair t a j b c,
    cubicTensor_blockEmbed_pair t a k d e,
    cubicTensor_blockEmbed_mixed t a hjk b d,
    cubicTensor_blockEmbed_mixed t a hjk b e,
    cubicTensor_blockEmbed_mixed t a hjk.symm e c,
    cubicTensor_blockEmbed_mixed t a hjk c d,
    hbc, hde] at hs
  norm_num at hs

theorem lowContraction_iff_atMostOneActiveBlock (t : ℕ) (a : Y t) :
    LowContraction t a ↔ AtMostOneActiveBlock t a :=
  ⟨atMostOneActiveBlock_of_lowContraction,
    lowContraction_of_atMostOneActiveBlock⟩

theorem lowContraction_preserved_by_tensor_equiv {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (a : Y t) : LowContraction t (D a) ↔ LowContraction t a := by
  constructor
  · intro h b c d e
    have hs := h (D b) (D c) (D d) (D e)
    simpa only [contractionSquare, hD] using hs
  · intro h b c d e
    obtain ⟨b', rfl⟩ := D.surjective b
    obtain ⟨c', rfl⟩ := D.surjective c
    obtain ⟨d', rfl⟩ := D.surjective d
    obtain ⟨e', rfl⟩ := D.surjective e
    simpa only [contractionSquare, hD] using h b' c' d' e'

theorem atMostOneActiveBlock_preserved_by_tensor_equiv {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (a : Y t) :
    AtMostOneActiveBlock t (D a) ↔ AtMostOneActiveBlock t a := by
  rw [← lowContraction_iff_atMostOneActiveBlock,
    ← lowContraction_iff_atMostOneActiveBlock]
  exact lowContraction_preserved_by_tensor_equiv D hD a

def SupportedInBlock (t : ℕ) (a : Y t) (j : Fin t) : Prop :=
  ∀ k : Fin t, k ≠ j → blockSlice a k = 0

theorem supportedInBlock_blockEmbed (t : ℕ) (j : Fin t) (a : Block₃) :
    SupportedInBlock t (blockEmbed t j a) j := by
  intro k hkj
  exact blockSlice_blockEmbed_of_ne t hkj a

theorem supportedInBlock_zero (t : ℕ) (j : Fin t) :
    SupportedInBlock t (0 : Y t) j := by
  intro k _
  funext q
  rfl

theorem SupportedInBlock.add {t : ℕ} {a b : Y t} {j : Fin t}
    (ha : SupportedInBlock t a j) (hb : SupportedInBlock t b j) :
    SupportedInBlock t (a + b) j := by
  intro k hkj
  simp [ha k hkj, hb k hkj]

theorem SupportedInBlock.smul {t : ℕ} {a : Y t} {j : Fin t}
    (ha : SupportedInBlock t a j) (r : F₂) :
    SupportedInBlock t (r • a) j := by
  intro k hkj
  simp [ha k hkj]

theorem exists_supportedInBlock_of_ne_zero_atMostOne {t : ℕ} {a : Y t}
    (ha0 : a ≠ 0) (ha : AtMostOneActiveBlock t a) :
    ∃ j : Fin t, SupportedInBlock t a j := by
  have hex : ∃ j : Fin t, blockSlice a j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply ha0
    funext i
    rcases i with ⟨j, k⟩
    simpa using congrFun (h j) k
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_⟩
  intro k hkj
  rcases ha j k hkj.symm with hzero | hzero
  · exact (hj hzero).elim
  · exact hzero

theorem blockSlice_ne_zero_of_supported_ne_zero {t : ℕ} {a : Y t} {j : Fin t}
    (ha : SupportedInBlock t a j) (ha0 : a ≠ 0) : blockSlice a j ≠ 0 := by
  intro hj
  apply ha0
  funext i
  rcases i with ⟨k, q⟩
  by_cases hkj : k = j
  · subst k
    simpa using congrFun hj q
  · simpa using congrFun (ha k hkj) q

theorem common_support_of_sum_atMostOne {t : ℕ} {a b : Y t}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : AtMostOneActiveBlock t a) (hb : AtMostOneActiveBlock t b)
    (hab : AtMostOneActiveBlock t (a + b)) :
    ∃ j : Fin t, SupportedInBlock t a j ∧ SupportedInBlock t b j := by
  obtain ⟨j, haj⟩ := exists_supportedInBlock_of_ne_zero_atMostOne ha0 ha
  obtain ⟨k, hbk⟩ := exists_supportedInBlock_of_ne_zero_atMostOne hb0 hb
  have haj0 := blockSlice_ne_zero_of_supported_ne_zero haj ha0
  have hbk0 := blockSlice_ne_zero_of_supported_ne_zero hbk hb0
  by_cases hjk : j = k
  · subst k
    exact ⟨j, haj, hbk⟩
  · have hbj : blockSlice b j = 0 := hbk j hjk
    have hak : blockSlice a k = 0 := haj k (fun h => hjk h.symm)
    have hjnz : blockSlice (a + b) j ≠ 0 := by simp [haj0, hbj]
    have hknz : blockSlice (a + b) k ≠ 0 := by simp [hbk0, hak]
    rcases hab j k hjk with hz | hz
    · exact (hjnz hz).elim
    · exact (hknz hz).elim

theorem atMostOneActiveBlock_of_supportedInBlock {t : ℕ} {a : Y t} {j : Fin t}
    (ha : SupportedInBlock t a j) : AtMostOneActiveBlock t a := by
  intro k l hkl
  by_cases hkj : k = j
  · right
    apply ha l
    intro hlj
    apply hkl
    exact hkj.trans hlj.symm
  · exact Or.inl (ha k hkj)

theorem blockEmbed_ne_zero {t : ℕ} (j : Fin t) {a : Block₃} (ha : a ≠ 0) :
    blockEmbed t j a ≠ 0 := by
  intro h
  apply ha
  rw [← blockSlice_blockEmbed_same t j a, h]
  funext k
  rfl

theorem blockEmbed_decompose (t : ℕ) (j : Fin t) (a : Block₃) :
    blockEmbed t j a =
      a 0 • blockEmbed t j (unitFin 3 0) +
      a 1 • blockEmbed t j (unitFin 3 1) +
      a 2 • blockEmbed t j (unitFin 3 2) := by
  funext i
  rcases i with ⟨k, q⟩
  by_cases hkj : k = j
  · subst k
    fin_cases q <;> simp [blockEmbed, unitFin]
  · simp [blockEmbed, unitFin, hkj]

theorem unitFin_three_ne_zero (q : Fin 3) : unitFin 3 q ≠ (0 : Block₃) := by
  intro h
  have := congrFun h q
  simp [unitFin] at this

/-- Every tensor-preserving linear equivalence maps each coordinate three-block
into a single coordinate three-block. This is the substantive converse to the
explicit wreath-product construction. -/
theorem tensorEquiv_maps_block {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (j : Fin t) :
    ∃ k : Fin t, ∀ a : Block₃,
      SupportedInBlock t (D (blockEmbed t j a)) k := by
  let e0 := blockEmbed t j (unitFin 3 0)
  let e1 := blockEmbed t j (unitFin 3 1)
  let e2 := blockEmbed t j (unitFin 3 2)
  have he0 : e0 ≠ 0 := blockEmbed_ne_zero j (unitFin_three_ne_zero 0)
  have he1 : e1 ≠ 0 := blockEmbed_ne_zero j (unitFin_three_ne_zero 1)
  have he2 : e2 ≠ 0 := blockEmbed_ne_zero j (unitFin_three_ne_zero 2)
  have hDe0 : D e0 ≠ 0 := by
    intro h
    apply he0
    apply D.injective
    simpa using h
  have hDe1 : D e1 ≠ 0 := by
    intro h
    apply he1
    apply D.injective
    simpa using h
  have hDe2 : D e2 ≠ 0 := by
    intro h
    apply he2
    apply D.injective
    simpa using h
  have hlow (q : Fin 3) : AtMostOneActiveBlock t
      (D (blockEmbed t j (unitFin 3 q))) := by
    rw [atMostOneActiveBlock_preserved_by_tensor_equiv D hD]
    exact atMostOneActiveBlock_of_supportedInBlock
      (supportedInBlock_blockEmbed t j (unitFin 3 q))
  have hlow01 : AtMostOneActiveBlock t (D e0 + D e1) := by
    rw [← D.map_add, atMostOneActiveBlock_preserved_by_tensor_equiv D hD]
    exact atMostOneActiveBlock_of_supportedInBlock
      ((supportedInBlock_blockEmbed t j (unitFin 3 0)).add
        (supportedInBlock_blockEmbed t j (unitFin 3 1)))
  have hlow02 : AtMostOneActiveBlock t (D e0 + D e2) := by
    rw [← D.map_add, atMostOneActiveBlock_preserved_by_tensor_equiv D hD]
    exact atMostOneActiveBlock_of_supportedInBlock
      ((supportedInBlock_blockEmbed t j (unitFin 3 0)).add
        (supportedInBlock_blockEmbed t j (unitFin 3 2)))
  obtain ⟨k, hk0, hk1⟩ := common_support_of_sum_atMostOne
    hDe0 hDe1 (hlow 0) (hlow 1) hlow01
  obtain ⟨l, hl0, hl2⟩ := common_support_of_sum_atMostOne
    hDe0 hDe2 (hlow 0) (hlow 2) hlow02
  have hkl : k = l := by
    by_contra hne
    have hz := hl0 k hne
    exact (blockSlice_ne_zero_of_supported_ne_zero hk0 hDe0) hz
  subst l
  refine ⟨k, ?_⟩
  intro a
  rw [blockEmbed_decompose t j a, map_add, map_add, map_smul, map_smul, map_smul]
  exact ((hk0.smul (a 0)).add (hk1.smul (a 1))).add (hl2.smul (a 2))

noncomputable def tensorTarget {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (j : Fin t) : Fin t :=
  Classical.choose (tensorEquiv_maps_block D hD j)

theorem tensorTarget_support {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (j : Fin t) (a : Block₃) :
    SupportedInBlock t (D (blockEmbed t j a)) (tensorTarget D hD j) :=
  Classical.choose_spec (tensorEquiv_maps_block D hD j) a

theorem sum_blockEmbed_slices (t : ℕ) (y : Y t) :
    (∑ j : Fin t, blockEmbed t j (blockSlice y j)) = y := by
  classical
  funext i
  rcases i with ⟨j, k⟩
  simp [blockEmbed]

theorem blockSlice_sum {t : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Y t)
    (j : Fin t) :
    blockSlice (∑ i ∈ s, f i) j = ∑ i ∈ s, blockSlice (f i) j := by
  funext k
  simp

theorem tensorTarget_surjective {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c) :
    Function.Surjective (tensorTarget D hD) := by
  intro k
  by_contra hk
  simp only [not_exists] at hk
  let v : Y t := blockEmbed t k (unitFin 3 0)
  let y : Y t := D.symm v
  have hdecomp := congrArg D (sum_blockEmbed_slices t y)
  have himage : D y = v := by simp [y, v]
  have hslice : blockSlice (D y) k = 0 := by
    rw [← hdecomp]
    simp only [map_sum]
    rw [blockSlice_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact tensorTarget_support D hD j (blockSlice y j) k (fun h => hk j h.symm)
  rw [himage, blockSlice_blockEmbed_same] at hslice
  exact unitFin_three_ne_zero 0 hslice

noncomputable def tensorBlockPerm {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c) :
    Equiv.Perm (Fin t) :=
  Equiv.ofBijective (tensorTarget D hD)
    (tensorTarget_surjective D hD).bijective_of_finite

@[simp] theorem tensorBlockPerm_apply {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (j : Fin t) : tensorBlockPerm D hD j = tensorTarget D hD j := rfl

theorem eq_of_supportedInBlock_of_slice_eq {t : ℕ} {a b : Y t} {j : Fin t}
    (ha : SupportedInBlock t a j) (hb : SupportedInBlock t b j)
    (h : blockSlice a j = blockSlice b j) : a = b := by
  funext i
  rcases i with ⟨k, q⟩
  by_cases hkj : k = j
  · subst k
    exact congrFun h q
  · calc
      a (k, q) = 0 := by simpa using congrFun (ha k hkj) q
      _ = b (k, q) := by simpa using (congrFun (hb k hkj) q).symm

noncomputable def inducedBlockLinearMap {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (k : Fin t) : Block₃ →ₗ[F₂] Block₃ where
  toFun a := blockSlice
    (D (blockEmbed t ((tensorBlockPerm D hD).symm k) a)) k
  map_add' a b := by simp
  map_smul' r a := by simp

theorem inducedBlockLinearMap_injective {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (k : Fin t) : Function.Injective (inducedBlockLinearMap D hD k) := by
  intro a b hab
  let j := (tensorBlockPerm D hD).symm k
  have hj : tensorTarget D hD j = k := by
    change tensorBlockPerm D hD j = k
    simp [j]
  have ha := tensorTarget_support D hD j a
  have hb := tensorTarget_support D hD j b
  rw [hj] at ha hb
  have himage : D (blockEmbed t j a) = D (blockEmbed t j b) :=
    eq_of_supportedInBlock_of_slice_eq ha hb hab
  have hembed := D.injective himage
  have hslice := congrArg (fun y => blockSlice y j) hembed
  simpa using hslice

noncomputable def inducedBlockLinearEquiv {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (k : Fin t) : Block₃ ≃ₗ[F₂] Block₃ :=
  LinearEquiv.ofBijective (inducedBlockLinearMap D hD k)
    ⟨inducedBlockLinearMap_injective D hD k,
      Function.Injective.surjective_of_finite (Equiv.refl Block₃)
        (inducedBlockLinearMap_injective D hD k)⟩

theorem blockSlice_univ_sum {t : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Y t) (j : Fin t) :
    blockSlice (∑ i, f i) j = ∑ i, blockSlice (f i) j := by
  funext k
  simp

theorem blockSlice_tensorEquiv_eq_induced {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c)
    (y : Y t) (k : Fin t) :
    blockSlice (D y) k = inducedBlockLinearEquiv D hD k
      (blockSlice y ((tensorBlockPerm D hD).symm k)) := by
  classical
  have hdecomp := congrArg D (sum_blockEmbed_slices t y)
  rw [map_sum] at hdecomp
  have hs := congrArg (fun z => blockSlice z k) hdecomp
  rw [blockSlice_univ_sum] at hs
  rw [← hs, Finset.sum_eq_single ((tensorBlockPerm D hD).symm k)]
  · rfl
  · intro j _ hj
    have htarget : tensorTarget D hD j ≠ k := by
      intro heq
      have hp : tensorBlockPerm D hD j =
          tensorBlockPerm D hD ((tensorBlockPerm D hD).symm k) := by simpa using heq
      exact hj ((tensorBlockPerm D hD).injective hp)
    exact tensorTarget_support D hD j (blockSlice y j) k (fun h => htarget h.symm)
  · simp

/-- Complete classification of the cubic-tensor stabilizer: every stabilizer is
the explicit blockwise `GL(3,2)` action followed by a block permutation. -/
theorem cubicTensor_stabilizer_classification {t : ℕ}
    (D : Y t ≃ₗ[F₂] Y t)
    (hD : ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c) :
    D = blockTransformLinearEquiv (inducedBlockLinearEquiv D hD)
      (tensorBlockPerm D hD) := by
  ext y i
  rcases i with ⟨k, q⟩
  exact congrFun (blockSlice_tensorEquiv_eq_induced D hD y k) q

theorem blockTransform_blockEmbed_supported {t : ℕ}
    (A : ∀ j : Fin t, Block₃ ≃ₗ[F₂] Block₃) (π : Equiv.Perm (Fin t))
    (j : Fin t) (a : Block₃) :
    SupportedInBlock t
      (blockTransformLinearEquiv A π (blockEmbed t j a)) (π j) := by
  intro k hkj
  change blockSlice (blockTransform A π (blockEmbed t j a)) k = 0
  rw [blockSlice_blockTransform]
  have hsource : π.symm k ≠ j := by
    intro h
    apply hkj
    simpa using congrArg π h
  rw [blockSlice_blockEmbed_of_ne t hsource]
  simp

theorem supportedInBlock_unique {t : ℕ} {a : Y t} {j k : Fin t}
    (hj : SupportedInBlock t a j) (hk : SupportedInBlock t a k) (ha : a ≠ 0) :
    j = k := by
  by_contra hjk
  have hzero := hk j hjk
  exact (blockSlice_ne_zero_of_supported_ne_zero hj ha) hzero

def cubicBlockDatumAction {t : ℕ} (p : CubicBlockDatum t) : Y t ≃ₗ[F₂] Y t :=
  blockTransformLinearEquiv p.1 p.2

theorem cubicBlockDatumAction_injective (t : ℕ) :
    Function.Injective (cubicBlockDatumAction : CubicBlockDatum t → Y t ≃ₗ[F₂] Y t) := by
  rintro ⟨A, π⟩ ⟨B, ρ⟩ haction
  have hperm : π = ρ := by
    ext j
    let e := blockEmbed t j (unitFin 3 0)
    let v := blockTransformLinearEquiv A π e
    have hv : v ≠ 0 := by
      intro hz
      have : e = 0 := (blockTransformLinearEquiv A π).injective (by simpa [v] using hz)
      exact blockEmbed_ne_zero j (unitFin_three_ne_zero 0) this
    have hvEq : v = blockTransformLinearEquiv B ρ e := by
      simpa only [v, cubicBlockDatumAction] using DFunLike.congr_fun haction e
    have hp := blockTransform_blockEmbed_supported A π j (unitFin 3 0)
    have hr := blockTransform_blockEmbed_supported B ρ j (unitFin 3 0)
    rw [← hvEq] at hr
    exact congrArg Fin.val (supportedInBlock_unique hp hr hv)
  subst ρ
  congr
  funext k
  apply LinearEquiv.ext
  intro a
  funext q
  have hfun := DFunLike.congr_fun haction
    (blockEmbed t (π.symm k) a)
  have hs := congrArg (fun y => blockSlice y k) hfun
  change blockSlice (blockTransform A π (blockEmbed t (π.symm k) a)) k =
    blockSlice (blockTransform B π (blockEmbed t (π.symm k) a)) k at hs
  rw [blockSlice_blockTransform, blockSlice_blockTransform,
    blockSlice_blockEmbed_same] at hs
  exact congrFun hs q

abbrev CubicTensorStabilizer (t : ℕ) :=
  {D : Y t ≃ₗ[F₂] Y t //
    ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c}

noncomputable def cubicTensorStabilizerEquivDatum (t : ℕ) :
    CubicTensorStabilizer t ≃ CubicBlockDatum t where
  toFun D := (inducedBlockLinearEquiv D.1 D.2, tensorBlockPerm D.1 D.2)
  invFun p := ⟨cubicBlockDatumAction p,
    cubicTensor_blockTransformLinearEquiv p.1 p.2⟩
  left_inv D := by
    apply Subtype.ext
    exact (cubicTensor_stabilizer_classification D.1 D.2).symm
  right_inv p := by
    apply cubicBlockDatumAction_injective t
    exact (cubicTensor_stabilizer_classification (cubicBlockDatumAction p)
      (cubicTensor_blockTransformLinearEquiv p.1 p.2)).symm

theorem card_cubicTensorStabilizer (t : ℕ) :
    Nat.card (CubicTensorStabilizer t) = 168 ^ t * Nat.factorial t := by
  rw [Nat.card_congr (cubicTensorStabilizerEquivDatum t), card_cubicBlockDatum]

end IntrinsicBlockRecovery

end ExplicitCubicTensorSymmetries

end CubicBentAutomorphisms
end


/-! ## Affine evaluation-code reconstruction -/

section
namespace AffineEvaluationCodes

abbrev F₂ := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

def restriction (S : Set V) : (V →ᵃ[F₂] F₂) →ₗ[F₂] (S → F₂) where
  toFun f x := f x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def code (S : Set V) : Submodule F₂ (S → F₂) :=
  LinearMap.range (restriction S)

@[simp] theorem mem_code (S : Set V) (w : S → F₂) :
    w ∈ code S ↔ ∃ f : V →ᵃ[F₂] F₂, ∀ x : S, f x.val = w x := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨f, fun x => congrFun hf x⟩
  · rintro ⟨f,hf⟩
    exact ⟨f, funext hf⟩

def pullback {S : Set V} (π : Equiv.Perm S) (w : S → F₂) : S → F₂ := w ∘ π

def codeAut (S : Set V) : Subgroup (Equiv.Perm S) where
  carrier := {π | ∀ w, w ∈ code S ↔ pullback π w ∈ code S}
  one_mem' := by intro w; rfl
  mul_mem' := by
    intro π ρ hπ hρ w
    exact (hπ w).trans (hρ (pullback π w))
  inv_mem' := by
    intro π hπ w
    change w ∈ code S ↔ pullback π.symm w ∈ code S
    have h := hπ (pullback π.symm w)
    simpa only [pullback, Function.comp_def, Equiv.symm_apply_apply] using h.symm

@[simp] theorem mem_codeAut (S : Set V) (π : Equiv.Perm S) :
    π ∈ codeAut S ↔ ∀ w, w ∈ code S ↔ pullback π w ∈ code S := Iff.rfl

def affineSetStabilizer (S : Set V) : Subgroup (V ≃ᵃ[F₂] V) where
  carrier := {e | ∀ x, x ∈ S ↔ e x ∈ S}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro e f he hf x
    exact (hf x).trans (he (f x))
  inv_mem' := by
    intro e he x
    change x ∈ S ↔ e.symm x ∈ S
    have h := he (e.symm x)
    simpa using h.symm

def restrictPerm {S : Set V} (e : affineSetStabilizer S) : Equiv.Perm S where
  toFun x := ⟨e.val x.val, (e.property x.val).mp x.property⟩
  invFun x := ⟨e.val.symm x.val, (e.property (e.val.symm x.val)).mpr (by simpa using x.property)⟩
  left_inv x := by apply Subtype.ext; exact e.val.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.val.apply_symm_apply x.val

@[simp] theorem restrictPerm_apply {S : Set V} (e : affineSetStabilizer S) (x : S) :
    (restrictPerm e x).val = e.val x.val := rfl

theorem restrictPerm_code {S : Set V} (e : affineSetStabilizer S) :
    restrictPerm e ∈ codeAut S := by
  intro w
  constructor
  · intro hw
    obtain ⟨f,hf⟩ := (mem_code S w).mp hw
    apply (mem_code S _).mpr
    exact ⟨f.comp e.val.toAffineMap, fun x => hf (restrictPerm e x)⟩
  · intro hw
    obtain ⟨f,hf⟩ := (mem_code S _).mp hw
    apply (mem_code S _).mpr
    refine ⟨f.comp e.val.symm.toAffineMap, ?_⟩
    intro x
    have h := hf ((restrictPerm e).symm x)
    simpa [pullback, restrictPerm] using h

def restrictHom (S : Set V) : affineSetStabilizer S →* codeAut S where
  toFun e := ⟨restrictPerm e, restrictPerm_code e⟩
  map_one' := by apply Subtype.ext; apply Equiv.ext; intro x; rfl
  map_mul' e f := by apply Subtype.ext; apply Equiv.ext; intro x; rfl

theorem restrictHom_injective (S : Set V) (hS : affineSpan F₂ S = ⊤) :
    Function.Injective (restrictHom S) := by
  intro e f hef
  apply Subtype.ext
  apply AffineEquiv.ext_on hS
  intro x hx
  have h := congrArg (fun g : codeAut S => (g.val ⟨x,hx⟩).val) hef
  exact h

theorem exists_affine_extension [FiniteDimensional F₂ V] (S : Set V)
    (π : codeAut S) :
    ∃ A : V →ᵃ[F₂] V, ∀ x : S, A x.val = (π.val x).val := by
  classical
  let b := Module.finBasis F₂ V
  have hc (i : Fin (Module.finrank F₂ V)) :
      pullback π.val (restriction S (b.coord i).toAffineMap) ∈ code S := by
    apply (π.property _).mp
    exact ⟨(b.coord i).toAffineMap, rfl⟩
  have hex (i : Fin (Module.finrank F₂ V)) :
      ∃ f : V →ᵃ[F₂] F₂, ∀ x : S, f x.val = b.coord i (π.val x).val := by
    exact (mem_code S _).mp (hc i)
  choose f hf using hex
  refine ⟨b.equivFun.symm.toLinearMap.toAffineMap.comp (AffineMap.pi f), ?_⟩
  intro x
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm (fun i => f i x.val)) = b.equivFun (π.val x).val
  rw [b.equivFun.apply_symm_apply]
  funext i
  exact hf i x

theorem restrictHom_surjective [FiniteDimensional F₂ V]
    (S : Set V) (hS : affineSpan F₂ S = ⊤) :
    Function.Surjective (restrictHom S) := by
  classical
  intro π
  obtain ⟨A,hA⟩ := exists_affine_extension S π
  obtain ⟨B,hB⟩ := exists_affine_extension S π⁻¹
  have hBA : B.comp A = AffineMap.id F₂ V := by
    apply AffineMap.ext_on hS
    intro x hx
    change B (A x) = x
    rw [hA ⟨x,hx⟩, hB (π.val ⟨x,hx⟩)]
    exact congrArg Subtype.val (π.val.symm_apply_apply ⟨x,hx⟩)
  have hAB : A.comp B = AffineMap.id F₂ V := by
    apply AffineMap.ext_on hS
    intro x hx
    change A (B x) = x
    rw [hB ⟨x,hx⟩, hA ((π⁻¹).val ⟨x,hx⟩)]
    exact congrArg Subtype.val (π.val.apply_symm_apply ⟨x,hx⟩)
  have hleft : Function.LeftInverse B A := fun x => congrArg (fun f : V →ᵃ[F₂] V => f x) hBA
  have hright : Function.RightInverse B A := fun x => congrArg (fun f : V →ᵃ[F₂] V => f x) hAB
  let e : V ≃ᵃ[F₂] V := AffineEquiv.ofBijective (φ := A) ⟨hleft.injective, hright.surjective⟩
  have he : e ∈ affineSetStabilizer S := by
    intro x
    constructor
    · intro hx
      change A x ∈ S
      rw [hA ⟨x,hx⟩]
      exact (π.val ⟨x,hx⟩).property
    · intro hx
      change A x ∈ S at hx
      have hb := hB ⟨A x,hx⟩
      rw [hleft x] at hb
      rw [hb]
      exact ((π⁻¹).val ⟨A x,hx⟩).property
  refine ⟨⟨e,he⟩, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact hA x

/-- Every code coordinate automorphism extends uniquely to an affine symmetry
of the spanning point set, with the same group multiplication. -/
noncomputable def affineStabilizerEquivCodeAut [FiniteDimensional F₂ V]
    (S : Set V) (hS : affineSpan F₂ S = ⊤) :
    affineSetStabilizer S ≃* codeAut S :=
  MulEquiv.ofBijective (restrictHom S)
    ⟨restrictHom_injective S hS, restrictHom_surjective S hS⟩

noncomputable def codeAutEquivAffineStabilizer [FiniteDimensional F₂ V]
    (S : Set V) (hS : affineSpan F₂ S = ⊤) :
    codeAut S ≃* affineSetStabilizer S :=
  (affineStabilizerEquivCodeAut S hS).symm


end AffineEvaluationCodes
end


/-! ## Dual-graph support designs -/

section
namespace DualSupportDesign
abbrev F₂ := ZMod 2

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

def affineWord (S : Set W) (l : Module.Dual F₂ W) (c : F₂) : S → F₂ :=
  fun x => l x + c

def blockWords (S : Set W) (g : Module.Dual F₂ W → F₂) : Set (S → F₂) :=
  {w | ∃ l : Module.Dual F₂ W, l ≠ 0 ∧ w = affineWord S l (g l)}

theorem block_mem_span (S : Set W) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (l : Module.Dual F₂ W) :
    affineWord S l (g l) ∈ Submodule.span F₂ (blockWords S g) := by
  by_cases hl : l = 0
  · subst l
    rw [hg]
    have he : affineWord S 0 0 = 0 := by ext x; simp [affineWord]
    rw [he]
    exact (Submodule.span F₂ (blockWords S g)).zero_mem
  · exact Submodule.subset_span ⟨l,hl,rfl⟩

theorem binary_defect (a b c : F₂) (h : c ≠ a+b) : a+b+c = 1 := by
  exact (by decide : ∀ a b c : F₂, c ≠ a+b → a+b+c=1) a b c h

theorem one_mem_span (S : Set W) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (l m : Module.Dual F₂ W) (h : g (l+m) ≠ g l + g m) :
    (fun _ : S => (1:F₂)) ∈ Submodule.span F₂ (blockWords S g) := by
  have hh := (Submodule.span F₂ (blockWords S g)).add_mem
    ((Submodule.span F₂ (blockWords S g)).add_mem
      (block_mem_span S g hg l) (block_mem_span S g hg m))
    (block_mem_span S g hg (l+m))
  have he : affineWord S l (g l) + affineWord S m (g m) +
      affineWord S (l+m) (g (l+m)) = fun _ : S => (1:F₂) := by
    funext x
    change (l x + g l) + (m x + g m) + (l x + m x + g (l+m)) = 1
    calc
      _ = (l x+l x)+(m x+m x)+(g l+g m+g (l+m)) := by ring
      _ = 1 := by simp [CubicBentAutomorphisms.add_self_F₂,
        binary_defect _ _ _ h]
  rwa [he] at hh

theorem affineWord_mem_span (S : Set W) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (h : ∃ l m, g (l+m) ≠ g l + g m)
    (l : Module.Dual F₂ W) (c : F₂) :
    affineWord S l c ∈ Submodule.span F₂ (blockWords S g) := by
  obtain ⟨a,b,hab⟩ := h
  have hc := (Submodule.span F₂ (blockWords S g)).smul_mem (g l+c)
    (one_mem_span S g hg a b hab)
  have hh := (Submodule.span F₂ (blockWords S g)).add_mem
    (block_mem_span S g hg l) hc
  convert hh using 1
  funext x
  change l x+c = (l x+g l)+(g l+c)*1
  rw [mul_one]
  have hzero := CubicBentAutomorphisms.add_self_F₂ (g l)
  calc
    _ = l x+c+0 := by rw [add_zero]
    _ = _ := by rw [← hzero]; abel

def pullback {I : Type*} (π : Equiv.Perm I) : (I → F₂) →ₗ[F₂] (I → F₂) where
  toFun w := w ∘ π
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def wordAut {I : Type*} (B : Set (I → F₂)) : Subgroup (Equiv.Perm I) where
  carrier := {π | ∀ w, w ∈ B ↔ pullback π w ∈ B}
  one_mem' := by intro w; rfl
  mul_mem' := by
    intro π τ hπ hτ w
    exact (hπ w).trans (hτ (pullback π w))
  inv_mem' := by
    intro π hπ w
    have h := hπ (pullback π⁻¹ w)
    simpa [pullback, Function.comp_def] using h.symm

theorem pullback_span {I : Type*} (B : Set (I → F₂)) (π : Equiv.Perm I)
    (hπ : π ∈ wordAut B) (w : I → F₂) (hw : w ∈ Submodule.span F₂ B) :
    pullback π w ∈ Submodule.span F₂ B := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span ((hπ w).mp hw)
  | zero => simpa using (Submodule.span F₂ B).zero_mem
  | add a b ha hb iha ihb => simpa using (Submodule.span F₂ B).add_mem iha ihb
  | smul r a ha iha => simpa using (Submodule.span F₂ B).smul_mem r iha

theorem wordAut_le_spanAut {I : Type*} (B : Set (I → F₂)) :
    wordAut B ≤ wordAut (Submodule.span F₂ B : Set (I → F₂)) := by
  intro π hπ w
  constructor
  · exact pullback_span B π hπ w
  · intro hw
    have hh := pullback_span B π⁻¹ ((wordAut B).inv_mem hπ) (pullback π w) hw
    simpa [pullback, Function.comp_def] using hh

def wordSupport {I : Type*} (w : I → F₂) : Set I := {i | w i = 1}

theorem wordSupport_injective (I : Type*) :
    Function.Injective (wordSupport : (I → F₂) → Set I) := by
  intro u v h
  funext i
  have hh : u i = 1 ↔ v i = 1 := Set.ext_iff.mp h i
  have helper (a b : F₂) (hab : a=1 ↔ b=1) : a=b := by
    exact (by decide : ∀ a b : F₂, (a=1 ↔ b=1) → a=b) a b hab
  exact helper _ _ hh

theorem wordSupport_surjective (I : Type*) :
    Function.Surjective (wordSupport : (I → F₂) → Set I) := by
  classical
  intro T
  refine ⟨fun i => if i ∈ T then 1 else 0, ?_⟩
  ext i
  simp [wordSupport]

def designBlocks {I : Type*} (B : Set (I → F₂)) : Set (Set I) := wordSupport '' B

theorem support_mem_blocks_iff {I : Type*} (B : Set (I → F₂)) (w : I → F₂) :
    wordSupport w ∈ designBlocks B ↔ w ∈ B := by
  constructor
  · rintro ⟨v,hv,he⟩
    exact (wordSupport_injective I he) ▸ hv
  · intro hw
    exact ⟨w,hw,rfl⟩

def setDesignAut {I : Type*} (B : Set (Set I)) : Subgroup (Equiv.Perm I) where
  carrier := {π | ∀ T, T ∈ B ↔ π ⁻¹' T ∈ B}
  one_mem' := by intro T; rfl
  mul_mem' := by
    intro π τ hπ hτ T
    exact (hπ T).trans (hτ (π ⁻¹' T))
  inv_mem' := by
    intro π hπ T
    have hh := hπ (π.symm ⁻¹' T)
    simpa [Set.preimage_preimage, Function.comp_def] using hh.symm

/-- The function formulation has exactly the ordinary point-permutation
automorphism group of the actual family of design subsets. -/
theorem wordAut_eq_setDesignAut {I : Type*} (B : Set (I → F₂)) :
    wordAut B = setDesignAut (designBlocks B) := by
  apply Subgroup.ext
  intro π
  constructor
  · intro hπ T
    obtain ⟨w,rfl⟩ := wordSupport_surjective I T
    change wordSupport w ∈ designBlocks B ↔ wordSupport (pullback π w) ∈ designBlocks B
    simpa only [support_mem_blocks_iff] using hπ w
  · intro hπ w
    have hh := hπ (wordSupport w)
    change wordSupport w ∈ designBlocks B ↔ wordSupport (pullback π w) ∈ designBlocks B at hh
    simpa only [support_mem_blocks_iff] using hh

theorem affineWord_mem_code (S : Set W) (l : Module.Dual F₂ W) (c : F₂) :
    affineWord S l c ∈ AffineEvaluationCodes.code S := by
  apply (AffineEvaluationCodes.mem_code S _).mpr
  exact ⟨l.toAffineMap + AffineMap.const F₂ W c, fun _ => rfl⟩

theorem span_blocks_eq_code (S : Set W) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (h : ∃ l m, g (l+m) ≠ g l + g m) :
    Submodule.span F₂ (blockWords S g) = AffineEvaluationCodes.code S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨l,hl,rfl⟩
    exact affineWord_mem_code S l (g l)
  · intro w hw
    obtain ⟨f,hf⟩ := (AffineEvaluationCodes.mem_code S w).mp hw
    have he : w = affineWord S f.linear (f 0) := by
      funext x
      rw [← hf x]
      exact congrFun f.decomp x.val
    rw [he]
    exact affineWord_mem_span S g hg h _ _

theorem wordAut_le_codeAut (S : Set W) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (h : ∃ l m, g (l+m) ≠ g l + g m) :
    wordAut (blockWords S g) ≤ AffineEvaluationCodes.codeAut S := by
  have hh := wordAut_le_spanAut (blockWords S g)
  rw [span_blocks_eq_code S g hg h] at hh
  exact hh

theorem linear_comp_equiv_ne_zero (l : Module.Dual F₂ W) (hl : l ≠ 0)
    (e : W ≃ₗ[F₂] W) : l.comp e.toLinearMap ≠ 0 := by
  intro hz
  apply hl
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := e.surjective w
  exact congrArg (fun k : Module.Dual F₂ W => k v) hz

theorem restrict_preserves_blocks (S : Set W) (g : Module.Dual F₂ W → F₂)
    (e : AffineEvaluationCodes.affineSetStabilizer S)
    (hc : ∀ l : Module.Dual F₂ W,
      g (l.comp e.1.linear.toLinearMap) = g l + l (e.1 0))
    (w : S → F₂) (hw : w ∈ blockWords S g) :
    pullback (AffineEvaluationCodes.restrictPerm e) w ∈ blockWords S g := by
  obtain ⟨l,hl,rfl⟩ := hw
  refine ⟨l.comp e.1.linear.toLinearMap, linear_comp_equiv_ne_zero l hl e.1.linear, ?_⟩
  funext x
  change l (e.1 x.val) + g l = l (e.1.linear x.val) + g (l.comp e.1.linear.toLinearMap)
  rw [hc, CubicBentAutomorphisms.affine_apply_eq_linear_add,
    map_add]
  abel

theorem codeAut_eq_wordAut [FiniteDimensional F₂ W]
    (S : Set W) (hS : affineSpan F₂ S = ⊤) (g : Module.Dual F₂ W → F₂)
    (hg : g 0 = 0) (hn : ∃ l m, g (l+m) ≠ g l + g m)
    (hc : ∀ e : AffineEvaluationCodes.affineSetStabilizer S,
      ∀ l : Module.Dual F₂ W, g (l.comp e.1.linear.toLinearMap) = g l + l (e.1 0)) :
    AffineEvaluationCodes.codeAut S = wordAut (blockWords S g) := by
  apply le_antisymm
  · intro π hπ
    obtain ⟨e,he⟩ := AffineEvaluationCodes.restrictHom_surjective S hS ⟨π,hπ⟩
    have hp : AffineEvaluationCodes.restrictPerm e = π := congrArg Subtype.val he
    rw [← hp]
    intro w
    constructor
    · exact restrict_preserves_blocks S g e (hc e) w
    · intro hw
      have hh := restrict_preserves_blocks S g e⁻¹ (hc e⁻¹)
        (pullback (AffineEvaluationCodes.restrictPerm e) w) hw
      have heq : pullback (AffineEvaluationCodes.restrictPerm e⁻¹)
          (pullback (AffineEvaluationCodes.restrictPerm e) w) = w := by
        funext x
        change w ⟨e.1 (e.1.symm x.val), _⟩ = w x
        congr 1
        apply Subtype.ext
        exact e.1.apply_symm_apply x.val
      rwa [heq] at hh
  · exact wordAut_le_codeAut S g hg hn

end DualSupportDesign
end


/-! ## Quadratic affine isometries -/

section
open scoped BigOperators
open CubicBentAutomorphisms

namespace QuadraticAffineIsometries

def sign (x : F₂) : ℤ := if x = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := rfl
@[simp] theorem sign_one : sign 1 = -1 := by decide

theorem sign_add (x y : F₂) : sign (x + y) = sign x * sign y := by
  fin_cases x <;> fin_cases y <;> decide

theorem sign_sq (x : F₂) : sign x * sign x = 1 := by
  fin_cases x <;> decide

theorem sign_eq_one_iff (x : F₂) : sign x = 1 ↔ x = 0 := by
  fin_cases x <;> norm_num [sign]

section FiniteQuadratic

variable {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
variable (q : W → F₂) (B : LinearMap.BilinForm F₂ W)
variable (hq : ∀ x y, q (x + y) = q x + q y + B x y)
variable (hB : B.Nondegenerate)

include hq in
theorem polar_symmetric (x y : W) : B x y = B y x := by
  have h : q x + q y + B x y = q y + q x + B y x := by
    rw [← hq, ← hq, add_comm x y]
  rw [add_comm (q y) (q x)] at h
  exact add_left_cancel h

include hB in
theorem gauss_linear_zero {a : W} (ha : a ≠ 0) :
    (∑ x : W, sign (B a x)) = 0 := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, B a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact ha (hB.1 a hn)
  have hb1 : B a b = 1 := by
    have hf : ∀ r : F₂, r ≠ 0 → r = 1 := by decide
    exact hf _ hb
  have hs := Equiv.sum_comp (Equiv.addRight b) (fun x : W => sign (B a x))
  have hn : (∑ x : W, sign (B a (x + b))) = -(∑ x : W, sign (B a x)) := by
    simp [map_add, sign_add, hb1, Finset.sum_neg_distrib]
  change (∑ x : W, sign (B a (x + b))) = _ at hs
  rw [hn] at hs
  linarith

include hq hB

theorem gauss_square :
    (∑ x : W, sign (q x)) ^ 2 = Fintype.card W := by
  classical
  calc
    (∑ x : W, sign (q x)) ^ 2 =
        ∑ x : W, ∑ y : W, sign (q x) * sign (q y) := by
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ x : W, ∑ a : W, sign (q a) * sign (B x a) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Equiv.sum_comp (Equiv.addLeft x) (fun y : W => sign (q x) * sign (q y))]
      apply Finset.sum_congr rfl
      intro a _
      change sign (q x) * sign (q (x + a)) = _
      rw [hq, sign_add, sign_add]
      calc
        sign (q x) * (sign (q x) * sign (q a) * sign (B x a)) =
            (sign (q x) * sign (q x)) * sign (q a) * sign (B x a) := by ring
        _ = _ := by rw [sign_sq, one_mul]
    _ = ∑ a : W, sign (q a) * ∑ x : W, sign (B a x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [polar_symmetric q B hq x a]
    _ = Fintype.card W := by
      have hq0 : q (0 : W) = 0 := by
        have hh := hq 0 0
        simpa using hh
      rw [Finset.sum_eq_single (0 : W)]
      · simp [hq0]
      · intro a _ ha
        rw [gauss_linear_zero B hB ha, mul_zero]
      · simp

theorem gauss_ne_zero : (∑ x : W, sign (q x)) ≠ 0 := by
  intro hz
  have hs := gauss_square q B hq hB
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at hs
  have hc : (0 : ℤ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  linarith

omit hB in
theorem quadratic_zero : q (0 : W) = 0 := by
  have hh := hq 0 0
  simpa using hh

omit hB in
theorem quadratic_second (x y a : W) :
    q (x + y + a) + q (x + a) + q (y + a) + q a = B x y := by
  simp only [hq, map_add, LinearMap.add_apply]
  ring_nf
  simp

variable [FiniteDimensional F₂ W]

omit hB in
def linearDefect (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) : W →ₗ[F₂] F₂ where
  toFun x := q (M x) + q x
  map_add' x y := by
    rw [map_add, hq, hq, hM]
    have hh := add_self_F₂ (B x y)
    linear_combination hh
  map_smul' r x := by
    have hf : ∀ r : F₂, r = 0 ∨ r = 1 := by decide
    rcases hf r with rfl | rfl <;> simp [quadratic_zero q B hq]

noncomputable def liftTranslation (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) : W :=
  (B.toDual hB).symm ((linearDefect q B hq M hM).comp M.symm.toLinearMap)

theorem liftTranslation_pairing (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) (x : W) :
    B (M x) (liftTranslation q B hq hB M hM) = q (M x) + q x := by
  rw [polar_symmetric q B hq]
  simp [liftTranslation, linearDefect]

theorem liftTranslation_quadratic (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) (x : W) :
    q (M x + liftTranslation q B hq hB M hM) =
      q x + q (liftTranslation q B hq hB M hM) := by
  rw [hq, liftTranslation_pairing]
  have hh := add_self_F₂ (q (M x))
  linear_combination hh

theorem liftTranslation_isotropic (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) :
    q (liftTranslation q B hq hB M hM) = 0 := by
  classical
  let a := liftTranslation q B hq hB M hM
  have hs := Equiv.sum_comp (affineOfLinearTranslation M a).toEquiv
    (fun x => sign (q x))
  change (∑ x : W, sign (q (M x + a))) = ∑ x : W, sign (q x) at hs
  have hh : (∑ x : W, sign (q (M x + a))) =
      (∑ x : W, sign (q x)) * sign (q a) := by
    simp only [a, liftTranslation_quadratic, sign_add, Finset.sum_mul]
  rw [hh] at hs
  have hn := gauss_ne_zero q B hq hB
  have he : sign (q a) = 1 := mul_left_cancel₀ hn (hs.trans (mul_one _).symm)
  exact (sign_eq_one_iff _).mp he

theorem liftTranslation_preserves (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) (x : W) :
    q (M x + liftTranslation q B hq hB M hM) = q x := by
  rw [liftTranslation_quadratic q B hq hB M hM x,
    liftTranslation_isotropic q B hq hB M hM, add_zero]

theorem quadratic_translation_unique (M : W ≃ₗ[F₂] W) (a b : W)
    (ha : ∀ x, q (M x + a) = q x) (hb : ∀ x, q (M x + b) = q x) : a = b := by
  have hqa : q a = 0 := by simpa [quadratic_zero q B hq] using ha 0
  have hqb : q b = 0 := by simpa [quadratic_zero q B hq] using hb 0
  apply eq_of_sub_eq_zero
  apply hB.2
  intro y
  obtain ⟨x, rfl⟩ := M.surjective y
  have hea := ha x
  have heb := hb x
  rw [hq, hqa, add_zero] at hea
  rw [hq, hqb, add_zero] at heb
  rw [map_sub]
  exact sub_eq_zero.mpr (add_left_cancel (hea.trans heb.symm))

/-- Every polar-form automorphism has exactly one affine lift preserving `q`. -/
theorem existsUnique_quadratic_translation (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) :
    ∃! a : W, ∀ x : W, q (M x + a) = q x := by
  refine ⟨liftTranslation q B hq hB M hM,
    liftTranslation_preserves q B hq hB M hM, ?_⟩
  intro a ha
  exact quadratic_translation_unique q B hq hB M a _ ha
    (liftTranslation_preserves q B hq hB M hM)

omit hB [FiniteDimensional F₂ W] in
theorem affine_preserves_polar (e : W ≃ᵃ[F₂] W)
    (he : ∀ x, q (e x) = q x) (x y : W) :
    B (e.linear x) (e.linear y) = B x y := by
  have hs := quadratic_second q B hq (e.linear x) (e.linear y) (e 0)
  have ht := quadratic_second q B hq x y 0
  have hxy : e.linear x + e.linear y + e 0 = e (x + y) := by
    rw [affine_apply_eq_linear_add e (x + y), map_add]
  rw [hxy, ← affine_apply_eq_linear_add, ← affine_apply_eq_linear_add,
    he, he, he, he] at hs
  simp only [add_zero] at ht
  exact hs.symm.trans ht

/-- Forgetting translation is a bijection from affine quadratic isometries
to linear polar-form isometries. -/
noncomputable def affinePolarEquiv :
    {e : W ≃ᵃ[F₂] W // ∀ x, q (e x) = q x} ≃
      {M : W ≃ₗ[F₂] W // ∀ x y, B (M x) (M y) = B x y} where
  toFun e := ⟨e.1.linear, affine_preserves_polar q B hq e.1 e.2⟩
  invFun M := ⟨affineOfLinearTranslation M.1 (liftTranslation q B hq hB M.1 M.2),
    liftTranslation_preserves q B hq hB M.1 M.2⟩
  left_inv e := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change e.1.linear x + _ = e.1 x
    rw [affine_apply_eq_linear_add e.1 x]
    congr 1
    apply quadratic_translation_unique q B hq hB e.1.linear
    · exact liftTranslation_preserves q B hq hB _ _
    · intro y
      rw [← affine_apply_eq_linear_add]
      exact e.2 y
  right_inv M := by apply Subtype.ext; rfl

/-- The full group of affine automorphisms of the quadratic function. -/
def quadraticAffineSubgroup : Subgroup (W ≃ᵃ[F₂] W) where
  carrier := {e | ∀ x, q (e x) = q x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro e f he hf x
    exact (he (f x)).trans (hf x)
  inv_mem' := by
    intro e he x
    have hh := he (e.symm x)
    simpa [AffineEquiv.inv_def] using hh.symm

/-- The full group of linear automorphisms of the polar form. -/
def polarLinearSubgroup : Subgroup (W ≃ₗ[F₂] W) where
  carrier := {M | ∀ x y, B (M x) (M y) = B x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro M N hM hN x y
    exact (hM (N x) (N y)).trans (hN x y)
  inv_mem' := by
    intro M hM x y
    have hh := hM (M.symm x) (M.symm y)
    simpa using hh.symm

/-- The affine lifting bijection respects group multiplication. -/
noncomputable def affinePolarMulEquiv :
    quadraticAffineSubgroup q ≃* polarLinearSubgroup B where
  __ := affinePolarEquiv q B hq hB
  map_mul' e f := by apply Subtype.ext; rfl

/-- The unique translation is orthogonal to every vector whose quadratic
value is preserved by the linear part; in particular to any invariant
totally singular subspace. -/
theorem liftTranslation_orthogonal (M : W ≃ₗ[F₂] W)
    (hM : ∀ x y, B (M x) (M y) = B x y) (x : W)
    (hx : q (M x) = q x) :
    B (M x) (liftTranslation q B hq hB M hM) = 0 := by
  rw [liftTranslation_pairing, hx, add_self_F₂]


end FiniteQuadratic

/-- The concrete polar pairing on the cubic-family ambient space. -/
def beta (t s : ℕ) (a b : V t s) : F₂ :=
  dot a.1.1 b.1.2 + dot b.1.1 a.1.2 +
    dot a.2.1 b.2.2 + dot b.2.1 a.2.2

theorem beta_add_left (t s : ℕ) (a b c : V t s) :
    beta t s (a + b) c = beta t s a c + beta t s b c := by
  simp only [beta, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
  ring

theorem beta_add_right (t s : ℕ) (a b c : V t s) :
    beta t s a (b + c) = beta t s a b + beta t s a c := by
  simp only [beta, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
  ring

@[simp] theorem beta_zero_left (t s : ℕ) (a : V t s) : beta t s 0 a = 0 := by
  simp [beta]

@[simp] theorem beta_zero_right (t s : ℕ) (a : V t s) : beta t s a 0 = 0 := by
  simp [beta]

theorem beta_comm (t s : ℕ) (a b : V t s) : beta t s a b = beta t s b a := by
  unfold beta
  ring

/-- The concrete polar form, with both linearity proofs. -/
def quadPolar (t s : ℕ) : LinearMap.BilinForm F₂ (V t s) where
  toFun a :=
    { toFun := beta t s a
      map_add' := beta_add_right t s a
      map_smul' := by
        intro r x
        have hf : ∀ r : F₂, r = 0 ∨ r = 1 := by decide
        rcases hf r with rfl | rfl <;> simp }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact beta_add_left t s a b c
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    change beta t s (r • a) b = r * beta t s a b
    have hf : ∀ r : F₂, r = 0 ∨ r = 1 := by decide
    rcases hf r with rfl | rfl <;> simp

@[simp] theorem quadPolar_apply (t s : ℕ) (a b : V t s) :
    quadPolar t s a b = beta t s a b := rfl

theorem quad_polarization (t s : ℕ) (a b : V t s) :
    quad t s (a + b) = quad t s a + quad t s b + quadPolar t s a b := by
  simp only [quad, hyperbolic, quadPolar_apply, beta, Prod.fst_add,
    Prod.snd_add, dot_add_left, dot_add_right]
  ring

theorem beta_separating (t s : ℕ) (a : V t s)
    (ha : ∀ b, beta t s a b = 0) : a = 0 := by
  have hx : a.1.1 = 0 := (dot_nondegenerate t a.1.1).mp (by
    intro y
    have hh := ha ((0, y), 0)
    simpa [beta, dot_comm] using hh)
  have hy : a.1.2 = 0 := (dot_nondegenerate t a.1.2).mp (by
    intro x
    have hh := ha ((x, 0), 0)
    simpa [beta] using hh)
  have hz : a.2 = 0 := (polarZ_nondegenerate s a.2).mp (by
    intro z
    have hh := ha ((0, 0), z)
    simpa [beta, polarZ] using hh)
  exact Prod.ext (Prod.ext hx hy) hz

theorem quadPolar_nondegenerate (t s : ℕ) : (quadPolar t s).Nondegenerate := by
  constructor
  · exact beta_separating t s
  · intro a ha
    apply beta_separating t s a
    intro b
    rw [beta_comm]
    exact ha b

/-- The full affine stabilizer of the family's quadratic part is the full
symplectic group of its explicit polar form. -/
noncomputable def affineQuadPolarEquiv (t s : ℕ) :
    quadraticAffineSubgroup (quad t s) ≃* polarLinearSubgroup (quadPolar t s) :=
  affinePolarMulEquiv (quad t s) (quadPolar t s)
    (quad_polarization t s) (quadPolar_nondegenerate t s)

/-- A polar isometry preserving the distinguished totally singular X-space
has affine-lift translation with zero Y-coordinate. -/
theorem quad_liftTranslation_y_zero (t s : ℕ) (M : V t s ≃ₗ[F₂] V t s)
    (hM : ∀ a b, quadPolar t s (M a) (M b) = quadPolar t s a b)
    (hX : ∀ x : Y t, ∃ y : Y t, M ((y, 0), 0) = ((x, 0), 0)) :
    (liftTranslation (quad t s) (quadPolar t s) (quad_polarization t s)
      (quadPolar_nondegenerate t s) M hM).1.2 = 0 := by
  apply (dot_nondegenerate t _).mp
  intro x
  obtain ⟨y, hy⟩ := hX x
  have hh := liftTranslation_orthogonal (quad t s) (quadPolar t s)
    (quad_polarization t s) (quadPolar_nondegenerate t s) M hM ((y, 0), 0)
    (by rw [hy]; simp [quad, hyperbolic])
  rw [hy] at hh
  simpa [quadPolar_apply, beta] using hh

/-- The zero Y-translation property holds for every affine quadratic
isometry with an invariant X-space, independently of how it was built. -/
theorem quad_affine_translation_y_zero (t s : ℕ) (e : V t s ≃ᵃ[F₂] V t s)
    (he : ∀ v, quad t s (e v) = quad t s v)
    (hX : ∀ x : Y t, ∃ y : Y t, e.linear ((y, 0), 0) = ((x, 0), 0)) :
    (e 0).1.2 = 0 := by
  let hM := affine_preserves_polar (quad t s) (quadPolar t s)
    (quad_polarization t s) e he
  have ht : e 0 = liftTranslation (quad t s) (quadPolar t s)
      (quad_polarization t s) (quadPolar_nondegenerate t s) e.linear hM := by
    apply quadratic_translation_unique (quad t s) (quadPolar t s)
      (quad_polarization t s) (quadPolar_nondegenerate t s) e.linear
    · intro x
      rw [← affine_apply_eq_linear_add]
      exact he x
    · exact liftTranslation_preserves _ _ _ _ _ _
  rw [ht]
  exact quad_liftTranslation_y_zero t s e.linear hM hX

end QuadraticAffineIsometries
end


/-! ## Walsh spectrum and spanning -/

section
open scoped BigOperators
open QuadraticAffineIsometries
namespace CubicBentAutomorphisms

theorem binary_cases (x : F₂) : x = 0 ∨ x = 1 :=
  (by decide : ∀ x : F₂, x = 0 ∨ x = 1) x

theorem binary_sign_injective : Function.Injective sign := by
  intro x y h
  rcases binary_cases x with rfl | rfl <;>
    rcases binary_cases y with rfl | rfl <;> simp_all

theorem binary_add_zero_iff {W : Type*} [AddCommGroup W] [Module F₂ W] (x y : W) :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z => z + y) h
    simpa only [add_assoc, module_add_self, add_zero, zero_add] using hh
  · rintro rfl
    exact module_add_self x

theorem sum_sign_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → F₂) :
    (∑ x : ι → F₂, sign (dot a x)) =
      if a = 0 then (2 : ℤ) ^ Fintype.card ι else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, Fintype.card_fun, ZMod.card]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hh
      apply ha
      funext i
      exact not_not.mp (fun h => hh ⟨i, h⟩)
    have hai : a i = 1 := (binary_cases (a i)).resolve_left hi
    let e : ι → F₂ := Pi.single i 1
    have he : dot a e = 1 := by
      change dotProduct a (Pi.single i 1) = 1
      simpa using hai
    have hs := Equiv.sum_comp (Equiv.addRight e) (fun x => sign (dot a x))
    change (∑ x, sign (dot a (x + e))) = ∑ x, sign (dot a x) at hs
    simp_rw [dot_add_right, sign_add, he, sign_one, mul_neg_one] at hs
    rw [Finset.sum_neg_distrib] at hs
    linarith

/-- The exact Maiorana--McFarland Walsh evaluation, with an arbitrary Boolean
perturbation on the second half of the coordinates. -/
theorem walsh_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → F₂) → F₂)
    (a b : ι → F₂) :
    (∑ x : ι → F₂, ∑ y : ι → F₂,
      sign (dot x y + h y + dot a x + dot b y)) =
      (2 : ℤ) ^ Fintype.card ι * sign (h a + dot a b) := by
  classical
  rw [Finset.sum_comm]
  have he (y x : ι → F₂) :
      dot x y + h y + dot a x + dot b y = (h y + dot b y) + dot (y + a) x := by
    rw [dot_add_left, dot_comm x y]
    ring
  simp_rw [he, sign_add]
  simp_rw [← Finset.mul_sum, sum_sign_dot, binary_add_zero_iff]
  rw [Finset.sum_eq_single a]
  · simp [dot_comm, mul_comm]
  · intro y _ hy
    simp [hy]
  · simp

def stdDot (t s : ℕ) (a b : V t s) : F₂ :=
  (dot a.1.1 b.1.1 + dot a.1.2 b.1.2) +
    (dot a.2.1 b.2.1 + dot a.2.2 b.2.2)

/-- Standard coordinate dot product identifies the ambient space with its dual. -/
def stdDual (t s : ℕ) : V t s ≃ₗ[F₂] Module.Dual F₂ (V t s) :=
  let ey := dotProductEquiv F₂ (Fin t × Fin 3)
  let ez := dotProductEquiv F₂ (Fin s)
  let eyy := (ey.prodCongr ey).trans (Module.dualProdDualEquivDual F₂ (Y t) (Y t))
  let ezz := (ez.prodCongr ez).trans
    (Module.dualProdDualEquivDual F₂ (Fin s → F₂) (Fin s → F₂))
  (eyy.prodCongr ezz).trans
    (Module.dualProdDualEquivDual F₂ (Y t × Y t) (Z s))

@[simp] theorem stdDual_apply (t s : ℕ) (a b : V t s) :
    stdDual t s a b = stdDot t s a b := rfl

theorem stdDot_comm (t s : ℕ) (a b : V t s) : stdDot t s a b = stdDot t s b a := by
  simp only [stdDot, dot_comm]

def walshDual {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
    (f : W → F₂) (l : Module.Dual F₂ W) : ℤ := ∑ v, sign (f v + l v)

def dualBentFamily (t s : ℕ) (a : V t s) : F₂ :=
  quad t s a + cubic t a.1.1

def dualFunction (t s : ℕ) (l : Module.Dual F₂ (V t s)) : F₂ :=
  dualBentFamily t s ((stdDual t s).symm l)

theorem walsh_bentFamily_coordinates (t s : ℕ) (a : V t s) :
    walshDual (bentFamily t s) (stdDual t s a) =
      (2 : ℤ) ^ (3*t+s) * sign (dualBentFamily t s a) := by
  classical
  unfold walshDual
  simp only [Fintype.sum_prod_type]
  have he (x y : Y t) (u v : Fin s → F₂) :
      bentFamily t s ((x,y),(u,v)) + stdDual t s a ((x,y),(u,v)) =
      (dot x y + cubic t y + dot a.1.1 x + dot a.1.2 y) +
        (dot u v + (0 : F₂) + dot a.2.1 u + dot a.2.2 v) := by
    simp only [bentFamily, quad, hyperbolic, stdDual_apply, stdDot]
    ring
  have hs (x y : Y t) (u v : Fin s → F₂) :
      sign (bentFamily t s ((x,y),(u,v)) + stdDual t s a ((x,y),(u,v))) =
      sign (dot x y + cubic t y + dot a.1.1 x + dot a.1.2 y) *
        sign (dot u v + (0 : F₂) + dot a.2.1 u + dot a.2.2 v) := by
    rw [he, sign_add]
  simp_rw [hs]
  simp_rw [← Finset.mul_sum]
  rw [walsh_pair (fun _ => (0 : F₂)) a.2.1 a.2.2]
  simp_rw [← Finset.sum_mul]
  rw [walsh_pair (cubic t) a.1.1 a.1.2]
  simp only [Fintype.card_prod, Fintype.card_fin, zero_add]
  rw [show t * 3 = 3 * t by omega, pow_add]
  simp only [dualBentFamily, quad, hyperbolic, sign_add]
  ring

theorem walsh_bentFamily (t s : ℕ) (l : Module.Dual F₂ (V t s)) :
    walshDual (bentFamily t s) l = (2 : ℤ) ^ (3*t+s) * sign (dualFunction t s l) := by
  have hh := walsh_bentFamily_coordinates t s ((stdDual t s).symm l)
  simpa only [LinearEquiv.apply_symm_apply, dualFunction] using hh

theorem bentFamily_walsh_square (t s : ℕ) (l : Module.Dual F₂ (V t s)) :
    walshDual (bentFamily t s) l ^ 2 = (2 : ℤ) ^ (2*(3*t+s)) := by
  rw [walsh_bentFamily, mul_pow]
  have hs : sign (dualFunction t s l) ^ 2 = 1 := by simpa [pow_two] using sign_sq (dualFunction t s l)
  rw [hs, mul_one, ← pow_mul]
  congr 1
  omega

@[simp] theorem dualBentFamily_zero (t s : ℕ) : dualBentFamily t s 0 = 0 := by
  simp [dualBentFamily, quad, hyperbolic, cubic]

@[simp] theorem dualFunction_zero (t s : ℕ) : dualFunction t s 0 = 0 := by
  simp [dualFunction]

/-- Affine covariance is proved directly by a finite change of variables. -/
theorem walsh_affine_covariance {W : Type*} [AddCommGroup W] [Module F₂ W]
    [Fintype W] (f : W → F₂) (e : W ≃ᵃ[F₂] W)
    (he : ∀ v, f (e v) = f v) (l : Module.Dual F₂ W) :
    walshDual f (l.comp e.linear.toLinearMap) = sign (l (e 0)) * walshDual f l := by
  have hs := Equiv.sum_comp e.toEquiv (fun v => sign (f v + l v))
  change (∑ v, sign (f (e v) + l (e v))) = walshDual f l at hs
  have hv (v : W) : sign (f (e v) + l (e v)) =
      sign (f v + l (e.linear v)) * sign (l (e 0)) := by
    rw [he, affine_apply_eq_linear_add e v, map_add, ← add_assoc, sign_add]
  simp_rw [hv] at hs
  rw [← Finset.sum_mul] at hs
  change walshDual f (l.comp e.linear.toLinearMap) * sign (l (e 0)) = walshDual f l at hs
  calc
    walshDual f (l.comp e.linear.toLinearMap) =
        sign (l (e 0)) * (walshDual f (l.comp e.linear.toLinearMap) * sign (l (e 0))) := by
      rw [mul_left_comm, sign_sq, mul_one]
    _ = _ := by rw [hs]

/-- The dual function transforms by the exact affine translation character. -/
theorem dualFunction_affine_covariance (t s : ℕ) (e : AffineStabilizer t s)
    (l : Module.Dual F₂ (V t s)) :
    dualFunction t s (l.comp e.1.linear.toLinearMap) =
      dualFunction t s l + l (e.1 0) := by
  have hs := walsh_affine_covariance (bentFamily t s) e.1 e.2 l
  rw [walsh_bentFamily, walsh_bentFamily] at hs
  apply binary_sign_injective
  rw [sign_add]
  apply mul_left_cancel₀ (pow_ne_zero (3*t+s) (by norm_num : (2 : ℤ) ≠ 0))
  calc
    (2 : ℤ) ^ (3*t+s) * sign (dualFunction t s (l.comp e.1.linear.toLinearMap)) =
        sign (l (e.1 0)) * ((2 : ℤ) ^ (3*t+s) * sign (dualFunction t s l)) := hs
    _ = _ := by ring

theorem card_V (t s : ℕ) : Fintype.card (V t s) = 2 ^ (2*(3*t+s)) := by
  simp only [V, Y, Z, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

theorem sum_sign_linear_zero {W : Type*} [AddCommGroup W] [Module F₂ W]
    [Fintype W] (l : Module.Dual F₂ W) (hl : l ≠ 0) : (∑ v, sign (l v)) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hl
    apply LinearMap.ext
    exact hn
  have ha1 : l a = 1 := (binary_cases (l a)).resolve_left ha
  have hs := Equiv.sum_comp (Equiv.addRight a) (fun v => sign (l v))
  change (∑ v, sign (l (v+a))) = ∑ v, sign (l v) at hs
  simp_rw [map_add, sign_add, ha1, sign_one, mul_neg_one] at hs
  rw [Finset.sum_neg_distrib] at hs
  linarith

/-- The support is contained in no proper affine hyperplane. -/
theorem bent_support_affine_spanning (t s : ℕ) (ht : 0 < t)
    (l : Module.Dual F₂ (V t s)) (c : F₂)
    (h : ∀ v, bentFamily t s v = 1 → l v + c = 0) : l = 0 ∧ c = 0 := by
  have hp (v : V t s) :
      sign (l v) - sign (bentFamily t s v + l v) =
        sign c * (1 - sign (bentFamily t s v)) := by
    rcases binary_cases (bentFamily t s v) with hv | hv
    · simp [hv]
    · have hc : l v = c := (binary_add_zero_iff _ _).mp (h v hv)
      rw [hv, hc, sign_add, sign_one]
      ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => hp v)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hzero : (∑ v, sign (bentFamily t s v)) = walshDual (bentFamily t s) 0 := by
    simp [walshDual]
  rw [hzero] at hs
  change (∑ v, sign (l v)) - walshDual (bentFamily t s) l =
    sign c * ((Fintype.card (V t s) : ℤ) - walshDual (bentFamily t s) 0) at hs
  rw [walsh_bentFamily, walsh_bentFamily, dualFunction_zero, sign_zero, mul_one, card_V] at hs
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hs
  have hm : 3 ≤ 3*t+s := by omega
  have hN : (8 : ℤ) ≤ 2 ^ (3*t+s) := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ (3*t+s) := pow_le_pow_right₀ (by norm_num) hm
  rw [show 2*(3*t+s) = (3*t+s)*2 by omega, pow_mul] at hs
  have hl : l = 0 := by
    by_contra hn
    rw [sum_sign_linear_zero l hn, zero_sub] at hs
    rcases binary_cases c with hc | hc <;>
      rcases binary_cases (dualFunction t s l) with hg | hg <;>
      rw [hc, hg] at hs <;> norm_num at hs <;> nlinarith
  refine ⟨hl, ?_⟩
  rw [hl] at hs
  simp only [LinearMap.zero_apply, sign_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, dualFunction_zero] at hs
  rw [card_V] at hs
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hs
  rw [show 2*(3*t+s) = (3*t+s)*2 by omega, pow_mul] at hs
  rcases binary_cases c with hc | hc
  · exact hc
  · rw [hc, sign_one] at hs
    nlinarith

theorem cubic_unitY_zero (t : ℕ) (j : Fin t) (k : Fin 3) :
    cubic t (unitY t j k) = 0 := by
  unfold cubic
  apply Finset.sum_eq_zero
  intro i _
  fin_cases k <;> simp [unitY]

/-- The actual affine span of the support is the entire ambient space. -/
theorem bent_support_affineSpan_eq_top (t s : ℕ) (ht : 0 < t) :
    affineSpan F₂ {v : V t s | bentFamily t s v = 1} = ⊤ := by
  let S : Set (V t s) := {v | bentFamily t s v = 1}
  have hS : S.Nonempty := by
    by_contra hn
    have hh := bent_support_affine_spanning t s ht 0 1 (by
      intro v hv
      exact False.elim (hn ⟨v, hv⟩))
    exact (by decide : (1 : F₂) ≠ 0) hh.2
  apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
    F₂ (V t s) (V t s) hS).mpr
  by_contra hn
  obtain ⟨l, hl, hker⟩ := (vectorSpan F₂ S).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hn)
  obtain ⟨p, hp⟩ := hS
  apply hl
  exact (bent_support_affine_spanning t s ht l (l p) (by
    intro v hv
    have hm := hker (vsub_mem_vectorSpan F₂ hv hp)
    change l (v - p) = 0 at hm
    rw [map_sub, sub_eq_zero] at hm
    rw [hm, add_self_F₂])).1

/-- An explicit polar pair witnesses nonadditivity of the dual function. -/
theorem dualFunction_not_additive (t s : ℕ) (ht : 0 < t) :
    ¬ ∀ a b : Module.Dual F₂ (V t s),
      dualFunction t s (a+b) = dualFunction t s a + dualFunction t s b := by
  intro h
  let j : Fin t := ⟨0, ht⟩
  let u := unitY t j 0
  let x : V t s := ((u,0),0)
  let y : V t s := ((0,u),0)
  have hh := h (stdDual t s x) (stdDual t s y)
  rw [← map_add] at hh
  simp only [dualFunction, LinearEquiv.symm_apply_apply] at hh
  have hu : dot u u = 1 := by
    rw [dot_unitY_left]
    simp [u, unitY]
  have hcu : cubic t u = 0 := cubic_unitY_zero t j 0
  have hx : dualBentFamily t s x = 0 := by
    simp [dualBentFamily, quad, hyperbolic, x, hcu]
  have hy : dualBentFamily t s y = 0 := by
    simp [dualBentFamily, quad, hyperbolic, y, cubic]
  have hxy : dualBentFamily t s (x+y) = 1 := by
    simpa [dualBentFamily, quad, hyperbolic, x, y, hcu] using hu
  rw [hx, hy, hxy] at hh
  exact (by decide : (1 : F₂) ≠ 0) (by simpa using hh)


end CubicBentAutomorphisms
end


/-! ## Affine action and quadratic conjugation -/

section
open scoped BigOperators
namespace CubicBentAutomorphisms

def includeX (t s : ℕ) : Y t →ₗ[F₂] V t s where
  toFun x := ((x, 0), 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def includeY (t s : ℕ) : Y t →ₗ[F₂] V t s where
  toFun y := ((0, y), 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def projectX (t s : ℕ) : V t s →ₗ[F₂] Y t :=
  (LinearMap.fst F₂ (Y t) (Y t)).comp (LinearMap.fst F₂ (Y t × Y t) (Z s))

def projectY (t s : ℕ) : V t s →ₗ[F₂] Y t :=
  (LinearMap.snd F₂ (Y t) (Y t)).comp (LinearMap.fst F₂ (Y t × Y t) (Z s))

def stabilizerXMap {t s : ℕ} (e : AffineStabilizer t s) : Y t →ₗ[F₂] Y t :=
  (projectX t s).comp (e.1.linear.toLinearMap.comp (includeX t s))

def stabilizerYMap {t s : ℕ} (e : AffineStabilizer t s) : Y t →ₗ[F₂] Y t :=
  (projectY t s).comp (e.1.linear.toLinearMap.comp (includeY t s))

theorem stabilizer_linear_includeX {t s : ℕ} (e : AffineStabilizer t s) (x : Y t) :
    e.1.linear (includeX t s x) = includeX t s (stabilizerXMap e x) := by
  have h := affine_stabilizer_preserves_intrinsic_x_space e (a := includeX t s x) rfl rfl
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact h.1
  · exact h.2

theorem stabilizer_linear_y {t s : ℕ} (e : AffineStabilizer t s) (w : V t s) :
    (e.1.linear w).1.2 = stabilizerYMap e w.1.2 := by
  have hw : w = includeY t s w.1.2 + ((w.1.1,0),w.2) := by ext <;> simp [includeY]
  have hz := affine_stabilizer_preserves_cubic_radical e
    (a := ((w.1.1,0),w.2)) rfl
  conv_lhs => rw [hw, map_add]
  change (e.1.linear (includeY t s w.1.2)).1.2 +
    (e.1.linear ((w.1.1,0),w.2)).1.2 = _
  rw [hz, add_zero]
  rfl

def stabilizerXEquiv {t s : ℕ} (e : AffineStabilizer t s) : Y t ≃ₗ[F₂] Y t where
  toLinearMap := stabilizerXMap e
  invFun := stabilizerXMap (stabilizerSymm e)
  left_inv x := by
    have h := congrArg (fun w : V t s => w.1.1)
      (e.1.linear.symm_apply_apply (includeX t s x))
    rw [stabilizer_linear_includeX] at h
    exact h
  right_inv x := by
    have h := congrArg (fun w : V t s => w.1.1)
      (e.1.linear.apply_symm_apply (includeX t s x))
    change (e.1.linear ((stabilizerSymm e).1.linear (includeX t s x))).1.1 = x at h
    rw [stabilizer_linear_includeX] at h
    exact h

def stabilizerYEquiv {t s : ℕ} (e : AffineStabilizer t s) : Y t ≃ₗ[F₂] Y t where
  toLinearMap := stabilizerYMap e
  invFun := stabilizerYMap (stabilizerSymm e)
  left_inv y := by
    have h := congrArg (fun w : V t s => w.1.2)
      (e.1.linear.symm_apply_apply (includeY t s y))
    change ((stabilizerSymm e).1.linear (e.1.linear (includeY t s y))).1.2 = y at h
    rw [stabilizer_linear_y, stabilizer_linear_y] at h
    exact h
  right_inv y := by
    have h := congrArg (fun w : V t s => w.1.2)
      (e.1.linear.apply_symm_apply (includeY t s y))
    change (e.1.linear ((stabilizerSymm e).1.linear (includeY t s y))).1.2 = y at h
    rw [stabilizer_linear_y, stabilizer_linear_y] at h
    exact h

theorem stabilizerYEquiv_preserves_tensor {t s : ℕ} (e : AffineStabilizer t s)
    (a b c : Y t) :
    cubicTensor t (stabilizerYEquiv e a) (stabilizerYEquiv e b)
      (stabilizerYEquiv e c) = cubicTensor t a b c := by
  exact affine_stabilizer_preserves_cubicTensor e
    (includeY t s a) (includeY t s b) (includeY t s c)

theorem bent_add_includeX (t s : ℕ) (w : V t s) (x : Y t) :
    bentFamily t s (w + includeX t s x) = bentFamily t s w + dot x w.1.2 := by
  simp only [bentFamily, quad, includeX, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.fst_add, Prod.snd_add, add_zero, dot_add_left]
  abel

theorem stabilizer_first_difference {t s : ℕ} (e : AffineStabilizer t s)
    (w : V t s) (x : Y t) :
    dot (stabilizerXEquiv e x) (e.1 w).1.2 = dot x w.1.2 := by
  have h := e.2 (w + includeX t s x)
  rw [affine_add, stabilizer_linear_includeX, bent_add_includeX,
    bent_add_includeX, e.2] at h
  exact add_left_cancel h

theorem stabilizer_translation_y_zero {t s : ℕ} (e : AffineStabilizer t s) :
    (e.1 0).1.2 = 0 := by
  apply (dot_nondegenerate t _).mp
  intro x
  obtain ⟨a, rfl⟩ := (stabilizerXEquiv e).surjective x
  simpa using stabilizer_first_difference e 0 a

theorem stabilizer_affine_y {t s : ℕ} (e : AffineStabilizer t s) (w : V t s) :
    (e.1 w).1.2 = stabilizerYEquiv e w.1.2 := by
  rw [affine_apply_eq_linear_add]
  change (e.1.linear w).1.2 + (e.1 0).1.2 = _
  rw [stabilizer_translation_y_zero, add_zero, stabilizer_linear_y]
  rfl

theorem stabilizer_pairing {t s : ℕ} (e : AffineStabilizer t s) (x y : Y t) :
    dot (stabilizerXEquiv e x) (stabilizerYEquiv e y) = dot x y := by
  have h := stabilizer_first_difference e (includeY t s y) x
  rw [stabilizer_affine_y] at h
  exact h


/-- Affine maps with the intrinsic X/Y actions required by cubic-gradient conjugacy. -/
structure CubicAdaptedAffine (t s : ℕ) where
  affine : V t s ≃ᵃ[F₂] V t s
  xAction : Y t ≃ₗ[F₂] Y t
  yAction : Y t ≃ₗ[F₂] Y t
  map_x : ∀ x, affine.linear (includeX t s x) = includeX t s (xAction x)
  map_y : ∀ w, (affine w).1.2 = yAction w.1.2
  pairing : ∀ x y, dot (xAction x) (yAction y) = dot x y
  tensor : ∀ a b c, cubicTensor t (yAction a) (yAction b) (yAction c) =
    cubicTensor t a b c

def stabilizerAdapted {t s : ℕ} (e : AffineStabilizer t s) : CubicAdaptedAffine t s where
  affine := e.1
  xAction := stabilizerXEquiv e
  yAction := stabilizerYEquiv e
  map_x := stabilizer_linear_includeX e
  map_y := stabilizer_affine_y e
  pairing := stabilizer_pairing e
  tensor := stabilizerYEquiv_preserves_tensor e

def adaptedCorrection {t s : ℕ} (e : CubicAdaptedAffine t s) : V t s →ₗ[F₂] V t s :=
  (includeX t s).comp
    ((gradientCorrectionLinear e.xAction e.yAction e.pairing e.tensor).comp (projectY t s))

theorem shear_eq_add_includeX (t s : ℕ) (w : V t s) :
    shear t s w = w + includeX t s (gradient t w.1.2) := by
  ext <;> simp [shear, includeX]

theorem shear_conjugate_formula {t s : ℕ} (e : CubicAdaptedAffine t s) (w : V t s) :
    shear t s (e.affine (shear t s w)) = e.affine w + adaptedCorrection e w := by
  rw [show shear t s w = w + includeX t s (gradient t w.1.2) from
    shear_eq_add_includeX t s w, affine_add, e.map_x, shear_eq_add_includeX]
  have hy : (e.affine w + includeX t s (e.xAction (gradient t w.1.2))).1.2 =
      e.yAction w.1.2 := by simpa [includeX] using e.map_y w
  rw [hy]
  change e.affine w + includeX t s (e.xAction (gradient t w.1.2)) +
      includeX t s (gradient t (e.yAction w.1.2)) =
    e.affine w + includeX t s
      (e.xAction (gradient t w.1.2) + gradient t (e.yAction w.1.2))
  rw [map_add, add_assoc]

def shearConjugateAffineMap {t s : ℕ} (e : CubicAdaptedAffine t s) :
    V t s →ᵃ[F₂] V t s where
  toFun w := shear t s (e.affine (shear t s w))
  linear := e.affine.linear.toLinearMap + adaptedCorrection e
  map_vadd' w v := by
    change shear t s (e.affine (shear t s (v+w))) =
      (e.affine.linear v + adaptedCorrection e v) + shear t s (e.affine (shear t s w))
    rw [shear_conjugate_formula, shear_conjugate_formula,
      affine_apply_eq_linear_add e.affine (v+w), affine_apply_eq_linear_add e.affine w]
    simp only [map_add]
    abel

noncomputable def shearConjugateAffine {t s : ℕ} (e : CubicAdaptedAffine t s) :
    V t s ≃ᵃ[F₂] V t s :=
  AffineEquiv.ofBijective (φ := shearConjugateAffineMap e)
    ((shearEquiv t s).bijective.comp (e.affine.bijective.comp (shearEquiv t s).bijective))

@[simp] theorem shearConjugateAffine_apply {t s : ℕ} (e : CubicAdaptedAffine t s)
    (w : V t s) :
    shearConjugateAffine e w = shear t s (e.affine (shear t s w)) := rfl

theorem shearConjugateAffine_linear {t s : ℕ} (e : CubicAdaptedAffine t s)
    (w : V t s) :
    (shearConjugateAffine e).linear w = e.affine.linear w + adaptedCorrection e w := rfl

theorem shearConjugate_preserves_quad_iff {t s : ℕ} (e : CubicAdaptedAffine t s) :
    (∀ w, quad t s (shearConjugateAffine e w) = quad t s w) ↔
      (∀ w, bentFamily t s (e.affine w) = bentFamily t s w) := by
  constructor
  · intro h w
    have hw := h (shear t s w)
    simpa only [shearConjugateAffine_apply, shear_involutive t s w, quad_shear] using hw
  · intro h w
    rw [shearConjugateAffine_apply, quad_shear, h, bentFamily_eq_quad_shear,
      shear_involutive]

theorem shearConjugate_preserves_bent_iff {t s : ℕ} (e : CubicAdaptedAffine t s) :
    (∀ w, bentFamily t s (shearConjugateAffine e w) = bentFamily t s w) ↔
      (∀ w, quad t s (e.affine w) = quad t s w) := by
  constructor
  · intro h w
    have hw := h (shear t s w)
    simp only [shearConjugateAffine_apply, bentFamily_eq_quad_shear] at hw
    rw [shear_involutive, shear_involutive] at hw
    exact hw
  · intro h w
    rw [shearConjugateAffine_apply, bentFamily_eq_quad_shear, shear_involutive,
      h, quad_shear]

noncomputable def shearConjugateAdapted {t s : ℕ} (e : CubicAdaptedAffine t s) :
    CubicAdaptedAffine t s where
  affine := shearConjugateAffine e
  xAction := e.xAction
  yAction := e.yAction
  map_x x := by
    rw [shearConjugateAffine_linear, e.map_x]
    have hz : adaptedCorrection e (includeX t s x) = 0 := by
      change includeX t s (gradientCorrectionLinear e.xAction e.yAction e.pairing e.tensor 0) = 0
      simp
    rw [hz, add_zero]
  map_y w := by
    rw [shearConjugateAffine_apply]
    change (e.affine (shear t s w)).1.2 = _
    rw [e.map_y]
    rfl
  pairing := e.pairing
  tensor := e.tensor

theorem shearConjugateAdapted_involutive {t s : ℕ} (e : CubicAdaptedAffine t s) :
    shearConjugateAdapted (shearConjugateAdapted e) = e := by
  have h : (shearConjugateAdapted (shearConjugateAdapted e)).affine = e.affine := by
    apply AffineEquiv.ext
    intro w
    change shear t s (shear t s (e.affine (shear t s (shear t s w)))) = e.affine w
    rw [shear_involutive, shear_involutive]
  cases e
  simp only [shearConjugateAdapted, CubicAdaptedAffine.mk.injEq] at h ⊢
  exact ⟨h, trivial, trivial⟩


theorem CubicAdaptedAffine.ext_affine {t s : ℕ} {e f : CubicAdaptedAffine t s}
    (h : e.affine = f.affine) : e = f := by
  have hx : e.xAction = f.xAction := by
    apply LinearEquiv.ext
    intro x
    have hxe := e.map_x x
    rw [h, f.map_x] at hxe
    exact (congrArg (fun w : V t s => w.1.1) hxe).symm
  have hy : e.yAction = f.yAction := by
    apply LinearEquiv.ext
    intro y
    have hye := e.map_y (includeY t s y)
    rw [h, f.map_y] at hye
    exact hye.symm
  cases e
  cases f
  simp_all only [CubicAdaptedAffine.mk.injEq]

abbrev AdaptedBentStabilizer (t s : ℕ) :=
  {e : CubicAdaptedAffine t s // ∀ w, bentFamily t s (e.affine w) = bentFamily t s w}

abbrev AdaptedQuadStabilizer (t s : ℕ) :=
  {e : CubicAdaptedAffine t s // ∀ w, quad t s (e.affine w) = quad t s w}

def affineStabilizerEquivAdapted (t s : ℕ) :
    AffineStabilizer t s ≃ AdaptedBentStabilizer t s where
  toFun e := ⟨stabilizerAdapted e, e.2⟩
  invFun e := ⟨e.1.affine, e.2⟩
  left_inv e := rfl
  right_inv e := by
    apply Subtype.ext
    apply CubicAdaptedAffine.ext_affine
    rfl

noncomputable def adaptedBentEquivQuad (t s : ℕ) :
    AdaptedBentStabilizer t s ≃ AdaptedQuadStabilizer t s where
  toFun e := ⟨shearConjugateAdapted e.1,
    (shearConjugate_preserves_quad_iff e.1).mpr e.2⟩
  invFun e := ⟨shearConjugateAdapted e.1,
    (shearConjugate_preserves_bent_iff e.1).mpr e.2⟩
  left_inv e := Subtype.ext (shearConjugateAdapted_involutive e.1)
  right_inv e := Subtype.ext (shearConjugateAdapted_involutive e.1)

/-- Complete, two-way cubic-gradient conjugacy; both inverse maps are affine. -/
noncomputable def affineBentEquivAdaptedQuad (t s : ℕ) :
    AffineStabilizer t s ≃ AdaptedQuadStabilizer t s :=
  (affineStabilizerEquivAdapted t s).trans (adaptedBentEquivQuad t s)

theorem card_affineBent_eq_adaptedQuad (t s : ℕ) :
    Nat.card (AffineStabilizer t s) = Nat.card (AdaptedQuadStabilizer t s) :=
  Nat.card_congr (affineBentEquivAdaptedQuad t s)

end CubicBentAutomorphisms
end


/-! ## Polar-form classification -/

section
open QuadraticAffineIsometries
namespace CubicBentAutomorphisms

/-- Polar isometries with the intrinsic X/Y actions recovered from the cubic
function. These data impose no arbitrary choice of fixed coordinates. -/
structure AdaptedPolar (t s : ℕ) where
  linear : V t s ≃ₗ[F₂] V t s
  xAction : Y t ≃ₗ[F₂] Y t
  yAction : Y t ≃ₗ[F₂] Y t
  map_x : ∀ x, linear (includeX t s x) = includeX t s (xAction x)
  map_y : ∀ w, (linear w).1.2 = yAction w.1.2
  pairing : ∀ x y, dot (xAction x) (yAction y) = dot x y
  tensor : ∀ a b c, cubicTensor t (yAction a) (yAction b) (yAction c) =
    cubicTensor t a b c
  polar : ∀ a b, quadPolar t s (linear a) (linear b) = quadPolar t s a b

theorem AdaptedPolar.ext_linear {t s : ℕ} {e f : AdaptedPolar t s}
    (h : e.linear = f.linear) : e = f := by
  have hx : e.xAction = f.xAction := by
    apply LinearEquiv.ext
    intro x
    have hh := e.map_x x
    rw [h, f.map_x] at hh
    exact (congrArg (fun w : V t s => w.1.1) hh).symm
  have hy : e.yAction = f.yAction := by
    apply LinearEquiv.ext
    intro y
    have hh := e.map_y (includeY t s y)
    rw [h, f.map_y] at hh
    exact hh.symm
  cases e
  cases f
  simp_all only [AdaptedPolar.mk.injEq]

def adaptedQuadToPolar {t s : ℕ} (e : AdaptedQuadStabilizer t s) :
    AdaptedPolar t s where
  linear := e.1.affine.linear
  xAction := e.1.xAction
  yAction := e.1.yAction
  map_x := e.1.map_x
  map_y w := by
    have hz : (e.1.affine 0).1.2 = 0 := by simpa using e.1.map_y 0
    have hw := e.1.map_y w
    rw [affine_apply_eq_linear_add e.1.affine w] at hw
    change (e.1.affine.linear w).1.2 + (e.1.affine 0).1.2 = _ at hw
    simpa only [hz, add_zero] using hw
  pairing := e.1.pairing
  tensor := e.1.tensor
  polar := affine_preserves_polar (quad t s) (quadPolar t s)
    (quad_polarization t s) e.1.affine e.2

noncomputable def AdaptedPolar.translation {t s : ℕ} (e : AdaptedPolar t s) : V t s :=
  liftTranslation (quad t s) (quadPolar t s) (quad_polarization t s)
    (quadPolar_nondegenerate t s) e.linear e.polar

theorem AdaptedPolar.translation_y_zero {t s : ℕ} (e : AdaptedPolar t s) :
    e.translation.1.2 = 0 := by
  apply quad_liftTranslation_y_zero t s e.linear e.polar
  intro x
  refine ⟨e.xAction.symm x, ?_⟩
  change e.linear (includeX t s (e.xAction.symm x)) = includeX t s x
  rw [e.map_x, e.xAction.apply_symm_apply]

noncomputable def adaptedPolarToQuad {t s : ℕ} (e : AdaptedPolar t s) :
    AdaptedQuadStabilizer t s :=
  ⟨{ affine := affineOfLinearTranslation e.linear e.translation
     xAction := e.xAction
     yAction := e.yAction
     map_x := e.map_x
     map_y := by
       intro w
       change (e.linear w).1.2 + e.translation.1.2 = e.yAction w.1.2
       rw [e.translation_y_zero, add_zero, e.map_y]
     pairing := e.pairing
     tensor := e.tensor },
    liftTranslation_preserves (quad t s) (quadPolar t s)
      (quad_polarization t s) (quadPolar_nondegenerate t s) e.linear e.polar⟩

theorem quadAffine_ext_linear {t s : ℕ} (e f : V t s ≃ᵃ[F₂] V t s)
    (he : ∀ w, quad t s (e w) = quad t s w)
    (hf : ∀ w, quad t s (f w) = quad t s w)
    (h : e.linear = f.linear) : e = f := by
  have hc : e 0 = f 0 := by
    apply quadratic_translation_unique (quad t s) (quadPolar t s)
      (quad_polarization t s) (quadPolar_nondegenerate t s) e.linear
    · intro w
      rw [← affine_apply_eq_linear_add]
      exact he w
    · intro w
      rw [h, ← affine_apply_eq_linear_add]
      exact hf w
  apply AffineEquiv.ext
  intro w
  rw [affine_apply_eq_linear_add e w, affine_apply_eq_linear_add f w, h, hc]

/-- The complete adapted quadratic stabilizer is equivalent to its linear
polar model: every compatible polar isometry has exactly one affine lift. -/
noncomputable def adaptedQuadEquivPolar (t s : ℕ) :
    AdaptedQuadStabilizer t s ≃ AdaptedPolar t s where
  toFun := adaptedQuadToPolar
  invFun := adaptedPolarToQuad
  left_inv e := by
    apply Subtype.ext
    apply CubicAdaptedAffine.ext_affine
    exact quadAffine_ext_linear _ _ (adaptedPolarToQuad (adaptedQuadToPolar e)).2 e.2 rfl
  right_inv e := by apply AdaptedPolar.ext_linear; rfl

/-- Complete equivalence from the unrestricted affine bent-function
stabilizer to compatible polar isometries. -/
noncomputable def affineBentEquivAdaptedPolar (t s : ℕ) :
    AffineStabilizer t s ≃ AdaptedPolar t s :=
  (affineBentEquivAdaptedQuad t s).trans (adaptedQuadEquivPolar t s)

theorem card_affineBent_eq_adaptedPolar (t s : ℕ) :
    Nat.card (AffineStabilizer t s) = Nat.card (AdaptedPolar t s) :=
  Nat.card_congr (affineBentEquivAdaptedPolar t s)


end CubicBentAutomorphisms
end


/-! ## The complete parabolic kernel -/

section
open scoped BigOperators Matrix

namespace CubicBentAutomorphisms
namespace ParabolicKernel

abbrev SymmetricMatrix (ι : Type*) :=
  {S : Matrix ι ι F₂ // ∀ i j, S i j = S j i}

theorem card_symmetricMatrix (ι : Type*) [Fintype ι] :
    Nat.card (SymmetricMatrix ι) = 2 ^ (Fintype.card ι * (Fintype.card ι + 1) / 2) := by
  classical
  change Nat.card {f : ι → ι → F₂ // ∀ i j, f i j = f j i} = _
  rw [Nat.card_congr Sym2.lift,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Sym2.card,
    Nat.choose_two_right]
  congr 1
  simp [Nat.mul_comm]

section General
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem dot_transpose (A : Matrix κ ι F₂) (x : ι → F₂) (z : κ → F₂) :
    dot (A.transpose.mulVec z) x = dot z (A.mulVec x) := by
  rw [dot_comm]
  exact Matrix.dotProduct_transpose_mulVec A x z

theorem square_F₂ (x : F₂) : x * x = x := by
  have h : x = 0 ∨ x = 1 := (by decide : ∀ q : F₂, q = 0 ∨ q = 1) x
  rcases h with rfl | rfl <;> simp

def symmetricQuadraticLinear (S : SymmetricMatrix ι) : (ι → F₂) →ₗ[F₂] F₂ where
  toFun y := dot (S.1.mulVec y) y
  map_add' x y := by
    simp only [Matrix.mulVec_add, dot_add_left, dot_add_right]
    have h : dot (S.1.mulVec x) y = dot (S.1.mulVec y) x := by
      have hs : S.1.transpose = S.1 := by ext i j; exact S.2 j i
      calc
        dot (S.1.mulVec x) y = dot (S.1.transpose.mulVec x) y := by rw [hs]
        _ = dot x (S.1.mulVec y) := dot_transpose S.1 y x
        _ = _ := dot_comm _ _
    rw [h]
    calc
      dot (S.val.mulVec x) x + dot (S.val.mulVec y) x +
          (dot (S.val.mulVec y) x + dot (S.val.mulVec y) y) =
          dot (S.val.mulVec x) x + dot (S.val.mulVec y) y +
          (dot (S.val.mulVec y) x + dot (S.val.mulVec y) x) := by abel
      _ = _ := by simp
  map_smul' r y := by
    have hr : r = 0 ∨ r = 1 := (by decide : ∀ q : F₂, q = 0 ∨ q = 1) r
    rcases hr with rfl | rfl <;> simp [dot]

theorem symmetric_diagonal_identity (S : SymmetricMatrix ι) (y : ι → F₂) :
    dot (S.1.mulVec y) y = dot (fun i => S.1 i i) y := by
  classical
  let L := symmetricQuadraticLinear S
  have hy : y = ∑ i, y i • Pi.single i (1 : F₂) := by
    funext j
    simp [Pi.single_apply, eq_comm]
  change L y = _
  conv_lhs => rw [hy, map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i, y i * dot (S.1.mulVec (Pi.single i 1)) (Pi.single i 1)) = _
  simp [dot, Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm, mul_comm]

end General

abbrev KernelDatum (t s : ℕ) :=
  (Matrix (Fin s) (Fin t × Fin 3) F₂ × Matrix (Fin s) (Fin t × Fin 3) F₂) ×
    SymmetricMatrix (Fin t × Fin 3)

theorem card_kernelDatum (t s : ℕ) :
    Nat.card (KernelDatum t s) = 2 ^ ((3*t)*(3*t+1)/2 + 6*t*s) := by
  rw [Nat.card_prod, Nat.card_prod, card_symmetricMatrix]
  simp only [Matrix, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_prod, Fintype.card_fin, ZMod.card]
  simp only [← pow_mul, ← pow_add]
  congr 1
  rw [Nat.mul_comm t 3]
  ring

def kernelMap {t s : ℕ} (p : KernelDatum t s) (w : V t s) : V t s :=
  ((w.1.1 + p.2.1.mulVec w.1.2 +
      p.1.1.transpose.mulVec (p.1.2.mulVec w.1.2) +
      (p.1.1.transpose.mulVec w.2.2 + p.1.2.transpose.mulVec w.2.1) +
      (fun i => p.2.1 i i), w.1.2),
    (w.2.1 + p.1.1.mulVec w.1.2, w.2.2 + p.1.2.mulVec w.1.2))

theorem kernelMap_preserves_quad {t s : ℕ} (p : KernelDatum t s) (w : V t s) :
    quad t s (kernelMap p w) = quad t s w := by
  simp only [quad, kernelMap, hyperbolic, dot_add_left, dot_add_right,
    dot_transpose, symmetric_diagonal_identity]
  rw [dot_comm w.2.2 (p.1.1.mulVec w.1.2)]
  have h1 := add_self_F₂ (dot (fun i => p.2.1 i i) w.1.2)
  have h2 := add_self_F₂ (dot (p.1.2.mulVec w.1.2) (p.1.1.mulVec w.1.2))
  rw [dot_comm (p.1.2.mulVec w.1.2) (p.1.1.mulVec w.1.2)] at h2 ⊢
  have h3 := add_self_F₂ (dot w.2.1 (p.1.2.mulVec w.1.2))
  have h4 := add_self_F₂ (dot (p.1.1.mulVec w.1.2) w.2.2)
  linear_combination h1 + h2 + h3 + h4

theorem kernelMap_preserves_bentFamily {t s : ℕ}
    (p : KernelDatum t s) (w : V t s) :
    bentFamily t s (kernelMap p w) = bentFamily t s w := by
  unfold bentFamily
  rw [kernelMap_preserves_quad]
  rfl

def triangularLinearEquiv {t s : ℕ}
    (B : Y t →ₗ[F₂] Y t) (C : Z s →ₗ[F₂] Y t) (E : Y t →ₗ[F₂] Z s) :
    V t s ≃ₗ[F₂] V t s where
  toFun w := ((w.1.1 + B w.1.2 + C w.2, w.1.2), w.2 + E w.1.2)
  invFun w := ((w.1.1 + B w.1.2 + C (w.2 + E w.1.2), w.1.2),
    w.2 + E w.1.2)
  left_inv w := by
    dsimp
    simp only [map_add]
    apply Prod.ext
    · apply Prod.ext
      · dsimp
        have hz := module_add_self (C (E w.1.2))
        have hb := module_add_self (B w.1.2)
        have hc := module_add_self (C w.2)
        calc
          _ = w.1.1 + (B w.1.2 + B w.1.2) + (C w.2 + C w.2) +
              (C (E w.1.2) + C (E w.1.2)) := by abel
          _ = _ := by rw [hz, hb, hc]; simp
      · rfl
    · dsimp
      rw [add_assoc, module_add_self, add_zero]
  right_inv w := by
    dsimp
    simp only [map_add]
    apply Prod.ext
    · apply Prod.ext
      · dsimp
        calc
          _ = w.1.1 + (B w.1.2 + B w.1.2) +
              ((C w.2 + C (E w.1.2)) + (C w.2 + C (E w.1.2))) := by abel
          _ = _ := by rw [module_add_self, module_add_self]; simp
      · rfl
    · dsimp
      rw [add_assoc, module_add_self, add_zero]
  map_add' a b := by
    ext <;> simp [map_add] <;> abel
  map_smul' r w := by
    simp [map_smul, smul_add]

def kernelLinearEquiv {t s : ℕ} (p : KernelDatum t s) : V t s ≃ₗ[F₂] V t s :=
  triangularLinearEquiv
    (p.2.1.mulVecLin + p.1.1.transpose.mulVecLin.comp p.1.2.mulVecLin)
    (p.1.1.transpose.mulVecLin.comp (LinearMap.snd F₂ _ _) +
      p.1.2.transpose.mulVecLin.comp (LinearMap.fst F₂ _ _))
    (p.1.1.mulVecLin.prod p.1.2.mulVecLin)

def kernelAffineEquiv {t s : ℕ} (p : KernelDatum t s) : V t s ≃ᵃ[F₂] V t s :=
  affineOfLinearTranslation (kernelLinearEquiv p) (((fun i => p.2.1 i i), 0), 0)

@[simp] theorem kernelAffineEquiv_apply {t s : ℕ} (p : KernelDatum t s) (w : V t s) :
    kernelAffineEquiv p w = kernelMap p w := by
  change ((w.1.1 + (p.2.1.mulVec w.1.2 +
    p.1.1.transpose.mulVec (p.1.2.mulVec w.1.2)) +
    (p.1.1.transpose.mulVec w.2.2 + p.1.2.transpose.mulVec w.2.1), w.1.2),
    w.2 + (p.1.1.mulVec w.1.2, p.1.2.mulVec w.1.2)) +
    (((fun i => p.2.1 i i), 0), 0) = kernelMap p w
  ext <;> simp only [kernelMap, Prod.fst_add, Prod.snd_add,
    Prod.fst_zero, Prod.snd_zero, Pi.add_apply, Pi.zero_apply] <;> abel

def kernelStabilizer {t s : ℕ} (p : KernelDatum t s) : AffineStabilizer t s :=
  ⟨kernelAffineEquiv p, by
    intro w
    rw [kernelAffineEquiv_apply]
    exact kernelMap_preserves_bentFamily p w⟩

theorem matrix_eq_of_mulVec_eq {ι κ : Type*} [Fintype ι]
    (A B : Matrix κ ι F₂) (h : ∀ y, A.mulVec y = B.mulVec y) : A = B := by
  classical
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hj

theorem kernelStabilizer_injective (t s : ℕ) :
    Function.Injective (kernelStabilizer : KernelDatum t s → AffineStabilizer t s) := by
  rintro ⟨⟨A, B⟩, S⟩ ⟨⟨A', B'⟩, S'⟩ heq
  have hmap (w : V t s) : kernelMap ((A,B),S) w = kernelMap ((A',B'),S') w := by
    have hh := congrArg (fun e : AffineStabilizer t s => e.1 w) heq
    simpa only [kernelStabilizer, kernelAffineEquiv_apply] using hh
  have hA : A = A' := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun w : V t s => w.2.1) (hmap ((0,y),0))
    simpa [kernelMap] using h
  have hB : B = B' := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun w : V t s => w.2.2) (hmap ((0,y),0))
    simpa [kernelMap] using h
  subst A'
  subst B'
  have hdiag : (fun i => S.1 i i) = (fun i => S'.1 i i) := by
    have h := congrArg (fun w : V t s => w.1.1) (hmap 0)
    simpa [kernelMap] using h
  have hS : S.1 = S'.1 := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun w : V t s => w.1.1) (hmap ((0,y),0))
    simp only [kernelMap, Prod.fst_zero, Prod.snd_zero,
      Matrix.mulVec_zero, zero_add, add_zero] at h
    rw [hdiag] at h
    exact add_right_cancel (add_right_cancel h)
  have hs : S = S' := Subtype.ext hS
  subst S'
  rfl

abbrev KernelSymmetries (t s : ℕ) :=
  {e : AffineStabilizer t s // e ∈ Set.range (@kernelStabilizer t s)}

noncomputable def kernelDatumEquivSymmetries (t s : ℕ) :
    KernelDatum t s ≃ KernelSymmetries t s :=
  Equiv.ofInjective (@kernelStabilizer t s) (kernelStabilizer_injective t s)

theorem card_kernelSymmetries (t s : ℕ) :
    Nat.card (KernelSymmetries t s) = 2 ^ ((3*t)*(3*t+1)/2 + 6*t*s) := by
  rw [← Nat.card_congr (kernelDatumEquivSymmetries t s), card_kernelDatum]

def beta (t s : ℕ) (v w : V t s) : F₂ :=
  dot v.1.1 w.1.2 + dot w.1.1 v.1.2 + polarZ s v.2 w.2

def kernelRawLinear {t s : ℕ}
    (A B : Matrix (Fin s) (Fin t × Fin 3) F₂)
    (R : Matrix (Fin t × Fin 3) (Fin t × Fin 3) F₂)
    (C₁ C₂ : Matrix (Fin t × Fin 3) (Fin s) F₂) : V t s ≃ₗ[F₂] V t s :=
  triangularLinearEquiv R.mulVecLin
    (C₁.mulVecLin.comp (LinearMap.fst F₂ _ _) +
      C₂.mulVecLin.comp (LinearMap.snd F₂ _ _))
    (A.mulVecLin.prod B.mulVecLin)

theorem dot_single_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → F₂) (i : ι) : dot x (Pi.single i 1) = x i := by
  simp [dot, Pi.single_apply]

theorem mulVec_single {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix κ ι F₂) (i : ι) (j : κ) : M.mulVec (Pi.single i 1) j = M j i := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem kernelRaw_cross_conditions {t s : ℕ}
    (A B : Matrix (Fin s) (Fin t × Fin 3) F₂)
    (R : Matrix (Fin t × Fin 3) (Fin t × Fin 3) F₂)
    (C₁ C₂ : Matrix (Fin t × Fin 3) (Fin s) F₂)
    (h : ∀ v w, beta t s (kernelRawLinear A B R C₁ C₂ v)
      (kernelRawLinear A B R C₁ C₂ w) = beta t s v w) :
    C₁ = B.transpose ∧ C₂ = A.transpose := by
  classical
  have hc (y : Y t) (z : Z s) :
      dot (C₁.mulVec z.1 + C₂.mulVec z.2) y +
        (dot (A.mulVec y) z.2 + dot z.1 (B.mulVec y)) = 0 := by
    have hh := h ((0,y),0) ((0,0),z)
    simpa [beta, kernelRawLinear, triangularLinearEquiv, polarZ, dot] using hh
  constructor
  · ext i j
    have hh := hc (Pi.single i 1) (Pi.single j 1,0)
    simp only [Matrix.mulVec_zero, add_zero, dot_zero_right, zero_add,
      dot_single_right, mulVec_single] at hh
    rw [dot_comm, dot_single_right, mulVec_single] at hh
    change C₁ i j = B j i
    have hz := add_self_F₂ (B j i)
    linear_combination hh - hz
  · ext i j
    have hh := hc (Pi.single i 1) (0,Pi.single j 1)
    simp only [Matrix.mulVec_zero, zero_add, dot_zero_left, add_zero,
      dot_single_right, mulVec_single] at hh
    change C₂ i j = A j i
    have hz := add_self_F₂ (A j i)
    linear_combination hh - hz

theorem kernelRaw_symmetry_condition {t s : ℕ}
    (A B : Matrix (Fin s) (Fin t × Fin 3) F₂)
    (R : Matrix (Fin t × Fin 3) (Fin t × Fin 3) F₂)
    (C₁ C₂ : Matrix (Fin t × Fin 3) (Fin s) F₂)
    (h : ∀ v w, beta t s (kernelRawLinear A B R C₁ C₂ v)
      (kernelRawLinear A B R C₁ C₂ w) = beta t s v w) :
    ∀ i j, (R + A.transpose * B) i j = (R + A.transpose * B) j i := by
  classical
  intro i j
  have hh : dot (R.mulVec (Pi.single i 1)) (Pi.single j 1) +
      dot (R.mulVec (Pi.single j 1)) (Pi.single i 1) +
      polarZ s (A.mulVec (Pi.single i 1), B.mulVec (Pi.single i 1))
      (A.mulVec (Pi.single j 1), B.mulVec (Pi.single j 1)) = 0 := by
    simpa [beta, kernelRawLinear, triangularLinearEquiv, polarZ, dot] using
      h ((0, Pi.single i 1),0) ((0, Pi.single j 1),0)
  simp only [Matrix.mulVec_zero, add_zero, dot_single_right, mulVec_single,
    polarZ] at hh
  have hij : dot (A.mulVec (Pi.single i 1)) (B.mulVec (Pi.single j 1)) =
      (A.transpose * B) i j := by
    simp [dot, Matrix.mul_apply, Matrix.transpose_apply, mulVec_single]
  have hji : dot (A.mulVec (Pi.single j 1)) (B.mulVec (Pi.single i 1)) =
      (A.transpose * B) j i := by
    simp [dot, Matrix.mul_apply, Matrix.transpose_apply, mulVec_single]
  rw [hij, hji] at hh
  change R i j + (A.transpose * B) i j = R j i + (A.transpose * B) j i
  have hz₁ := add_self_F₂ (R j i)
  have hz₂ := add_self_F₂ ((A.transpose * B) j i)
  linear_combination hh - hz₁ - hz₂

theorem kernelRaw_complete {t s : ℕ}
    (A B : Matrix (Fin s) (Fin t × Fin 3) F₂)
    (R : Matrix (Fin t × Fin 3) (Fin t × Fin 3) F₂)
    (C₁ C₂ : Matrix (Fin t × Fin 3) (Fin s) F₂)
    (h : ∀ v w, beta t s (kernelRawLinear A B R C₁ C₂ v)
      (kernelRawLinear A B R C₁ C₂ w) = beta t s v w) :
    ∃ S : SymmetricMatrix (Fin t × Fin 3),
      kernelRawLinear A B R C₁ C₂ = kernelLinearEquiv ((A,B),S) := by
  let S : SymmetricMatrix (Fin t × Fin 3) :=
    ⟨R + A.transpose * B, kernelRaw_symmetry_condition A B R C₁ C₂ h⟩
  refine ⟨S, ?_⟩
  obtain ⟨hc₁,hc₂⟩ := kernelRaw_cross_conditions A B R C₁ C₂ h
  have hR : R = S.1 + A.transpose * B := by
    ext i j
    change R i j = (R i j + (A.transpose * B) i j) + (A.transpose * B) i j
    rw [add_assoc, add_self_F₂, add_zero]
  subst C₁
  subst C₂
  apply LinearEquiv.ext
  intro w
  change ((w.1.1 + R.mulVec w.1.2 +
    (B.transpose.mulVec w.2.1 + A.transpose.mulVec w.2.2), w.1.2),
    w.2 + (A.mulVec w.1.2, B.mulVec w.1.2)) =
    ((w.1.1 + (S.1.mulVec w.1.2 + A.transpose.mulVec (B.mulVec w.1.2)) +
    (A.transpose.mulVec w.2.2 + B.transpose.mulVec w.2.1), w.1.2),
    w.2 + (A.mulVec w.1.2, B.mulVec w.1.2))
  rw [hR, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  rw [add_comm (B.transpose.mulVec w.2.1) (A.transpose.mulVec w.2.2)]

theorem secondDifference_quad_eq_beta {t s : ℕ} (a b x : V t s) :
    secondDifference (quad t s) a b x = beta t s a b := by
  have h₁ := secondDifference_dot_pair a.1 b.1 x.1
  have h₂ := secondDifference_dot_pair a.2 b.2 x.2
  simp only [secondDifference, quad, hyperbolic, beta, polarZ,
    Prod.fst_add, Prod.snd_add] at h₁ h₂ ⊢
  linear_combination h₁ + h₂

theorem kernelLinear_preserves_beta {t s : ℕ} (p : KernelDatum t s) (v w : V t s) :
    beta t s (kernelLinearEquiv p v) (kernelLinearEquiv p w) = beta t s v w := by
  have hpres (x : V t s) : quad t s (kernelAffineEquiv p x) = quad t s x := by
    rw [kernelAffineEquiv_apply]
    exact kernelMap_preserves_quad p x
  have hh := secondDifference_affine (quad t s) (kernelAffineEquiv p) v w 0
  rw [secondDifference_congr hpres, secondDifference_quad_eq_beta,
    secondDifference_quad_eq_beta] at hh
  exact hh.symm

theorem kernelLinearEquiv_injective (t s : ℕ) :
    Function.Injective (kernelLinearEquiv : KernelDatum t s → V t s ≃ₗ[F₂] V t s) := by
  rintro ⟨⟨A,B⟩,S⟩ ⟨⟨A',B'⟩,S'⟩ heq
  have hA : A = A' := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,y),0)).2.1) heq
    simpa [kernelLinearEquiv, triangularLinearEquiv] using h
  have hB : B = B' := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,y),0)).2.2) heq
    simpa [kernelLinearEquiv, triangularLinearEquiv] using h
  subst A'
  subst B'
  have hS : S.1 = S'.1 := by
    apply matrix_eq_of_mulVec_eq
    intro y
    have h := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,y),0)).1.1) heq
    change (0 + (S.1.mulVec y + A.transpose.mulVec (B.mulVec y)) +
      (A.transpose.mulVec 0 + B.transpose.mulVec 0)) =
      (0 + (S'.1.mulVec y + A.transpose.mulVec (B.mulVec y)) +
      (A.transpose.mulVec 0 + B.transpose.mulVec 0)) at h
    simp only [Matrix.mulVec_zero, zero_add, add_zero] at h
    exact add_right_cancel h
  have hs : S = S' := Subtype.ext hS
  subst S'
  rfl

def inclX (t s : ℕ) : Y t →ₗ[F₂] V t s where
  toFun x := ((x,0),0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def inclY (t s : ℕ) : Y t →ₗ[F₂] V t s where
  toFun y := ((0,y),0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def inclU (t s : ℕ) : (Fin s → F₂) →ₗ[F₂] V t s where
  toFun u := ((0,0),(u,0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def inclV (t s : ℕ) : (Fin s → F₂) →ₗ[F₂] V t s where
  toFun v := ((0,0),(0,v))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def projX (t s : ℕ) : V t s →ₗ[F₂] Y t :=
  (LinearMap.fst F₂ _ _).comp (LinearMap.fst F₂ _ _)
def projU (t s : ℕ) : V t s →ₗ[F₂] (Fin s → F₂) :=
  (LinearMap.fst F₂ _ _).comp (LinearMap.snd F₂ _ _)
def projV (t s : ℕ) : V t s →ₗ[F₂] (Fin s → F₂) :=
  (LinearMap.snd F₂ _ _).comp (LinearMap.snd F₂ _ _)

def coefficientA {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) :=
  LinearMap.toMatrix' ((projU t s).comp (M.toLinearMap.comp (inclY t s)))
def coefficientB {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) :=
  LinearMap.toMatrix' ((projV t s).comp (M.toLinearMap.comp (inclY t s)))
def coefficientR {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) :=
  LinearMap.toMatrix' ((projX t s).comp (M.toLinearMap.comp (inclY t s)))
def coefficientC₁ {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) :=
  LinearMap.toMatrix' ((projX t s).comp (M.toLinearMap.comp (inclU t s)))
def coefficientC₂ {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) :=
  LinearMap.toMatrix' ((projX t s).comp (M.toLinearMap.comp (inclV t s)))

def IsNormalizedKernel {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) : Prop :=
  (∀ x, M ((x,0),0) = ((x,0),0)) ∧
  (∀ w, (M w).1.2 = w.1.2) ∧
  (∀ z, (M ((0,0),z)).2 = z) ∧
  (∀ v w, beta t s (M v) (M w) = beta t s v w)

theorem linear_four_decomposition {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s) (w : V t s) :
    M w = M (inclX t s w.1.1) + M (inclY t s w.1.2) +
      M (inclU t s w.2.1) + M (inclV t s w.2.2) := by
  rw [← map_add, ← map_add, ← map_add]
  congr 1
  ext <;> simp [inclX, inclY, inclU, inclV]

theorem normalizedKernel_eq_raw {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s)
    (h : IsNormalizedKernel M) :
    M = kernelRawLinear (coefficientA M) (coefficientB M) (coefficientR M)
      (coefficientC₁ M) (coefficientC₂ M) := by
  obtain ⟨hx, hy, hz, _⟩ := h
  apply LinearEquiv.ext
  intro w
  have hd := linear_four_decomposition M w
  change M w = M ((w.1.1,0),0) + M ((0,w.1.2),0) +
    M ((0,0),(w.2.1,0)) + M ((0,0),(0,w.2.2)) at hd
  rw [hx] at hd
  have hA y : (coefficientA M).mulVec y = (M ((0,y),0)).2.1 :=
    LinearMap.toMatrix'_mulVec _ _
  have hB y : (coefficientB M).mulVec y = (M ((0,y),0)).2.2 :=
    LinearMap.toMatrix'_mulVec _ _
  have hR y : (coefficientR M).mulVec y = (M ((0,y),0)).1.1 :=
    LinearMap.toMatrix'_mulVec _ _
  have hC₁ u : (coefficientC₁ M).mulVec u = (M ((0,0),(u,0))).1.1 :=
    LinearMap.toMatrix'_mulVec _ _
  have hC₂ v : (coefficientC₂ M).mulVec v = (M ((0,0),(0,v))).1.1 :=
    LinearMap.toMatrix'_mulVec _ _
  change M w = ((w.1.1 + (coefficientR M).mulVec w.1.2 +
    ((coefficientC₁ M).mulVec w.2.1 + (coefficientC₂ M).mulVec w.2.2),w.1.2),
    w.2 + ((coefficientA M).mulVec w.1.2,(coefficientB M).mulVec w.1.2))
  rw [hA,hB,hR,hC₁,hC₂]
  have hxu := congrArg (fun v : V t s => v.2.1) (hx w.1.1)
  have hxv := congrArg (fun v : V t s => v.2.2) (hx w.1.1)
  have huu := congrArg (fun z : Z s => z.1) (hz (w.2.1,0))
  have huv := congrArg (fun z : Z s => z.2) (hz (w.2.1,0))
  have hvu := congrArg (fun z : Z s => z.1) (hz (0,w.2.2))
  have hvv := congrArg (fun z : Z s => z.2) (hz (0,w.2.2))
  apply Prod.ext
  · apply Prod.ext
    · have hh := congrArg (fun v : V t s => v.1.1) hd
      change (M w).1.1 = w.1.1 + (M ((0,w.1.2),0)).1.1 +
        (M ((0,0),(w.2.1,0))).1.1 + (M ((0,0),(0,w.2.2))).1.1 at hh
      exact hh.trans (add_assoc _ _ _)
    · exact hy w
  · apply Prod.ext
    · have hh := congrArg (fun v : V t s => v.2.1) hd
      change (M w).2.1 = 0 + (M ((0,w.1.2),0)).2.1 +
        (M ((0,0),(w.2.1,0))).2.1 + (M ((0,0),(0,w.2.2))).2.1 at hh
      rw [huu, hvu, zero_add, add_zero] at hh
      exact hh.trans (add_comm _ _)
    · have hh := congrArg (fun v : V t s => v.2.2) hd
      change (M w).2.2 = 0 + (M ((0,w.1.2),0)).2.2 +
        (M ((0,0),(w.2.1,0))).2.2 + (M ((0,0),(0,w.2.2))).2.2 at hh
      rw [huv, hvv, zero_add, add_zero] at hh
      exact hh.trans (add_comm _ _)

theorem normalizedKernel_complete {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s)
    (h : IsNormalizedKernel M) :
    ∃ p : KernelDatum t s, M = kernelLinearEquiv p := by
  have heq := normalizedKernel_eq_raw M h
  have hb := h.2.2.2
  rw [heq] at hb
  obtain ⟨S,hS⟩ := kernelRaw_complete _ _ _ _ _ hb
  exact ⟨((coefficientA M,coefficientB M),S), heq.trans hS⟩

theorem kernelLinear_isNormalized {t s : ℕ} (p : KernelDatum t s) :
    IsNormalizedKernel (kernelLinearEquiv p) := by
  refine ⟨?_, ?_, ?_, kernelLinear_preserves_beta p⟩
  · intro x
    simp [kernelLinearEquiv, triangularLinearEquiv]
  · intro w
    rfl
  · intro z
    simp [kernelLinearEquiv, triangularLinearEquiv]

abbrev NormalizedKernel (t s : ℕ) :=
  {M : V t s ≃ₗ[F₂] V t s // IsNormalizedKernel M}

noncomputable def kernelDatumEquivNormalized (t s : ℕ) :
    KernelDatum t s ≃ NormalizedKernel t s :=
  Equiv.ofBijective (fun p => ⟨kernelLinearEquiv p, kernelLinear_isNormalized p⟩) (by
    constructor
    · intro p q h
      exact kernelLinearEquiv_injective t s (congrArg Subtype.val h)
    · intro M
      obtain ⟨p,hp⟩ := normalizedKernel_complete M.1 M.2
      exact ⟨p, Subtype.ext hp.symm⟩)

theorem card_normalizedKernel (t s : ℕ) :
    Nat.card (NormalizedKernel t s) = 2 ^ ((3*t)*(3*t+1)/2 + 6*t*s) := by
  rw [← Nat.card_congr (kernelDatumEquivNormalized t s), card_kernelDatum]

end ParabolicKernel
end CubicBentAutomorphisms
end


/-! ## Contragredient actions -/

section
namespace CubicBentAutomorphisms

/-- The inverse-transpose action, constructed without choosing matrix entries. -/
def dualAction {t : ℕ} (D : Y t ≃ₗ[F₂] Y t) : Y t ≃ₗ[F₂] Y t :=
  (dotProductEquiv F₂ (Fin t × Fin 3)).trans
    (D.symm.dualMap.trans (dotProductEquiv F₂ (Fin t × Fin 3)).symm)

theorem dualAction_pairing {t : ℕ} (D : Y t ≃ₗ[F₂] Y t) (x y : Y t) :
    dot (dualAction D x) (D y) = dot x y := by
  change (dotProductEquiv F₂ (Fin t × Fin 3) (dualAction D x)) (D y) = _
  simp [dualAction, LinearEquiv.dualMap_apply, dot, dotProduct]

/-- The dual action is uniquely forced by preservation of the X/Y pairing. -/
theorem dualAction_unique {t : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (h : ∀ x y, dot (P x) (D y) = dot x y) : P = dualAction D := by
  apply LinearEquiv.ext
  intro x
  apply (dotProductEquiv F₂ (Fin t × Fin 3)).injective
  apply LinearMap.ext
  intro z
  change dot (P x) z = dot (dualAction D x) z
  obtain ⟨y, rfl⟩ := D.surjective z
  rw [h, dualAction_pairing]

@[simp] theorem dualAction_refl (t : ℕ) :
    dualAction (LinearEquiv.refl F₂ (Y t)) = LinearEquiv.refl F₂ (Y t) := by
  symm
  apply dualAction_unique
  intro x y
  rfl

theorem dualAction_trans {t : ℕ} (D E : Y t ≃ₗ[F₂] Y t) :
    dualAction (D.trans E) = (dualAction D).trans (dualAction E) := by
  symm
  apply dualAction_unique
  intro x y
  change dot (dualAction E (dualAction D x)) (E (D y)) = dot x y
  rw [dualAction_pairing, dualAction_pairing]

@[simp] theorem dualAction_symm {t : ℕ} (D : Y t ≃ₗ[F₂] Y t) :
    dualAction D.symm = (dualAction D).symm := by
  symm
  apply dualAction_unique
  intro x y
  have hh := dualAction_pairing D ((dualAction D).symm x) (D.symm y)
  simpa using hh.symm


end CubicBentAutomorphisms
end


/-! ## Complete parabolic decomposition -/

section
open QuadraticAffineIsometries
namespace CubicBentAutomorphisms

abbrev SmallSymplectic (s : ℕ) :=
  {F : Z s ≃ₗ[F₂] Z s // ∀ a b, polarZ s (F a) (F b) = polarZ s a b}

def includeZ (t s : ℕ) : Z s →ₗ[F₂] V t s where
  toFun z := ((0,0),z)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def AdaptedPolar.zMap {t s : ℕ} (e : AdaptedPolar t s) : Z s →ₗ[F₂] Z s :=
  (LinearMap.snd F₂ _ _).comp (e.linear.toLinearMap.comp (includeZ t s))

theorem quadPolar_eq_kernelBeta (t s : ℕ) (a b : V t s) :
    quadPolar t s a b = ParabolicKernel.beta t s a b := by
  simp [quadPolar_apply, QuadraticAffineIsometries.beta, ParabolicKernel.beta,
    polarZ, add_assoc]

theorem AdaptedPolar.zMap_preserves {t s : ℕ} (e : AdaptedPolar t s) (a b : Z s) :
    polarZ s (e.zMap a) (e.zMap b) = polarZ s a b := by
  have h := e.polar (includeZ t s a) (includeZ t s b)
  have ha := e.map_y (includeZ t s a)
  have hb := e.map_y (includeZ t s b)
  change polarZ s (e.linear (includeZ t s a)).2 (e.linear (includeZ t s b)).2 = _
  simp only [includeZ, LinearMap.coe_mk, AddHom.coe_mk, map_zero] at ha hb
  simpa only [quadPolar_eq_kernelBeta, ParabolicKernel.beta, ha, hb,
    dot_zero_left, dot_zero_right, zero_add, includeZ, LinearMap.coe_mk,
    AddHom.coe_mk] using h

theorem AdaptedPolar.zMap_injective {t s : ℕ} (e : AdaptedPolar t s) :
    Function.Injective e.zMap := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  apply (polarZ_nondegenerate s z).mp
  intro w
  rw [← e.zMap_preserves, hz]
  simp [polarZ]

noncomputable def AdaptedPolar.zEquiv {t s : ℕ} (e : AdaptedPolar t s) :
    Z s ≃ₗ[F₂] Z s :=
  LinearEquiv.ofBijective e.zMap ((Finite.injective_iff_bijective).mp e.zMap_injective)

noncomputable def AdaptedPolar.zSymplectic {t s : ℕ} (e : AdaptedPolar t s) :
    SmallSymplectic s := ⟨e.zEquiv, e.zMap_preserves⟩

def leviLinear {t s : ℕ} (P D : Y t ≃ₗ[F₂] Y t) (F : Z s ≃ₗ[F₂] Z s) :
    V t s ≃ₗ[F₂] V t s := (P.prodCongr D).prodCongr F

@[simp] theorem leviLinear_apply {t s : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (F : Z s ≃ₗ[F₂] Z s) (w : V t s) :
    leviLinear P D F w = ((P w.1.1, D w.1.2),F w.2) := rfl

theorem leviLinear_preserves {t s : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (F : SmallSymplectic s) (hp : ∀ x y, dot (P x) (D y) = dot x y)
    (a b : V t s) :
    quadPolar t s (leviLinear P D F.1 a) (leviLinear P D F.1 b) = quadPolar t s a b := by
  simp only [quadPolar_eq_kernelBeta, ParabolicKernel.beta, leviLinear_apply, hp, F.2]

theorem leviLinear_symm_preserves {t s : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (F : SmallSymplectic s) (hp : ∀ x y, dot (P x) (D y) = dot x y)
    (a b : V t s) :
    quadPolar t s ((leviLinear P D F.1).symm a) ((leviLinear P D F.1).symm b) =
      quadPolar t s a b := by
  simpa using (leviLinear_preserves P D F hp
    ((leviLinear P D F.1).symm a) ((leviLinear P D F.1).symm b)).symm

noncomputable def AdaptedPolar.normalized {t s : ℕ} (e : AdaptedPolar t s) :
    V t s ≃ₗ[F₂] V t s :=
  e.linear.trans (leviLinear e.xAction e.yAction e.zEquiv).symm

theorem AdaptedPolar.normalized_isKernel {t s : ℕ} (e : AdaptedPolar t s) :
    ParabolicKernel.IsNormalizedKernel e.normalized := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change (leviLinear e.xAction e.yAction e.zEquiv).symm
      (e.linear (includeX t s x)) = _
    rw [e.map_x]
    change ((e.xAction.symm (e.xAction x), e.yAction.symm 0), e.zEquiv.symm 0) = _
    simp
  · intro w
    change e.yAction.symm (e.linear w).1.2 = w.1.2
    rw [e.map_y, e.yAction.symm_apply_apply]
  · intro z
    change e.zEquiv.symm (e.zEquiv z) = z
    exact e.zEquiv.symm_apply_apply z
  · intro a b
    simp only [← quadPolar_eq_kernelBeta]
    change quadPolar t s
      ((leviLinear e.xAction e.yAction e.zEquiv).symm (e.linear a))
      ((leviLinear e.xAction e.yAction e.zEquiv).symm (e.linear b)) = _
    exact (leviLinear_symm_preserves e.xAction e.yAction e.zSymplectic e.pairing
      (e.linear a) (e.linear b)).trans (e.polar a b)

abbrev ParabolicParameters (t s : ℕ) :=
  CubicTensorStabilizer t × SmallSymplectic s × ParabolicKernel.NormalizedKernel t s

def parametersToPolar {t s : ℕ} (p : ParabolicParameters t s) : AdaptedPolar t s where
  linear := p.2.2.1.trans (leviLinear (dualAction p.1.1) p.1.1 p.2.1.1)
  xAction := dualAction p.1.1
  yAction := p.1.1
  map_x x := by
    change leviLinear _ _ _ (p.2.2.1 ((x,0),0)) = _
    rw [p.2.2.2.1]
    simp [includeX]
  map_y w := by
    change p.1.1 (p.2.2.1 w).1.2 = p.1.1 w.1.2
    rw [p.2.2.2.2.1]
  pairing := dualAction_pairing p.1.1
  tensor := p.1.2
  polar a b := by
    change quadPolar t s (leviLinear _ _ _ (p.2.2.1 a))
      (leviLinear _ _ _ (p.2.2.1 b)) = _
    rw [leviLinear_preserves _ _ p.2.1 (dualAction_pairing p.1.1)]
    simp only [quadPolar_eq_kernelBeta]
    exact p.2.2.2.2.2.2 a b

theorem parametersToPolar_injective (t s : ℕ) :
    Function.Injective (parametersToPolar : ParabolicParameters t s → AdaptedPolar t s) := by
  rintro ⟨D,F,K⟩ ⟨D',F',K'⟩ he
  have hD : D = D' := Subtype.ext (congrArg AdaptedPolar.yAction he)
  subst D'
  have hlin := congrArg AdaptedPolar.linear he
  have hF : F = F' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    have hh := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,0),z)).2) hlin
    change F.1 (K.1 ((0,0),z)).2 = F'.1 (K'.1 ((0,0),z)).2 at hh
    simpa only [K.2.2.2.1, K'.2.2.2.1] using hh
  subst F'
  have hK : K = K' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply (leviLinear (dualAction D.1) D.1 F.1).injective
    exact congrArg (fun L : V t s ≃ₗ[F₂] V t s => L w) hlin
  subst K'
  rfl

theorem parametersToPolar_surjective (t s : ℕ) :
    Function.Surjective (parametersToPolar : ParabolicParameters t s → AdaptedPolar t s) := by
  intro e
  refine ⟨(⟨e.yAction,e.tensor⟩,e.zSymplectic,⟨e.normalized,e.normalized_isKernel⟩), ?_⟩
  apply AdaptedPolar.ext_linear
  apply LinearEquiv.ext
  intro w
  have hp := dualAction_unique e.xAction e.yAction e.pairing
  change leviLinear (dualAction e.yAction) e.yAction e.zEquiv
    ((leviLinear e.xAction e.yAction e.zEquiv).symm (e.linear w)) = e.linear w
  rw [← hp]
  exact (leviLinear e.xAction e.yAction e.zEquiv).apply_symm_apply _

/-- The complete parameterization: no restriction to a chosen subgroup is imposed. -/
noncomputable def parabolicParametersEquiv (t s : ℕ) :
    ParabolicParameters t s ≃ AdaptedPolar t s :=
  Equiv.ofBijective parametersToPolar
    ⟨parametersToPolar_injective t s,parametersToPolar_surjective t s⟩

theorem card_affineStabilizer_factors (t s : ℕ) :
    Nat.card (AffineStabilizer t s) =
      (168^t * Nat.factorial t) * Nat.card (SmallSymplectic s) *
        2^((3*t)*(3*t+1)/2 + 6*t*s) := by
  rw [card_affineBent_eq_adaptedPolar,
    ← Nat.card_congr (parabolicParametersEquiv t s)]
  simp only [ParabolicParameters, Nat.card_prod, card_cubicTensorStabilizer,
    ParabolicKernel.card_normalizedKernel]
  ring


end CubicBentAutomorphisms
end


/-! ## Multiplicative parabolic structure -/

section
open QuadraticAffineIsometries
namespace CubicBentAutomorphisms
namespace ParabolicGroup

def affineSubgroup (t s : ℕ) : Subgroup (V t s ≃ᵃ[F₂] V t s) where
  carrier := {e | ∀ w, bentFamily t s (e w) = bentFamily t s w}
  one_mem' := by intro w; rfl
  mul_mem' {e f} he hf w := (he (f w)).trans (hf w)
  inv_mem' {e} he w := by
    change bentFamily t s (e.symm w) = bentFamily t s w
    have h := he (e.symm w)
    simpa using h.symm

instance affineStabilizerGroup (t s : ℕ) : Group (AffineStabilizer t s) :=
  inferInstanceAs (Group (affineSubgroup t s))

def cubicSubgroup (t : ℕ) : Subgroup (Y t ≃ₗ[F₂] Y t) where
  carrier := {D | ∀ a b c, cubicTensor t (D a) (D b) (D c) = cubicTensor t a b c}
  one_mem' := by intro a b c; rfl
  mul_mem' hD hE a b c := (hD _ _ _).trans (hE a b c)
  inv_mem' {D} hD a b c := by
    simpa using (hD (D.symm a) (D.symm b) (D.symm c)).symm

instance cubicStabilizerGroup (t : ℕ) : Group (CubicTensorStabilizer t) :=
  inferInstanceAs (Group (cubicSubgroup t))

def smallSymplecticSubgroup (s : ℕ) : Subgroup (Z s ≃ₗ[F₂] Z s) where
  carrier := {F | ∀ a b, polarZ s (F a) (F b) = polarZ s a b}
  one_mem' := by intro a b; rfl
  mul_mem' hF hG a b := (hF _ _).trans (hG a b)
  inv_mem' {F} hF a b := by
    simpa using (hF (F.symm a) (F.symm b)).symm

instance smallSymplecticGroup (s : ℕ) : Group (SmallSymplectic s) :=
  inferInstanceAs (Group (smallSymplecticSubgroup s))

theorem normalized_z_of_y_zero {t s : ℕ} (M : V t s ≃ₗ[F₂] V t s)
    (hM : ParabolicKernel.IsNormalizedKernel M) (w : V t s) (hy : w.1.2 = 0) :
    (M w).2 = w.2 := by
  have hw : w = ((w.1.1,0),0) + ((0,0),w.2) := by
    ext <;> simp [hy]
  conv_lhs => rw [hw, map_add, hM.1]
  change 0 + (M ((0,0),w.2)).2 = w.2
  rw [zero_add,hM.2.2.1]

def normalizedSubgroup (t s : ℕ) : Subgroup (V t s ≃ₗ[F₂] V t s) where
  carrier := {M | ParabolicKernel.IsNormalizedKernel M}
  one_mem' := by refine ⟨?_,?_,?_,?_⟩ <;> intros <;> rfl
  mul_mem' {M N} hM hN := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      change M (N ((x,0),0)) = _
      rw [hN.1,hM.1]
    · intro w
      change (M (N w)).1.2 = _
      rw [hM.2.1,hN.2.1]
    · intro z
      change (M (N ((0,0),z))).2 = z
      rw [normalized_z_of_y_zero M hM _ (hN.2.1 _),hN.2.2.1]
    · intro v w
      exact (hM.2.2.2 _ _).trans (hN.2.2.2 v w)
  inv_mem' {M} hM := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      apply M.injective
      change M (M.symm ((x,0),0)) = M ((x,0),0)
      rw [M.apply_symm_apply,hM.1]
    · intro w
      have h := hM.2.1 (M.symm w)
      simpa using h.symm
    · intro z
      have hy : (M.symm ((0,0),z)).1.2 = 0 := by
        have h := hM.2.1 (M.symm ((0,0),z))
        simpa using h.symm
      have hz := normalized_z_of_y_zero M hM (M.symm ((0,0),z)) hy
      simpa using hz.symm
    · intro v w
      simpa using (hM.2.2.2 (M.symm v) (M.symm w)).symm

instance normalizedKernelGroup (t s : ℕ) : Group (ParabolicKernel.NormalizedKernel t s) :=
  inferInstanceAs (Group (normalizedSubgroup t s))

def adaptedOne (t s : ℕ) : AdaptedPolar t s where
  linear := 1
  xAction := 1
  yAction := 1
  map_x _ := rfl
  map_y _ := rfl
  pairing _ _ := rfl
  tensor _ _ _ := rfl
  polar _ _ := rfl

def adaptedMul {t s : ℕ} (e f : AdaptedPolar t s) : AdaptedPolar t s where
  linear := e.linear * f.linear
  xAction := e.xAction * f.xAction
  yAction := e.yAction * f.yAction
  map_x x := by
    change e.linear (f.linear (includeX t s x)) = includeX t s (e.xAction (f.xAction x))
    rw [f.map_x,e.map_x]
  map_y w := by
    change (e.linear (f.linear w)).1.2 = e.yAction (f.yAction w.1.2)
    rw [e.map_y,f.map_y]
  pairing x y := (e.pairing _ _).trans (f.pairing x y)
  tensor a b c := (e.tensor _ _ _).trans (f.tensor a b c)
  polar a b := (e.polar _ _).trans (f.polar a b)

def adaptedInv {t s : ℕ} (e : AdaptedPolar t s) : AdaptedPolar t s where
  linear := e.linear.symm
  xAction := e.xAction.symm
  yAction := e.yAction.symm
  map_x x := by
    apply e.linear.injective
    rw [e.linear.apply_symm_apply,e.map_x,e.xAction.apply_symm_apply]
  map_y w := by
    apply e.yAction.injective
    have h := e.map_y (e.linear.symm w)
    simpa using h.symm
  pairing x y := by simpa using (e.pairing (e.xAction.symm x) (e.yAction.symm y)).symm
  tensor a b c := by simpa using
    (e.tensor (e.yAction.symm a) (e.yAction.symm b) (e.yAction.symm c)).symm
  polar a b := by simpa using (e.polar (e.linear.symm a) (e.linear.symm b)).symm

def adaptedSubgroup (t s : ℕ) : Subgroup (V t s ≃ₗ[F₂] V t s) where
  carrier := {M | ∃ e : AdaptedPolar t s, e.linear = M}
  one_mem' := ⟨adaptedOne t s,rfl⟩
  mul_mem' := by rintro M N ⟨e,rfl⟩ ⟨f,rfl⟩; exact ⟨adaptedMul e f,rfl⟩
  inv_mem' := by rintro M ⟨e,rfl⟩; exact ⟨adaptedInv e,rfl⟩

noncomputable def adaptedEquivSubgroup (t s : ℕ) : AdaptedPolar t s ≃ adaptedSubgroup t s where
  toFun e := ⟨e.linear,e,rfl⟩
  invFun M := M.2.choose
  left_inv e := AdaptedPolar.ext_linear (Exists.choose_spec (show ∃ f, f.linear = e.linear from ⟨e,rfl⟩))
  right_inv M := Subtype.ext M.2.choose_spec

noncomputable instance adaptedPolarGroup (t s : ℕ) : Group (AdaptedPolar t s) :=
  (adaptedEquivSubgroup t s).group

@[simp] theorem adapted_linear_mul {t s : ℕ} (e f : AdaptedPolar t s) :
    (e * f).linear = e.linear * f.linear :=
  congrArg Subtype.val ((adaptedEquivSubgroup t s).apply_symm_apply
    ((adaptedEquivSubgroup t s e) * (adaptedEquivSubgroup t s f)))

@[simp] theorem adapted_linear_one (t s : ℕ) : (1 : AdaptedPolar t s).linear = 1 :=
  congrArg Subtype.val ((adaptedEquivSubgroup t s).apply_symm_apply 1)

@[simp] theorem adapted_linear_inv {t s : ℕ} (e : AdaptedPolar t s) :
    e⁻¹.linear = e.linear⁻¹ :=
  congrArg Subtype.val ((adaptedEquivSubgroup t s).apply_symm_apply
    (adaptedEquivSubgroup t s e)⁻¹)

abbrev Levi (t s : ℕ) := CubicTensorStabilizer t × SmallSymplectic s

theorem dualAction_mul {t : ℕ} (D E : Y t ≃ₗ[F₂] Y t) :
    dualAction (D * E) = dualAction D * dualAction E := dualAction_trans E D

def leviHom (t s : ℕ) : Levi t s →* (V t s ≃ₗ[F₂] V t s) where
  toFun g := leviLinear (dualAction g.1.1) g.1.1 g.2.1
  map_one' := by
    change leviLinear (dualAction (LinearEquiv.refl F₂ (Y t)))
      (LinearEquiv.refl F₂ (Y t)) (LinearEquiv.refl F₂ (Z s)) = 1
    rw [dualAction_refl]
    rfl
  map_mul' g h := by
    change leviLinear (dualAction (g.1.1 * h.1.1)) (g.1.1 * h.1.1)
      (g.2.1 * h.2.1) = _
    rw [dualAction_mul]
    rfl

def kernelToAdapted {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s) : AdaptedPolar t s where
  linear := K.1
  xAction := 1
  yAction := 1
  map_x := K.2.1
  map_y := K.2.2.1
  pairing _ _ := rfl
  tensor _ _ _ := rfl
  polar a b := by simpa only [quadPolar_eq_kernelBeta] using K.2.2.2.2 a b

noncomputable def kernelInclusion (t s : ℕ) :
    ParabolicKernel.NormalizedKernel t s →* AdaptedPolar t s where
  toFun := kernelToAdapted
  map_one' := AdaptedPolar.ext_linear (adapted_linear_one t s).symm
  map_mul' a b := by
    apply AdaptedPolar.ext_linear
    change a.1 * b.1 = (kernelToAdapted a * kernelToAdapted b).linear
    exact (adapted_linear_mul (kernelToAdapted a) (kernelToAdapted b)).symm

def leviToAdapted {t s : ℕ} (g : Levi t s) : AdaptedPolar t s where
  linear := leviHom t s g
  xAction := dualAction g.1.1
  yAction := g.1.1
  map_x x := by simp [leviHom,leviLinear_apply,includeX]
  map_y _ := rfl
  pairing := dualAction_pairing g.1.1
  tensor := g.1.2
  polar := leviLinear_preserves _ _ g.2 (dualAction_pairing g.1.1)

noncomputable def leviInclusion (t s : ℕ) : Levi t s →* AdaptedPolar t s where
  toFun := leviToAdapted
  map_one' := by
    apply AdaptedPolar.ext_linear
    change leviHom t s 1 = (1 : AdaptedPolar t s).linear
    rw [map_one,adapted_linear_one]
  map_mul' a b := by
    apply AdaptedPolar.ext_linear
    change leviHom t s (a*b) = (leviToAdapted a * leviToAdapted b).linear
    rw [map_mul,adapted_linear_mul]
    rfl

@[simp] theorem leviLinear_symm_apply {t s : ℕ} (P D : Y t ≃ₗ[F₂] Y t)
    (F : Z s ≃ₗ[F₂] Z s) (w : V t s) :
    (leviLinear P D F).symm w = ((P.symm w.1.1,D.symm w.1.2),F.symm w.2) := rfl

def leviConjugate {t s : ℕ} (g : Levi t s)
    (K : ParabolicKernel.NormalizedKernel t s) : ParabolicKernel.NormalizedKernel t s :=
  ⟨leviHom t s g * K.1 * (leviHom t s g)⁻¹, by
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      change leviLinear _ _ _ (K.1 ((leviLinear _ _ _).symm ((x,0),0))) = _
      rw [leviLinear_symm_apply]
      simp only [map_zero,K.2.1,leviLinear_apply,LinearEquiv.apply_symm_apply]
    · intro w
      change g.1.1 (K.1 ((leviHom t s g)⁻¹ w)).1.2 = w.1.2
      rw [K.2.2.1]
      exact g.1.1.apply_symm_apply _
    · intro z
      change g.2.1 (K.1 ((leviLinear _ _ _).symm ((0,0),z))).2 = z
      rw [leviLinear_symm_apply]
      simp only [map_zero,K.2.2.2.1,LinearEquiv.apply_symm_apply]
    · intro a b
      simp only [← quadPolar_eq_kernelBeta]
      change quadPolar t s (leviLinear _ _ _ (K.1 ((leviLinear _ _ _).symm a)))
        (leviLinear _ _ _ (K.1 ((leviLinear _ _ _).symm b))) = _
      rw [leviLinear_preserves _ _ g.2 (dualAction_pairing g.1.1),
        quadPolar_eq_kernelBeta,K.2.2.2.2,← quadPolar_eq_kernelBeta]
      exact leviLinear_symm_preserves _ _ g.2 (dualAction_pairing g.1.1) a b⟩

def leviAction (t s : ℕ) : Levi t s →* MulAut (ParabolicKernel.NormalizedKernel t s) where
  toFun g :=
    { toFun := leviConjugate g
      invFun := leviConjugate g⁻¹
      left_inv K := by
        apply Subtype.ext
        change (leviHom t s g⁻¹) * ((leviHom t s g) * K.1 * (leviHom t s g)⁻¹) *
          (leviHom t s g⁻¹)⁻¹ = K.1
        rw [map_inv]
        simp [mul_assoc]
      right_inv K := by
        apply Subtype.ext
        change (leviHom t s g) * ((leviHom t s g⁻¹) * K.1 * (leviHom t s g⁻¹)⁻¹) *
          (leviHom t s g)⁻¹ = K.1
        rw [map_inv]
        simp [mul_assoc]
      map_mul' K L := by
        apply Subtype.ext
        change (leviHom t s g) * (K.1 * L.1) * (leviHom t s g)⁻¹ =
          ((leviHom t s g) * K.1 * (leviHom t s g)⁻¹) *
          ((leviHom t s g) * L.1 * (leviHom t s g)⁻¹)
        simp [mul_assoc] }
  map_one' := by
    apply MulEquiv.ext
    intro K
    apply Subtype.ext
    change leviHom t s 1 * K.1 * (leviHom t s 1)⁻¹ = K.1
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro K
    apply Subtype.ext
    change leviHom t s (g*h) * K.1 * (leviHom t s (g*h))⁻¹ =
      (leviHom t s g) * ((leviHom t s h) * K.1 * (leviHom t s h)⁻¹) *
        (leviHom t s g)⁻¹
    simp [mul_assoc]

abbrev ExplicitSemidirect (t s : ℕ) :=
  ParabolicKernel.NormalizedKernel t s ⋊[leviAction t s] Levi t s

noncomputable def semidirectToAdapted (t s : ℕ) : ExplicitSemidirect t s →* AdaptedPolar t s :=
  SemidirectProduct.lift (kernelInclusion t s) (leviInclusion t s) (by
    intro g
    ext K
    apply AdaptedPolar.ext_linear
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      adapted_linear_mul,adapted_linear_inv]
    rfl)

@[simp] theorem semidirectToAdapted_linear {t s : ℕ} (p : ExplicitSemidirect t s) :
    (semidirectToAdapted t s p).linear = p.left.1 * leviHom t s p.right := by
  change (kernelToAdapted p.left * leviToAdapted p.right).linear = _
  rw [adapted_linear_mul]
  rfl

theorem semidirectToAdapted_injective (t s : ℕ) :
    Function.Injective (semidirectToAdapted t s) := by
  intro p q he
  have hh := congrArg AdaptedPolar.linear he
  rw [semidirectToAdapted_linear,semidirectToAdapted_linear] at hh
  have hD : p.right.1 = q.right.1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have h := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,y),0)).1.2) hh
    change (p.left.1 (leviHom t s p.right ((0,y),0))).1.2 =
      (q.left.1 (leviHom t s q.right ((0,y),0))).1.2 at h
    rw [p.left.2.2.1,q.left.2.2.1] at h
    exact h
  have hF : p.right.2 = q.right.2 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    have h := congrArg (fun L : V t s ≃ₗ[F₂] V t s => (L ((0,0),z)).2) hh
    change (p.left.1 ((dualAction p.right.1.1 0,p.right.1.1 0),p.right.2.1 z)).2 =
      (q.left.1 ((dualAction q.right.1.1 0,q.right.1.1 0),q.right.2.1 z)).2 at h
    simpa only [map_zero,p.left.2.2.2.1,q.left.2.2.2.1] using h
  have hg : p.right = q.right := Prod.ext hD hF
  have hk : p.left = q.left := by
    apply Subtype.ext
    rw [hg] at hh
    exact mul_right_cancel hh
  exact SemidirectProduct.ext hk hg

theorem semidirectToAdapted_surjective (t s : ℕ) :
    Function.Surjective (semidirectToAdapted t s) := by
  intro e
  obtain ⟨⟨D,F,K⟩,he⟩ := parametersToPolar_surjective t s e
  let g : Levi t s := (D,F)
  refine ⟨⟨leviConjugate g K,g⟩,?_⟩
  rw [← he]
  apply AdaptedPolar.ext_linear
  rw [semidirectToAdapted_linear]
  change ((leviHom t s g) * K.1 * (leviHom t s g)⁻¹) * (leviHom t s g) =
    (leviHom t s g) * K.1
  simp [mul_assoc]

noncomputable def semidirectMulEquivAdapted (t s : ℕ) :
    ExplicitSemidirect t s ≃* AdaptedPolar t s :=
  MulEquiv.ofBijective (semidirectToAdapted t s)
    ⟨semidirectToAdapted_injective t s,semidirectToAdapted_surjective t s⟩

theorem affineConjugate_mul {t s : ℕ} (e f : AffineStabilizer t s) :
    shearConjugateAffine (stabilizerAdapted (e*f)) =
      shearConjugateAffine (stabilizerAdapted e) *
      shearConjugateAffine (stabilizerAdapted f) := by
  apply AffineEquiv.ext
  intro w
  change shear t s (e.1 (f.1 (shear t s w))) =
    shear t s (e.1 (shear t s (shear t s (f.1 (shear t s w)))))
  rw [shear_involutive]

noncomputable def affineBentMulEquivAdapted (t s : ℕ) :
    AffineStabilizer t s ≃* AdaptedPolar t s where
  toEquiv := affineBentEquivAdaptedPolar t s
  map_mul' e f := by
    apply AdaptedPolar.ext_linear
    rw [adapted_linear_mul]
    exact congrArg AffineEquiv.linear (affineConjugate_mul e f)

/-- The full affine stabilizer, with its ordinary composition law, is the
explicit semidirect product of the normalized kernel by the cubic and
symplectic Levi factors. -/
noncomputable def affineStabilizerMulEquivSemidirect (t s : ℕ) :
    AffineStabilizer t s ≃* ExplicitSemidirect t s :=
  (affineBentMulEquivAdapted t s).trans (semidirectMulEquivAdapted t s).symm

def kernelE {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s) : Y t →ₗ[F₂] Z s :=
  (LinearMap.snd F₂ _ _).comp (K.1.toLinearMap.comp (includeY t s))

def kernelB {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s) : Y t →ₗ[F₂] Y t :=
  (ParabolicKernel.projX t s).comp (K.1.toLinearMap.comp (includeY t s))

def kernelC {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s) : Z s →ₗ[F₂] Y t :=
  (ParabolicKernel.projX t s).comp (K.1.toLinearMap.comp (includeZ t s))

theorem kernel_formula {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s) (w : V t s) :
    K.1 w = ((w.1.1 + kernelB K w.1.2 + kernelC K w.2,w.1.2),
      w.2 + kernelE K w.1.2) := by
  have hw : w = ((w.1.1,0),0) + ((0,w.1.2),0) + ((0,0),w.2) := by
    ext <;> simp
  have hd := congrArg K.1 hw
  rw [map_add,map_add,K.2.1] at hd
  apply Prod.ext
  · apply Prod.ext
    · have hx := congrArg (fun v : V t s => v.1.1) hd
      change (K.1 w).1.1 = w.1.1 + kernelB K w.1.2 + kernelC K w.2 at hx
      exact hx
    · exact K.2.2.1 w
  · have hh := congrArg (fun v : V t s => v.2) hd
    change (K.1 w).2 = 0 + kernelE K w.1.2 + (K.1 ((0,0),w.2)).2 at hh
    rw [zero_add,K.2.2.2.1] at hh
    exact hh.trans (add_comm _ _)

/-- The cross map is exactly the adjoint `EᵀJ`, expressed without a chosen
matrix convention. -/
theorem kernelC_pairing {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s)
    (z : Z s) (y : Y t) :
    dot (kernelC K z) y = polarZ s (kernelE K y) z := by
  have hh := K.2.2.2.2 ((0,y),0) ((0,0),z)
  rw [kernel_formula,kernel_formula] at hh
  have hp : dot (kernelC K z) y + polarZ s (kernelE K y) z = 0 := by
    simpa [ParabolicKernel.beta,polarZ,dot] using hh
  have hz := add_self_F₂ (polarZ s (kernelE K y) z)
  linear_combination hp - hz

/-- The complete quadratic coefficient relation `B+Bᵀ=EᵀJE`. -/
theorem kernelB_constraint {t s : ℕ} (K : ParabolicKernel.NormalizedKernel t s)
    (u v : Y t) :
    dot (kernelB K u) v + dot (kernelB K v) u =
      polarZ s (kernelE K u) (kernelE K v) := by
  have hh := K.2.2.2.2 ((0,u),0) ((0,v),0)
  rw [kernel_formula,kernel_formula] at hh
  have hp : dot (kernelB K u) v + dot (kernelB K v) u +
      polarZ s (kernelE K u) (kernelE K v) = 0 := by
    simpa [ParabolicKernel.beta,polarZ,dot] using hh
  have hz := add_self_F₂ (polarZ s (kernelE K u) (kernelE K v))
  linear_combination hp - hz

@[simp] theorem kernelE_mul {t s : ℕ} (K L : ParabolicKernel.NormalizedKernel t s) :
    kernelE (K*L) = kernelE K + kernelE L := by
  apply LinearMap.ext
  intro y
  change (K.1 (L.1 ((0,y),0))).2 = kernelE K y + kernelE L y
  rw [kernel_formula K,kernel_formula L]
  change (0 + kernelE L y) + kernelE K y = _
  rw [zero_add,add_comm]

/-- Concrete kernel multiplication: `(E,B)(E',B') =
`(E+E', B+B'+EᵀJE')`. The adjoint in the cocycle is certified by
`kernelC_pairing`. -/
@[simp] theorem kernelB_mul {t s : ℕ} (K L : ParabolicKernel.NormalizedKernel t s) :
    kernelB (K*L) = kernelB K + kernelB L + (kernelC K).comp (kernelE L) := by
  apply LinearMap.ext
  intro y
  change (K.1 (L.1 ((0,y),0))).1.1 =
    kernelB K y + kernelB L y + kernelC K (kernelE L y)
  rw [kernel_formula K,kernel_formula L]
  change (0 + kernelB L y + kernelC L 0) + kernelB K y +
    kernelC K (0 + kernelE L y) = _
  rw [map_zero,zero_add,add_zero,zero_add]
  rw [add_comm (kernelB L y) (kernelB K y)]

theorem kernel_coordinates_injective (t s : ℕ) :
    Function.Injective (fun K : ParabolicKernel.NormalizedKernel t s =>
      (kernelE K,kernelB K)) := by
  intro K L h
  have he := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change kernelE K = kernelE L at he
  change kernelB K = kernelB L at hb
  have hc : kernelC K = kernelC L := by
    apply LinearMap.ext
    intro z
    apply (dotProductEquiv F₂ (Fin t × Fin 3)).injective
    apply LinearMap.ext
    intro y
    change dot (kernelC K z) y = dot (kernelC L z) y
    rw [kernelC_pairing,kernelC_pairing,he]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  rw [kernel_formula,kernel_formula,he,hb,hc]

/-- Explicit Levi conjugation `E ↦ F E D⁻¹`. -/
theorem leviAction_kernelE {t s : ℕ} (g : Levi t s)
    (K : ParabolicKernel.NormalizedKernel t s) :
    kernelE (leviAction t s g K) =
      g.2.1.toLinearMap.comp ((kernelE K).comp g.1.1.symm.toLinearMap) := by
  apply LinearMap.ext
  intro y
  change g.2.1 (K.1 (((dualAction g.1.1).symm 0,g.1.1.symm y),g.2.1.symm 0)).2 =
    g.2.1 (kernelE K (g.1.1.symm y))
  simp only [map_zero]
  rfl

/-- Explicit Levi conjugation `B ↦ D⁻ᵀ B D⁻¹`. -/
theorem leviAction_kernelB {t s : ℕ} (g : Levi t s)
    (K : ParabolicKernel.NormalizedKernel t s) :
    kernelB (leviAction t s g K) =
      (dualAction g.1.1).toLinearMap.comp ((kernelB K).comp g.1.1.symm.toLinearMap) := by
  apply LinearMap.ext
  intro y
  change dualAction g.1.1 (K.1 (((dualAction g.1.1).symm 0,g.1.1.symm y),g.2.1.symm 0)).1.1 =
    dualAction g.1.1 (kernelB K (g.1.1.symm y))
  simp only [map_zero]
  rfl

def smallPolar (s : ℕ) : LinearMap.BilinForm F₂ (Z s) :=
  (quadPolar 0 s).comp (includeZ 0 s) (includeZ 0 s)

@[simp] theorem smallPolar_apply (s : ℕ) (a b : Z s) :
    smallPolar s a b = polarZ s a b := by
  simp [smallPolar,Module.Dual.transpose_apply,includeZ,quadPolar_apply,
    QuadraticAffineIsometries.beta,polarZ,dot]

theorem polarZ_comm (s : ℕ) (a b : Z s) : polarZ s a b = polarZ s b a := by
  simp [polarZ,add_comm]

theorem polarZ_add_left (s : ℕ) (a b c : Z s) :
    polarZ s (a+b) c = polarZ s a c + polarZ s b c := by
  simp only [← smallPolar_apply,map_add,LinearMap.add_apply]

theorem polarZ_add_right (s : ℕ) (a b c : Z s) :
    polarZ s a (b+c) = polarZ s a b + polarZ s a c := by
  simp only [← smallPolar_apply,map_add]

def kernelAdjoint {t s : ℕ} (E : Y t →ₗ[F₂] Z s) : Z s →ₗ[F₂] Y t :=
  (dotProductEquiv F₂ (Fin t × Fin 3)).symm.toLinearMap.comp
    ((Module.Dual.transpose E).comp (smallPolar s))

theorem kernelAdjoint_pairing {t s : ℕ} (E : Y t →ₗ[F₂] Z s) (z : Z s) (y : Y t) :
    dot (kernelAdjoint E z) y = polarZ s (E y) z := by
  change (dotProductEquiv F₂ (Fin t × Fin 3)
    ((dotProductEquiv F₂ (Fin t × Fin 3)).symm
      ((Module.Dual.transpose E) (smallPolar s z)))) y = _
  rw [LinearEquiv.apply_symm_apply]
  change smallPolar s z (E y) = _
  rw [smallPolar_apply,polarZ_comm]

abbrev KernelCoordinates (t s : ℕ) :=
  {p : (Y t →ₗ[F₂] Z s) × (Y t →ₗ[F₂] Y t) //
    ∀ u v, dot (p.2 u) v + dot (p.2 v) u = polarZ s (p.1 u) (p.1 v)}

def coordinatesToKernel {t s : ℕ} (p : KernelCoordinates t s) :
    ParabolicKernel.NormalizedKernel t s :=
  ⟨ParabolicKernel.triangularLinearEquiv p.1.2 (kernelAdjoint p.1.1) p.1.1, by
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      simp [ParabolicKernel.triangularLinearEquiv]
    · intro w
      rfl
    · intro z
      simp [ParabolicKernel.triangularLinearEquiv]
    · intro a b
      change dot (a.1.1 + p.1.2 a.1.2 + kernelAdjoint p.1.1 a.2) b.1.2 +
        dot (b.1.1 + p.1.2 b.1.2 + kernelAdjoint p.1.1 b.2) a.1.2 +
        polarZ s (a.2+p.1.1 a.1.2) (b.2+p.1.1 b.1.2) =
        dot a.1.1 b.1.2 + dot b.1.1 a.1.2 + polarZ s a.2 b.2
      simp only [dot_add_left,kernelAdjoint_pairing,polarZ_add_left,polarZ_add_right]
      rw [polarZ_comm s a.2 (p.1.1 b.1.2)]
      have h₁ := add_self_F₂ (polarZ s (p.1.1 a.1.2) (p.1.1 b.1.2))
      have h₂ := add_self_F₂ (polarZ s (p.1.1 a.1.2) b.2)
      have h₃ := add_self_F₂ (polarZ s (p.1.1 b.1.2) a.2)
      linear_combination p.2 a.1.2 b.1.2 + h₁ + h₂ + h₃⟩

@[simp] theorem kernelE_coordinatesToKernel {t s : ℕ} (p : KernelCoordinates t s) :
    kernelE (coordinatesToKernel p) = p.1.1 := by
  ext y i <;> simp [kernelE,coordinatesToKernel,ParabolicKernel.triangularLinearEquiv,includeY]

@[simp] theorem kernelB_coordinatesToKernel {t s : ℕ} (p : KernelCoordinates t s) :
    kernelB (coordinatesToKernel p) = p.1.2 := by
  ext y i
  simp [kernelB,coordinatesToKernel,ParabolicKernel.triangularLinearEquiv,
    includeY,ParabolicKernel.projX]

def normalizedKernelEquivCoordinates (t s : ℕ) :
    ParabolicKernel.NormalizedKernel t s ≃ KernelCoordinates t s where
  toFun K := ⟨(kernelE K,kernelB K),kernelB_constraint K⟩
  invFun := coordinatesToKernel
  left_inv K := by
    apply kernel_coordinates_injective t s
    simp
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (kernelE_coordinatesToKernel p) (kernelB_coordinatesToKernel p)

@[simp] theorem kernelC_coordinatesToKernel {t s : ℕ} (p : KernelCoordinates t s) :
    kernelC (coordinatesToKernel p) = kernelAdjoint p.1.1 := by
  apply LinearMap.ext
  intro z
  change 0 + p.1.2 0 + kernelAdjoint p.1.1 z = kernelAdjoint p.1.1 z
  simp

noncomputable instance kernelCoordinatesGroup (t s : ℕ) : Group (KernelCoordinates t s) :=
  (normalizedKernelEquivCoordinates t s).symm.group

noncomputable def normalizedKernelMulEquivCoordinates (t s : ℕ) :
    ParabolicKernel.NormalizedKernel t s ≃* KernelCoordinates t s :=
  ((normalizedKernelEquivCoordinates t s).symm.mulEquiv).symm

@[simp] theorem coordinatesToKernel_mul {t s : ℕ} (p q : KernelCoordinates t s) :
    coordinatesToKernel (p*q) = coordinatesToKernel p * coordinatesToKernel q :=
  (normalizedKernelMulEquivCoordinates t s).symm.map_mul p q

/-- Multiplication on the explicit pair type, with no additional assumptions
beyond its displayed alternating relation. -/
theorem kernelCoordinates_mul_E {t s : ℕ} (p q : KernelCoordinates t s) :
    (p*q).1.1 = p.1.1 + q.1.1 := by
  rw [← kernelE_coordinatesToKernel (p*q),coordinatesToKernel_mul,kernelE_mul,
    kernelE_coordinatesToKernel,kernelE_coordinatesToKernel]

theorem kernelCoordinates_mul_B {t s : ℕ} (p q : KernelCoordinates t s) :
    (p*q).1.2 = p.1.2 + q.1.2 + (kernelAdjoint p.1.1).comp q.1.1 := by
  rw [← kernelB_coordinatesToKernel (p*q),coordinatesToKernel_mul,kernelB_mul,
    kernelB_coordinatesToKernel,kernelB_coordinatesToKernel,kernelE_coordinatesToKernel,
    kernelC_coordinatesToKernel]

noncomputable def coordinateLeviAction (t s : ℕ) : Levi t s →* MulAut (KernelCoordinates t s) :=
  (MulAut.congr (normalizedKernelMulEquivCoordinates t s)).toMonoidHom.comp (leviAction t s)

noncomputable abbrev CoordinateSemidirect (t s : ℕ) :=
  KernelCoordinates t s ⋊[coordinateLeviAction t s] Levi t s

noncomputable def semidirectMulEquivCoordinates (t s : ℕ) :
    ExplicitSemidirect t s ≃* CoordinateSemidirect t s :=
  SemidirectProduct.congr (normalizedKernelMulEquivCoordinates t s) (MulEquiv.refl _) (by
    intro g
    apply MulEquiv.ext
    intro K
    change (normalizedKernelMulEquivCoordinates t s) (leviAction t s g K) =
      (normalizedKernelMulEquivCoordinates t s) (leviAction t s g
        ((normalizedKernelMulEquivCoordinates t s).symm
          ((normalizedKernelMulEquivCoordinates t s) K)))
    rw [MulEquiv.symm_apply_apply])

/-- Full multiplicative classification with the kernel literally the displayed
set of pairs `(E,B)` satisfying `B+Bᵀ=EᵀJE`. -/
noncomputable def affineStabilizerMulEquivCoordinateSemidirect (t s : ℕ) :
    AffineStabilizer t s ≃* CoordinateSemidirect t s :=
  (affineStabilizerMulEquivSemidirect t s).trans (semidirectMulEquivCoordinates t s)

theorem coordinateLeviAction_E {t s : ℕ} (g : Levi t s) (p : KernelCoordinates t s) :
    (coordinateLeviAction t s g p).1.1 =
      g.2.1.toLinearMap.comp (p.1.1.comp g.1.1.symm.toLinearMap) := by
  change kernelE (leviAction t s g (coordinatesToKernel p)) = _
  rw [leviAction_kernelE,kernelE_coordinatesToKernel]

theorem coordinateLeviAction_B {t s : ℕ} (g : Levi t s) (p : KernelCoordinates t s) :
    (coordinateLeviAction t s g p).1.2 =
      (dualAction g.1.1).toLinearMap.comp (p.1.2.comp g.1.1.symm.toLinearMap) := by
  change kernelB (leviAction t s g (coordinatesToKernel p)) = _
  rw [leviAction_kernelB,kernelB_coordinatesToKernel]

theorem card_kernelCoordinates (t s : ℕ) :
    Nat.card (KernelCoordinates t s) = 2 ^ ((3*t)*(3*t+1)/2 + 6*t*s) := by
  rw [← Nat.card_congr (normalizedKernelEquivCoordinates t s),
    ParabolicKernel.card_normalizedKernel]

end ParabolicGroup
end CubicBentAutomorphisms
end


/-! ## Orders of binary symplectic groups -/

section
open scoped BigOperators
namespace SymplecticOrder

abbrev F₂ := ZMod 2

@[simp] theorem add_self (a : F₂) : a + a = 0 := by
  fin_cases a <;> decide

theorem scalar_eq_zero_or_one (a : F₂) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

section Abstract
variable {V : Type*} [AddCommGroup V] [Module F₂ V]

@[simp] theorem vector_add_self (v : V) : v + v = 0 := by
  have h : (1 : F₂) + 1 = 0 := rfl
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun a : F₂ => a • v) h

structure SymplecticForm (V : Type*) [AddCommGroup V] [Module F₂ V] where
  form : LinearMap.BilinForm F₂ V
  symm : ∀ x y, form x y = form y x
  alternating : ∀ x, form x x = 0
  nondegenerate : ∀ x, (∀ y, form x y = 0) → x = 0

namespace SymplecticForm
variable (B : SymplecticForm V)

abbrev Sp := {e : V ≃ₗ[F₂] V // ∀ x y, B.form (e x) (e y) = B.form x y}

instance [Finite V] : Finite B.Sp :=
  Finite.of_injective (fun e : B.Sp => (e.val : V → V)) (by
    intro e f h
    apply Subtype.ext
    exact LinearEquiv.ext (congrFun h))

def transvectionMap (v : V) : V →ₗ[F₂] V where
  toFun x := x + B.form v x • v
  map_add' x y := by simp [map_add, add_smul]; abel
  map_smul' c x := by simp [map_smul, smul_add, smul_smul, mul_comm]

theorem transvectionMap_involutive (v : V) :
    Function.Involutive (B.transvectionMap v) := by
  intro x
  simp [transvectionMap, map_add, map_smul, B.alternating, add_assoc]

def transvection (v : V) : V ≃ₗ[F₂] V :=
  { B.transvectionMap v with
    invFun := B.transvectionMap v
    left_inv := B.transvectionMap_involutive v
    right_inv := B.transvectionMap_involutive v }

theorem transvection_preserves (v x y : V) :
    B.form (B.transvection v x) (B.transvection v y) = B.form x y := by
  change B.form (x + B.form v x • v) (y + B.form v y • v) = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, B.alternating, mul_zero, add_zero]
  rw [B.symm x v]
  have h := add_self (B.form v x * B.form v y)
  linear_combination h

def transvectionSp (v : V) : B.Sp :=
  ⟨B.transvection v, B.transvection_preserves v⟩

theorem transvection_maps (a b : V) (h : B.form a b = 1) :
    B.transvection (a + b) a = b := by
  change a + B.form (a + b) a • (a + b) = b
  simp [map_add, B.alternating, B.symm b a, h, ← add_assoc]

theorem exists_mate (a : V) (ha : a ≠ 0) : ∃ b, B.form a b = 1 := by
  by_contra h
  push_neg at h
  apply ha
  apply B.nondegenerate
  intro b
  exact (scalar_eq_zero_or_one (B.form a b)).resolve_right (h b)

theorem exists_common_mate (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c, B.form a c = 1 ∧ B.form b c = 1 := by
  obtain ⟨x, hx⟩ := B.exists_mate a ha
  obtain ⟨y, hy⟩ := B.exists_mate b hb
  rcases scalar_eq_zero_or_one (B.form b x) with hbx | hbx
  · rcases scalar_eq_zero_or_one (B.form a y) with hay | hay
    · exact ⟨x + y, by simp [map_add, hx, hay], by simp [map_add, hbx, hy]⟩
    · exact ⟨y, hay, hy⟩
  · exact ⟨x, hx, hbx⟩

theorem transitive_nonzero (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ e : B.Sp, e.val a = b := by
  obtain ⟨c, hac, hbc⟩ := B.exists_common_mate a b ha hb
  refine ⟨⟨(B.transvection (a+c)).trans (B.transvection (c+b)), ?_⟩, ?_⟩
  · intro x y
    change B.form (B.transvection (c+b) (B.transvection (a+c) x))
      (B.transvection (c+b) (B.transvection (a+c) y)) = _
    rw [B.transvection_preserves, B.transvection_preserves]
  · change B.transvection (c+b) (B.transvection (a+c) a) = b
    rw [B.transvection_maps a c hac, B.transvection_maps c b ((B.symm c b).trans hbc)]

def spTrans (e f : B.Sp) : B.Sp :=
  ⟨e.val.trans f.val, by intro x y; exact (f.property _ _).trans (e.property x y)⟩

def spSymm (e : B.Sp) : B.Sp :=
  ⟨e.val.symm, by
    intro x y
    have h := e.property (e.val.symm x) (e.val.symm y)
    simpa using h.symm⟩

@[simp] theorem transvection_fix (a v : V) (h : B.form v a = 0) :
    B.transvection v a = a := by
  change a + B.form v a • v = a
  simp [h]

theorem transitive_mates (a b d : V) (hab : B.form a b = 1)
    (had : B.form a d = 1) :
    ∃ e : B.Sp, e.val a = a ∧ e.val b = d := by
  have habd : B.form (b+d) a = 0 := by
    simp [map_add, B.symm b a, B.symm d a, hab, had]
  rcases scalar_eq_zero_or_one (B.form b d) with hbd | hbd
  · have hacd : B.form (a+b+d) a = 0 := by
      simp [map_add, B.alternating, B.symm b a, B.symm d a, hab, had]
    have had' : B.form (a+b) d = 1 := by simp [map_add, had, hbd]
    refine ⟨B.spTrans (B.transvectionSp a) (B.transvectionSp (a+b+d)), ?_, ?_⟩
    · change B.transvection (a+b+d) (B.transvection a a) = a
      rw [B.transvection_fix a a (B.alternating a), B.transvection_fix a _ hacd]
    · change B.transvection (a+b+d) (B.transvection a b) = d
      have h : B.transvection a b = a+b := by
        change b + B.form a b • a = a+b
        simp [hab, add_comm]
      rw [h, B.transvection_maps (a+b) d had']
  · refine ⟨B.transvectionSp (b+d), B.transvection_fix a _ habd,
      B.transvection_maps b d hbd⟩

abbrev Pair := {p : V × V // B.form p.1 p.2 = 1}

theorem pair_fst_ne_zero (p : B.Pair) : p.val.1 ≠ 0 := by
  intro h
  have hp := p.property
  rw [h] at hp
  simpa using hp

theorem transitive_pairs (p q : B.Pair) :
    ∃ e : B.Sp, e.val p.val.1 = q.val.1 ∧ e.val p.val.2 = q.val.2 := by
  obtain ⟨e, he⟩ := B.transitive_nonzero p.val.1 q.val.1
    (B.pair_fst_ne_zero p) (B.pair_fst_ne_zero q)
  have h : B.form q.val.1 (e.val p.val.2) = 1 := by
    rw [← he, e.property]
    exact p.property
  obtain ⟨f, hfa, hfb⟩ := B.transitive_mates q.val.1 (e.val p.val.2) q.val.2 h q.property
  exact ⟨B.spTrans e f, by change f.val (e.val p.val.1) = _; rw [he, hfa], hfb⟩

abbrev Mate (a : V) := {b : V // B.form a b = 1}

def mateSplitting (a b : V) (hab : B.form a b = 1) : V ≃ F₂ × B.Mate a where
  toFun v := (B.form a v, ⟨v + (B.form a v + 1) • b, by
    simp [map_add, map_smul, hab, ← add_assoc]⟩)
  invFun p := p.2.val + (p.1 + 1) • b
  left_inv v := by simp [add_assoc]
  right_inv p := by
    obtain ⟨c, w, hw⟩ := p
    apply Prod.ext
    · simp [map_add, map_smul, hab, hw, add_comm, add_left_comm]
    · apply Subtype.ext
      simp [map_add, map_smul, hab, hw, add_comm, add_left_comm]

theorem twice_card_mate [Finite V] (a : V) (ha : a ≠ 0) :
    2 * Nat.card (B.Mate a) = Nat.card V := by
  obtain ⟨b, hab⟩ := B.exists_mate a ha
  have h := Nat.card_congr (B.mateSplitting a b hab)
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card] using h.symm

def pairSigmaEquiv : B.Pair ≃ (a : {a : V // a ≠ 0}) × B.Mate a.val where
  toFun p := ⟨⟨p.val.1, B.pair_fst_ne_zero p⟩, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_pair [Finite V] (k : ℕ) (hk : Nat.card V = 2*k) :
    Nat.card B.Pair = (Nat.card V - 1) * k := by
  classical
  letI := Fintype.ofFinite V
  rw [Nat.card_congr B.pairSigmaEquiv, Nat.card_sigma]
  have hmate (a : {a : V // a ≠ 0}) : Nat.card (B.Mate a.val) = k := by
    have h := B.twice_card_mate a.val a.property
    rw [hk] at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h
  simp_rw [hmate]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  simp [Fintype.card_subtype_compl, Nat.card_eq_fintype_card]

def pairAction (e : B.Sp) (p : B.Pair) : B.Pair :=
  ⟨(e.val p.val.1, e.val p.val.2), (e.property _ _).trans p.property⟩

abbrev PairStabilizer (p : B.Pair) := {e : B.Sp // B.pairAction e p = p}

noncomputable def pairTransport (p q : B.Pair) : B.Sp :=
  (B.transitive_pairs p q).choose

theorem pairTransport_spec (p q : B.Pair) :
    B.pairAction (B.pairTransport p q) p = q := by
  apply Subtype.ext
  exact Prod.ext (B.transitive_pairs p q).choose_spec.1
    (B.transitive_pairs p q).choose_spec.2

noncomputable def pairFiberEquiv (p q : B.Pair) :
    {e : B.Sp // B.pairAction e p = q} ≃ B.PairStabilizer p where
  toFun e := ⟨B.spTrans e.val (B.spSymm (B.pairTransport p q)), by
    have hq := B.pairTransport_spec p q
    have he := e.property
    apply Subtype.ext
    have hx := congrArg (fun r : B.Pair => r.val.1) he
    have hy := congrArg (fun r : B.Pair => r.val.2) he
    have htx := congrArg (fun r : B.Pair => r.val.1) hq
    have hty := congrArg (fun r : B.Pair => r.val.2) hq
    apply Prod.ext
    · change (B.pairTransport p q).val.symm (e.val.val p.val.1) = p.val.1
      change e.val.val p.val.1 = q.val.1 at hx
      change (B.pairTransport p q).val p.val.1 = q.val.1 at htx
      rw [hx, ← htx, LinearEquiv.symm_apply_apply]
    · change (B.pairTransport p q).val.symm (e.val.val p.val.2) = p.val.2
      change e.val.val p.val.2 = q.val.2 at hy
      change (B.pairTransport p q).val p.val.2 = q.val.2 at hty
      rw [hy, ← hty, LinearEquiv.symm_apply_apply]⟩
  invFun e := ⟨B.spTrans e.val (B.pairTransport p q), by
    have hq := B.pairTransport_spec p q
    have he := e.property
    apply Subtype.ext
    have hx := congrArg (fun r : B.Pair => r.val.1) he
    have hy := congrArg (fun r : B.Pair => r.val.2) he
    have htx := congrArg (fun r : B.Pair => r.val.1) hq
    have hty := congrArg (fun r : B.Pair => r.val.2) hq
    apply Prod.ext
    · change (B.pairTransport p q).val (e.val.val p.val.1) = q.val.1
      change e.val.val p.val.1 = p.val.1 at hx
      rw [hx]
      exact htx
    · change (B.pairTransport p q).val (e.val.val p.val.2) = q.val.2
      change e.val.val p.val.2 = p.val.2 at hy
      rw [hy]
      exact hty⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact (B.pairTransport p q).val.apply_symm_apply (e.val.val x)
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact (B.pairTransport p q).val.symm_apply_apply (e.val.val x)

theorem card_sp_eq_pair_mul_stabilizer [Finite V] (p : B.Pair) :
    Nat.card B.Sp = Nat.card B.Pair * Nat.card (B.PairStabilizer p) := by
  classical
  letI := Fintype.ofFinite B.Pair
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun e : B.Sp => B.pairAction e p)),
    Nat.card_sigma]
  simp_rw [Nat.card_congr (B.pairFiberEquiv p _)]
  simp [Nat.card_eq_fintype_card]

abbrev H (V : Type*) := (F₂ × F₂) × V

def extend : SymplecticForm (H V) where
  form :=
    { toFun := fun x =>
        { toFun := fun y => x.1.1 * y.1.2 + x.1.2 * y.1.1 + B.form x.2 y.2
          map_add' := by intro y z; simp [map_add, mul_add]; ring
          map_smul' := by intro c y; simp [map_smul, smul_eq_mul]; ring }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change (x.1.1+y.1.1)*z.1.2 + (x.1.2+y.1.2)*z.1.1 + B.form (x.2+y.2) z.2 = _
        simp [map_add, add_mul]; ring
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change (c*x.1.1)*y.1.2 + (c*x.1.2)*y.1.1 + B.form (c • x.2) y.2 = _
        simp [map_smul, smul_eq_mul]; ring }
  symm := by intro x y; simp [B.symm x.2 y.2]; ring
  alternating := by intro x; simp [B.alternating, mul_comm]
  nondegenerate := by
    intro x hx
    have h1 := hx ((0,1),0)
    have h2 := hx ((1,0),0)
    have ht : x.2 = 0 := B.nondegenerate x.2 (fun y => by
      simpa using hx ((0,0),y))
    apply Prod.ext
    · exact Prod.ext (by simpa using h1) (by simpa using h2)
    · exact ht

@[simp] theorem extend_form (x y : H V) :
    B.extend.form x y = x.1.1 * y.1.2 + x.1.2 * y.1.1 + B.form x.2 y.2 := rfl

def standardPair : B.extend.Pair := ⟨(((1,0),0),((0,1),0)), by simp⟩

theorem standardPair_fixed (e : B.extend.PairStabilizer B.standardPair) :
    e.val.val ((1,0),0) = ((1,0),0) ∧ e.val.val ((0,1),0) = ((0,1),0) := by
  have h := congrArg Subtype.val e.property
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem standard_stabilizer_coordinates (e : B.extend.PairStabilizer B.standardPair)
    (x : H V) : (e.val.val x).1 = x.1 := by
  have h := B.standardPair_fixed e
  have h1 := e.val.property ((0,1),0) x
  have h2 := e.val.property ((1,0),0) x
  rw [h.2] at h1
  rw [h.1] at h2
  exact Prod.ext (by simpa using h1) (by simpa using h2)

theorem standard_stabilizer_tail (e : B.extend.PairStabilizer B.standardPair)
    (v : V) : e.val.val ((0,0),v) = ((0,0),(e.val.val ((0,0),v)).2) := by
  exact Prod.ext (B.standard_stabilizer_coordinates e _) rfl

noncomputable def restrictStandard (e : B.extend.PairStabilizer B.standardPair)
    [Finite V] : V ≃ₗ[F₂] V :=
  LinearEquiv.ofInjectiveEndo
    ((LinearMap.snd F₂ (F₂ × F₂) V).comp
      (e.val.val.toLinearMap.comp (LinearMap.inr F₂ (F₂ × F₂) V))) (by
        intro x y h
        have ht := B.standard_stabilizer_tail e
        have he : e.val.val ((0,0),x) = e.val.val ((0,0),y) := by
          rw [ht x, ht y]
          exact congrArg (fun v : V => ((0,0),v)) h
        exact congrArg Prod.snd (e.val.val.injective he))

@[simp] theorem restrictStandard_apply [Finite V]
    (e : B.extend.PairStabilizer B.standardPair) (v : V) :
    B.restrictStandard e v = (e.val.val ((0,0),v)).2 := rfl

noncomputable def restrictStandardSp [Finite V]
    (e : B.extend.PairStabilizer B.standardPair) : B.Sp :=
  ⟨B.restrictStandard e, by
    intro x y
    have h := e.val.property ((0,0),x) ((0,0),y)
    rw [B.standard_stabilizer_tail e x, B.standard_stabilizer_tail e y] at h
    simpa using h⟩

def liftSp (e : B.Sp) : B.extend.PairStabilizer B.standardPair :=
  ⟨⟨(LinearEquiv.refl F₂ (F₂ × F₂)).prodCongr e.val, by
    intro x y
    change x.1.1*y.1.2 + x.1.2*y.1.1 + B.form (e.val x.2) (e.val y.2) = _
    rw [e.property]
    rfl⟩, by
    apply Subtype.ext
    simp [pairAction, standardPair]⟩

theorem standard_stabilizer_apply (e : B.extend.PairStabilizer B.standardPair)
    (x : H V) : e.val.val x = (x.1, (e.val.val ((0,0),x.2)).2) := by
  have hx : x = x.1.1 • ((1,0),0) + x.1.2 • ((0,1),0) + ((0,0),x.2) := by
    ext <;> simp
  have h := B.standardPair_fixed e
  conv_lhs => rw [hx]
  rw [map_add, map_add, map_smul, map_smul, h.1, h.2,
    B.standard_stabilizer_tail e]
  ext <;> simp

noncomputable def stabilizerEquiv [Finite V] :
    B.extend.PairStabilizer B.standardPair ≃ B.Sp where
  toFun := B.restrictStandardSp
  invFun := B.liftSp
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (B.standard_stabilizer_apply e x).symm
  right_inv e := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

theorem card_sp_extend [Finite V] :
    Nat.card B.extend.Sp = (4*Nat.card V - 1) * (2*Nat.card V) * Nat.card B.Sp := by
  have hc : Nat.card (H V) = 4 * Nat.card V := by
    simp [H, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
  rw [B.extend.card_sp_eq_pair_mul_stabilizer B.standardPair,
    Nat.card_congr B.stabilizerEquiv,
    B.extend.card_pair (2 * Nat.card V) (by rw [hc]; omega), hc]

noncomputable def spCongr {W : Type*} [AddCommGroup W] [Module F₂ W]
    (C : SymplecticForm W) (e : V ≃ₗ[F₂] W)
    (he : ∀ x y, C.form (e x) (e y) = B.form x y) : B.Sp ≃ C.Sp where
  toFun f := ⟨e.symm.trans (f.val.trans e), by
    intro x y
    change C.form (e (f.val (e.symm x))) (e (f.val (e.symm y))) = C.form x y
    rw [he, f.property, ← he, e.apply_symm_apply, e.apply_symm_apply]⟩
  invFun f := ⟨e.trans (f.val.trans e.symm), by
    intro x y
    change B.form (e.symm (f.val (e x))) (e.symm (f.val (e y))) = B.form x y
    rw [← he, e.apply_symm_apply, e.apply_symm_apply, f.property, he]⟩
  left_inv f := by apply Subtype.ext; ext x; simp
  right_inv f := by apply Subtype.ext; ext x; simp

end SymplecticForm
end Abstract

abbrev Z (s : ℕ) := (Fin s → F₂) × (Fin s → F₂)

def dot {ι : Type*} [Fintype ι] (x y : ι → F₂) : F₂ := ∑ i, x i * y i

def coordinateForm (s : ℕ) : SymplecticForm (Z s) where
  form :=
    { toFun := fun x =>
        { toFun := fun y => dot x.1 y.2 + dot y.1 x.2
          map_add' := by
            intro y z
            simp [dot, mul_add, add_mul, Finset.sum_add_distrib]
            ring
          map_smul' := by
            intro c y
            simp [dot, mul_add, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change dot (x.1+y.1) z.2 + dot z.1 (x.2+y.2) = _
        simp [dot, mul_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change dot (c • x.1) y.2 + dot y.1 (c • x.2) = _
        simp [dot, mul_add, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] }
  symm := by intro x y; exact add_comm _ _
  alternating := by intro x; exact add_self _
  nondegenerate := by
    classical
    intro x hx
    apply Prod.ext
    · funext i
      have h := hx (0, Pi.single i 1)
      simpa [dot, Pi.single_apply] using h
    · funext i
      have h := hx (Pi.single i 1, 0)
      simpa [dot, Pi.single_apply] using h

@[simp] theorem coordinateForm_apply (s : ℕ) (x y : Z s) :
    (coordinateForm s).form x y = dot x.1 y.2 + dot y.1 x.2 := rfl

def splitCoordinates (s : ℕ) : Z (s+1) ≃ₗ[F₂] SymplecticForm.H (Z s) where
  toFun x := ((x.1 0, x.2 0), (Fin.tail x.1, Fin.tail x.2))
  invFun x := (Fin.cons x.1.1 x.2.1, Fin.cons x.1.2 x.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by ext i <;> cases i using Fin.cases <;> rfl
  right_inv x := by rfl

theorem splitCoordinates_isometry (s : ℕ) (x y : Z (s+1)) :
    (coordinateForm s).extend.form (splitCoordinates s x) (splitCoordinates s y) =
      (coordinateForm (s+1)).form x y := by
  change x.1 0 * y.2 0 + x.2 0 * y.1 0 +
    (dot (Fin.tail x.1) (Fin.tail y.2) + dot (Fin.tail y.1) (Fin.tail x.2)) =
    dot x.1 y.2 + dot y.1 x.2
  simp [dot, Fin.sum_univ_succ, Fin.tail]
  ring

theorem card_Z (s : ℕ) : Nat.card (Z s) = 2^(2*s) := by
  simp [Z, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card,
    ← pow_add, two_mul]

theorem card_sp_succ (s : ℕ) :
    Nat.card (coordinateForm (s+1)).Sp =
      (2^(2*(s+1))-1) * 2^(2*s+1) * Nat.card (coordinateForm s).Sp := by
  rw [Nat.card_congr ((coordinateForm (s+1)).spCongr (coordinateForm s).extend
    (splitCoordinates s) (splitCoordinates_isometry s)),
    (coordinateForm s).card_sp_extend, card_Z]
  congr 2
  · congr 1
    rw [show 2*(s+1) = 2*s+2 by omega, pow_add]
    ring
  · rw [pow_succ]
    ring

theorem card_sp_zero : Nat.card (coordinateForm 0).Sp = 1 := by
  letI : Nonempty (coordinateForm 0).Sp :=
    ⟨⟨LinearEquiv.refl F₂ (Z 0), by intro x y; rfl⟩⟩
  letI : Subsingleton (coordinateForm 0).Sp := ⟨fun e f =>
    Subtype.ext (LinearEquiv.ext (fun x => Subsingleton.elim _ _))⟩
  exact Nat.card_unique

/-- The exact order of the binary symplectic group in every even dimension. -/
theorem card_symplectic (s : ℕ) :
    Nat.card (coordinateForm s).Sp =
      2^(s^2) * ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  induction s with
  | zero =>
    simpa only [zero_pow (by decide : 2 ≠ 0), pow_zero,
      Finset.range_zero, Finset.prod_empty, mul_one] using card_sp_zero
  | succ s ih =>
    rw [card_sp_succ, ih, Finset.prod_range_succ]
    have hp : 2^(2*s+1) * 2^(s^2) = 2^((s+1)^2) := by
      rw [← pow_add]
      congr 1
      ring
    calc
      (2^(2*(s+1))-1) * 2^(2*s+1) *
          (2^(s^2) * ∏ i ∈ Finset.range s, (2^(2*(i+1))-1)) =
        (2^(2*s+1) * 2^(s^2)) *
          ((∏ i ∈ Finset.range s, (2^(2*(i+1))-1)) * (2^(2*(s+1))-1)) := by ring
      _ = _ := by rw [hp]

/-- The group-order theorem with the exact coordinates and polar form used in
the cubic bent-family automorphism theorem. -/
theorem card_polarZ_stabilizer (s : ℕ) :
    Nat.card {e : CubicBentAutomorphisms.Z s ≃ₗ[F₂]
        CubicBentAutomorphisms.Z s //
      ∀ a b, CubicBentAutomorphisms.polarZ s (e a) (e b) =
        CubicBentAutomorphisms.polarZ s a b} =
      2^(s^2) * ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  exact card_symplectic s

end SymplecticOrder
end


/-! ## The full affine-stabilizer order -/

section
open scoped BigOperators

namespace CubicBentAutomorphisms

/-- The exact full affine-stabilizer order, including all cubic/quadratic mixing.
The zero-cubic-block case is included as well. -/
theorem card_affineStabilizer (t s : ℕ) :
    Nat.card (AffineStabilizer t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  rw [card_affineStabilizer_factors,
    SymplecticOrder.card_polarZ_stabilizer]
  rw [pow_add]
  ring

/-- A complete, reversible parameterization of every affine symmetry. -/
noncomputable def affineStabilizerEquivParameters (t s : ℕ) :
    AffineStabilizer t s ≃ ParabolicParameters t s :=
  (affineBentEquivAdaptedPolar t s).trans (parabolicParametersEquiv t s).symm

end CubicBentAutomorphisms

namespace CubicAffineOrder

abbrev Y (t : ℕ) := Fin t × Fin 3 → ZMod 2
abbrev Z (s : ℕ) := (Fin s → ZMod 2) × (Fin s → ZMod 2)
abbrev V (t s : ℕ) := (Y t × Y t) × Z s

def f (t s : ℕ) (v : V t s) : ZMod 2 :=
  (∑ i, v.1.1 i * v.1.2 i) +
  (∑ j : Fin t, v.1.2 (j,0) * v.1.2 (j,1) * v.1.2 (j,2)) +
  ∑ i, v.2.1 i * v.2.2 i

theorem f_eq_bentFamily (t s : ℕ) (v : V t s) :
    f t s v = CubicBentAutomorphisms.bentFamily t s v := by
  simp only [f, CubicBentAutomorphisms.bentFamily,
    CubicBentAutomorphisms.quad,
    CubicBentAutomorphisms.hyperbolic,
    CubicBentAutomorphisms.dot,
    CubicBentAutomorphisms.cubic]
  ring

/-- The exact two-parameter affine group-order formula. -/
theorem full_affine_group_order (t s : ℕ) (ht : 0 < t) :
    Nat.card {e : V t s ≃ᵃ[ZMod 2] V t s // ∀ v, f t s (e v) = f t s v} =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  simp only [f_eq_bentFamily]
  exact CubicBentAutomorphisms.card_affineStabilizer t s


end CubicAffineOrder
end


/-! ## The general-linear wreath factor -/

section
namespace CubicBentAutomorphisms
namespace CubicWreathGroup

def permutationAction (t : ℕ) (G : Type*) [Group G] :
    Equiv.Perm (Fin t) →* MulAut (Fin t → G) where
  toFun π :=
    { toFun := fun A k => A (π.symm k)
      invFun := fun A k => A (π k)
      left_inv := by intro A; funext k; simp
      right_inv := by intro A; funext k; simp
      map_mul' := by intro A B; rfl }
  map_one' := by apply MulEquiv.ext; intro A; rfl
  map_mul' π ρ := by apply MulEquiv.ext; intro A; rfl

abbrev Wreath (t : ℕ) :=
  (Fin t → GL (Fin 3) F₂) ⋊[permutationAction t (GL (Fin 3) F₂)] Equiv.Perm (Fin t)

@[simp] theorem wreath_mul_blocks {t : ℕ} (a b : Wreath t) (k : Fin t) :
    (a*b).left k = a.left k * b.left (a.right.symm k) := rfl

@[simp] theorem wreath_mul_perm {t : ℕ} (a b : Wreath t) :
    (a*b).right = a.right*b.right := rfl

@[simp] theorem wreath_inv_blocks {t : ℕ} (a : Wreath t) (k : Fin t) :
    a⁻¹.left k = (a.left (a.right k))⁻¹ := rfl

@[simp] theorem wreath_inv_perm {t : ℕ} (a : Wreath t) :
    a⁻¹.right = a.right⁻¹ := rfl

noncomputable def blockGL : GL (Fin 3) F₂ ≃* (Block₃ ≃ₗ[F₂] Block₃) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F₂ Block₃)

theorem blockTransformLinearEquiv_mul {t : ℕ}
    (A B : Fin t → (Block₃ ≃ₗ[F₂] Block₃)) (π ρ : Equiv.Perm (Fin t)) :
    blockTransformLinearEquiv (fun k => A k * B (π.symm k)) (π*ρ) =
      blockTransformLinearEquiv A π * blockTransformLinearEquiv B ρ := by
  apply LinearEquiv.ext
  intro y
  funext i
  rcases i with ⟨k,q⟩
  change (A k * B (π.symm k)) (blockSlice y ((π*ρ).symm k)) q =
    A k (blockSlice (blockTransform B ρ y) (π.symm k)) q
  rw [blockSlice_blockTransform]
  rfl

noncomputable def wreathToStabilizer (t : ℕ) : Wreath t →* CubicTensorStabilizer t where
  toFun p := ⟨blockTransformLinearEquiv (fun k => blockGL (p.left k)) p.right,
    cubicTensor_blockTransformLinearEquiv _ _⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    funext i
    change blockGL 1 (blockSlice y i.1) i.2 = y i
    rw [map_one]
    rfl
  map_mul' p q := by
    apply Subtype.ext
    change blockTransformLinearEquiv
      (fun k => blockGL (p.left k * q.left (p.right.symm k))) (p.right*q.right) = _
    simp only [map_mul]
    exact blockTransformLinearEquiv_mul
      (fun k => blockGL (p.left k)) (fun k => blockGL (q.left k)) p.right q.right

noncomputable def wreathEquivDatum (t : ℕ) : Wreath t ≃ CubicBlockDatum t :=
  SemidirectProduct.equivProd.trans
    (Equiv.prodCongr (Equiv.piCongrRight (fun _ => blockGL.toEquiv)) (Equiv.refl _))

theorem wreathToStabilizer_bijective (t : ℕ) :
    Function.Bijective (wreathToStabilizer t) := by
  exact ((wreathEquivDatum t).trans (cubicTensorStabilizerEquivDatum t).symm).bijective

/-- Full multiplicative classification of the cubic tensor stabilizer. -/
noncomputable def wreathMulEquivStabilizer (t : ℕ) :
    Wreath t ≃* CubicTensorStabilizer t :=
  MulEquiv.ofBijective (wreathToStabilizer t) (wreathToStabilizer_bijective t)

noncomputable def cubicTensorStabilizerMulEquivWreath (t : ℕ) :
    CubicTensorStabilizer t ≃* Wreath t :=
  (wreathMulEquivStabilizer t).symm

noncomputable def leviMulEquivWreathSymplectic (t s : ℕ) :
    ParabolicGroup.Levi t s ≃* Wreath t × SmallSymplectic s :=
  (cubicTensorStabilizerMulEquivWreath t).prodCongr (MulEquiv.refl _)

noncomputable def wreathLeviAction (t s : ℕ) :
    Wreath t × SmallSymplectic s →* MulAut (ParabolicKernel.NormalizedKernel t s) :=
  (ParabolicGroup.leviAction t s).comp (leviMulEquivWreathSymplectic t s).symm.toMonoidHom

abbrev FullSemidirect (t s : ℕ) :=
  ParabolicKernel.NormalizedKernel t s ⋊[wreathLeviAction t s]
    (Wreath t × SmallSymplectic s)

/-- The complete affine stabilizer with its cubic Levi factor replaced by the
explicit matrix general-linear wreath product. -/
noncomputable def affineStabilizerMulEquivFullSemidirect (t s : ℕ) :
    AffineStabilizer t s ≃* FullSemidirect t s :=
  (ParabolicGroup.affineStabilizerMulEquivSemidirect t s).trans
    (SemidirectProduct.congr (MulEquiv.refl _) (leviMulEquivWreathSymplectic t s) (by
      intro g
      apply MulEquiv.ext
      intro K
      simp [wreathLeviAction]))

noncomputable def coordinateWreathLeviAction (t s : ℕ) :
    Wreath t × SmallSymplectic s →* MulAut (ParabolicGroup.KernelCoordinates t s) :=
  (ParabolicGroup.coordinateLeviAction t s).comp
    (leviMulEquivWreathSymplectic t s).symm.toMonoidHom

noncomputable abbrev CoordinateFullSemidirect (t s : ℕ) :=
  ParabolicGroup.KernelCoordinates t s ⋊[coordinateWreathLeviAction t s]
    (Wreath t × SmallSymplectic s)

/-- The full affine group with both factors literal: the pair kernel
`{(E,B) | B+Bᵀ=EᵀJE}` and the matrix `GL(3,2)^t ⋊ Sym(t)` wreath product. -/
noncomputable def affineStabilizerMulEquivCoordinateFullSemidirect (t s : ℕ) :
    AffineStabilizer t s ≃* CoordinateFullSemidirect t s :=
  (ParabolicGroup.affineStabilizerMulEquivCoordinateSemidirect t s).trans
    (SemidirectProduct.congr (MulEquiv.refl _) (leviMulEquivWreathSymplectic t s) (by
      intro g
      apply MulEquiv.ext
      intro K
      simp [coordinateWreathLeviAction]))

theorem coordinateWreathLeviAction_E {t s : ℕ}
    (g : Wreath t × SmallSymplectic s) (p : ParabolicGroup.KernelCoordinates t s) :
    (coordinateWreathLeviAction t s g p).1.1 =
      g.2.1.toLinearMap.comp
        (p.1.1.comp (wreathToStabilizer t g.1).1.symm.toLinearMap) := by
  exact ParabolicGroup.coordinateLeviAction_E
    ((leviMulEquivWreathSymplectic t s).symm g) p

theorem coordinateWreathLeviAction_B {t s : ℕ}
    (g : Wreath t × SmallSymplectic s) (p : ParabolicGroup.KernelCoordinates t s) :
    (coordinateWreathLeviAction t s g p).1.2 =
      (dualAction (wreathToStabilizer t g.1).1).toLinearMap.comp
        (p.1.2.comp (wreathToStabilizer t g.1).1.symm.toLinearMap) := by
  exact ParabolicGroup.coordinateLeviAction_B
    ((leviMulEquivWreathSymplectic t s).symm g) p


end CubicWreathGroup
end CubicBentAutomorphisms
end


/-! ## Incidence automorphisms -/

section
namespace IncidenceAutomorphisms

variable {I : Type*}

def incidenceAut (B : Set (Set I)) :
    Subgroup (Equiv.Perm I × Equiv.Perm B) where
  carrier := {e | ∀ p b, p ∈ b.val ↔ e.1 p ∈ (e.2 b).val}
  one_mem' := by intro p b; rfl
  mul_mem' := by
    intro e f he hf p b
    exact (hf p b).trans (he (f.1 p) (f.2 b))
  inv_mem' := by
    intro e he p b
    simpa using (he (e.1.symm p) (e.2.symm b)).symm

theorem inverse_block_preimage (B : Set (Set I)) (e : incidenceAut B) (b : B) :
    ((e.1.2.symm b).val : Set I) = e.1.1 ⁻¹' b.val := by
  ext p
  exact (e.2 p (e.1.2.symm b)).trans (by simp)

theorem point_mem_setDesignAut (B : Set (Set I)) (e : incidenceAut B) :
    e.1.1 ∈ DualSupportDesign.setDesignAut B := by
  intro T
  constructor
  · intro hT
    rw [← inverse_block_preimage B e ⟨T,hT⟩]
    exact (e.1.2.symm ⟨T,hT⟩).property
  · intro hT
    let b : B := ⟨e.1.1 ⁻¹' T,hT⟩
    have hb : (e.1.2 b).val = T := by
      ext p
      have h := e.2 (e.1.1.symm p) b
      simpa [b] using h.symm
    rw [← hb]
    exact (e.1.2 b).property

def pointHom (B : Set (Set I)) :
    incidenceAut B →* DualSupportDesign.setDesignAut B where
  toFun e := ⟨e.1.1, point_mem_setDesignAut B e⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def inducedBlockPerm (B : Set (Set I))
    (π : DualSupportDesign.setDesignAut B) : Equiv.Perm B where
  toFun b := ⟨π.1.symm ⁻¹' b.val,
    ((DualSupportDesign.setDesignAut B).inv_mem π.2 b.val).mp b.property⟩
  invFun b := ⟨π.1 ⁻¹' b.val, (π.2 b.val).mp b.property⟩
  left_inv b := by
    apply Subtype.ext
    ext p
    simp
  right_inv b := by
    apply Subtype.ext
    ext p
    simp

def liftPoint (B : Set (Set I))
    (π : DualSupportDesign.setDesignAut B) : incidenceAut B :=
  ⟨(π.1, inducedBlockPerm B π), by
    intro p b
    change p ∈ b.val ↔ π.1.symm (π.1 p) ∈ b.val
    simp⟩

theorem pointHom_injective (B : Set (Set I)) :
    Function.Injective (pointHom B) := by
  intro e f h
  have hp : e.1.1 = f.1.1 := congrArg (fun a => a.val) h
  apply Subtype.ext
  apply Prod.ext hp
  apply Equiv.ext
  intro b
  apply Subtype.ext
  ext p
  obtain ⟨q,rfl⟩ := e.1.1.surjective p
  exact (e.2 q b).symm.trans (by simpa [hp] using f.2 q b)

theorem pointHom_surjective (B : Set (Set I)) :
    Function.Surjective (pointHom B) := by
  intro π
  exact ⟨liftPoint B π, rfl⟩

/-- The literal incidence-pair automorphism group is the full point group. -/
noncomputable def incidenceMulEquivPointAut (B : Set (Set I)) :
    incidenceAut B ≃* DualSupportDesign.setDesignAut B :=
  MulEquiv.ofBijective (pointHom B)
    ⟨pointHom_injective B, pointHom_surjective B⟩

@[simp] theorem incidenceMulEquivPointAut_apply (B : Set (Set I))
    (e : incidenceAut B) : (incidenceMulEquivPointAut B e).val = e.1.1 := rfl

end IncidenceAutomorphisms
end


/-! ## Full code and design automorphism groups -/

section
open scoped BigOperators
open DualSupportDesign AffineEvaluationCodes

namespace CubicBentAutomorphisms

def bentSupport (t s : ℕ) : Set (V t s) := {v | bentFamily t s v = 1}

def supportCode (t s : ℕ) := AffineEvaluationCodes.code (bentSupport t s)

def supportCodeAut (t s : ℕ) := AffineEvaluationCodes.codeAut (bentSupport t s)

/-- The actual subsets `B_l = {p in D_f | l(p)+f*(l)=1}`, with `l≠0`. -/
def supportDesign (t s : ℕ) : Set (Set (bentSupport t s)) :=
  designBlocks (blockWords (bentSupport t s) (dualFunction t s))

def supportDesignAut (t s : ℕ) := setDesignAut (supportDesign t s)

/-- The paper's equivalent convention: a point permutation paired with its
incidence-preserving block permutation. -/
def supportIncidenceAut (t s : ℕ) :=
  IncidenceAutomorphisms.incidenceAut (supportDesign t s)

theorem supportCode_coordinates (t s : ℕ) (w : bentSupport t s → F₂) :
    w ∈ supportCode t s ↔ ∃ a : V t s, ∃ c : F₂,
      ∀ p : bentSupport t s, w p = stdDot t s a p.val + c := by
  constructor
  · intro hw
    obtain ⟨f,hf⟩ := (mem_code (bentSupport t s) w).mp hw
    obtain ⟨a,ha⟩ := (stdDual t s).surjective f.linear
    refine ⟨a,f 0,?_⟩
    intro p
    rw [← hf p]
    have hd := congrFun f.decomp p.val
    simpa only [← ha, stdDual_apply, Pi.add_apply] using hd
  · rintro ⟨a,c,hw⟩
    have he : w = affineWord (bentSupport t s) (stdDual t s a) c := funext hw
    rw [he]
    exact affineWord_mem_code _ _ _

theorem supportDesign_coordinates (t s : ℕ) (T : Set (bentSupport t s)) :
    T ∈ supportDesign t s ↔ ∃ a : V t s, a ≠ 0 ∧
      T = {p | stdDot t s a p.val + dualBentFamily t s a = 1} := by
  constructor
  · rintro ⟨w,⟨l,hl,rfl⟩,he⟩
    obtain ⟨a,rfl⟩ := (stdDual t s).surjective l
    refine ⟨a,?_,?_⟩
    · intro ha
      apply hl
      simp [ha]
    · rw [← he]
      ext p
      simp [wordSupport, affineWord, dualFunction]
  · rintro ⟨a,ha,rfl⟩
    refine ⟨affineWord (bentSupport t s) (stdDual t s a) (dualFunction t s (stdDual t s a)),
      ⟨stdDual t s a,?_,rfl⟩,?_⟩
    · intro hz
      apply ha
      exact (stdDual t s).injective (by simpa using hz)
    · ext p
      simp [wordSupport, affineWord, dualFunction]

def supportStabilizerToAffine {t s : ℕ}
    (e : affineSetStabilizer (bentSupport t s)) : AffineStabilizer t s :=
  ⟨e.1, fun v => (by decide : ∀ a b : F₂, (a=1 ↔ b=1) → b=a)
    (bentFamily t s v) (bentFamily t s (e.1 v)) (e.2 v)⟩

/-- The nonzero dual indices label distinct actual blocks, so passing to the
set of subsets does not forget block multiplicities or add automorphisms. -/
theorem supportBlock_injective (t s : ℕ) (ht : 0 < t) :
    Function.Injective (fun l : Module.Dual F₂ (V t s) =>
      wordSupport (affineWord (bentSupport t s) l (dualFunction t s l))) := by
  intro l m he
  have hw := wordSupport_injective (bentSupport t s) he
  have hf : l.toAffineMap + AffineMap.const F₂ (V t s) (dualFunction t s l) =
      m.toAffineMap + AffineMap.const F₂ (V t s) (dualFunction t s m) := by
    apply AffineMap.ext_on (bent_support_affineSpan_eq_top t s ht)
    intro v hv
    exact congrFun hw ⟨v,hv⟩
  have hh := congrArg AffineMap.linear hf
  simpa using hh

def affineToSupportStabilizer {t s : ℕ} (e : AffineStabilizer t s) :
    affineSetStabilizer (bentSupport t s) :=
  ⟨e.1, fun v => by change bentFamily t s v=1 ↔ bentFamily t s (e.1 v)=1; rw [e.2]⟩

def supportStabilizerMulEquivAffine (t s : ℕ) :
    affineSetStabilizer (bentSupport t s) ≃* AffineStabilizer t s where
  toFun := supportStabilizerToAffine
  invFun := affineToSupportStabilizer
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

theorem supportCodeAut_eq_designAut (t s : ℕ) (ht : 0 < t) :
    supportCodeAut t s = supportDesignAut t s := by
  change codeAut (bentSupport t s) = setDesignAut (designBlocks
    (blockWords (bentSupport t s) (dualFunction t s)))
  rw [← wordAut_eq_setDesignAut]
  apply codeAut_eq_wordAut
  · exact bent_support_affineSpan_eq_top t s ht
  · exact dualFunction_zero t s
  · simpa only [not_forall] using dualFunction_not_additive t s ht
  · intro e l
    exact dualFunction_affine_covariance t s (supportStabilizerToAffine e) l

noncomputable def supportCodeMulEquivAffine (t s : ℕ) (ht : 0 < t) :
    supportCodeAut t s ≃* AffineStabilizer t s :=
  (codeAutEquivAffineStabilizer (bentSupport t s) (bent_support_affineSpan_eq_top t s ht)).trans
    (supportStabilizerMulEquivAffine t s)

noncomputable def supportDesignMulEquivAffine (t s : ℕ) (ht : 0 < t) :
    supportDesignAut t s ≃* AffineStabilizer t s :=
  (MulEquiv.subgroupCongr (supportCodeAut_eq_designAut t s ht).symm).trans
    (supportCodeMulEquivAffine t s ht)

noncomputable def supportCodeMulEquivSemidirect (t s : ℕ) (ht : 0 < t) :
    supportCodeAut t s ≃* ParabolicGroup.ExplicitSemidirect t s :=
  (supportCodeMulEquivAffine t s ht).trans
    (ParabolicGroup.affineStabilizerMulEquivSemidirect t s)

noncomputable def supportDesignMulEquivSemidirect (t s : ℕ) (ht : 0 < t) :
    supportDesignAut t s ≃* ParabolicGroup.ExplicitSemidirect t s :=
  (supportDesignMulEquivAffine t s ht).trans
    (ParabolicGroup.affineStabilizerMulEquivSemidirect t s)

noncomputable def supportCodeMulEquivFullSemidirect (t s : ℕ) (ht : 0 < t) :
    supportCodeAut t s ≃* CubicWreathGroup.FullSemidirect t s :=
  (supportCodeMulEquivAffine t s ht).trans
    (CubicWreathGroup.affineStabilizerMulEquivFullSemidirect t s)

noncomputable def supportDesignMulEquivFullSemidirect (t s : ℕ) (ht : 0 < t) :
    supportDesignAut t s ≃* CubicWreathGroup.FullSemidirect t s :=
  (supportDesignMulEquivAffine t s ht).trans
    (CubicWreathGroup.affineStabilizerMulEquivFullSemidirect t s)

theorem card_supportCodeAut (t s : ℕ) (ht : 0 < t) :
    Nat.card (supportCodeAut t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  rw [Nat.card_congr (supportCodeMulEquivAffine t s ht).toEquiv, card_affineStabilizer]

noncomputable def supportCodeMulEquivExplicitGroup (t s : ℕ) (ht : 0 < t) :
    supportCodeAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s :=
  (supportCodeMulEquivAffine t s ht).trans
    (CubicWreathGroup.affineStabilizerMulEquivCoordinateFullSemidirect t s)

noncomputable def supportDesignMulEquivExplicitGroup (t s : ℕ) (ht : 0 < t) :
    supportDesignAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s :=
  (supportDesignMulEquivAffine t s ht).trans
    (CubicWreathGroup.affineStabilizerMulEquivCoordinateFullSemidirect t s)

noncomputable def supportIncidenceMulEquivExplicitGroup (t s : ℕ) (ht : 0 < t) :
    supportIncidenceAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s :=
  (IncidenceAutomorphisms.incidenceMulEquivPointAut (supportDesign t s)).trans
    (supportDesignMulEquivExplicitGroup t s ht)

theorem card_supportDesignAut (t s : ℕ) (ht : 0 < t) :
    Nat.card (supportDesignAut t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  rw [Nat.card_congr (supportDesignMulEquivAffine t s ht).toEquiv, card_affineStabilizer]

theorem complete_code_design_result (t s : ℕ) (ht : 0 < t) :
    Nonempty (supportCodeAut t s ≃* CubicWreathGroup.FullSemidirect t s) ∧
    Nonempty (supportDesignAut t s ≃* CubicWreathGroup.FullSemidirect t s) ∧
    Nat.card (supportCodeAut t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) ∧
    Nat.card (supportDesignAut t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  exact ⟨⟨supportCodeMulEquivFullSemidirect t s ht⟩,
    ⟨supportDesignMulEquivFullSemidirect t s ht⟩,
    card_supportCodeAut t s ht, card_supportDesignAut t s ht⟩

/-- Both requested groups with literal pair-kernel and GL(3,2) wreath factors. -/
theorem explicit_code_design_groups (t s : ℕ) (ht : 0 < t) :
    Nonempty (supportCodeAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s) ∧
    Nonempty (supportDesignAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s) :=
  ⟨⟨supportCodeMulEquivExplicitGroup t s ht⟩, ⟨supportDesignMulEquivExplicitGroup t s ht⟩⟩

theorem explicit_incidence_group (t s : ℕ) (ht : 0 < t) :
    Nonempty (supportIncidenceAut t s ≃* CubicWreathGroup.CoordinateFullSemidirect t s) :=
  ⟨supportIncidenceMulEquivExplicitGroup t s ht⟩

theorem card_supportIncidenceAut (t s : ℕ) (ht : 0 < t) :
    Nat.card (supportIncidenceAut t s) =
      2 ^ ((3*t)*(3*t+1)/2 + 6*t*s + s^2) * 168^t * Nat.factorial t *
        ∏ i ∈ Finset.range s, (2^(2*(i+1))-1) := by
  exact (Nat.card_congr
    (IncidenceAutomorphisms.incidenceMulEquivPointAut (supportDesign t s)).toEquiv).trans
      (card_supportDesignAut t s ht)


end CubicBentAutomorphisms
end
