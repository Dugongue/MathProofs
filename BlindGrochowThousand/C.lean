import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace C1000

open scoped BigOperators

section Split

variable {K ι : Type*} [Field K] [Fintype ι]

def diagonalFunctional (a x : ι → K) : K := ∑ i, a i * x i

def diagonal (a x y z : ι → K) : K :=
  diagonalFunctional a (x * y * z)

def Independent (a b : ι → K) : Prop :=
  ∃ X Y Z : (ι → K) ≃ₗ[K] (ι → K), ∀ x y z,
    diagonal a x y z = diagonal b (X x) (Y y) (Z z)

def Common (a b : ι → K) : Prop :=
  ∃ T : (ι → K) ≃ₗ[K] (ι → K), ∀ x y z,
    diagonal a x y z = diagonal b (T x) (T y) (T z)

def Contrast (a b : ι → K) : Prop := Independent a b ∧ ¬ Common a b

private theorem deltaValue [DecidableEq ι] (a x : ι → K) (i : ι) :
    diagonalFunctional a (x * Pi.single i 1) = a i * x i := by
  unfold diagonalFunctional
  trans a i * ((x * (Pi.single i (1 : K) : ι → K)) i)
  · apply Fintype.sum_eq_single i
    intro j hj
    simp [Pi.mul_apply, Pi.single_eq_of_ne hj]
  · simp [Pi.mul_apply]

private theorem separates (a : ι → K) (ha : ∀ i, a i ≠ 0) (x y : ι → K)
    (h : ∀ z, diagonalFunctional a (x * z) = diagonalFunctional a (y * z)) :
    x = y := by
  classical
  funext i
  exact mul_left_cancel₀ (ha i) (by simpa only [deltaValue] using h (Pi.single i 1))

theorem independentOfNonzero (a b : ι → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    Independent a b := by
  let u : (ι → K)ˣ :=
    ⟨fun i => a i / b i, fun i => b i / a i,
      by
        ext i
        change (a i / b i) * (b i / a i) = 1
        field_simp [ha i, hb i],
      by
        ext i
        change (b i / a i) * (a i / b i) = 1
        field_simp [ha i, hb i]⟩
  refine ⟨u.mulLeftLinearEquiv K (ι → K), LinearEquiv.refl _ _, LinearEquiv.refl _ _, ?_⟩
  intro x y z
  unfold diagonal diagonalFunctional
  apply Finset.sum_congr rfl
  intro i _
  change a i * (x i * y i * z i) = b i * (a i / b i * x i * y i * z i)
  field_simp [hb i]

theorem commonForcesCubicPermutation (a b : ι → K) (hb : ∀ i, b i ≠ 0)
    (eqv : Common a b) :
    ∃ π : ι ≃ ι, ∃ u : ι → K, (∀ j, u j ≠ 0) ∧ ∀ j, a (π j) = b j * u j ^ 3 := by
  classical
  obtain ⟨T, h⟩ := eqv
  have mulTransport (x y : ι → K) : T x * T y = T 1 * T (x * y) := by
    apply separates b hb
    intro z
    obtain ⟨v, rfl⟩ := T.surjective z
    change diagonal b (T x) (T y) (T v) =
      diagonalFunctional b (T 1 * T (x * y) * T v)
    rw [← h x y v, ← mul_comm (T (x * y))]
    change diagonal a x y v = diagonal b (T (x * y)) (T 1) (T v)
    rw [← h (x * y) 1 v]
    simp [diagonal]
  obtain ⟨v, hv⟩ := T.surjective 1
  obtain ⟨u, hu⟩ : IsUnit (T 1) :=
    isUnit_iff_exists_inv.mpr ⟨T (v * v), by rw [← mulTransport, hv, one_mul]⟩
  let L := T.trans ((u⁻¹).mulLeftLinearEquiv K (ι → K))
  have normal (x : ι → K) : L x = (↑u⁻¹ : ι → K) * T x := rfl
  have cancel : (↑u⁻¹ : ι → K) * (u : ι → K) = 1 := u.inv_val
  have cancel' : (u : ι → K) * (↑u⁻¹ : ι → K) = 1 := u.val_inv
  have unit : L 1 = 1 := by rw [normal, ← hu, cancel]
  have mul (x y : ι → K) : L (x * y) = L x * L y := by
    calc
      L (x * y) = ((↑u⁻¹ : ι → K) * (u : ι → K)) * ((↑u⁻¹ : ι → K) * T (x * y)) := by
        rw [cancel, one_mul, normal]
      _ = ((↑u⁻¹ : ι → K) * (↑u⁻¹ : ι → K)) * (T 1 * T (x * y)) := by
        rw [← hu]
        ac_rfl
      _ = L x * L y := by rw [← mulTransport, normal, normal]; ac_rfl
  let σ := AlgEquiv.ofLinearEquiv L unit mul
  have huσ (x : ι → K) : T x = (u : ι → K) * σ x := by
    change T x = (u : ι → K) * L x
    rw [normal, ← mul_assoc, cancel', one_mul]
  have coordinate (j : ι) : ∃ i, ∀ x, σ x j = x i := by
    let f := (Pi.evalAlgHom K (fun _ : ι => K) j).comp σ.toAlgHom
    obtain ⟨i, hi⟩ := f.eq_piEvalAlgHom
    exact ⟨i, fun x => DFunLike.congr_fun hi x⟩
  choose perm point using coordinate
  have inj : Function.Injective perm := by
    intro j k eq
    by_contra hne
    obtain ⟨x, hx⟩ := σ.surjective (Pi.single j 1)
    have eq' : σ x j = σ x k := (point j x).trans ((congrArg x eq).trans (point k x).symm)
    rw [hx] at eq'
    simpa [Pi.single_eq_of_ne (Ne.symm hne)] using eq'
  let π := Equiv.ofBijective perm ⟨inj, Finite.surjective_of_injective inj⟩
  refine ⟨π, (u : ι → K), ?_, ?_⟩
  · intro j ej
    have cv : (u : ι → K) j * (↑u⁻¹ : ι → K) j = 1 := congrFun cancel' j
    rw [ej, zero_mul] at cv
    exact zero_ne_one cv
  · intro j
    change a (perm j) = b j * (u : ι → K) j ^ 3
    let s : ι → K := Pi.single (perm j) 1
    have hs : σ s = Pi.single j 1 := by
      funext k
      rw [point]
      by_cases e : k = j
      · subst k
        simp [s]
      · have ep : perm k ≠ perm j := fun he => e (inj he)
        simp [s, Pi.single_eq_of_ne e, Pi.single_eq_of_ne ep]
    have e1 : diagonalFunctional a s = a (perm j) := by
      simpa [s] using (deltaValue a (1 : ι → K) (perm j))
    have e2 : diagonalFunctional b (((u : ι → K) ^ 3) * σ s) = b j * (u : ι → K) j ^ 3 := by
      rw [hs, deltaValue]
      rfl
    calc
      a (perm j) = diagonalFunctional a s := e1.symm
      _ = diagonal a s 1 1 := by simp [diagonal]
      _ = diagonal b (T s) (T 1) (T 1) := h s 1 1
      _ = diagonalFunctional b (((u : ι → K) ^ 3) * σ s) := by
        unfold diagonal
        rw [huσ s, ← hu]
        congr 1
        ring
      _ = b j * (u : ι → K) j ^ 3 := e2

theorem commonPreservesCubicMoment (a b : ι → K) (hb : ∀ j, b j ≠ 0)
    (s : K → K) (invariant : ∀ x t, t ≠ 0 → s (x * t ^ 3) = s x) (h : Common a b) :
    (∑ i, s (a i)) = ∑ i, s (b i) := by
  obtain ⟨π, u, hu, matchWeights⟩ := commonForcesCubicPermutation a b hb h
  calc
    (∑ i, s (a i)) = ∑ j, s (a (π j)) := (Equiv.sum_comp π (fun i => s (a i))).symm
    _ = ∑ j, s (b j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [matchWeights, invariant _ _ (hu j)]

end Split

theorem contrastOfCubicMoment {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (a b : ι → ZMod p) (exponent : 3 * ((p - 1) / 3) = p - 1)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (different : (∑ i, a i ^ ((p - 1) / 3)) ≠ ∑ i, b i ^ ((p - 1) / 3)) :
    Contrast a b := by
  refine ⟨independentOfNonzero a b ha hb, fun common => different ?_⟩
  apply commonPreservesCubicMoment a b hb (fun t => t ^ ((p - 1) / 3)) _ common
  intro x t ht
  rw [mul_pow, ← pow_mul, exponent, ZMod.pow_card_sub_one_eq_one ht, mul_one]

-- Generated instances follow.

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem p7_01 : Contrast (K := ZMod 7) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_02 : Contrast (K := ZMod 7) ![1, 1] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_03 : Contrast (K := ZMod 7) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_04 : Contrast (K := ZMod 7) ![1, 1] ![2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_05 : Contrast (K := ZMod 7) ![1, 2] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_06 : Contrast (K := ZMod 7) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_07 : Contrast (K := ZMod 7) ![1, 1, 1] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_08 : Contrast (K := ZMod 7) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_09 : Contrast (K := ZMod 7) ![1, 1, 1] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_10 : Contrast (K := ZMod 7) ![1, 1, 1] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_11 : Contrast (K := ZMod 7) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_12 : Contrast (K := ZMod 7) ![1, 1, 1] ![2, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_13 : Contrast (K := ZMod 7) ![1, 1, 2] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_14 : Contrast (K := ZMod 7) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_15 : Contrast (K := ZMod 7) ![1, 1, 2] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_16 : Contrast (K := ZMod 7) ![1, 1, 2] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_17 : Contrast (K := ZMod 7) ![1, 1, 2] ![2, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_18 : Contrast (K := ZMod 7) ![1, 1, 3] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_19 : Contrast (K := ZMod 7) ![1, 1, 3] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_20 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_21 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_22 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_23 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_24 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p7_25 : Contrast (K := ZMod 7) ![1, 1, 1, 1] ![1, 2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem p13_01 : Contrast (K := ZMod 13) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_02 : Contrast (K := ZMod 13) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_03 : Contrast (K := ZMod 13) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_04 : Contrast (K := ZMod 13) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_05 : Contrast (K := ZMod 13) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_06 : Contrast (K := ZMod 13) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_07 : Contrast (K := ZMod 13) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_08 : Contrast (K := ZMod 13) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_09 : Contrast (K := ZMod 13) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_10 : Contrast (K := ZMod 13) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_11 : Contrast (K := ZMod 13) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_12 : Contrast (K := ZMod 13) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_13 : Contrast (K := ZMod 13) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_14 : Contrast (K := ZMod 13) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_15 : Contrast (K := ZMod 13) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_16 : Contrast (K := ZMod 13) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_17 : Contrast (K := ZMod 13) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_18 : Contrast (K := ZMod 13) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_19 : Contrast (K := ZMod 13) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_20 : Contrast (K := ZMod 13) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_21 : Contrast (K := ZMod 13) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_22 : Contrast (K := ZMod 13) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_23 : Contrast (K := ZMod 13) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_24 : Contrast (K := ZMod 13) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p13_25 : Contrast (K := ZMod 13) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

theorem p19_01 : Contrast (K := ZMod 19) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_02 : Contrast (K := ZMod 19) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_03 : Contrast (K := ZMod 19) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_04 : Contrast (K := ZMod 19) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_05 : Contrast (K := ZMod 19) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_06 : Contrast (K := ZMod 19) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_07 : Contrast (K := ZMod 19) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_08 : Contrast (K := ZMod 19) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_09 : Contrast (K := ZMod 19) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_10 : Contrast (K := ZMod 19) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_11 : Contrast (K := ZMod 19) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_12 : Contrast (K := ZMod 19) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_13 : Contrast (K := ZMod 19) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_14 : Contrast (K := ZMod 19) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_15 : Contrast (K := ZMod 19) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_16 : Contrast (K := ZMod 19) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_17 : Contrast (K := ZMod 19) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_18 : Contrast (K := ZMod 19) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_19 : Contrast (K := ZMod 19) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_20 : Contrast (K := ZMod 19) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_21 : Contrast (K := ZMod 19) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_22 : Contrast (K := ZMod 19) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_23 : Contrast (K := ZMod 19) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_24 : Contrast (K := ZMod 19) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p19_25 : Contrast (K := ZMod 19) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

theorem p31_01 : Contrast (K := ZMod 31) ![1, 1] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_02 : Contrast (K := ZMod 31) ![1, 1] ![1, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_03 : Contrast (K := ZMod 31) ![1, 1] ![3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_04 : Contrast (K := ZMod 31) ![1, 1] ![3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_05 : Contrast (K := ZMod 31) ![1, 3] ![1, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_06 : Contrast (K := ZMod 31) ![1, 1, 1] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_07 : Contrast (K := ZMod 31) ![1, 1, 1] ![1, 1, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_08 : Contrast (K := ZMod 31) ![1, 1, 1] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_09 : Contrast (K := ZMod 31) ![1, 1, 1] ![1, 3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_10 : Contrast (K := ZMod 31) ![1, 1, 1] ![1, 5, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_11 : Contrast (K := ZMod 31) ![1, 1, 1] ![3, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_12 : Contrast (K := ZMod 31) ![1, 1, 1] ![3, 3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_13 : Contrast (K := ZMod 31) ![1, 1, 1] ![3, 5, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_14 : Contrast (K := ZMod 31) ![1, 1, 3] ![1, 1, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_15 : Contrast (K := ZMod 31) ![1, 1, 3] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_16 : Contrast (K := ZMod 31) ![1, 1, 3] ![1, 3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_17 : Contrast (K := ZMod 31) ![1, 1, 3] ![1, 5, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_18 : Contrast (K := ZMod 31) ![1, 1, 3] ![3, 5, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_19 : Contrast (K := ZMod 31) ![1, 1, 5] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_20 : Contrast (K := ZMod 31) ![1, 1, 5] ![1, 3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_21 : Contrast (K := ZMod 31) ![1, 1, 1, 1] ![1, 1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_22 : Contrast (K := ZMod 31) ![1, 1, 1, 1] ![1, 1, 1, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_23 : Contrast (K := ZMod 31) ![1, 1, 1, 1] ![1, 1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_24 : Contrast (K := ZMod 31) ![1, 1, 1, 1] ![1, 1, 3, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p31_25 : Contrast (K := ZMod 31) ![1, 1, 1, 1] ![1, 1, 5, 5] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

theorem p37_01 : Contrast (K := ZMod 37) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_02 : Contrast (K := ZMod 37) ![1, 1] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_03 : Contrast (K := ZMod 37) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_04 : Contrast (K := ZMod 37) ![1, 1] ![2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_05 : Contrast (K := ZMod 37) ![1, 2] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_06 : Contrast (K := ZMod 37) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_07 : Contrast (K := ZMod 37) ![1, 1, 1] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_08 : Contrast (K := ZMod 37) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_09 : Contrast (K := ZMod 37) ![1, 1, 1] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_10 : Contrast (K := ZMod 37) ![1, 1, 1] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_11 : Contrast (K := ZMod 37) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_12 : Contrast (K := ZMod 37) ![1, 1, 1] ![2, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_13 : Contrast (K := ZMod 37) ![1, 1, 1] ![2, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_14 : Contrast (K := ZMod 37) ![1, 1, 2] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_15 : Contrast (K := ZMod 37) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_16 : Contrast (K := ZMod 37) ![1, 1, 2] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_17 : Contrast (K := ZMod 37) ![1, 1, 2] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_18 : Contrast (K := ZMod 37) ![1, 1, 2] ![2, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_19 : Contrast (K := ZMod 37) ![1, 1, 3] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_20 : Contrast (K := ZMod 37) ![1, 1, 3] ![1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_21 : Contrast (K := ZMod 37) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_22 : Contrast (K := ZMod 37) ![1, 1, 1, 1] ![1, 1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_23 : Contrast (K := ZMod 37) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_24 : Contrast (K := ZMod 37) ![1, 1, 1, 1] ![1, 1, 2, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p37_25 : Contrast (K := ZMod 37) ![1, 1, 1, 1] ![1, 1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

theorem p43_01 : Contrast (K := ZMod 43) ![1, 1] ![1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_02 : Contrast (K := ZMod 43) ![1, 1] ![1, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_03 : Contrast (K := ZMod 43) ![1, 1] ![3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_04 : Contrast (K := ZMod 43) ![1, 1] ![3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_05 : Contrast (K := ZMod 43) ![1, 3] ![1, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_06 : Contrast (K := ZMod 43) ![1, 1, 1] ![1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_07 : Contrast (K := ZMod 43) ![1, 1, 1] ![1, 1, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_08 : Contrast (K := ZMod 43) ![1, 1, 1] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_09 : Contrast (K := ZMod 43) ![1, 1, 1] ![1, 3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_10 : Contrast (K := ZMod 43) ![1, 1, 1] ![1, 7, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_11 : Contrast (K := ZMod 43) ![1, 1, 1] ![3, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_12 : Contrast (K := ZMod 43) ![1, 1, 1] ![3, 3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_13 : Contrast (K := ZMod 43) ![1, 1, 1] ![3, 7, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_14 : Contrast (K := ZMod 43) ![1, 1, 3] ![1, 1, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_15 : Contrast (K := ZMod 43) ![1, 1, 3] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_16 : Contrast (K := ZMod 43) ![1, 1, 3] ![1, 3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_17 : Contrast (K := ZMod 43) ![1, 1, 3] ![1, 7, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_18 : Contrast (K := ZMod 43) ![1, 1, 3] ![3, 7, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_19 : Contrast (K := ZMod 43) ![1, 1, 7] ![1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_20 : Contrast (K := ZMod 43) ![1, 1, 7] ![1, 3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_21 : Contrast (K := ZMod 43) ![1, 1, 1, 1] ![1, 1, 1, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_22 : Contrast (K := ZMod 43) ![1, 1, 1, 1] ![1, 1, 1, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_23 : Contrast (K := ZMod 43) ![1, 1, 1, 1] ![1, 1, 3, 3] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_24 : Contrast (K := ZMod 43) ![1, 1, 1, 1] ![1, 1, 3, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p43_25 : Contrast (K := ZMod 43) ![1, 1, 1, 1] ![1, 1, 7, 7] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 61) := ⟨by decide⟩

theorem p61_01 : Contrast (K := ZMod 61) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_02 : Contrast (K := ZMod 61) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_03 : Contrast (K := ZMod 61) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_04 : Contrast (K := ZMod 61) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_05 : Contrast (K := ZMod 61) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_06 : Contrast (K := ZMod 61) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_07 : Contrast (K := ZMod 61) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_08 : Contrast (K := ZMod 61) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_09 : Contrast (K := ZMod 61) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_10 : Contrast (K := ZMod 61) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_11 : Contrast (K := ZMod 61) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_12 : Contrast (K := ZMod 61) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_13 : Contrast (K := ZMod 61) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_14 : Contrast (K := ZMod 61) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_15 : Contrast (K := ZMod 61) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_16 : Contrast (K := ZMod 61) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_17 : Contrast (K := ZMod 61) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_18 : Contrast (K := ZMod 61) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_19 : Contrast (K := ZMod 61) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_20 : Contrast (K := ZMod 61) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_21 : Contrast (K := ZMod 61) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_22 : Contrast (K := ZMod 61) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_23 : Contrast (K := ZMod 61) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_24 : Contrast (K := ZMod 61) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p61_25 : Contrast (K := ZMod 61) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 67) := ⟨by decide⟩

theorem p67_01 : Contrast (K := ZMod 67) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_02 : Contrast (K := ZMod 67) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_03 : Contrast (K := ZMod 67) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_04 : Contrast (K := ZMod 67) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_05 : Contrast (K := ZMod 67) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_06 : Contrast (K := ZMod 67) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_07 : Contrast (K := ZMod 67) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_08 : Contrast (K := ZMod 67) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_09 : Contrast (K := ZMod 67) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_10 : Contrast (K := ZMod 67) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_11 : Contrast (K := ZMod 67) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_12 : Contrast (K := ZMod 67) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_13 : Contrast (K := ZMod 67) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_14 : Contrast (K := ZMod 67) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_15 : Contrast (K := ZMod 67) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_16 : Contrast (K := ZMod 67) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_17 : Contrast (K := ZMod 67) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_18 : Contrast (K := ZMod 67) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_19 : Contrast (K := ZMod 67) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_20 : Contrast (K := ZMod 67) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_21 : Contrast (K := ZMod 67) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_22 : Contrast (K := ZMod 67) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_23 : Contrast (K := ZMod 67) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_24 : Contrast (K := ZMod 67) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p67_25 : Contrast (K := ZMod 67) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem p73_01 : Contrast (K := ZMod 73) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_02 : Contrast (K := ZMod 73) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_03 : Contrast (K := ZMod 73) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_04 : Contrast (K := ZMod 73) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_05 : Contrast (K := ZMod 73) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_06 : Contrast (K := ZMod 73) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_07 : Contrast (K := ZMod 73) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_08 : Contrast (K := ZMod 73) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_09 : Contrast (K := ZMod 73) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_10 : Contrast (K := ZMod 73) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_11 : Contrast (K := ZMod 73) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_12 : Contrast (K := ZMod 73) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_13 : Contrast (K := ZMod 73) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_14 : Contrast (K := ZMod 73) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_15 : Contrast (K := ZMod 73) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_16 : Contrast (K := ZMod 73) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_17 : Contrast (K := ZMod 73) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_18 : Contrast (K := ZMod 73) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_19 : Contrast (K := ZMod 73) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_20 : Contrast (K := ZMod 73) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_21 : Contrast (K := ZMod 73) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_22 : Contrast (K := ZMod 73) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_23 : Contrast (K := ZMod 73) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_24 : Contrast (K := ZMod 73) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p73_25 : Contrast (K := ZMod 73) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

local instance : Fact (Nat.Prime 79) := ⟨by decide⟩

theorem p79_01 : Contrast (K := ZMod 79) ![1, 1] ![1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_02 : Contrast (K := ZMod 79) ![1, 1] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_03 : Contrast (K := ZMod 79) ![1, 1] ![2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_04 : Contrast (K := ZMod 79) ![1, 1] ![2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_05 : Contrast (K := ZMod 79) ![1, 2] ![1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_06 : Contrast (K := ZMod 79) ![1, 1, 1] ![1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_07 : Contrast (K := ZMod 79) ![1, 1, 1] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_08 : Contrast (K := ZMod 79) ![1, 1, 1] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_09 : Contrast (K := ZMod 79) ![1, 1, 1] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_10 : Contrast (K := ZMod 79) ![1, 1, 1] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_11 : Contrast (K := ZMod 79) ![1, 1, 1] ![2, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_12 : Contrast (K := ZMod 79) ![1, 1, 1] ![2, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_13 : Contrast (K := ZMod 79) ![1, 1, 1] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_14 : Contrast (K := ZMod 79) ![1, 1, 2] ![1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_15 : Contrast (K := ZMod 79) ![1, 1, 2] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_16 : Contrast (K := ZMod 79) ![1, 1, 2] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_17 : Contrast (K := ZMod 79) ![1, 1, 2] ![1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_18 : Contrast (K := ZMod 79) ![1, 1, 2] ![2, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_19 : Contrast (K := ZMod 79) ![1, 1, 4] ![1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_20 : Contrast (K := ZMod 79) ![1, 1, 4] ![1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_21 : Contrast (K := ZMod 79) ![1, 1, 1, 1] ![1, 1, 1, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_22 : Contrast (K := ZMod 79) ![1, 1, 1, 1] ![1, 1, 1, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_23 : Contrast (K := ZMod 79) ![1, 1, 1, 1] ![1, 1, 2, 2] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_24 : Contrast (K := ZMod 79) ![1, 1, 1, 1] ![1, 1, 2, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

theorem p79_25 : Contrast (K := ZMod 79) ![1, 1, 1, 1] ![1, 1, 4, 4] := by
  apply contrastOfCubicMoment
  all_goals decide

end C1000
