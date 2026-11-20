import EvenP1LawSelect
import EvenLiveSingularBlock

namespace Mathproof.EvenTI.Reciprocal.Sampling

open Module Mathproof.EvenOrdinaryTISingular
open scoped BigOperators

noncomputable section

section FiniteMass

variable {X Y : Type*} [Finite X] [Finite Y]

/-- A finite map with equinumerous fibers sends uniform mass to uniform mass. -/
theorem uniformFraction_of_equal_fibers [Nonempty X] (f : X → Y)
    (h : ∀ y z : Y, Nat.card {x : X // f x = y} = Nat.card {x : X // f x = z})
    (P : Y → Prop) :
    uniformFraction X (fun x => P (f x)) = uniformFraction Y P := by
  classical
  let a : X := Classical.choice ‹Nonempty X›
  let C := Nat.card {x : X // f x = f a}
  have hC : 0 < C := by
    letI : Nonempty {x : X // f x = f a} := ⟨⟨a, rfl⟩⟩
    exact Nat.card_pos
  have count (Q : Y → Prop) :
      Nat.card {x : X // Q (f x)} = Nat.card {y : Y // Q y} * C := by
    let fQ (x : {x : X // Q (f x)}) : {y : Y // Q y} := ⟨f x.val, x.property⟩
    let E (y : {y : Y // Q y}) :
        {x : {x : X // Q (f x)} // fQ x = y} ≃ {x : X // f x = y.val} :=
      { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
        invFun := fun x => ⟨⟨x.val, x.property.symm ▸ y.property⟩, Subtype.ext x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    letI := Fintype.ofFinite {y : Y // Q y}
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fQ), Nat.card_sigma]
    simp only [fun y => (Nat.card_congr (E y)).trans (h y.val (f a)), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, C]
    norm_cast
  have hall := count (fun _ => True)
  simp only [Nat.card_subtype_true] at hall
  have hCR : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  unfold uniformFraction
  rw [count P, hall, Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hCR]

variable {X : Type*} [Fintype X] {Y : X → Type*} [∀ x, Finite (Y x)]

/-- The uniform sigma law is the two-stage uniform law whenever the
second-stage fibers have equal cardinality. -/
theorem uniformFraction_sigma [Nonempty (Σ x, Y x)]
    (h : ∀ x z, Nat.card (Y x) = Nat.card (Y z)) (P : (Σ x, Y x) → Prop) :
    uniformFraction (Σ x, Y x) P =
      (∑ x : X, uniformFraction (Y x) (fun y => P ⟨x, y⟩)) / Fintype.card X := by
  classical
  let z : Σ x, Y x := Classical.choice ‹Nonempty (Σ x, Y x)›
  let C := Nat.card (Y z.1)
  letI : Nonempty (Y z.1) := ⟨z.2⟩
  have hC : 0 < C := Nat.card_pos
  have hCR : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  let E : {t : (Σ x, Y x) // P t} ≃ Σ x : X, {y : Y x // P ⟨x, y⟩} :=
    { toFun := fun t => ⟨t.val.1, ⟨t.val.2, t.property⟩⟩
      invFun := fun t => ⟨⟨t.1, t.2.val⟩, t.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold uniformFraction
  rw [Nat.card_congr E, Nat.card_sigma, Nat.card_sigma]
  simp only [fun x => h x z.1, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, ← Finset.sum_div, div_div]
  rw [mul_comm (C : ℝ)]
  norm_cast

end FiniteMass

section Rows

variable {K V R A D C : Type*} [Field K] [Finite K] [Finite V]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype R] [DecidableEq R] [Fintype A] [Fintype D]

local instance finiteDual : Finite (Module.Dual K V) :=
  Finite.of_injective (fun f : Module.Dual K V => (f : V → K)) DFunLike.coe_injective

local instance finiteBases : Finite (Basis R K V) :=
  Finite.of_injective (fun b : Basis R K V => (b : R → V)) DFunLike.coe_injective

local instance primalFintype : Fintype (PrimalRows K A V) := Fintype.ofFinite _

theorem annihilator_finrank (u : PrimalRows K A V) :
    finrank K (rowAnnihilator (K := K) u.val) + Fintype.card A = finrank K V := by
  rw [add_comm, ← finrank_span_eq_card u.property]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

private theorem independent_card_eq {W W' : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    (hW : finrank K W = finrank K W') :
    Nat.card {d : D → W // LinearIndependent K d} =
      Nat.card {d : D → W' // LinearIndependent K d} := by
  let e : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq _ _ hW
  let E : {d : D → W // LinearIndependent K d} ≃ {d : D → W' // LinearIndependent K d} :=
    { toFun := fun d => ⟨e ∘ d.val, d.property.map' e.toLinearMap e.ker⟩
      invFun := fun d => ⟨e.symm ∘ d.val, d.property.map' e.symm.toLinearMap e.symm.ker⟩
      left_inv := fun d => Subtype.ext (funext fun i => e.symm_apply_apply (d.val i))
      right_inv := fun d => Subtype.ext (funext fun i => e.apply_symm_apply (d.val i)) }
  exact Nat.card_congr E

private theorem dualRows_card_eq (u v : PrimalRows K A V) :
    Nat.card (DualRows (K := K) u.val D) = Nat.card (DualRows (K := K) v.val D) := by
  have hu := annihilator_finrank u
  have hv := annihilator_finrank v
  exact independent_card_eq (W := rowAnnihilator (K := K) u.val)
    (W' := rowAnnihilator (K := K) v.val) (by omega)

theorem uniformFraction_selectBasisRows [Nonempty (Basis R K V)]
    (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    (P : RowSample K A D V → Prop) :
    uniformFraction (Basis R K V) (fun b => P (selectBasisRows p d dis b)) =
      (∑ u : PrimalRows K A V,
        uniformFraction (DualRows (K := K) u.val D) (fun e => P ⟨u, e⟩)) /
        Nat.card (PrimalRows K A V) := by
  classical
  letI : Nonempty (RowSample K A D V) := .map (selectBasisRows p d dis)
    ‹Nonempty (Basis R K V)›
  rw [uniformFraction_of_equal_fibers (selectBasisRows p d dis)
    (fun x y => Nat.card_congr (selectedBasisFibersEquiv p d dis x y)) P]
  rw [uniformFraction_sigma dualRows_card_eq P, Nat.card_eq_fintype_card]

variable [Fintype C] [DecidableEq C]

/-- Reinterpret the coordinate rows in the ambient vector space that the
rectangular rank estimate uses, then read the primal and dual labels. -/
def selectPairRows (w : (C → K) ≃ₗ[K] V)
    (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j) (b : BasisPairs K R C) :
    RowSample K A D V := selectBasisRows p d dis ((basisOfPair b).map w)

private def mappedPairEquiv (w : (C → K) ≃ₗ[K] V) : BasisPairs K R C ≃ Basis R K V :=
  basisPairsEquiv.trans
    { toFun := fun b => b.map w
      invFun := fun b => b.map w.symm
      left_inv := fun b => DFunLike.ext _ _ fun i => by simp only [Basis.map_apply, LinearEquiv.symm_apply_apply]
      right_inv := fun b => DFunLike.ext _ _ fun i => by simp only [Basis.map_apply, LinearEquiv.apply_symm_apply] }

theorem uniformFraction_selectPairRows_joint [Nonempty (BasisPairs K R C)]
    (w : (C → K) ≃ₗ[K] V) (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    (P : RowSample K A D V → Prop) :
    uniformFraction (BasisPairs K R C) (fun b => P (selectPairRows w p d dis b)) =
      uniformFraction (RowSample K A D V) P := by
  let E := mappedPairEquiv (K := K) (R := R) w
  letI : Nonempty (Basis R K V) := .map E ‹Nonempty (BasisPairs K R C)›
  rw [show (fun b => P (selectPairRows w p d dis b)) =
      (fun b => P (selectBasisRows p d dis (E b))) from rfl,
    uniformFraction_equiv E (fun b => P (selectBasisRows p d dis b))]
  exact uniformFraction_of_equal_fibers (selectBasisRows p d dis)
    (fun x y => Nat.card_congr (selectedBasisFibersEquiv p d dis x y)) P

theorem uniformFraction_selectPairRows [Nonempty (BasisPairs K R C)]
    (w : (C → K) ≃ₗ[K] V) (p : A ↪ R) (d : D ↪ R) (dis : ∀ i j, p i ≠ d j)
    (P : RowSample K A D V → Prop) :
    uniformFraction (BasisPairs K R C) (fun b => P (selectPairRows w p d dis b)) =
      (∑ u : PrimalRows K A V,
        uniformFraction (DualRows (K := K) u.val D) (fun e => P ⟨u, e⟩)) /
        Nat.card (PrimalRows K A V) := by
  letI : Nonempty (RowSample K A D V) := .map (selectPairRows w p d dis)
    ‹Nonempty (BasisPairs K R C)›
  rw [uniformFraction_selectPairRows_joint w p d dis P,
    uniformFraction_sigma dualRows_card_eq P, Nat.card_eq_fintype_card]

end Rows

#print axioms uniformFraction_of_equal_fibers
#print axioms uniformFraction_sigma
#print axioms uniformFraction_selectBasisRows
#print axioms uniformFraction_selectPairRows_joint
#print axioms uniformFraction_selectPairRows

end
end Mathproof.EvenTI.Reciprocal.Sampling
