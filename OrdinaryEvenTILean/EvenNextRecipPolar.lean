import EvenNextRecipBlocks
import EvenNextRecipGrid
import EvenReciprocalFourier

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq I] [DecidableEq J]

abbrev BigMatrix (K J I : Type*) := Matrix (Option J × I) (Option J × I) K

def block (u t : Option J) : BigMatrix K J I →ₗ[K] Matrix I I K where
  toFun A i j := A (u,i) (t,j)
  map_add' A B := by ext; rfl
  map_smul' k A := by ext; rfl

def traceBlocks (c : Module.Dual K (Matrix I I K)) : Module.Dual K (BigMatrix K J I) :=
  ∑ u : Option J, c.comp (block u u)

theorem traceBlocks_mul (c : Module.Dual K (Matrix I I K)) (A D : BigMatrix K J I) :
    traceBlocks c (A * D) = ∑ u : Option J, ∑ t : Option J, c (block u t A * block t u D) := by
  simp only [traceBlocks, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [← map_sum]
  congr 1
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply]
  change (A * D) (u,i) (u,j) =
    ∑ t : Option J, ∑ s : I, A (u,i) (t,s) * D (t,s) (u,j)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]

variable (U : (Sum H L × Option J) → Matrix I B K)
variable (V : (Sum H L × Option J) → Matrix B I K)

def rowLinear (t : J) : (H → L → K) →ₗ[K] Matrix I I K where
  toFun x := ∑ a : H, ∑ b : L, x a b • (U (.inr b, none) * V (.inl a, some t))
  map_add' x y := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' k x := by simp [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem rowLinear_apply (x : H → L → K) (t : J) (i j : I) :
    rowLinear U V t x i j = oneRow U V x t i j := by
  simp [rowLinear, oneRow, Matrix.sum_apply]

variable (S : Submodule K (Matrix I I K))
variable (hS : ∀ t x, rowLinear U V t x ∈ S)

def rowsLinear : (H → L → K) →ₗ[K] (J → S) :=
  LinearMap.pi (fun t => (rowLinear U V t).codRestrict S (hS t))

def gridRows : Restricted K H L J →ₗ[K] Grid J S :=
  LinearMap.pi fun p => (((rowLinear U V p.2).codRestrict S (hS p.2)).comp
    (LinearMap.proj p.1))

theorem gridRows_surjective (h : Function.Surjective (rowsLinear U V S hS)) :
    Function.Surjective (gridRows U V S hS) := by
  intro y
  choose x hx using fun u => h (fun t => y (u,t))
  refine ⟨x, ?_⟩
  funext p
  exact congrFun (hx p.1) p.2

private def δ : Restricted K H L J →ₗ[K] BigMatrix K J I :=
  (deltaLinear U V).comp includeShear

private theorem block_some_some (x : Restricted K H L J) (u t : J) :
    block (some u) (some t) (δ U V x) = (gridRows U V S hS x (u,t)).val := by
  ext i j
  change delta U V (includeShear x) (some u,i) (some t,j) =
    rowLinear U V t (x u) i j
  rw [delta_some_some, rowLinear_apply]

private theorem block_none_some (x : Restricted K H L J) (t : J) :
    block none (some t) (δ U V x) = 0 := by
  ext i j
  exact delta_none_some U V x t i j

private theorem block_none_none (x : Restricted K H L J) :
    block none none (δ U V x) = -(diagFold (K := K) (gridRows U V S hS x)).val := by
  ext i j
  change delta U V (includeShear x) (none,i) (none,j) =
    -(∑ t : J, gridRows U V S hS x (t,t)).val i j
  rw [delta_none_none]
  simp only [Submodule.coe_sum, Matrix.sum_apply]
  simp only [gridRows, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.codRestrict_apply,
    LinearMap.proj_apply, rowLinear_apply]

private theorem traceBlocks_delta_mul (c : Module.Dual K (Matrix I I K)) (x y : Restricted K H L J) :
    traceBlocks c (δ U V x * δ U V y) =
      (∑ p : J × J, c ((gridRows U V S hS x p).val * (gridRows U V S hS y p.swap).val)) +
      c ((diagFold (K := K) (gridRows U V S hS x)).val * (diagFold (K := K) (gridRows U V S hS y)).val) := by
  rw [traceBlocks_mul]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, block_none_none U V S hS,
    block_some_some U V S hS, block_none_some, zero_mul, mul_zero,
    map_zero, Finset.sum_const_zero, add_zero, zero_add, neg_mul_neg, Prod.swap_prod_mk]
  exact add_comm _ _

def labelForm (c : Module.Dual K (Matrix I I K)) : LinearMap.BilinForm K S :=
  (squarePolar LinearMap.id c).compl₁₂ S.subtype S.subtype

/-- Exact polar decomposition of the actual restricted reciprocal shear. -/
theorem restricted_polar (c : Module.Dual K (Matrix I I K)) :
    (squarePolar (deltaLinear U V) (traceBlocks c)).compl₁₂ includeShear includeShear =
      (gridForm (labelForm S c) + (labelForm S c).compl₁₂ diagFold diagFold).compl₁₂
        (gridRows U V S hS) (gridRows U V S hS) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change traceBlocks c (δ U V x * δ U V y + δ U V y * δ U V x) =
    gridForm (labelForm S c) (gridRows U V S hS x) (gridRows U V S hS y) +
      c ((diagFold (K := K) (gridRows U V S hS x)).val * (diagFold (K := K) (gridRows U V S hS y)).val +
        (diagFold (K := K) (gridRows U V S hS y)).val * (diagFold (K := K) (gridRows U V S hS x)).val)
  rw [map_add, traceBlocks_delta_mul U V S hS, traceBlocks_delta_mul U V S hS, map_add]
  have hswap :
      (∑ p : J × J, c ((gridRows U V S hS y p).val * (gridRows U V S hS x p.swap).val)) =
        ∑ p : J × J, c ((gridRows U V S hS y p.swap).val * (gridRows U V S hS x p).val) := by
    simpa using ((Equiv.prodComm J J).sum_comp (fun p =>
      c ((gridRows U V S hS y p).val * (gridRows U V S hS x p.swap).val))).symm
  rw [hswap]
  have hgrid : gridForm (labelForm S c) (gridRows U V S hS x) (gridRows U V S hS y) =
      (∑ p : J × J, c ((gridRows U V S hS x p).val * (gridRows U V S hS y p.swap).val)) +
      (∑ p : J × J, c ((gridRows U V S hS y p.swap).val * (gridRows U V S hS x p).val)) := by
    rw [gridForm_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact map_add c _ _
  rw [hgrid]
  abel

/-- One row-surjectivity event suffices for the full, unrestricted shear rank. -/
theorem shear_polar_rank (c : Module.Dual K (Matrix I I K))
    (h : Function.Surjective (rowsLinear U V S hS)) :
    (Fintype.card J ^ 2 - 1) * finrank K (labelForm S c).range ≤
      finrank K (squarePolar (deltaLinear U V) (traceBlocks c)).range := by
  have hlow := rank_of_surjective_grid (labelForm S c) (gridRows U V S hS)
    (gridRows_surjective U V S hS h)
  rw [← restricted_polar U V S hS c] at hlow
  exact hlow.trans (rank_pullback_le _ includeShear)

#print axioms traceBlocks_mul
#print axioms restricted_polar
#print axioms shear_polar_rank

end Mathproof.EvenTI.Reciprocal.Next


