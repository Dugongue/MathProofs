import EvenNextRecipHighOrder

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical Matrix
open Matrix Mathproof.EvenTI.Reciprocal.Next

noncomputable section

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J]
variable [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)

def zeroExtend {A C : Type*} (e : A ↪ C) (x : A → K) : C → K :=
  Function.extend e x 0

private theorem sum_zeroExtend_smul {A C W : Type*} [Fintype A] [Fintype C]
    [AddCommMonoid W] [Module K W] (e : A ↪ C) (x : A → K) (g : C → W) :
    (∑ c, zeroExtend e x c • g c) = ∑ a, x a • g (e a) := by
  change (∑ c ∈ Finset.univ, zeroExtend e x c • g c) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    simp only [zeroExtend, e.injective.extend_apply]
  · intro c _ hc
    have he : ¬ ∃ a, e a = c := by
      rintro ⟨a, rfl⟩
      exact hc (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    rw [zeroExtend, Function.extend_apply' _ _ _ he]
    simp

private theorem sum_zeroExtend_sum {A C W : Type*} [Fintype A] [Fintype C]
    [Fintype L] [AddCommMonoid W] [Module K W] (e : A ↪ C) (z : A → L → K)
    (g : C → L → W) :
    (∑ c, ∑ b : L, zeroExtend e (fun a => z a b) c • g c b) =
      ∑ a, ∑ b : L, z a b • g (e a) b := by
  rw [Finset.sum_comm]
  simp_rw [sum_zeroExtend_smul]
  rw [Finset.sum_comm]

/-- The selected rectangle keeps the low primal row at the distinguished
coordinate and the high reciprocal rows at all remaining coordinates. -/
def selectedPrimal {BL : Type*} (A : Bases) (low : BL ↪ L) (b : BL) : Matrix I B K :=
  matrixPrimal A.val.1 (.inr (low b), none)

def selectedDual {AH : Type*} (A : Bases) (high : AH ↪ H) (a : AH) (t : J) : Matrix B I K :=
  matrixDual A.val.2 (.inl (high a), some t)

def selectedOutputs {AH BL : Type*} [Fintype AH] [Fintype BL]
    (U : BL → Matrix I B K) (V : AH → J → Matrix B I K)
    (x : AH → BL → K) (t : J) : Matrix I I K :=
  ∑ a, ∑ b, x a b • (U b * V a t)

/-- Surjectivity from any selected rectangle is enough for the full
square-zero shear. This is an exact zero extension of its coefficients. -/
theorem baselineRows_surjective_of_selected {AH BL : Type*} [Fintype AH] [Fintype BL]
    (A : Bases) (high : AH ↪ H) (low : BL ↪ L)
    (h : ∀ y : J → traceKernel (K := K) (I := I),
      ∃ x : AH → BL → K, ∀ t,
        selectedOutputs (selectedPrimal A low) (selectedDual A high) x t = (y t).val) :
    Function.Surjective (baselineRows A) := by
  intro y
  obtain ⟨x, hx⟩ := h y
  let z : H → L → K := fun a b => zeroExtend high (fun p => zeroExtend low (x p) b) a
  refine ⟨z, ?_⟩
  funext t
  apply Subtype.ext
  let g (a : H) (b : L) : Matrix I I K :=
    matrixPrimal A.val.1 (.inr b, none) * matrixDual A.val.2 (.inl a, some t)
  change (∑ a, ∑ b, z a b • g a b) = (y t).val
  dsimp [z]
  rw [sum_zeroExtend_sum]
  simp_rw [sum_zeroExtend_smul]
  exact hx t

#print axioms baselineRows_surjective_of_selected

end
end Mathproof.EvenTI.Reciprocal.Coverage
