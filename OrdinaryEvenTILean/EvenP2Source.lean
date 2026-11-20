import EvenP2Fibers
import EvenP2SpectralFiber

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Action EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)

noncomputable section

variable {K : Type*} [Field K] [Fintype K] {l n : ℕ}

abbrev CutSide (K : Type*) (l n : ℕ) := Coord (l+1) n → K
abbrev Source (K : Type*) [Field K] (l n : ℕ) := Tensor K ((l+1)+(l+1)) n
abbrev KernelPair (K : Type*) [Field K] (l n : ℕ) :=
  Submodule K (CutSide K l n) × Submodule K (CutSide K l n)

def exactKernels (T : Source K l n) : KernelPair K l n :=
  ((flatten T).toLin'.ker, (flatten T)ᵀ.toLin'.ker)

def withExactKernels (T : Source K l n) :
    DenseKernelFiber (exactKernels T).1 (exactKernels T).2 := ⟨T, rfl, rfl⟩

def exactKernelsEquiv (k : KernelPair K l n) :
    DenseKernelFiber k.1 k.2 ≃ {T : Source K l n // exactKernels T = k} :=
  (Equiv.refl (Source K l n)).subtypeEquiv (fun T => by
    change (_ = _ ∧ _ = _) ↔ (exactKernels T = k)
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩)

/-- The singular source test accepts whenever some suitable pair in the
actual two kernels has all its physical anchors inside the joint budget. -/
def singularShapeAccepted (T : Source K l n) : Prop :=
  ∃ (k : KernelPair K l n) (A : DenseKernelFiber k.1 k.2), A.val = T ∧
    Fintype.card K ^ finrank K k.1 ≤ n ∧
    ∃ p : GoodPair k.1 k.2, Fintype.card K ^ singularBudget p A ≤ n^((l+1)+(l+1))

def singularShapeBad (T : Source K l n) : Prop :=
  (flatten T).det = 0 ∧ ¬ singularShapeAccepted T

def exceptionalKernels (k : KernelPair K l n) : Prop :=
  n < Fintype.card K ^ finrank K k.1 ∨ FiberBadForm k.1 ∨ FiberBadForm k.2

abbrev spectralFailureBound (K : Type*) [Fintype K] (n : ℕ) : ℝ :=
  (budgetConstant K + 2) * Real.log (Fintype.card K) / Real.log n

theorem spectralFailureBound_nonneg (hn : 2 ≤ n) :
    0 ≤ spectralFailureBound K n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := K)))
  exact div_nonneg (mul_nonneg (by linarith [budgetConstant_nonneg (K := K)])
    (Real.log_nonneg hq)) (Real.log_nonneg hn')

theorem nonexceptionalFiber_bad (k : KernelPair K l n) (hl : 2 ≤ l) (hn : 64 ≤ n)
    (hk : ¬ exceptionalKernels k) :
    uniformFraction {T : Source K l n // exactKernels T = k}
      (fun T => singularShapeBad T.val) ≤ spectralFailureBound K n := by
  rw [← uniformFraction_equiv (exactKernelsEquiv k)]
  change uniformFraction (DenseKernelFiber k.1 k.2)
    (fun T => singularShapeBad T.val) ≤ _
  have hp := spectralFailureBound_nonneg (K := K) (n := n) (by omega)
  classical
  by_cases hA : Nonempty (DenseKernelFiber k.1 k.2)
  · let A₀ := Classical.choice hA
    by_cases hs : k.1 = ⊥
    · have hz : uniformFraction (DenseKernelFiber k.1 k.2)
          (fun T => singularShapeBad T.val) ≤
          uniformFraction (DenseKernelFiber k.1 k.2) (fun _ => False) :=
        uniformFraction_le_of_imp fun T h => (fiber_singular_iff T).mp h.1 hs
      exact hz.trans (by simpa [uniformFraction] using hp)
    · have hg : Fintype.card K ^ finrank K k.1 ≤ n :=
        Nat.le_of_not_gt (fun h => hk (Or.inl h))
      have hL : ¬ FiberBadForm k.2 := fun h => hk (Or.inr (Or.inr h))
      have hR : ¬ FiberBadForm k.1 := fun h => hk (Or.inr (Or.inl h))
      obtain ⟨p⟩ := nonemptyGoodPair_of_fiber A₀ hs hL hR
      refine (uniformFraction_le_of_imp (fun A h => ?_)).trans
        (singular_fiber_spectral_gate p A₀ hl hn hg)
      exact lt_of_not_ge (fun hBudget => h.2 ⟨k, A, rfl, hg, p, hBudget⟩)
  · letI : IsEmpty (DenseKernelFiber k.1 k.2) := not_nonempty_iff.mp hA
    simpa [uniformFraction, Nat.card_of_isEmpty] using hp

#print axioms nonexceptionalFiber_bad

end
end Mathproof.EvenTI.Singular.Coverage
