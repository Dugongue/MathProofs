import EvenP18ScalarInstalledProbe
import EvenP15ScalarKernelProbe

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace EvenTI.P18Scalar

open EvenTI.P15Scalar Matrix

def chartResidueSubgroup {M L n : ℕ} (chart : List ℕ) (zero : ℕ)
    (site : Fin L → Fin n) (reference : Fin n) : AddSubgroup (Fin n → ZMod M) where
  carrier := {x | ∀ k : Fin L, chart.getD k.val 0 ≠ zero → x (site k)=x reference}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy k hk
    change x (site k)+y (site k)=x reference+y reference
    rw [hx k hk,hy k hk]
  neg_mem' := by
    intro x hx k hk
    change -x (site k)=-x reference
    rw [hx k hk]

theorem chartResidueTest_iff_mem {M L n : ℕ} [NeZero M]
    (chart : List ℕ) (zero : ℕ) (site : Fin L → Fin n) (reference : Fin n)
    (x : Fin n → ZMod M) :
    chartResidueTest chart zero site reference x=true ↔
      x ∈ chartResidueSubgroup chart zero site reference := by
  change decide (∀ k : Fin L, chart.getD k.val 0 ≠ zero →
    (x (site k)).val=(x reference).val)=true ↔
      ∀ k : Fin L, chart.getD k.val 0 ≠ zero → x (site k)=x reference
  rw [decide_eq_true_eq]
  constructor
  · intro h k hk
    exact ZMod.val_injective M (h k hk)
  · intro h k hk
    exact congrArg ZMod.val (h k hk)

/-- The exact finite family of CRT prefix probes detects all scalar
row equalities on the entire homogeneous kernel. The tested subgroup is
constructed explicitly from the installed chart and native-site map. -/
theorem scanChartResidueProbes_iff {M m n L : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M))
    (chart : List ℕ) (zero : ℕ) (site : Fin L → Fin n) (reference : Fin n) :
    scanRecoveryKernelProbes A (chartResidueTest chart zero site reference)=true ↔
      ∀ x, A.mulVec x=0 →
        ∀ k : Fin L, chart.getD k.val 0 ≠ zero → x (site k)=x reference := by
  exact scanRecoveryKernelProbes_iff A (chartResidueTest chart zero site reference)
    (chartResidueSubgroup chart zero site reference)
    (fun x _ => chartResidueTest_iff_mem chart zero site reference x)

#print axioms chartResidueTest_iff_mem
#print axioms scanChartResidueProbes_iff
end EvenTI.P18Scalar
