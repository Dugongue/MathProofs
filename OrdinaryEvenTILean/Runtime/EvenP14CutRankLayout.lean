import EvenP12ComparePrepFour
import EvenP12RecognizeLoadRank

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace EvenTI.P12ComparePrep

open Mathproof.P15DecideIMPKerBasis20261007 (XBs KBLay)

def placedRankSource (m : ℕ) : ℕ := augmentedMatrixBase.value m + m
def placedRankRows (m : ℕ) : ℕ := augmentedMatrixBase.value m + 2*m
def placedRankAugmented (m : ℕ) : ℕ := augmentedMatrixBase.value m + 3*m
def placedRankOutput (m : ℕ) : ℕ := augmentedMatrixBase.value m + 5*m

structure PlacedRankFits (r n m B : ℕ) : Prop where
  layout : KBLay r n (placedRankAugmented m) (placedRankOutput m)
    (constantsBase.value m) (pairCutSlotCount.value m) B
  scratch_below : (n+1)*XBs r n ≤ augmentedMatrixBase.value m
  source_before_rows : placedRankSource m + r*n ≤ placedRankRows m
  rows_before_augmented : placedRankRows m + r*n ≤ placedRankAugmented m
  output_before_bases : placedRankOutput m + n*n ≤ firstOutputBase.value m

private theorem rankBlock_monotone {r n m : ℕ} (hr : r ≤ m) (hn : n ≤ m) :
    XBs r n ≤ XBs m m := by
  unfold XBs Mathproof.Problem18IMPIntertwinerScan20261001.blockSize
    Mathproof.Problem18ClaudeIMPPivot20261001.rowStart
  have hW : r+n+1+n ≤ m+m+1+m := by omega
  have hP := Nat.mul_le_mul hn hW
  omega

/-- The retained-rank arena uses the spent cut-matrix workspace below all
four persistent bases. The candidate form stays in its existing bank. -/
theorem placedRankFits_of_cut {d n B : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1)) + n^(d+1) + n^(d+1) + 10 < B) :
    PlacedRankFits (n^d) n (n^(d+1)) B := by
  let r := n^d
  let m := n^(d+1)
  have hp : 0 < n := by omega
  have hm : r*n = m := (pow_succ n d).symm
  have hR : r ≤ m := Nat.pow_le_pow_right hp (by omega)
  have hN : n ≤ m := by simpa only [pow_one] using Nat.pow_le_pow_right hp (show 1 ≤ d+1 by omega)
  have hNN : n*n ≤ m := by rw [← pow_two]; exact Nat.pow_le_pow_right hp (by omega : 2 ≤ d+1)
  have hM4 : 4 ≤ m := (show 2*2 ≤ n*n from Nat.mul_le_mul hn hn).trans hNN
  have hCut : 6*m ≤ 2*(m*m) := by
    calc
      6*m ≤ (2*m)*m := Nat.mul_le_mul_right _ (by omega)
      _ = 2*(m*m) := Nat.mul_assoc .. 
  have hOne : (n+1)*XBs r n ≤ (m+1)*XBs m m :=
    Nat.mul_le_mul (Nat.succ_le_succ hN) (rankBlock_monotone hR hN)
  have hA : (n+1)*XBs r n ≤ augmentedMatrixBase.value m := by
    apply hOne.trans
    simp [augmentedMatrixBase,rawMatrixBase,Address.value,rowKernelBlock_value]
  have hAug : n*(r+n) ≤ 2*m := by
    rw [Nat.mul_add,Nat.mul_comm n r,hm]
    omega
  have hb : placedRankOutput m + n*n ≤ firstOutputBase.value m := by
    simp only [placedRankOutput,firstOutputBase,Address.value,cutArea_value]
    omega
  have hOut : placedRankOutput m + n*n ≤ constantsBase.value m :=
    hb.trans (by simp [constantsBase,Address.value])
  refine ⟨⟨hp,?_,?_,hOut,?_,?_⟩,hA,?_,?_,hb⟩
  · change (n+1)*XBs r n ≤ placedRankAugmented m
    unfold placedRankAugmented
    omega
  · change placedRankAugmented m+n*(r+n) ≤ placedRankOutput m
    unfold placedRankAugmented placedRankOutput
    omega
  · simp [pairCutSlotCount,Address.value]
  · change pairCutSlotCount.value m+r+n+10 < B
    change pairCutSlotCount.value m+m+m+10 < B at hB
    omega
  · change placedRankSource m+r*n ≤ placedRankRows m
    simp only [placedRankSource,placedRankRows,hm]
    omega
  · change placedRankRows m+r*n ≤ placedRankAugmented m
    simp only [placedRankRows,placedRankAugmented,hm]
    omega

theorem placedRankOutput_below_basis {r n m B : ℕ} (h : PlacedRankFits r n m B)
    (j : Fin 4) : placedRankOutput m + n*n ≤ (outputBase j).value m := by
  rw [outputBase_value]
  exact h.output_before_bases.trans (Nat.le_add_right _ _)

#print axioms placedRankFits_of_cut
#print axioms placedRankOutput_below_basis
end EvenTI.P12ComparePrep
