import Mathproof.MinimumGenerationRankBerkowitzPrimeWord
import Mathproof.MinimumGenerationRankStreamedSum

namespace Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic

open PrimeWord

def numeratorWidth (terms wordWidth : Nat) : Nat :=
  terms.size + wordWidth + wordWidth + wordWidth

/-- Coefficient multiplication samples only bits of its three operands per
term. Reduction happens once on the unreduced sum of all those products. -/
def multiplyCoordinateBit (terms width : Nat) (modulus reciprocal : Nat → Bool)
    (left right reduction : Fin terms → Nat → Bool) (index : Nat) : Bool :=
  reduceBit (numeratorWidth terms width) modulus reciprocal
    (StreamedSum.bit fun i =>
      ColumnProduct.outputBit (ColumnProduct.outputBit (left i) (right i)) (reduction i))
    index

theorem numerator_lt {terms width modulus : Nat} (hm : modulus ≤ 2^width)
    (left right reduction : Fin terms → Nat)
    (hl : ∀ i, left i < modulus) (hr : ∀ i, right i < modulus)
    (hc : ∀ i, reduction i < modulus) :
    (∑ i, left i * right i * reduction i) < 2^numeratorWidth terms width := by
  let bound := 2^width * 2^width * 2^width
  calc
    _ ≤ ∑ _ : Fin terms, bound := by
      exact Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul (Nat.mul_le_mul ((hl i).le.trans hm) ((hr i).le.trans hm)) ((hc i).le.trans hm)
    _ = terms * bound := by simp
    _ < 2^terms.size * bound := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by
      unfold bound
      exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) (Nat.two_pow_pos _))
    _ = _ := by simp only [numeratorWidth,bound,Nat.pow_add,Nat.mul_assoc]

theorem multiplyCoordinateBit_eq {terms width modulus : Nat}
    (hm : 0 < modulus) (hWidth : modulus ≤ 2^width)
    (left right reduction : Fin terms → Nat)
    (hl : ∀ i, left i < modulus) (hr : ∀ i, right i < modulus)
    (hc : ∀ i, reduction i < modulus) (index : Nat) :
    multiplyCoordinateBit terms width modulus.testBit
      (2^numeratorWidth terms width / modulus).testBit
      (fun i => (left i).testBit) (fun i => (right i).testBit)
      (fun i => (reduction i).testBit) index =
      ((∑ i, left i * right i * reduction i) % modulus).testBit index := by
  have hProduct (i : Fin terms) :
      ColumnProduct.outputBit
        (ColumnProduct.outputBit (left i).testBit (right i).testBit) (reduction i).testBit =
      (left i * right i * reduction i).testBit := by
    rw [funext (ColumnProduct.outputBit_eq (left i) (right i))]
    exact funext (ColumnProduct.outputBit_eq _ _)
  let product := fun i : Fin terms => left i * right i * reduction i
  have hSum : (StreamedSum.bit fun i => ColumnProduct.outputBit
      (ColumnProduct.outputBit (left i).testBit (right i).testBit) (reduction i).testBit) =
      (∑ i, product i).testBit := by
    rw [show (fun i : Fin terms => ColumnProduct.outputBit
        (ColumnProduct.outputBit (left i).testBit (right i).testBit) (reduction i).testBit) =
      (fun i => (product i).testBit) from funext hProduct]
    exact funext (StreamedSum.bit_eq_testBit_sum product)
  unfold multiplyCoordinateBit
  rw [hSum]
  have hp : modulus < 2^(numeratorWidth terms width+1) := by
    exact hWidth.trans_lt (Nat.pow_lt_pow_right (by decide) (by unfold numeratorWidth; omega))
  exact reduceBit_eq hm hp (numerator_lt hWidth left right reduction hl hr hc)

end Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic
