import Mathproof.MinimumGenerationRankFieldBits
import Mathproof.MinimumGenerationRankGridDriver
import Mathproof.MinimumGenerationRankEntry

namespace Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic

open Formula Module RankMinors

def nonzeroBits (d width : Nat) (operand : Fin d × Nat → Bool) : Bool :=
  (List.finRange d).any fun i => (List.range width).any fun k => operand (i,k)

variable {R : Type*} [Field R] {p d : Nat} [Fact p.Prime] [Algebra (ZMod p) R]

theorem nonzeroBits_repr (basis : Basis (Fin d) (ZMod p) R) (width : Nat)
    (hWidth : p ≤ 2^width) (x : R) [DecidableEq R] :
    nonzeroBits d width (reprBits basis x) = decide (x ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro h hx
    subst x
    simpa [nonzeroBits,reprBits] using h
  · intro hx
    by_contra hn
    apply hx
    apply basis.repr.injective
    ext i
    have hzero : (basis.repr x i).val = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < width
      · have hf : reprBits basis x (i,k) ≠ true := by
          intro ht
          apply hn
          unfold nonzeroBits
          rw [List.any_eq_true]
          exact ⟨i,by simp,List.any_eq_true.mpr ⟨k,List.mem_range.mpr hk,ht⟩⟩
        cases hBit : reprBits basis x (i,k) with
        | false => simpa only [reprBits,Nat.zero_testBit] using hBit
        | true => exact (hf hBit).elim
      · rw [Nat.zero_testBit]
        exact Nat.testBit_eq_false_of_lt
          ((basis.repr x i).val_lt.trans_le
            (hWidth.trans (Nat.pow_le_pow_right (by decide) (by omega))))
    have hval := congrArg (fun t : Nat => (t : ZMod p)) hzero
    simpa only [map_zero,Finsupp.zero_apply,ZMod.natCast_zmod_val,Nat.cast_zero] using hval

variable [DecidableEq R] [Fintype R]

/-- Query the exact weighted grid test through the addressed coefficient
evaluator. The input callback is for the streamed Gram entry, and setup
supplies the constants of the chosen basis. -/
theorem callbackProbe_eq {m n : Nat} (A : Matrix (Fin m) (Fin n) R)
    (a : R → Fin m → R) (b : R → Fin n → R) (tk : R × Fin (n+1))
    (basis : Basis (Fin d) (ZMod p) R) (width : Nat) (hWidth : p ≤ 2^width)
    (unitWord : Fin d × Nat → Bool) (hUnit : unitWord = reprBits basis 1)
    (table : Fin d → Fin d → Fin d → Nat → Bool)
    (hTable : ∀ i j k, table i j k = (basis.repr (basis i * basis j) k).val.testBit)
    (read : Nat → Nat → Fin d × Nat → Bool)
    (hRead : ∀ i j, read i j = reprBits basis
      (Berkowitz.matrixSource (weightedGram A (a tk.1) (b tk.1)) i j)) :
    nonzeroBits d width ((basisBitOperations basis width hWidth unitWord hUnit table hTable
      ).coefficientBit ⟨n-tk.2.val,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ read) =
      RankGridDriver.probe A a b tk := by
  let C := basisBitOperations basis width hWidth unitWord hUnit table hTable
  have h := C.coefficientBit_exact (weightedGram A (a tk.1) (b tk.1))
    ⟨n-tk.2.val,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ read hRead
  rw [h]
  change nonzeroBits d width (reprBits basis _) = _
  rw [nonzeroBits_repr basis width hWidth]
  unfold RankGridDriver.probe
  rw [Berkowitz.balancedCoefficient_eq]

/-- Matrix input leaves are evaluated by the checked row fold, which requests
individual original entries rather than storing a Gram matrix. -/
noncomputable def gramReader {m n : Nat} (basis : Basis (Fin d) (ZMod p) R)
    (A : Matrix (Fin m) (Fin n) R) (a : Fin m → R) (b : Fin n → R)
    (i j : Nat) : Fin d × Nat → Bool :=
  if hi : i < n then
    if hj : j < n then
      reprBits basis (streamWeightedGramEntry A a b ⟨i,hi⟩ ⟨j,hj⟩)
    else fun _ => false
  else fun _ => false

theorem gramReader_exact {m n : Nat} (basis : Basis (Fin d) (ZMod p) R)
    (A : Matrix (Fin m) (Fin n) R) (a : Fin m → R) (b : Fin n → R) (i j : Nat) :
    gramReader basis A a b i j = reprBits basis (Berkowitz.matrixSource (weightedGram A a b) i j) := by
  unfold gramReader Berkowitz.matrixSource
  split_ifs
  · rw [streamWeightedGramEntry_eq]
  · funext a; simp [reprBits]
  · funext a; simp [reprBits]

theorem streamedProbe_eq {m n : Nat} (A : Matrix (Fin m) (Fin n) R)
    (a : R → Fin m → R) (b : R → Fin n → R) (tk : R × Fin (n+1))
    (basis : Basis (Fin d) (ZMod p) R) (width : Nat) (hWidth : p ≤ 2^width)
    (unitWord : Fin d × Nat → Bool) (hUnit : unitWord = reprBits basis 1)
    (table : Fin d → Fin d → Fin d → Nat → Bool)
    (hTable : ∀ i j k, table i j k = (basis.repr (basis i * basis j) k).val.testBit) :
    nonzeroBits d width ((basisBitOperations basis width hWidth unitWord hUnit table hTable
      ).coefficientBit ⟨n-tk.2.val,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
        (gramReader basis A (a tk.1) (b tk.1))) =
      RankGridDriver.probe A a b tk :=
  callbackProbe_eq A a b tk basis width hWidth unitWord hUnit table hTable _
    (gramReader_exact basis A (a tk.1) (b tk.1))
end Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic
