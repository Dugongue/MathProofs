import Mathproof.MinimumGenerationRankBitGrid
import Mathproof.MinimumGenerationRankGrid

namespace Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic

open Module Formula RankMinors SearchTransducer RankGridDriver

variable {R : Type*} [Field R] [Fintype R] [DecidableEq R] {p d m n : Nat}
variable [Fact p.Prime] [Algebra (ZMod p) R]

/-- Each grid probe is the addressed bit evaluation with streamed input
entries, in the field representation selected during setup. -/
noncomputable def preparedProbe (A : Matrix (Fin m) (Fin n) R)
    (basis : Basis (Fin d) (ZMod p) R) (width : Nat) (hWidth : p ≤ 2^width)
    (unitWord : Fin d × Nat → Bool) (hUnit : unitWord = reprBits basis 1)
    (table : Fin d → Fin d → Fin d → Nat → Bool)
    (hTable : ∀ i j k, table i j k = (basis.repr (basis i * basis j) k).val.testBit)
    (q : R × Fin (n+1)) : Bool :=
  let C := basisBitOperations basis width hWidth unitWord hUnit table hTable
  nonzeroBits d width (C.coefficientBit ⟨n-q.2.val,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    (gramReader basis A (fun i => q.1^i.val)
      (fun j => q.1^(((∑ i : Fin m, i.val)+1)*j.val))))

/-- The actual finite outer controller returns rank with a common physical
head bound as soon as one certified bit-probe implementation is installed.
The proof uses the exact callback algorithm above as its local contract. -/
theorem executeRankFromProbes {S W : Nat} (P : ProbeCode S W) {word : List Bool} {B : Nat}
    (A : Matrix (Fin m) (Fin n) R) (hField : rankProbeDegree m n < Fintype.card R)
    (basis : Basis (Fin d) (ZMod p) R) (width : Nat) (hWidth : p ≤ 2^width)
    (unitWord : Fin d × Nat → Bool) (hUnit : unitWord = reprBits basis 1)
    (table : Fin d → Fin d → Fin d → Nat → Bool)
    (hTable : ∀ i j k, table i j k = (basis.repr (basis i * basis j) k).val.testBit)
    (L : P.Layout (R × Fin (n+1)))
    (h : P.Contract word B (fun q => q.2.val)
      (preparedProbe A basis width hWidth unitWord hUnit table hTable) L)
    (qs : List (R × Fin (n+1))) (hCover : ∀ q, q ∈ qs)
    (c : P.Cfg) (hc : L.ready qs 0 c) :
    ∃ k d, P.stages.machine.BoundedSegment word B (P.stages.tag 0 c) (P.stages.tag 0 d) k ∧
      P.stages.machine.step word (P.stages.tag 0 d) = none ∧
      L.output A.rank d ∧ d.outputReversed = c.outputReversed := by
  let a : R → Fin m → R := fun t i => t^i.val
  let b : R → Fin n → R := fun t j => t^(((∑ i : Fin m, i.val)+1)*j.val)
  have hExact : preparedProbe A basis width hWidth unitWord hUnit table hTable =
      RankGridDriver.probe A a b := by
    funext q
    exact streamedProbe_eq A a b q basis width hWidth unitWord hUnit table hTable
  rw [hExact] at h
  obtain ⟨k,d,hSeg,hStop,hOut,hPrior⟩ := executeBerkowitzScan P A a b L h qs hCover c hc
  have hRank : scanWeightedBerkowitzRank A a b = A.rank :=
    scanWeightedBerkowitzRank_eq_rank A hField
  rw [hRank] at hOut
  exact ⟨k,d,hSeg,hStop,hOut,hPrior⟩

end Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic
