import EvenP12ScalarSemantics
import EvenP15ScalarBranchCRT
import EvenP12ScalarSpectralRank

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

namespace EvenTI.P17Scalar

open EvenTI.Comparison EvenTI.P10Scan EvenTI.P10Oracle
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.Part8 EvenTI.P12Scalar EvenTI.P15Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {l n q : ℕ}

/-- The literal self-pair scanner can use comparison's actual CRT recovery
on every banked branch, with the same raw scalar verdict. -/
theorem checkSelfPair_eq_comparisonCRT (D : FieldEncoding K) (F : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (L : BaseUnitLog K)
    (T : Dense K l n) (P Q : PreparedTrial K l n)
    (out : BankedTrial D) (hOut : compileTrialBanks D T T P Q = some out)
    (hn : 0 < n) (hRank : rawRetainedFullRank (l := (l+1)+l) T = true) :
    checkSelfPair D F enum T P Q =
      out.branches.attach.all
        (fun b => matrixSelfBranchViaComparison D F T P Q out hOut b L) := by
  classical
  unfold checkSelfPair
  split
  · rename_i h
    rw [hOut] at h
    contradiction
  · rename_i out' hOut'
    have he : out' = out := Option.some.inj (hOut'.symm.trans hOut)
    subst out'
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    apply forall_congr'
    intro b
    apply imp_congr_right
    intro _
    rw [matrixSelfBranchViaComparison_exact D F T P Q out hOut b L hn hRank,
      matrixSelfBranch_exact D F enum T P Q out hOut b hn hRank]

/-- A raw prepared self request reduces to the concrete CRT branch scan.
This is the exact decision word required by the live scalar controller. -/
theorem preparedSelfWords_encode_eq_comparisonCRT
    (D : FieldEncoding K) (F : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (L : BaseUnitLog K)
    (words : List ℕ) (p : ParsedPair K)
    (hp : decodePair D words = some p)
    (h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1))
    (b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n)
    (out : BankedTrial D)
    (hOut : compileTrialBanks D (castDense (cutHalf p.d) h p.source)
      (castDense (cutHalf p.d) h p.source) b.1 b.2 = some out)
    (hn : 0 < p.n)
    (hRank : rawRetainedFullRank (l := (cutHalf p.d+1)+cutHalf p.d)
      (castDense (cutHalf p.d) h p.source) = true) :
    preparedSelfWords D F enum
      (pairW words (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2))) =
      if out.branches.attach.all (fun branch =>
        matrixSelfBranchViaComparison D F (castDense (cutHalf p.d) h p.source)
          b.1 b.2 out hOut branch L) then [1] else [0] := by
  rw [preparedSelfWords_encode D F enum words p hp h b,
    checkSelfPair_eq_comparisonCRT D F enum L
      (castDense (cutHalf p.d) h p.source) b.1 b.2 out hOut hn hRank]

#print axioms checkSelfPair_eq_comparisonCRT
#print axioms preparedSelfWords_encode_eq_comparisonCRT
end EvenTI.P17Scalar
