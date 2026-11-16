import Mathproof.MinimumGenerationNativeBipartiteReingold
import Mathproof.MinimumGenerationNativeReingoldExecution

namespace Mathproof.MinimumGeneration.NativeBipartiteReingold

open SearchTransducer ReingoldLiveInput
open Cslib.Complexity

open scoped Classical in
/-- One actual finite native Reingold machine decides all raw Cayley prefix
queries through their exact virtual cell reader. The cost is logarithmic in
the original Cayley word length at every prefix of the native run. -/
theorem nativePrefixRun :
    ∃ (M : SearchTransducer) (C : Nat), ∀ {n : Nat}
      (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n),
      let word := @encodeCayley n G.toMul
      let cells := inputCells G eligible cut x
      ∃ (k : Nat) (d : M.Config),
        callbackRun M cells M.initial k = some d ∧ callbackStep M cells d = none ∧
        d.outputReversed = [decide (x ∈ @Subgroup.closure (Fin n) G (seed eligible cut))] ∧
        ∀ j c, j ≤ k → callbackRun M cells M.initial j = some c →
          (-1 : Int) ≤ c.inputHead ∧
          c.inputHead ≤ (encUSTCON (instanceOf G eligible cut x)).length ∧
          ∀ i, (c.workHead i).natAbs ≤ C * (Nat.log2 (word.length + 1) + 1) := by
  obtain ⟨M,C,certificate⟩ := NativeReingoldCayley.nativeEncodedRun
  exact ⟨M,3*C,fun G eligible cut x => exactRun certificate G eligible cut x⟩

end Mathproof.MinimumGeneration.NativeBipartiteReingold
