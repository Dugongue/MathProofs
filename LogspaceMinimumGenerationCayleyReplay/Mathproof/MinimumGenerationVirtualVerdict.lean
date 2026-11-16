import Mathproof.MinimumGenerationLatchedVerdict
import Mathproof.MinimumGenerationVirtualCallbackDriver

namespace Mathproof.MinimumGeneration.VirtualCallbackDriver

open SearchTransducer

set_option backward.isDefEq.respectTransparency false

/-- Run an addressed computation as a silent physical subroutine. All its
work banks are relocated as one unit. The caller's other tapes are preserved
at every prefix, including all interventions by the input reader. -/
theorem ReaderContract.executeVerdict {M : SearchTransducer} {R : Callback}
    {e : Fin (VirtualTapeStep.routed M).workTapes ↪ Fin R.read.workTapes}
    {raw : List Bool} {source : Int → InputCell} {B w : Nat}
    (C : ReaderContract M R e raw source B w)
    {native next : M.Config} {start : R.read.Config} {rounds : Nat}
    (ready : C.ready native start)
    (trace : ReingoldLiveInput.callbackRun M source native rounds = some next)
    (halt : ReingoldLiveInput.callbackStep M source next = none)
    (answer : Bool) (output : next.outputReversed = [answer])
    {W : Nat} (banks : Fin (machine M R e).workTapes ↪ Fin W)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) (prior : List Bool)
    (parked : ∀ j ∉ Set.range banks, (heads j).natAbs ≤ B) :
    let L := LatchedVerdict.machine (machine M R e)
    let P := L.relocateBanks banks
    let entry := L.bankConfig banks (LatchedVerdict.lift _ (tagRead M R e native.state start) prior)
      heads cells
    ∃ (ticks : Nat) (d : P.Config), P.BoundedSegment raw B entry d ticks ∧
      P.step raw d = none ∧ LatchedVerdict.unpack (finProdFinEquiv.symm d.state).2 = some answer ∧
      d.outputReversed = prior ∧
      ∀ k c, P.runFrom raw entry k = some c → ∀ j ∉ Set.range banks,
        c.workHead j = heads j ∧ c.workCell j = cells j := by
  obtain ⟨k, stop, nativeExec, nativeHalt, nativeOut⟩ := C.executeHalting ready trace halt
  let L := LatchedVerdict.machine (machine M R e)
  let entry := LatchedVerdict.lift (machine M R e) (tagRead M R e native.state start) prior
  let terminal := LatchedVerdict.lift (machine M R e) stop prior
  obtain ⟨exec, hHalt, hVerdict, hOut⟩ := LatchedVerdict.execute _ (prior := prior) nativeExec nativeHalt
  let d := L.bankConfig banks terminal heads cells
  refine ⟨k, d, L.relocateBanks_segment banks exec parked, ?_, ?_, hOut, ?_⟩
  · change (L.relocateBanks banks).step raw (L.bankConfig banks terminal heads cells) = none
    rw [L.relocateBanks_step, hHalt]
    rfl
  · change LatchedVerdict.state (machine M R e) terminal = _
    rw [hVerdict, nativeOut, output]
    rfl
  · intro j c hc i hi
    change (L.relocateBanks banks).runFrom raw (L.bankConfig banks entry heads cells) j = _ at hc
    rw [L.relocateBanks_runFrom] at hc
    obtain ⟨v, _, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact L.bankConfig_frame banks v heads cells hi

end Mathproof.MinimumGeneration.VirtualCallbackDriver
