import Mathproof.MinimumGenerationPhysicalGreedyHeaderInstall

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateInputs

open SearchTransducer PhysicalGreedyHeader
open PhysicalGreedyHeaderInstall (wordAt)

abbrev Bank := Fin 7

/-- Copy the actual raw order into both wide operands, and the raw identity
into its own wide immutable register. -/
def sources (i : Bank) : Option Bank :=
  if i=3 ∨ i=4 then some 0 else if i=5 then some 2 else none

abbrev machine := TapeInstall.machine (0 : Bank) sources

/-- The wide destinations may be initialized once by the common zero
template. This pass produces both operands and the identity in one sweep. -/
theorem execute {raw prior : List Bool} {input : Int} {n : Nat} (id : Fin n)
    (old : Bank → Int → Option Bool)
    (bounds : (-1 : Int) ≤ input ∧ input ≤ raw.length)
    (order : old 0 = wordAt (TableIO.width n) n)
    (identity : old 2 = wordAt (TableIO.width n) id.val)
    (a : old 3 = wordAt (width n) 0)
    (b : old 4 = wordAt (width n) 0)
    (c : old 5 = wordAt (width n) 0) :
    let finish := TapeInstall.stop 0 sources input old prior (TableIO.width n)
    ∃ (ticks : Nat), machine.BoundedSegment raw (TableIO.width n+1)
      (TapeInstall.start 0 sources input old prior) finish ticks ∧
      machine.step raw finish = none ∧ finish.workHead = (fun _ => 0) ∧
      finish.inputHead = input ∧ finish.outputReversed = prior ∧
      finish.workCell 3 = wordAt (width n) n ∧ finish.workCell 4 = wordAt (width n) n ∧
      finish.workCell 5 = wordAt (width n) id.val ∧
      (∀ i : Bank, sources i = none → finish.workCell i = old i) := by
  obtain ⟨run,stop⟩ := TapeInstall.execute 0 sources (by decide) raw (encodeLabel (TableIO.width n) n)
    prior input old order bounds
  rw [length_encodeLabel] at run stop
  have fits : n < 2^TableIO.width n := Nat.lt_log2_self
  exact ⟨_,run,stop,rfl,rfl,rfl,
    installLow fits 3 0 sources (by decide) old order a,
    installLow fits 4 0 sources (by decide) old order b,
    installLow (id.isLt.trans fits) 5 2 sources (by decide) old identity c,
    fun i hi => TapeInstall.installed_source sources old (TableIO.width n) i hi⟩

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateInputs
