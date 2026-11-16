import Mathproof.MinimumGenerationPhysicalGreedyHeaderDriver

namespace Mathproof.MinimumGeneration.PhysicalGreedyHeaderCheckout

open SearchTransducer PhysicalGreedyHeader PhysicalGreedyHeaderInstall

def restore : Bank → Option Bank := fun j => if 11 ≤ j.val then some 3 else none

abbrev machine := TapeInstall.machine (3 : Bank) restore

def cells (n : Nat) (old : Bank → Int → Option Bool) :=
  TapeInstall.installed restore old (width n)

theorem frame {n : Nat} (old : Bank → Int → Option Bool) (j : Bank) (hj : j.val < 11) :
    cells n old j = old j :=
  TapeInstall.installed_source _ _ _ _ (if_neg (by omega))

theorem scratch {n : Nat} (old : Bank → Int → Option Bool)
    (zero : old 3 = wordAt (width n) 0) (guard : ∀ j, 11 ≤ j.val → outside (width n) (old j))
    (j : Bank) (hj : 11 ≤ j.val) : cells n old j = wordAt (width n) 0 := by
  refine (TapeInstall.installed_exact restore old (width n) j 3 (if_pos hj) ?_).trans zero
  intro p hp
  rw [guard j hj p hp, zero, outside_word _ _ p hp]

/-- Scratch checkout restores all six mutable banks to the shared all-zero
template. It preserves every immutable input and output already produced. -/
theorem execute {n : Nat} {raw prior : List Bool} {input : Int}
    {old : Bank → Int → Option Bool}
    (zero : old 3 = wordAt (width n) 0) (guard : ∀ j, 11 ≤ j.val → outside (width n) (old j))
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    let q := TapeInstall.stop 3 restore input old prior (width n)
    ∃ (ticks : Nat),
      machine.BoundedSegment raw (width n+1) (TapeInstall.start 3 restore input old prior) q ticks ∧
      machine.step raw q = none ∧ q.inputHead = input ∧ q.workHead = (fun _ => 0) ∧
      q.outputReversed = prior ∧
      (∀ j : Bank, j.val < 11 → q.workCell j = old j) ∧
      (∀ j : Bank, 11 ≤ j.val → q.workCell j = wordAt (width n) 0) := by
  obtain ⟨run,halt⟩ := TapeInstall.execute 3 restore (by decide) raw (encodeLabel (width n) 0) prior
    input old zero hin
  rw [length_encodeLabel] at run halt
  exact ⟨_,run,halt,rfl,rfl,rfl,frame old,scratch old zero guard⟩

end Mathproof.MinimumGeneration.PhysicalGreedyHeaderCheckout
