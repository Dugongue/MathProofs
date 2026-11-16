/- Adapted by MathProofs for the Lean 4.33 logspace port. See NATIVE-PROVENANCE.md and the module manifest. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Cert
public import Complexity.Computability.USTCON.Reader.Invariant
public import Complexity.Computability.Machines.ReadMachine.StepMachine
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds

/-!
# Native resource certificate for undirected connectivity

The first theorem of the upstream space proof is independent of the
polynomial-time conversion and composition API. It gives an actual
finite binary multitape witness using logarithmic workspace.
-/
@[expose] public section

namespace Cslib.USTCON

open Turing MultiTapeTM Reader Cslib.Complexity

open scoped Classical in
/-- **Undirected connectivity in space `O(log n)`**: the decision of undirected `s`–`t`
connectivity is computable from the encoded instance in space linear in the logarithm of its
length. -/
theorem nativeComputableInBigO_decide : ∃ t, ComputableInBigO
    (fun I : USTCONInstance ↦ decide (I ∈ USTCON)) encUSTCON encBool t
    fun I ↦ Nat.log2 (encUSTCON I).length + 1 := by
  obtain ⟨T, hT⟩ := machine_resourceCertificate
  have hc (I : USTCONInstance) :
      machine.toStepMachine.Computes (encUSTCON I) [decide (I ∈ USTCON)] := by
    obtain ⟨k, hhalt, hout⟩ := exists_run_eq I
    have := ReadMachine.computes_toStepMachine (m := machine) (x := I.encode) (n := k) hhalt
    rwa [hout] at this
  choose rounds hr ho using hc
  let tS := ReadMachine.stateT encState T stateBudget
  let tMax (I : USTCONInstance) : ℕ := ∑ i ∈ Finset.range (rounds I + 1),
    tS (machine.toStepMachine.run (encUSTCON I) i).state
  refine ⟨_, (hT.computableInBigO (fun I : USTCONInstance ↦ decide (I ∈ USTCON))
    rounds hr (fun I ↦ by rw [encBool_apply, ho]) (tMax := tMax)
    (sMax := fun I ↦ 6 * stateConst * (Nat.log2 (encUSTCON I).length + 2) +
      2 * (Nat.log2 (encUSTCON I).length + 2) + 12) fun I i hi ↦ ⟨?_, ?_⟩).weaken
    (.refl _) (.of_le_linear (12 * stateConst + 4) (12 * stateConst + 16) fun I ↦ by nlinarith)⟩
  · exact Finset.single_le_sum (f := fun i ↦ tS (machine.toStepMachine.run (encUSTCON I) i).state)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.2 (by omega))
  · obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := machine) (encUSTCON I) i
    rw [hq]
    have hs : (encState (machine.run (encUSTCON I) j).state).length ≤
        stateConst * (Nat.log2 (encUSTCON I).length + 2) :=
      length_encState_run_le (I := I) j
    have hp : (encNat ((machine.toStepMachine.run (encUSTCON I) i).state.2)).length ≤
        Nat.log2 (encUSTCON I).length + 2 := by
      rw [length_encNat_eq_size]
      refine Nat.size_le.2 (hpos.trans_lt ?_)
      have := Nat.lt_log2_self (n := (encUSTCON I).length)
      rw [pow_succ]
      omega
    have hb : stateBudget (machine.run (encUSTCON I) j).state =
        2 * (encState (machine.run (encUSTCON I) j).state).length + 2 := by
      simp only [stateBudget, stepBudget, length_encPair, encBool_apply, List.length_singleton,
        encState_apply]
    simp only [ReadMachine.stateS, length_encPair, hb]
    nlinarith

end Cslib.USTCON
