import Mathproof.MinimumGenerationPhysicalGreedyTemplateProgram

namespace Mathproof.MinimumGeneration.PhysicalGreedyFixedTemplates

open PhysicalGreedyHeader PhysicalGreedyTemplateProgram

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev Bank := Fin 11

def cloneOrder (i : Bank) : Option Bank :=
  if i=3 ∨ i=4 then some 2 else none

def cloneHeader (i : Bank) : Option Bank :=
  if i=5 ∨ i=6 ∨ i=7 then some 4 else none

def identityBanks : Fin 4 ↪ Bank :=
  ⟨fun i => if i=0 then 4 else if i=1 then 8 else if i=2 then 10 else 0, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def squareBanks : Fin 4 ↪ Bank :=
  ⟨fun i => if i=0 then 6 else if i=1 then 9 else if i=2 then 10 else 0, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

/-- All instructions are fixed. The machine obtains its data from the
live tape words for the doubled order, wide identity, and square plus one.
The first eight return banks match the header reader's exact templates. -/
def program : List (Command 11) :=
  [.copy 0 cloneOrder, .increment 3, .add identityBanks, .increment 4, .increment 4,
    .copy 0 cloneHeader, .increment 5, .increment 6, .increment 7, .increment 7,
    .add squareBanks]

abbrev machine := compile program

def startValues (n id : Nat) (i : Bank) : Nat :=
  if i=1 then 1
  else if i=2 then graphOrder n
  else if i=8 then id
  else if i=9 then 1+graphOrder n*graphOrder n
  else 0

def endValues (n id : Nat) (i : Bank) : Nat :=
  if h : i.val < 8 then fixed n id ⟨i.val,h⟩
  else startValues n id i

theorem fits {n : Nat} (id : Fin n) : safe (width n) program (startValues n id.val) := by
  have hn : 0 < n := (Nat.zero_le _).trans_lt id.isLt
  have fitsN : n < 2^TableIO.width n := Nat.lt_log2_self
  have hid : id.val < 2^width n := (id.isLt.trans fitsN).trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold width; omega))
  have bound := virtualFit id.isLt hn
  change header n id.val 0 + graphOrder n * graphOrder n + 1 < 2^width n at bound
  have square : 1+graphOrder n*graphOrder n < 2^width n := by omega
  simp +decide [program, safe, Command.safe, Command.update, Function.update,
    cloneOrder, cloneHeader, identityBanks, squareBanks, startValues, hid, square]

theorem evaluate (n id : Nat) : eval program (startValues n id) = endValues n id := by
  funext i
  fin_cases i <;>
    simp +decide [program, eval, Command.update, Function.update, cloneOrder, cloneHeader,
      identityBanks, squareBanks, startValues, endValues, fixed, header, graphOrder] <;> omega

/-- Actual one-time arithmetic and installation in the eight final template
banks. This is a single finite controller, with physically checked copies,
increments, and additions. -/
theorem execute {n : Nat} (id : Fin n) {raw prior : List Bool} {input : Int}
    (bounds : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    machine.Run raw prior input (width n) (startValues n id.val) (endValues n id.val) := by
  rw [← evaluate]
  exact PhysicalGreedyTemplateProgram.execute bounds program (startValues n id.val) (fits id)

end Mathproof.MinimumGeneration.PhysicalGreedyFixedTemplates
