import Mathproof.MinimumGenerationBipartiteCayley
import Mathproof.MinimumGenerationMacroDispatch

namespace Mathproof.MinimumGeneration.OuterCayleyQuery

open SearchTransducer
open ReingoldLiveInput (difference)

set_option backward.isDefEq.respectTransparency false

abbrev solver := LiveInverse.machine

/-- The physical quotient and predicate macros share the quotient bank. -/
abbrev machine (P : SearchTransducer) {W : Nat}
    (solveBanks : Fin solver.workTapes ↪ Fin W) (testBanks : Fin P.workTapes ↪ Fin W) :=
  thenMachine solver P solveBanks testBanks

def entry {W : Nat} (P : SearchTransducer) (solveBanks : Fin solver.workTapes ↪ Fin W)
    (testBanks : Fin P.workTapes ↪ Fin W) (n x y : Nat) (prior : List Bool)
    (heads : Fin W → Int) (cells : Fin W → Int → Option Bool) :
    (machine P solveBanks testBanks).Config :=
  thenLeft solver P solveBanks testBanks
    (solver.bankConfig solveBanks (LiveInverse.start n x y prior) heads cells)

/-- Connect the two copies of each vertex by accepting the identity quotient. -/
def allowIdentity {n : Nat} (G : Group (Fin n)) (seed : Fin n → Bool) (x : Fin n) : Bool :=
  decide (x = G.toOne.one) || seed x

theorem allowIdentity_difference {n : Nat} (G : Group (Fin n)) (seed : Fin n → Bool)
    (x y : Fin n) :
    allowIdentity G seed (difference G x y) = true ↔
      (@BipartiteCayley.graph (Fin n) G {z | seed z = true}).Adj (.inl x) (.inr y) := by
  let _ : Group (Fin n) := G
  let _ : Mul (Fin n) := G.toMul
  let _ : Inv (Fin n) := G.toInv
  let _ : One (Fin n) := G.toOne
  change (decide (x⁻¹ * y = 1) || seed (x⁻¹ * y)) = true ↔
    x = y ∨ seed (x⁻¹ * y) = true
  rw [Bool.or_eq_true, decide_eq_true_eq, inv_mul_eq_one]

/-- Execute a live quotient lookup and hand its result to the predicate macro
on the same tapes. Banks disjoint from both computations are preserved. -/
theorem execute {n : Nat} (G : Group (Fin n)) (x y : Fin n) (P : SearchTransducer) {W : Nat}
    (solveBanks : Fin solver.workTapes ↪ Fin W) (testBanks : Fin P.workTapes ↪ Fin W)
    (argument : Fin P.workTapes) (wired : testBanks argument = solveBanks ⟨8, by decide⟩)
    (verdict : Fin P.states → Bool) (accept : Fin n → Bool)
    (prior : List Bool) (heads : Fin W → Int) (cells : Fin W → Int → Option Bool)
    (B : Nat) (cap : 3 * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B)
    (parked : ∀ i ∉ Set.range solveBanks, (heads i).natAbs ≤ B)
    (test :
      let word := @encodeCayley n G.toMul
      let Q := P.relocateBanks testBanks
      ∀ c : Q.Config, Q.Bounded word B c → c.state = P.initialState →
        c.outputReversed = prior →
        (∀ j ∉ Set.range solveBanks, c.workHead j = heads j ∧ c.workCell j = cells j) →
        c.workHead (testBanks argument) = 0 →
        c.workCell (testBanks argument) = InputPosition.work
          (encodeLabel (TableIO.width n) (difference G x y).val) →
        ∃ k d, Q.BoundedSegment word B c d k ∧ Q.step word d = none ∧
          verdict d.state = accept (difference G x y) ∧
          d.outputReversed = c.outputReversed ∧
          ∀ j ∉ Set.range testBanks, d.workHead j = c.workHead j ∧ d.workCell j = c.workCell j) :
    let word := @encodeCayley n G.toMul
    let M := machine P solveBanks testBanks
    ∃ (k : Nat) (exit : Fin P.states) (d : M.Config),
      M.BoundedSegment word B (entry P solveBanks testBanks n x.val y.val prior heads cells) d k ∧
      M.step word d = none ∧ d.state = Fin.natAdd solver.states exit ∧
      verdict exit = accept (difference G x y) ∧ d.outputReversed = prior ∧
      ∀ j, j ∉ Set.range solveBanks → j ∉ Set.range testBanks →
        d.workHead j = heads j ∧ d.workCell j = cells j := by
  let word := @encodeCayley n G.toMul
  obtain ⟨a, raw, ha, hs, label, output, zero⟩ := ReingoldLiveInput.liveDifference n G x y prior
  let mid := solver.bankConfig solveBanks raw heads cells
  have first := solver.relocateBanks_segment solveBanks (PhysicalEntry.segment_mono ha cap)
    (heads := heads) (cells := cells) parked
  have hS : (solver.relocateBanks solveBanks).step word mid = none := by
    unfold mid
    rw [solver.relocateBanks_step, hs]
    rfl
  let pass := thenEntry solver P solveBanks testBanks mid
  have hb := first.2 a le_rfl mid first.1
  have inputHead : pass.workHead (testBanks argument) = 0 := by
    change mid.workHead (testBanks argument) = 0
    rw [wired, bankConfig_head_image, zero]
  have inputCell : pass.workCell (testBanks argument) = InputPosition.work
      (encodeLabel (TableIO.width n) (difference G x y).val) := by
    change mid.workCell (testBanks argument) = _
    rw [wired, bankConfig_cell_image]
    exact label
  have unchanged : ∀ j ∉ Set.range solveBanks, pass.workHead j = heads j ∧
      pass.workCell j = cells j := fun j hj => solver.bankConfig_frame solveBanks raw heads cells hj
  obtain ⟨b, exit, second, halt, result, preserved, frame⟩ :=
    test pass hb rfl output unchanged inputHead inputCell
  let finish := thenRight solver P solveBanks testBanks exit
  refine ⟨a + 1 + b, exit.state, finish, thenSegment solver P solveBanks testBanks first hS second,
    ?_, rfl, result, preserved.trans output, ?_⟩
  · change (machine P solveBanks testBanks).step word finish = none
    rw [thenStep_right, halt]
    rfl
  · intro j hSolve hTest
    obtain ⟨h₁, h₂⟩ := frame j hTest
    obtain ⟨hm₁, hm₂⟩ := solver.bankConfig_frame solveBanks raw heads cells hSolve
    exact ⟨h₁.trans hm₁, h₂.trans hm₂⟩

end Mathproof.MinimumGeneration.OuterCayleyQuery
