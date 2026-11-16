import Mathproof.MinimumGenerationCayleyPrefixLeaf

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

/-- The literal entry registers. Slots one and four hold the wide row and
group order. The narrow target row, identity, and cutoff occupy slots seven,
nine, and ten respectively. -/
def entryRegisters (n x y identity cut : Nat) (i : Fin 11) : Int → Option Bool :=
  let w := TableIO.width n
  if i = 1 then work (encodeLabel (2*w) x)
  else if i = 4 then work (encodeLabel (2*w) n)
  else if i.val < 6 then work (encodeLabel (2*w) 0)
  else if i = 7 then work (encodeLabel w y)
  else if i = 9 then work (encodeLabel w identity)
  else if i = 10 then work (encodeLabel w cut)
  else work (encodeLabel w 0)

private theorem register_eq (w x : Nat) :
    TapeAddition.register w x = work (encodeLabel w x) := by
  funext p
  by_cases h : p ≤ 0
  · simp [TapeAddition.register, work, h, show p < 1 by omega]
  · simp [TapeAddition.register, work, h, show ¬ p < 1 by omega]

private theorem bitsZero (w : Nat) : encodeLabel w 0 = List.replicate w false := by
  have hz : Nat.testBit 0 = fun _ => false := funext Nat.zero_testBit
  simp [encodeLabel,hz]

theorem entry_layout (n x y identity cut : Nat) (prior : List Bool) :
    let c := entry n x y identity cut prior
    c.state = machine.initialState ∧ c.inputHead = (n+1 : Nat) ∧
      c.workHead = (fun _ => 0) ∧ c.workCell = entryRegisters n x y identity cut ∧
      c.outputReversed = prior := by
  dsimp only
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact register_eq _ _
    · exact register_eq _ _
    · exact register_eq _ _
    · exact register_eq _ _
    · exact register_eq _ _
    · exact register_eq _ _
    · change work (List.replicate (TableIO.width n) false) = work (encodeLabel (TableIO.width n) 0)
      rw [bitsZero]
    · rfl
    · rfl
    · rfl
    · rfl

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
