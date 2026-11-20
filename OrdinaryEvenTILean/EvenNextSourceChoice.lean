import EvenNextTargetPairs

namespace EvenTI.Contract
open Action

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

def chooseSourceForms (F : FieldEncoding K) (T : Tensor K ((l + 1) + (r + 1)) n)
    (frames : CutFrames T)
    (leftGood : (Coord (l + 1) n → K) → Bool)
    (rightGood : (Coord (r + 1) n → K) → Bool)
    (shape : CutFormPair K (l + 1) (r + 1) n → Bool) :
    Option (CutFormPair K (l + 1) (r + 1) n) :=
  (cutFormPairs F T frames leftGood rightGood).find? shape

theorem chooseSourceForms_spec (F : FieldEncoding K) (T : Tensor K ((l + 1) + (r + 1)) n)
    (frames : CutFrames T)
    (leftGood : (Coord (l + 1) n → K) → Bool)
    (rightGood : (Coord (r + 1) n → K) → Bool)
    (shape : CutFormPair K (l + 1) (r + 1) n → Bool) :
    (chooseSourceForms F T frames leftGood rightGood shape).isSome ↔
      ∃ p ∈ cutFormPairs F T frames leftGood rightGood, shape p = true :=
  List.find?_isSome

theorem chooseSourceForms_invariant (F : FieldEncoding K)
    (frames : ∀ T : Tensor K ((l + 1) + (r + 1)) n, CutFrames T)
    (leftGood : (Coord (l + 1) n → K) → Bool)
    (rightGood : (Coord (r + 1) n → K) → Bool)
    (leftSpec : ∀ x, leftGood x = true ↔ ∀ i, (retainedForm i x).rank = n)
    (rightSpec : ∀ y, rightGood y = true ↔ ∀ i, (retainedForm i y).rank = n)
    (shape : Tensor K ((l + 1) + (r + 1)) n → CutFormPair K (l + 1) (r + 1) n → Bool)
    (shapeCovariant : ∀ U a p, p ∈ cutFormPairs F U (frames U) leftGood rightGood →
      shape (act a U) (moveLeftForm a p.1, moveRightForm a p.2) = shape U p)
    (T : Tensor K ((l + 1) + (r + 1)) n) (g : Changes K ((l + 1) + (r + 1)) n) :
    (chooseSourceForms F (act g T) (frames (act g T)) leftGood rightGood (shape (act g T))).isSome ↔
      (chooseSourceForms F T (frames T) leftGood rightGood (shape T)).isSome := by
  simp only [chooseSourceForms_spec]
  have forward (U : Tensor K ((l + 1) + (r + 1)) n)
      (a : Changes K ((l + 1) + (r + 1)) n)
      (h : ∃ p ∈ cutFormPairs F U (frames U) leftGood rightGood, shape U p = true) :
      ∃ p ∈ cutFormPairs F (act a U) (frames (act a U)) leftGood rightGood, shape (act a U) p = true := by
    obtain ⟨⟨x, y⟩, hp, hs⟩ := h
    refine ⟨(moveLeftForm a x, moveRightForm a y), ?_, ?_⟩
    · exact cutFormPairs_transport_of_ranks F (frames U) (frames (act a U))
        a rfl leftGood rightGood leftSpec rightSpec x y hp
    · exact (shapeCovariant U a (x, y) hp).trans hs
  constructor
  · intro h
    have hinv : act g⁻¹ (act g T) = T := by rw [← act_mul, inv_mul_cancel, act_one]
    let P := fun U => ∃ p ∈ cutFormPairs F U (frames U) leftGood rightGood, shape U p = true
    have hw : P (act g⁻¹ (act g T)) := forward (act g T) g⁻¹ h
    exact Eq.mp (congrArg P hinv) hw
  · exact forward T g

#print axioms chooseSourceForms_spec
#print axioms chooseSourceForms_invariant

end EvenTI.Contract
