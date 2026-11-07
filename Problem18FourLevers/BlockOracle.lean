import Mathlib.Logic.Equiv.Basic

/-! A zero-error assembly rule for an intrinsically unordered family of blocks. -/
namespace BlockOracle

variable {I J : Type}

def Matching (R : I → J → Prop) : Prop :=
  ∃ e : I ≃ J, ∀ i, R i (e i)

theorem matching_mono {R S : I → J → Prop}
    (h : ∀ i j, R i j → S i j) : Matching R → Matching S := by
  rintro ⟨e, he⟩
  exact ⟨e, fun i => h i (e i) (he i)⟩

def confirmed (test : I → J → Option Bool) (i : I) (j : J) : Bool :=
  test i j == some true

def possible (test : I → J → Option Bool) (i : I) (j : J) : Bool :=
  !(test i j == some false)

def combine (matcher : (I → J → Bool) → Bool)
    (test : I → J → Option Bool) : Option Bool :=
  if matcher (confirmed test) then some true
  else if matcher (possible test) then none
  else some false

theorem confirmed_subset {R : I → J → Prop} {test : I → J → Option Bool}
    (yes : ∀ i j, test i j = some true → R i j) :
    ∀ i j, confirmed test i j = true → R i j := by
  intro i j h
  exact yes i j (by simpa [confirmed] using h)

theorem subset_possible {R : I → J → Prop} {test : I → J → Option Bool}
    (no : ∀ i j, test i j = some false → ¬ R i j) :
    ∀ i j, R i j → possible test i j = true := by
  intro i j h
  cases e : test i j with
  | none => simp [possible, e]
  | some b =>
    cases b with
    | false => exact False.elim (no i j e h)
    | true => simp [possible, e]

theorem combine_sound {R : I → J → Prop} {test : I → J → Option Bool}
    {matcher : (I → J → Bool) → Bool}
    (correct : ∀ a, matcher a = true ↔ Matching (fun i j => a i j = true))
    (yes : ∀ i j, test i j = some true → R i j)
    (no : ∀ i j, test i j = some false → ¬ R i j) :
    (combine matcher test = some true → Matching R) ∧
    (combine matcher test = some false → ¬ Matching R) := by
  constructor
  · intro h
    by_cases hc : matcher (confirmed test) = true
    · exact matching_mono (confirmed_subset yes) ((correct _).mp hc)
    · by_cases hp : matcher (possible test) = true <;> simp [combine, hc, hp] at h
  · intro h hr
    have hp : matcher (possible test) = true :=
      (correct _).mpr (matching_mono (subset_possible no) hr)
    by_cases hc : matcher (confirmed test) = true <;> simp [combine, hc, hp] at h

theorem combine_total_if_edges_decided
    {test : I → J → Option Bool} {matcher : (I → J → Bool) → Bool}
    (correct : ∀ a, matcher a = true ↔ Matching (fun i j => a i j = true))
    (total : ∀ i j, test i j ≠ none) :
    combine matcher test ≠ none := by
  by_cases hc : matcher (confirmed test) = true
  · simp [combine, hc]
  · have hp : matcher (possible test) ≠ true := by
      intro hp
      apply hc
      apply (correct _).mpr
      apply matching_mono _ ((correct _).mp hp)
      intro i j h
      cases e : test i j with
      | none => exact False.elim (total i j e)
      | some b => cases b <;> simp [confirmed, possible, e] at h ⊢
    simp [combine, hc, hp]

#print axioms combine_sound
#print axioms combine_total_if_edges_decided

/-- When this assembly abstains, the least and greatest edge completions
give opposite answers. Both respect the local YES and NO information. -/
theorem combine_unknown_iff {test : I → J → Option Bool}
    {matcher : (I → J → Bool) → Bool}
    (correct : ∀ a, matcher a = true ↔ Matching (fun i j => a i j = true)) :
    combine matcher test = none ↔
      ¬ Matching (fun i j => confirmed test i j = true) ∧
        Matching (fun i j => possible test i j = true) := by
  by_cases hc : matcher (confirmed test) = true <;>
    by_cases hp : matcher (possible test) = true <;>
    simp [combine, hc, hp, ← correct]

#print axioms combine_unknown_iff

end BlockOracle
