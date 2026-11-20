import EvenScalarCertification
import Mathlib.Data.List.FinRange

namespace EvenTI.Action

variable {K : Type*} [Field K] [DecidableEq K] {d n q : Nat}

def onlyScalarModes (enum : Fin q ≃ Kˣ) (a : Changes K d n) : Bool :=
  (List.finRange d).all fun i =>
    (List.finRange q).any fun j => decide (a i = scalar (enum j))

theorem onlyScalarModes_iff (enum : Fin q ≃ Kˣ) (a : Changes K d n) :
    onlyScalarModes enum a = true ↔ ∃ u : Fin d → Kˣ, a = scalars u := by
  simp only [onlyScalarModes, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies, true_and]
  constructor
  · intro h
    choose j hj using h
    exact ⟨fun i => enum (j i), funext hj⟩
  · rintro ⟨u, rfl⟩ i
    exact ⟨enum.symm (u i), by simp [scalars]⟩

structure StabilizerTrial (K : Type*) [Field K] (d n : Nat) where
  representative : Changes K d n
  generators : List (Changes K d n)

/-- A finite test on a completed self-comparison scan. -/
def verifyScalarTrials (enum : Fin q ≃ Kˣ) (xs : List (StabilizerTrial K d n)) : Bool :=
  xs.all fun p => onlyScalarModes enum p.representative && p.generators.all (onlyScalarModes enum)

theorem verifyScalarTrials_iff (enum : Fin q ≃ Kˣ)
    (xs : List (StabilizerTrial K d n)) (T : Tensor K d n)
    (cover : ∀ a, act a T = T → ∃ p ∈ xs, ∃ u,
      u ∈ Subgroup.closure {z | z ∈ p.generators} ∧ a = p.representative * u)
    (validRepresentative : ∀ p ∈ xs, act p.representative T = T)
    (validGenerator : ∀ p ∈ xs, ∀ z ∈ p.generators, act z T = T) :
    verifyScalarTrials enum xs = true ↔
      ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u := by
  simp only [verifyScalarTrials, List.all_eq_true, Bool.and_eq_true, onlyScalarModes_iff]
  constructor
  · intro h
    apply scalarOnly_of_branch_generators
      (representative := fun p : {p // p ∈ xs} => p.val.representative)
      (generators := fun p : {p // p ∈ xs} => {z | z ∈ p.val.generators})
    · intro a ha
      obtain ⟨p, hp, u, hu, he⟩ := cover a ha
      exact ⟨⟨p, hp⟩, u, hu, he⟩
    · exact fun p => (h p.val p.property).1
    · exact fun p z hz => (h p.val p.property).2 z hz
  · intro h p hp
    exact ⟨h _ (validRepresentative p hp), fun z hz => h z (validGenerator p hp z hz)⟩

#print axioms onlyScalarModes_iff
#print axioms verifyScalarTrials_iff

end EvenTI.Action
