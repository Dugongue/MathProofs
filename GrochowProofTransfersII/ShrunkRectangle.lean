import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Find

namespace ShrunkRectangle

open Module

variable {K V W ι : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def images (A : ι → V →ₗ[K] W) (U : Submodule K V) : Submodule K W :=
  ⨆ i, U.map (A i)

noncomputable def deficiency (A : ι → V →ₗ[K] W) (U : Submodule K V) : ℤ :=
  (finrank K U : ℤ) - finrank K (images A U)

omit [FiniteDimensional K V] [FiniteDimensional K W] in
lemma images_mono (A : ι → V →ₗ[K] W) {U T : Submodule K V} (h : U ≤ T) :
    images A U ≤ images A T :=
  iSup_mono (fun _ => Submodule.map_mono h)

omit [FiniteDimensional K V] [FiniteDimensional K W] in
lemma images_sup (A : ι → V →ₗ[K] W) (U T : Submodule K V) :
    images A (U ⊔ T) = images A U ⊔ images A T := by
  simp only [images, Submodule.map_sup, iSup_sup_eq]

theorem deficiency_supermodular (A : ι → V →ₗ[K] W) (U T : Submodule K V) :
    deficiency A U + deficiency A T ≤
      deficiency A (U ⊔ T) + deficiency A (U ⊓ T) := by
  have hu := Submodule.finrank_sup_add_finrank_inf_eq U T
  have hw := Submodule.finrank_sup_add_finrank_inf_eq (images A U) (images A T)
  have hcap : images A (U ⊓ T) ≤ images A U ⊓ images A T :=
    le_inf (images_mono A inf_le_left) (images_mono A inf_le_right)
  have hdim := Submodule.finrank_mono hcap
  unfold deficiency
  rw [images_sup]
  omega

theorem exists_largest_maximizer (A : ι → V →ₗ[K] W) {b : ℤ}
    (hbest : ∃ U : Submodule K V, deficiency A U = b)
    (hub : ∀ U : Submodule K V, deficiency A U ≤ b) :
    ∃ U : Submodule K V, deficiency A U = b ∧
      ∀ T : Submodule K V, deficiency A T = b → T ≤ U := by
  classical
  let P (n : ℕ) := ∃ U : Submodule K V, deficiency A U = b ∧ finrank K U = n
  obtain ⟨T, hT⟩ := hbest
  have h0 : P (finrank K T) := ⟨T, hT, rfl⟩
  have hmax : P (Nat.findGreatest P (finrank K V)) :=
    Nat.findGreatest_spec (Submodule.finrank_le T) h0
  obtain ⟨U, hU, hdim⟩ := hmax
  refine ⟨U, hU, ?_⟩
  intro S hS
  have hsup : deficiency A (U ⊔ S) = b := by
    have h := deficiency_supermodular A U S
    have hinter := hub (U ⊓ S)
    have hupper := hub (U ⊔ S)
    omega
  have hP : P (finrank K (U ⊔ S : Submodule K V)) := ⟨U ⊔ S, hsup, rfl⟩
  have hle : finrank K (U ⊔ S : Submodule K V) ≤ finrank K U :=
    (Nat.le_findGreatest (Submodule.finrank_le (U ⊔ S)) hP).trans_eq hdim.symm
  have heq : U = U ⊔ S := Submodule.eq_of_le_of_finrank_le le_sup_left hle
  rw [heq]
  exact le_sup_right

end ShrunkRectangle
