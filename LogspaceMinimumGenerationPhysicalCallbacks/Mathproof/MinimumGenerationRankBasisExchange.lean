import Mathproof.MinimumGenerationRankIsolation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace Mathproof.MinimumGeneration.RankIsolation

open Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype ι] [DecidableEq ι]

theorem finrank_span_image_eq_card (v : ι → V) {I : Finset ι}
    (hI : LinearIndepOn K v (I : Set ι)) :
    Module.finrank K (span K (v '' (I : Set ι))) = I.card := by
  have hr : Set.range (fun x : (I : Set ι) => v x.val) = v '' (I : Set ι) := by
    ext y
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hr, finrank_span_eq_card (show LinearIndependent K (fun x : (I : Set ι) => v x.val) from hI)]
  rw [← Set.toFinset_card]
  simp

/-- A label from one independent spanning family can be inserted into the other
by removing a label absent from the first family. No bounds on the field or
vector-space dimensions are required. -/
theorem exists_basis_exchange_for_same_span (v : ι → V) {I J : Finset ι}
    (hI : LinearIndepOn K v (I : Set ι)) (hJ : LinearIndepOn K v (J : Set ι))
    (hspan : span K (v '' (I : Set ι)) = span K (v '' (J : Set ι)))
    {i : ι} (hiI : i ∈ I) (hiJ : i ∉ J) :
    ∃ j ∈ J, j ∉ I ∧
      LinearIndepOn K v (↑(insert i (J.erase j)) : Set ι) ∧
      span K (v '' (↑(insert i (J.erase j)) : Set ι)) = span K (v '' (J : Set ι)) := by
  classical
  let S : Set ι := insert i ((I : Set ι) ∩ (J : Set ι))
  let T : Set ι := insert i (J : Set ι)
  have hSI : S ⊆ (I : Set ι) := by
    intro a ha
    rcases ha with he | ha
    · subst a
      exact hiI
    · exact ha.1
  have hST : S ⊆ T := by
    intro a ha
    rcases ha with he | ha
    · subst a
      exact Or.inl rfl
    · exact Or.inr ha.2
  have hS := hI.mono hSI
  let U := (hS.extend hST).toFinset
  have hU : (U : Set ι) = hS.extend hST := Set.coe_toFinset _
  have hUs : S ⊆ (U : Set ι) := by rw [hU]; exact hS.subset_extend hST
  have hUt : (U : Set ι) ⊆ T := by rw [hU]; exact hS.extend_subset hST
  have hUi : LinearIndepOn K v (U : Set ι) := by rw [hU]; exact hS.linearIndepOn_extend hST
  have hiv : v i ∈ span K (v '' (J : Set ι)) := by
    rw [← hspan]
    exact subset_span ⟨i, hiI, rfl⟩
  have hUspan : span K (v '' (U : Set ι)) = span K (v '' (J : Set ι)) := by
    rw [hU, hS.span_image_extend_eq_span_image hST]
    change span K (v '' insert i (J : Set ι)) = _
    rw [Set.image_insert_eq, span_insert_eq_span hiv]
  have hcard : U.card = J.card := by
    rw [← finrank_span_image_eq_card v hUi, ← finrank_span_image_eq_card v hJ, hUspan]
  have hiU : i ∈ U := hUs (Or.inl rfl)
  have hj : ∃ j ∈ J, j ∉ U := by
    by_contra! hJU
    have he : J = U := Finset.eq_of_subset_of_card_le hJU hcard.le
    exact hiJ (he.symm ▸ hiU)
  obtain ⟨j, hjJ, hjU⟩ := hj
  have hjI : j ∉ I := fun hjI => hjU (hUs (Or.inr ⟨hjI, hjJ⟩))
  have hsub : U ⊆ insert i (J.erase j) := by
    intro a ha
    have hT := hUt (show a ∈ (U : Set ι) from ha)
    rcases hT with he | haJ
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨
        fun he => hjU (he ▸ ha), haJ⟩)
  have hcount : (insert i (J.erase j)).card = J.card := by
    rw [Finset.card_insert_of_notMem (fun h => hiJ (Finset.mem_of_mem_erase h)),
      Finset.card_erase_add_one hjJ]
  have he := Finset.eq_of_subset_of_card_le hsub (hcount.trans hcard.symm).le
  exact ⟨j, hjJ, hjI, he ▸ hUi, he ▸ hUspan⟩

/-- Every finite spanning family has a uniquely lightest basis for strictly
increasing natural weights. The selected subfamily is an existence witness
used to prove that the determinant probe has a noncanceling coefficient. -/
theorem exists_unique_minimum_spanning_basis [LinearOrder ι]
    (v : ι → V) (u : Finset ι) (w : ι → ℕ) (hw : StrictMono w) :
    ∃ I : Finset ι, I ⊆ u ∧ LinearIndepOn K v (I : Set ι) ∧
      span K (v '' (I : Set ι)) = span K (v '' (u : Set ι)) ∧
      ∀ J : Finset ι, J ⊆ u → LinearIndepOn K v (J : Set ι) →
        span K (v '' (J : Set ι)) = span K (v '' (u : Set ι)) →
          J ≠ I → (∑ i ∈ I, w i) < ∑ j ∈ J, w j := by
  classical
  letI : DecidableEq ι := LinearOrder.toDecidableEq
  let B := u.powerset.filter fun I : Finset ι =>
    LinearIndepOn K v (I : Set ι) ∧ span K (v '' (I : Set ι)) = span K (v '' (u : Set ι))
  have hB (I : Finset ι) : I ∈ B ↔ I ⊆ u ∧ LinearIndepOn K v (I : Set ι) ∧
      span K (v '' (I : Set ι)) = span K (v '' (u : Set ι)) := by
    simp [B]
  have hne : B.Nonempty := by
    have hempty : LinearIndepOn K v (∅ : Set ι) := linearIndepOn_empty _ _
    let T := hempty.extend (Set.empty_subset (u : Set ι))
    refine ⟨T.toFinset, (hB _).mpr ⟨?_, ?_, ?_⟩⟩
    · intro i hi
      have hiT : i ∈ T := Set.mem_toFinset.mp hi
      exact hempty.extend_subset _ hiT
    · rw [Set.coe_toFinset]
      exact hempty.linearIndepOn_extend _
    · rw [Set.coe_toFinset]
      exact hempty.span_image_extend_eq_span_image _
  have hcard : ∀ I ∈ B, ∀ J ∈ B, I.card = J.card := by
    intro I hI J hJ
    obtain ⟨_, hIi, hIs⟩ := (hB I).mp hI
    obtain ⟨_, hJi, hJs⟩ := (hB J).mp hJ
    rw [← finrank_span_image_eq_card v hIi, ← finrank_span_image_eq_card v hJi, hIs, hJs]
  have hex : ∀ I ∈ B, ∀ J ∈ B, ∀ i ∈ I, i ∉ J →
      ∃ j ∈ J, j ∉ I ∧ insert i (J.erase j) ∈ B := by
    intro I hI J hJ i hiI hiJ
    obtain ⟨hIu, hIi, hIs⟩ := (hB I).mp hI
    obtain ⟨hJu, hJi, hJs⟩ := (hB J).mp hJ
    obtain ⟨j, hjJ, hjI, hx, hs⟩ :=
      exists_basis_exchange_for_same_span v hIi hJi (hIs.trans hJs.symm) hiI hiJ
    refine ⟨j, hjJ, hjI, (hB _).mpr ⟨?_, hx, hs.trans hJs⟩⟩
    exact Finset.insert_subset (hIu hiI) ((Finset.erase_subset _ _).trans hJu)
  obtain ⟨I, hI, hmin⟩ := exists_unique_minimum_basis_weight B w hw hne hcard hex
  obtain ⟨hIu, hIi, hIs⟩ := (hB I).mp hI
  exact ⟨I, hIu, hIi, hIs, fun J hJu hJi hJs hn => hmin J ((hB J).mpr ⟨hJu, hJi, hJs⟩) hn⟩

end Mathproof.MinimumGeneration.RankIsolation
