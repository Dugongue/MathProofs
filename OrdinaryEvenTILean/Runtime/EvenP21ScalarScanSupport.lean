import EvenP18ScalarProbeSubgroup

set_option autoImplicit false

namespace EvenTI.P21ScalarScan

open EvenTI.P18Scalar (chartResidueSubgroup)

/-- If every site is active, a single selected site supplies its reference.
The same statement covers empty modes. -/
theorem unpaddedChartMembership_iff {M L n : ℕ} (chart : List ℕ) (zero : ℕ)
    (site : Fin L → Fin n) (reference : Fin n) (z : Fin n → ZMod M)
    (active : ∀ i : Fin L, chart.getD i.val 0 ≠ zero)
    (refSite : ∀ i : Fin L, ∃ j : Fin L, site j = reference) :
    z ∈ chartResidueSubgroup chart zero site reference ↔
      ∀ i j : Fin L, z (site i) = z (site j) := by
  change (∀ i : Fin L, chart.getD i.val 0 ≠ zero → z (site i) = z reference) ↔ _
  constructor
  · intro h i j
    exact (h i (active i)).trans (h j (active j)).symm
  · intro h i _
    obtain ⟨j,hj⟩ := refSite i
    exact (h i j).trans (congrArg z hj)

/-- A zero-filled physical chart represents full support when inactive cells
would use marker `1`. Only the installed native site addresses matter. -/
theorem zeroChartMembership_iff {M L n c : ℕ}
    (site : Fin L → Fin n) (reference : Fin n) (z : Fin n → ZMod M)
    (refSite : ∀ i : Fin L, ∃ j : Fin L, site j = reference) :
    z ∈ chartResidueSubgroup (List.replicate c 0) 1 site reference ↔
      ∀ i j : Fin L, z (site i) = z (site j) := by
  apply unpaddedChartMembership_iff _ _ _ _ _ _ refSite
  intro i
  change (List.replicate c 0).getD i.val 0 ≠ 1
  simp [List.getD_eq_getElem?_getD]

#print axioms unpaddedChartMembership_iff
#print axioms zeroChartMembership_iff
end EvenTI.P21ScalarScan
