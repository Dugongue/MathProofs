import EvenP2FormsCoverage

/-! The successful form choice can be fixed once for each exact kernel fiber. -/
namespace Mathproof.EvenTI.Singular.Forms

open Mathproof.EvenOrdinaryTISingular
open EvenTI.Action Matrix Module
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {l n : ℕ}

structure GoodPair (R S : Submodule K (Coord (l+1) n → K)) where
  ell : Coord (l+1) n → K
  rho : Coord (l+1) n → K
  ell_ne_zero : ell ≠ 0
  rho_ne_zero : rho ≠ 0
  ell_mem : ell ∈ S
  rho_mem : rho ∈ R
  ell_rank : ∀ i, (retainedForm i ell).rank = n
  rho_rank : ∀ j, (retainedForm j rho).rank = n

variable {R S : Submodule K (Coord (l+1) n → K)}

theorem right_mem_iff_fiber (A : DenseKernelFiber R S) (x : Coord (l+1) n → K) :
    x ∈ R ↔ rightCutKernel A.val x = 0 := by
  change x ∈ R ↔ (flatten A.val).toLin' x = 0
  calc
    _ ↔ x ∈ (flatten A.val).toLin'.ker :=
      Iff.of_eq (congrArg (fun U : Submodule K _ => x ∈ U) A.property.1.symm)
    _ ↔ _ := LinearMap.mem_ker

theorem left_mem_iff_fiber (A : DenseKernelFiber R S) (x : Coord (l+1) n → K) :
    x ∈ S ↔ leftCutKernel A.val x = 0 := by
  change x ∈ S ↔ (flatten A.val)ᵀ.toLin' x = 0
  calc
    _ ↔ x ∈ (flatten A.val)ᵀ.toLin'.ker :=
      Iff.of_eq (congrArg (fun U : Submodule K _ => x ∈ U) A.property.2.symm)
    _ ↔ _ := LinearMap.mem_ker

/-- The bad form predicate is determined entirely by its cut kernel. -/
abbrev FiberBadForm (U : Submodule K (Coord (l+1) n → K)) : Prop :=
  ∃ x : Coord (l+1) n → K, x ≠ 0 ∧ x ∈ U ∧ BadRetained x

theorem badRightForm_iff_fiber (A : DenseKernelFiber R S) :
    BadRightForm A.val ↔ FiberBadForm R := by
  unfold BadRightForm FiberBadForm
  simp only [right_mem_iff_fiber A]

theorem badLeftForm_iff_fiber (A : DenseKernelFiber R S) :
    BadLeftForm A.val ↔ FiberBadForm S := by
  unfold BadLeftForm FiberBadForm
  simp only [left_mem_iff_fiber A]

theorem fiber_coranks_eq (A : DenseKernelFiber R S) :
    finrank K R = finrank K S := by
  let M := flatten A.val
  have hR := M.toLin'.finrank_range_add_finrank_ker
  have hS := Mᵀ.toLin'.finrank_range_add_finrank_ker
  change M.rank + finrank K M.toLin'.ker = finrank K (Coord (l+1) n → K) at hR
  change Mᵀ.rank + finrank K Mᵀ.toLin'.ker = finrank K (Coord (l+1) n → K) at hS
  have hR' : M.toLin'.ker = R := A.property.1
  have hS' : Mᵀ.toLin'.ker = S := A.property.2
  rw [hR'] at hR
  rw [hS', Matrix.rank_transpose] at hS
  omega

theorem fiber_singular_iff (A : DenseKernelFiber R S) :
    (flatten A.val).det = 0 ↔ R ≠ ⊥ := by
  rw [← Matrix.exists_mulVec_eq_zero_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, (right_mem_iff_fiber A x).mpr he, hx⟩
  · rintro ⟨x, hx, hnz⟩
    exact ⟨x, hnz, (right_mem_iff_fiber A x).mp hx⟩

variable [Fintype K]

theorem nonemptyGoodPair_of_raw (A : DenseKernelFiber R S) (hs : (flatten A.val).det = 0)
    (hL : ¬ BadLeftForm A.val) (hR : ¬ BadRightForm A.val) : Nonempty (GoodPair R S) := by
  obtain ⟨ell, rho, henz, he, hEr, hrnz, hr, hRr⟩ := singular_good_forms A.val hs hL hR
  exact ⟨⟨ell, rho, henz, hrnz, (left_mem_iff_fiber A ell).mpr he,
    (right_mem_iff_fiber A rho).mpr hr, hEr, hRr⟩⟩

def goodPair_of_raw (A : DenseKernelFiber R S) (hs : (flatten A.val).det = 0)
    (hL : ¬ BadLeftForm A.val) (hR : ¬ BadRightForm A.val) : GoodPair R S :=
  Classical.choice (nonemptyGoodPair_of_raw A hs hL hR)

theorem nonemptyGoodPair_of_fiber (A : DenseKernelFiber R S) (hs : R ≠ ⊥)
    (hL : ¬ FiberBadForm S) (hR : ¬ FiberBadForm R) : Nonempty (GoodPair R S) :=
  nonemptyGoodPair_of_raw A ((fiber_singular_iff A).mpr hs)
    (fun h => hL ((badLeftForm_iff_fiber A).mp h)) (fun h => hR ((badRightForm_iff_fiber A).mp h))

#print axioms goodPair_of_raw
#print axioms fiber_coranks_eq
#print axioms fiber_singular_iff
#print axioms nonemptyGoodPair_of_fiber

end
end Mathproof.EvenTI.Singular.Forms
