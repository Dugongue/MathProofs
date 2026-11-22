import EvenP21PadBasisSupport

set_option autoImplicit false

namespace EvenTI.P22Scalar

open Matrix

variable {K I J C L : Type} [Field K]

private theorem all_columns_zero_iff_span (P : Matrix C I K)
    (label : I → L) (u : L) (c : C) :
    (∀ i, label i=u → P c i=0) ↔
      Submodule.span K (P.col '' {i | label i=u}) ≤ LinearMap.ker (LinearMap.proj c) := by
  constructor
  · intro hz
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact LinearMap.mem_ker.mpr (hz i hi)
  · intro h i hi
    have hm : P.col i ∈ Submodule.span K (P.col '' {j | label j=u}) :=
      Submodule.subset_span ⟨i,hi,rfl⟩
    exact LinearMap.mem_ker.mp (h hm)

/-- For the dual occurrence, retained support of a transposed frame
depends only on the primary column spans of the original frame.
The two frames can store their primary blocks in different orders. -/
theorem transposeSupport_iff_of_columnSpans
    (P : Matrix C I K) (Q : Matrix C J K) (labelP : I → L) (labelQ : J → L)
    (spans : ∀ u, Submodule.span K (P.col '' {i | labelP i=u}) =
      Submodule.span K (Q.col '' {j | labelQ j=u}))
    (keep : C → Prop) (u : L) :
    (∃ c, keep c ∧ ∃ i, labelP i=u ∧ Pᵀ i c≠0) ↔
      ∃ c, keep c ∧ ∃ j, labelQ j=u ∧ Qᵀ j c≠0 := by
  have eqZero (c : C) : (∀ i, labelP i=u → P c i=0) ↔ (∀ j, labelQ j=u → Q c j=0) := by
    rw [all_columns_zero_iff_span,all_columns_zero_iff_span,spans]
  have eqNZ (c : C) : (∃ i, labelP i=u ∧ Pᵀ i c≠0) ↔
      ∃ j, labelQ j=u ∧ Qᵀ j c≠0 := by
    classical
    constructor
    · rintro ⟨i,hi,hnz⟩
      by_contra h
      have hz (j) (hj : labelQ j=u) : Q c j=0 := by
        by_contra h'
        exact h ⟨j,hj,h'⟩
      exact hnz ((eqZero c).mpr hz i hi)
    · rintro ⟨j,hj,hnz⟩
      by_contra h
      have hz (i) (hi : labelP i=u) : P c i=0 := by
        by_contra h'
        exact h ⟨i,hi,h'⟩
      exact hnz ((eqZero c).mp hz j hj)
  exact exists_congr (fun c => and_congr_right (fun _ => eqNZ c))

#print axioms transposeSupport_iff_of_columnSpans
end EvenTI.P22Scalar


