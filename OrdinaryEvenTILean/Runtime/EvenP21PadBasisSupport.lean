import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false

namespace EvenTI.P21Pad

open Module

variable {K V I J L C : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The inverse-chart coordinates in one primary block vanish exactly when
the vector lies in the span of every other primary block. -/
theorem basisBlockSupport_iff_complement (B : Basis I K V) (label : I → L)
    (v : L) (x : V) :
    (∃ i, label i = v ∧ B.repr x i ≠ 0) ↔
      x ∉ Submodule.span K (B '' {i | label i ≠ v}) := by
  classical
  rw [B.mem_span_image]
  constructor
  · rintro ⟨i,hi,hz⟩ hc
    exact (hc (show i ∈ (B.repr x).support from Finsupp.mem_support_iff.mpr hz)) hi
  · intro h
    by_contra hn
    apply h
    intro i hi he
    exact hn ⟨i,he,Finsupp.mem_support_iff.mp hi⟩

private theorem complement_span_le (B : Basis I K V) (D : Basis J K V)
    (b : I → L) (d : J → L) (v : L)
    (h : ∀ f, Submodule.span K (B '' {i | b i = f}) ≤
      Submodule.span K (D '' {j | d j = f})) :
    Submodule.span K (B '' {i | b i ≠ v}) ≤ Submodule.span K (D '' {j | d j ≠ v}) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  have hB : B i ∈ Submodule.span K (B '' {k | b k = b i}) :=
    Submodule.subset_span ⟨i,rfl,rfl⟩
  have hD := h (b i) hB
  apply Submodule.span_mono _ hD
  apply Set.image_mono
  intro j hj
  change d j = b i at hj
  exact hj.trans_ne hi

/-- A paid chart may choose any basis of each intrinsic primary subspace.
At every retained column it yields exactly the same active primary blocks,
even when its rows and factor blocks are ordered differently. -/
theorem basisBlockSupport_iff_of_primarySpans (B : Basis I K V) (D : Basis J K V)
    (b : I → L) (d : J → L)
    (h : ∀ f, Submodule.span K (B '' {i | b i = f}) =
      Submodule.span K (D '' {j | d j = f}))
    (vectors : C → V) (keep : C → Prop) (v : L) :
    (∃ c, keep c ∧ ∃ i, b i = v ∧ B.repr (vectors c) i ≠ 0) ↔
      ∃ c, keep c ∧ ∃ j, d j = v ∧ D.repr (vectors c) j ≠ 0 := by
  have eqSpan : Submodule.span K (B '' {i | b i ≠ v}) =
      Submodule.span K (D '' {j | d j ≠ v}) :=
    le_antisymm (complement_span_le B D b d v (fun f => le_of_eq (h f)))
      (complement_span_le D B d b v (fun f => le_of_eq (h f).symm))
  simp only [basisBlockSupport_iff_complement,eqSpan]


section MatrixFrame

variable {n : ℕ}

private noncomputable def matrixSourceBasis (U : (Matrix (Fin n) (Fin n) K)ˣ) :
    Basis (Fin n) K (Fin n → K) :=
  (Pi.basisFun K (Fin n)).map (Matrix.toLin'OfInv U.inv_val U.val_inv)

private theorem matrixSourceBasis_repr (U : (Matrix (Fin n) (Fin n) K)ˣ)
    (i j : Fin n) : (matrixSourceBasis U).repr (Pi.single j 1) i = U.inv i j := by
  change (Pi.basisFun K (Fin n)).repr (U.inv.mulVec (Pi.single j 1)) i = _
  rw [Pi.basisFun_repr,Matrix.mulVec_single_one]
  rfl

private theorem matrixSourceBasis_apply (U : (Matrix (Fin n) (Fin n) K)ˣ)
    (i : Fin n) : matrixSourceBasis U i = U.val.col i := by
  rw [matrixSourceBasis,Basis.map_apply,Pi.basisFun_apply]
  change U.val.mulVec (Pi.single i 1) = _
  rw [Matrix.mulVec_single_one]

/-- The actual inverse matrix entries used by the crop mask can use any
basis of each primary space. Both frames may enumerate factors independently. -/
theorem inverseMatrixSupport_iff_of_columnSpans
    (U D : (Matrix (Fin n) (Fin n) K)ˣ) (b d : Fin n → L)
    (h : ∀ f, Submodule.span K (U.val.col '' {i | b i = f}) =
      Submodule.span K (D.val.col '' {j | d j = f}))
    (keep : Fin n → Prop) (v : L) :
    (∃ c, keep c ∧ ∃ i, b i = v ∧ U.inv i c ≠ 0) ↔
      ∃ c, keep c ∧ ∃ j, d j = v ∧ D.inv j c ≠ 0 := by
  have hU : (matrixSourceBasis U : Fin n → Fin n → K) = U.val.col :=
    funext (matrixSourceBasis_apply U)
  have hD : (matrixSourceBasis D : Fin n → Fin n → K) = D.val.col :=
    funext (matrixSourceBasis_apply D)
  simpa only [matrixSourceBasis_repr] using
    basisBlockSupport_iff_of_primarySpans (matrixSourceBasis U) (matrixSourceBasis D)
      b d (by simpa only [hU,hD] using h) (fun c => Pi.single c 1) keep v

end MatrixFrame

#print axioms inverseMatrixSupport_iff_of_columnSpans
#print axioms basisBlockSupport_iff_complement
#print axioms basisBlockSupport_iff_of_primarySpans
end EvenTI.P21Pad


