import EvenNextRetainedCovariance
import EvenNextPairChoices
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace EvenTI.Contract
open Action Matrix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

theorem flatten_rank_act (g : Changes K (l + r) n) (T : Tensor K (l + r) n) :
    (flatten (act g T)).rank = (flatten T).rank := by
  let L := productUnit (leftModes g)
  let R := productUnit (rightModes g)
  have hL : (productMatrix (leftModes g)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp L.isUnit).ne_zero
  have hR : (productMatrix (rightModes g)).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp R.isUnit).ne_zero
  rw [flatten_action, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hR,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hL]

theorem cutFrames_dimensions_transport (g : Changes K (l + r) n)
    {T S : Tensor K (l + r) n} (hg : act g T = S) (ft : CutFrames T) (fs : CutFrames S) :
    ft.leftDim = fs.leftDim ∧ ft.rightDim = fs.rightDim := by
  have hr := flatten_rank_act g T
  rw [hg] at hr
  have hl (U : Tensor K (l + r) n) :
      (flatten U).rank + Module.finrank K (leftCutKernel U).ker =
        Module.finrank K (Coord l n → K) := by
    rw [← Matrix.rank_transpose]
    exact (leftCutKernel U).finrank_range_add_finrank_ker
  have hh (U : Tensor K (l + r) n) :
      (flatten U).rank + Module.finrank K (rightCutKernel U).ker =
        Module.finrank K (Coord r n → K) :=
    (rightCutKernel U).finrank_range_add_finrank_ker
  have hfl (U : Tensor K (l + r) n) (fu : CutFrames U) :
      fu.leftDim = Module.finrank K (leftCutKernel U).ker := by
    simpa using fu.left.finrank_eq
  have hfr (U : Tensor K (l + r) n) (fu : CutFrames U) :
      fu.rightDim = Module.finrank K (rightCutKernel U).ker := by
    simpa using fu.right.finrank_eq
  constructor <;> [rw [hfl T ft, hfl S fs]; rw [hfr T ft, hfr S fs]]
  · have ht := hl T
    have hs := hl S
    omega
  · have ht := hh T
    have hs := hh S
    omega

/-- The transported pair appears in the target list. Both corank budgets
and all physical rank tests follow from membership in the source list. -/
theorem cutFormPairs_transport_of_ranks (F : FieldEncoding K)
    {T S : Tensor K ((l + 1) + (r + 1)) n} (ft : CutFrames T) (fs : CutFrames S)
    (g : Changes K ((l + 1) + (r + 1)) n) (hg : act g T = S)
    (gLeft : (Coord (l + 1) n → K) → Bool) (gRight : (Coord (r + 1) n → K) → Bool)
    (leftSpec : ∀ x, gLeft x = true ↔ ∀ i, (retainedForm i x).rank = n)
    (rightSpec : ∀ y, gRight y = true ↔ ∀ i, (retainedForm i y).rank = n)
    (x : Coord (l + 1) n → K) (y : Coord (r + 1) n → K)
    (hsrc : (x, y) ∈ cutFormPairs F T ft gLeft gRight) :
    (moveLeftForm g x, moveRightForm g y) ∈ cutFormPairs F S fs gLeft gRight := by
  have hsrc' : x ∈ kernelForms F (leftCutKernel T) ft.left n gLeft ∧
      y ∈ kernelForms F (rightCutKernel T) ft.right n gRight :=
    List.mem_product.mp hsrc
  obtain ⟨⟨hx, hGateL⟩, hx0, hxOk⟩ := (mem_kernelForms F _ _ _ _ _).mp hsrc'.1
  obtain ⟨⟨hy, hGateR⟩, hy0, hyOk⟩ := (mem_kernelForms F _ _ _ _ _).mp hsrc'.2
  obtain ⟨hdL, hdR⟩ := cutFrames_dimensions_transport g hg ft fs
  apply cutFormPairs_covers_transporter F fs g hg gLeft gRight x y hx hy hx0 hy0
    (hdL ▸ hGateL) (hdR ▸ hGateR)
  · apply (leftSpec _).mpr
    exact (all_retained_fullRank_iff (leftModes g) x).mpr ((leftSpec x).mp hxOk)
  · apply (rightSpec _).mpr
    exact (all_retained_fullRank_iff (rightModes g) y).mpr ((rightSpec y).mp hyOk)

#print axioms flatten_rank_act
#print axioms cutFrames_dimensions_transport
#print axioms cutFormPairs_transport_of_ranks

end EvenTI.Contract
