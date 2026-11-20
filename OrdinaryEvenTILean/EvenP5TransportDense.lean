import EvenP5TransportReciprocal
import EvenP3RecipPrimary

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix
open Matrix EvenTI.Action EvenTI.Primary
open Mathproof.Problem17RepeatedBudget
noncomputable section

variable {K : Type} [Field K] [Fintype K] {l n : ℕ}

private def reindexUnit {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (U : (Matrix Y Y K)ˣ) : (Matrix X X K)ˣ where
  val := U.val.submatrix e e
  inv := U.inv.submatrix e e
  val_inv := by rw [Matrix.submatrix_mul_equiv, U.val_inv, Matrix.submatrix_one_equiv]
  inv_val := by rw [Matrix.submatrix_mul_equiv, U.inv_val, Matrix.submatrix_one_equiv]

private def leftLayout {H L J : Type*} (b : Sum H L ≃ Coord l n) (j : J ≃ Fin n)
    (i : Fin (l + 1)) : Sum H L × J ≃ Coord (l + 1) n :=
  (Equiv.prodCongr b j).trans ((Equiv.prodComm _ _).trans (retainedMode i))

private theorem leftLayout_product {H L J : Type*}
    (b : Sum H L ≃ Coord l n) (j : J ≃ Fin n) (i : Fin (l + 1))
    (g : Changes K (l + 1) n) :
    (productMatrix g).submatrix (leftLayout b j i) (leftLayout b j i) =
      kronecker ((productMatrix (fun k => g (i.succAbove k))).submatrix b b)
        ((g i).val.submatrix j j) := by
  ext x y
  change productMatrix g (retainedMode i (j x.2, b x.1)) (retainedMode i (j y.2, b y.1)) =
    productMatrix (fun k => g (i.succAbove k)) (b x.1) (b y.1) * (g i).val (j x.2) (j y.2)
  exact (retained_productMatrix g i _ _ _ _).trans (mul_comm _ _)

private theorem rightLayout_product (i : Fin (l + 1)) (g : Changes K (l + 1) n) :
    (productMatrix g).submatrix (rightRegroup i) (rightRegroup i) =
      kronecker (g i).val (productMatrix (fun k => g (i.succAbove k))) := by
  ext x y
  exact retained_productMatrix g i x.1 y.1 x.2 y.2

private theorem submatrix_mul_twice {A B X Y : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (u : X ≃ A) (v : Y ≃ B) (P : Matrix A A K) (M : Matrix A B K) (Q : Matrix B B K) :
    (P * M * Qᵀ).submatrix u v =
      P.submatrix u u * M.submatrix u v * (Q.submatrix v v)ᵀ := by
  have h : (Q.submatrix v v)ᵀ = Qᵀ.submatrix v v := rfl
  rw [h, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private theorem invTranspose_mul_twice {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : (Matrix X X K)ˣ) (M : Matrix X X K) :
    ((P.val * M * Q.valᵀ)⁻¹)ᵀ = P.invᵀ * (M⁻¹)ᵀ * Q.inv := by
  have hP : P.val⁻¹ = P.inv := Matrix.inv_eq_right_inv P.val_inv
  have hQ : Q.val⁻¹ = Q.inv := Matrix.inv_eq_right_inv Q.val_inv
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul,
    ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, hP, hQ]

private theorem orientCut_flatten (b : Bool) (T : InvertibleCut K (l + 1) n) :
    flatten (orientCut b T).val = if b then (flatten T.val)ᵀ else flatten T.val := by
  cases b
  · rfl
  · ext a b
    change T.val (cutEquiv (cutEquiv.symm (cutEquiv (a,b))).swap) = T.val (cutEquiv (b,a))
    rw [Equiv.symm_apply_apply]
    rfl

private def actInvertibleCut (g : Changes K ((l + 1) + (l + 1)) n)
    (T : InvertibleCut K (l + 1) n) : InvertibleCut K (l + 1) n :=
  ⟨act g T.val, by
    rw [flatten_action]
    have h : IsUnit (productMatrix (rightModes g))ᵀ := by
      rw [Matrix.isUnit_transpose]
      exact (productUnit (rightModes g)).isUnit
    exact ((productUnit (leftModes g)).isUnit.mul T.property).mul
      h⟩

private theorem denseAnchor_of_flatten_transport {H L J : Type*}
    [Fintype H] [Fintype L] [Fintype J] [DecidableEq H] [DecidableEq L] [DecidableEq J]
    (b : Sum H L ≃ Coord l n) (j : Option J ≃ Fin n) (i k : Fin (l + 1))
    (T S : InvertibleCut K (l + 1) n) (g h : Changes K (l + 1) n)
    (htransport : flatten S.val = productMatrix g * flatten T.val * (productMatrix h)ᵀ) :
    denseAnchor (leftLayout b j i) (rightRegroup k) S =
      (h k).val * denseAnchor (leftLayout b j i) (rightRegroup k) T * (h k).inv := by
  let a := reindexUnit b (productUnit (fun x => g (i.succAbove x)))
  let p := reindexUnit j (g i)
  let q := h k
  let c := productUnit (fun x => h (k.succAbove x))
  let e₁ := leftLayout b j i
  let e₂ := rightRegroup (n := n) k
  let U := (flatten T.val).submatrix e₁ e₂
  let V := ((flatten T.val)⁻¹)ᵀ.submatrix e₁ e₂
  have hu : (flatten S.val).submatrix e₁ e₂ =
      kronecker a.val p.val * U * (kronecker q.val c.val)ᵀ := by
    rw [htransport, submatrix_mul_twice, leftLayout_product, rightLayout_product]
    rfl
  have hv : ((flatten S.val)⁻¹)ᵀ.submatrix e₁ e₂ =
      kronecker a.invᵀ p.invᵀ * V * (kronecker q.invᵀ c.invᵀ)ᵀ := by
    have hg : (productUnit g).val = productMatrix g := rfl
    have hh : (productUnit h).val = productMatrix h := rfl
    rw [htransport, ← hg, ← hh, invTranspose_mul_twice]
    have hiA : ((productUnit g).invᵀ).submatrix e₁ e₁ =
        kronecker a.invᵀ p.invᵀ := by
      have hh := leftLayout_product b j i g⁻¹
      exact congrArg Matrix.transpose hh
    have hiB : ((productUnit h).invᵀ).submatrix e₂ e₂ =
        kronecker q.invᵀ c.invᵀ := by
      have hh := rightLayout_product k h⁻¹
      exact congrArg Matrix.transpose hh
    rw [show (productUnit h).inv = ((productUnit h).invᵀ)ᵀ from
      (Matrix.transpose_transpose _).symm, submatrix_mul_twice, hiA, hiB]
  unfold denseAnchor
  rw [hu, hv]
  exact reciprocal_twice_trace_transport a p q c U V

private theorem denseAnchor_orient_act {H L J : Type*}
    [Fintype H] [Fintype L] [Fintype J] [DecidableEq H] [DecidableEq L] [DecidableEq J]
    (b : Sum H L ≃ Coord l n) (j : Option J ≃ Fin n) (i k : Fin (l + 1))
    (m : Bool) (T : InvertibleCut K (l + 1) n) (g : Changes K ((l + 1) + (l + 1)) n) :
    let q := if m then leftModes g k else rightModes g k
    denseAnchor (leftLayout b j i) (rightRegroup k) (orientCut m (actInvertibleCut g T)) =
      q.val * denseAnchor (leftLayout b j i) (rightRegroup k) (orientCut m T) * q.inv := by
  cases m
  · exact denseAnchor_of_flatten_transport b j i k _ _ (leftModes g) (rightModes g)
      (flatten_action g T.val)
  · apply denseAnchor_of_flatten_transport b j i k _ _ (rightModes g) (leftModes g)
    rw [orientCut_flatten, orientCut_flatten, if_pos rfl, if_pos rfl]
    change (flatten (act g T.val))ᵀ =
      productMatrix (rightModes g) * (flatten T.val)ᵀ * (productMatrix (leftModes g))ᵀ
    rw [flatten_action, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc]

/-- The actual dense higher-order anchor has the requisite physical covariance
in either prescribed cut orientation. -/
theorem higherDenseModeAnchor_transport (hn : 1 ≤ n) (i : HigherModes l)
    (T S : InvertibleCut K (l + 1) n) (g : Changes K ((l + 1) + (l + 1)) n)
    (hg : act g T.val = S.val) :
    let q := if i.1 then leftModes g i.2 else rightModes g i.2
    higherDenseModeAnchor hn i S = q.val * higherDenseModeAnchor hn i T * q.inv := by
  have hS : S = actInvertibleCut g T := Subtype.ext hg.symm
  rw [hS]
  exact denseAnchor_orient_act (bundleEquiv l n) (distinguishedEquiv n hn) 0 i.2 i.1 T g

/-- The particular order-four reciprocal anchor, using its four marked
groups, has the same physical covariance. -/
theorem squareDenseModeAnchor_transport (hn : 5 ≤ n) (i : FourModes)
    (T S : InvertibleCut K 2 n) (g : Changes K (2 + 2) n) (hg : act g T.val = S.val) :
    let q := if i.1 then leftModes g i.2 else rightModes g i.2
    squareDenseModeAnchor hn i S = q.val * squareDenseModeAnchor hn i T * q.inv := by
  let e : SquareGroups n ≃ OtherModes n := Fintype.equivOfCardEq (by
    rw [squareGroups_card n hn, Fintype.card_fin])
  let d := (Equiv.optionCongr e).trans (distinguishedEquiv n (by omega))
  have hS : S = actInvertibleCut g T := Subtype.ext hg.symm
  rw [hS]
  have he : squareLeftRegroup hn 0 = leftLayout (bundleEquiv 1 n) d 0 := by
    ext x
    rfl
  unfold squareDenseModeAnchor
  rw [he]
  exact denseAnchor_orient_act (bundleEquiv 1 n) d 0 i.2 i.1 T g

/-- A genuine transporter preserves the complete higher-order reciprocal
budget, so it survives the actual budget gate. -/
theorem higherReciprocalBudget_transport (hn : 1 ≤ n)
    (T S : InvertibleCut K (l + 1) n) (g : Changes K ((l + 1) + (l + 1)) n)
    (hg : act g T.val = S.val) : higherReciprocalBudget hn S = higherReciprocalBudget hn T := by
  unfold higherReciprocalBudget
  apply Finset.sum_congr rfl
  intro i _
  rw [higherDenseModeAnchor_transport hn i T S g hg]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_val, Matrix.one_mul]

/-- A genuine transporter preserves the complete order-four reciprocal
budget as well. -/
theorem squareReciprocalBudget_transport (hn : 5 ≤ n)
    (T S : InvertibleCut K 2 n) (g : Changes K (2 + 2) n)
    (hg : act g T.val = S.val) : squareReciprocalBudget hn S = squareReciprocalBudget hn T := by
  unfold squareReciprocalBudget
  apply Finset.sum_congr rfl
  intro i _
  rw [squareDenseModeAnchor_transport hn i T S g hg]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_val, Matrix.one_mul]

end
end Mathproof.EvenTI.Reciprocal.Coverage

#print axioms Mathproof.EvenTI.Reciprocal.Coverage.higherReciprocalBudget_transport
#print axioms Mathproof.EvenTI.Reciprocal.Coverage.squareReciprocalBudget_transport
