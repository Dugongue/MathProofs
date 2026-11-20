import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic

/-! An executable specialization of the pivot argument in Mathlib's
`Matrix.Pivot`. The elementary matrices and block identities come from that
file (Apache-2.0). -/
namespace EvenTI.TrialProducer

open Matrix Matrix.TransvectionStruct

variable {K : Type*} [Field K] [DecidableEq K]

abbrev Elementary (K ι : Type*) [Field K] :=
  List (Matrix.TransvectionStruct ι K) × List (Matrix.TransvectionStruct ι K)

def applyElementary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Elementary K ι) (M : Matrix ι ι K) : Matrix ι ι K :=
  (p.1.map toMatrix).prod * M * (p.2.map toMatrix).prod

private abbrev last (n : ℕ) : Fin n ⊕ Unit := .inr ()

private def clearPivot {n : ℕ} (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K) :
    Elementary K (Fin n ⊕ Unit) :=
  (List.ofFn fun i : Fin n =>
      ⟨.inl i, last n, by simp, -M (.inl i) (last n) / M (last n) (last n)⟩,
    List.ofFn fun i : Fin n =>
      ⟨last n, .inl i, by simp, -M (last n) (.inl i) / M (last n) (last n)⟩)

private theorem clearPivot_spec {n : ℕ} (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (h : M (last n) (last n) ≠ 0) :
    IsTwoBlockDiagonal (applyElementary (clearPivot M) M) := by
  simpa only [applyElementary, clearPivot, List.map_ofFn, Function.comp_def, toMatrix_mk,
    Matrix.Pivot.listTransvecCol, Matrix.Pivot.listTransvecRow] using
    Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M h

private def finishLast {n : ℕ} (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K) :
    Elementary K (Fin n ⊕ Unit) :=
  if M (last n) (last n) = 0 then
    match (List.finRange n).find? (fun i => M (.inl i) (last n) ≠ 0) with
    | some i =>
      let t : TransvectionStruct (Fin n ⊕ Unit) K := ⟨last n, .inl i, by simp, 1⟩
      let p := clearPivot (t.toMatrix * M)
      (p.1 ++ [t], p.2)
    | none =>
      match (List.finRange n).find? (fun i => M (last n) (.inl i) ≠ 0) with
      | some i =>
        let t : TransvectionStruct (Fin n ⊕ Unit) K := ⟨.inl i, last n, by simp, 1⟩
        let p := clearPivot (M * t.toMatrix)
        (p.1, t :: p.2)
      | none => ([], [])
  else clearPivot M

private theorem finishLast_spec {n : ℕ} (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K) :
    IsTwoBlockDiagonal (applyElementary (finishLast M) M) := by
  unfold finishLast
  split
  next hz =>
    split
    next i hi =>
      have hp : M (.inl i) (last n) ≠ 0 := by
        have ht := List.find?_some hi
        simpa only [decide_eq_true_eq] using ht
      let t : TransvectionStruct (Fin n ⊕ Unit) K := ⟨last n, .inl i, by simp, 1⟩
      have ht : (t.toMatrix * M) (last n) (last n) ≠ 0 := by
        simpa [t, hz] using hp
      simpa [t, applyElementary, Matrix.mul_assoc] using clearPivot_spec (t.toMatrix * M) ht
    next hc =>
      split
      next i hi =>
        have hp : M (last n) (.inl i) ≠ 0 := by
          have ht := List.find?_some hi
          simpa only [decide_eq_true_eq] using ht
        let t : TransvectionStruct (Fin n ⊕ Unit) K := ⟨.inl i, last n, by simp, 1⟩
        have ht : (M * t.toMatrix) (last n) (last n) ≠ 0 := by
          simpa [t, hz] using hp
        simpa [t, applyElementary, Matrix.mul_assoc] using clearPivot_spec (M * t.toMatrix) ht
      next hr =>
        have hzero1 (i : Fin n) : M (.inl i) (last n) = 0 := by
          simpa using List.find?_eq_none.mp hc i (List.mem_finRange _)
        have hzero2 (i : Fin n) : M (last n) (.inl i) = 0 := by
          simpa using List.find?_eq_none.mp hr i (List.mem_finRange _)
        simpa [applyElementary] using (show IsTwoBlockDiagonal M from
          ⟨by ext i j; cases j; exact hzero1 i,
            by ext i j; cases i; exact hzero2 j⟩)
  next hn => exact clearPivot_spec M hn

private def splitIndex (n : ℕ) : Fin (n+1) ≃ Fin n ⊕ Unit :=
  (finSumFinEquiv (m := n) (n := 1)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv)

/-- Clear the last off-diagonal row and column, recurse on the leading block,
and compose the actual row and column operations. -/
def diagonalize : {n : ℕ} → Matrix (Fin n) (Fin n) K → Elementary K (Fin n)
  | 0, _ => ([], [])
  | n + 1, M =>
      let e := splitIndex n
      let S := reindexAlgEquiv K _ e M
      let p := finishLast S
      let q := diagonalize ((applyElementary p S).toBlocks₁₁)
      ((q.1.map (sumInl Unit) ++ p.1).map (reindexEquiv e.symm),
        (p.2 ++ q.2.map (sumInl Unit)).map (reindexEquiv e.symm))

private theorem liftElementary_spec {n : ℕ} (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (h : IsTwoBlockDiagonal A) (p : Elementary K (Fin n))
    (D : Fin n → K) (hD : applyElementary p A.toBlocks₁₁ = diagonal D) :
    applyElementary (p.1.map (sumInl Unit), p.2.map (sumInl Unit)) A =
      diagonal (Sum.elim D fun _ => A (last n) (last n)) := by
  let S := A.toBlocks₁₁
  let c := A (last n) (last n)
  have he : A = fromBlocks S 0 0 (diagonal fun _ : Unit => c) := by
    rw [← fromBlocks_toBlocks A, h.1, h.2]
    rfl
  simp only [applyElementary, List.map_map]
  change applyElementary p S = diagonal D at hD
  simp only [applyElementary] at hD
  conv_lhs => rw [he]
  rw [sumInl_toMatrix_prod_mul, mul_sumInl_toMatrix_prod, hD]
  exact fromBlocks_diagonal _ _

theorem diagonalize_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    ∃ D : Fin n → K, applyElementary (diagonalize M) M = diagonal D := by
  induction n with
  | zero => exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    let e := splitIndex n
    let S := reindexAlgEquiv K _ e M
    let p := finishLast S
    let A := applyElementary p S
    let q := diagonalize A.toBlocks₁₁
    obtain ⟨D, hD⟩ := ih A.toBlocks₁₁
    let d := Sum.elim D fun _ : Unit => A (last n) (last n)
    have h : applyElementary (q.1.map (sumInl Unit) ++ p.1,
        p.2 ++ q.2.map (sumInl Unit)) S = diagonal d := by
      simpa [A, d, applyElementary, Matrix.mul_assoc] using
        liftElementary_spec A (finishLast_spec S) q D hD
    refine ⟨d ∘ e, ?_⟩
    rw [diagonalize]
    change applyElementary (((q.1.map (sumInl Unit)) ++ p.1).map (reindexEquiv e.symm),
      (p.2 ++ q.2.map (sumInl Unit)).map (reindexEquiv e.symm)) M = _
    simp only [applyElementary, List.map_map, toMatrix_reindexEquiv_prod]
    have he : M = reindexAlgEquiv K _ e.symm S := by simp [S]
    rw [he, ← map_mul, ← map_mul]
    change reindexAlgEquiv K _ e.symm (applyElementary
      (q.1.map (sumInl Unit) ++ p.1, p.2 ++ q.2.map (sumInl Unit)) S) = _
    rw [h]
    simp

#print axioms diagonalize_spec

end EvenTI.TrialProducer
