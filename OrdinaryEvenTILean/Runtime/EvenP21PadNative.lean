import EvenP20PadGeometry
import EvenP20ScalarUnpadded

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover

section BlockAction

variable {K : Type} [Field K] {d p : ℕ} {width : Fin d → ℕ}
  {C : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (C i v)] [∀ i v, DecidableEq (C i v)]
  {A : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (A i v)] [∀ i v, Algebra K (A i v)]
  (t : ∀ i v, WordTable K (C i v))
  (E : ∀ i v, (C i v → K) ≃ₗ[K] A i v)
  (hOne : ∀ i v, E i v (t i v).one = 1)
  (hMul : ∀ i v a b, E i v ((t i v).multiply a b) = E i v a * E i v b)

include hOne hMul in
theorem decodeBlock_mul_column (i : Fin d) (a : ∀ v, A i v)
    (T : Matrix (LiveModeIndex C i) (Fin p) K) (j : Fin p) :
    blockDecode (E i) (fun z => (liveActionMatrix t E i a*T) z j) =
      a * blockDecode (E i) (fun z => T z j) := by
  let U := blockTable (t i)
  let F := blockDecode (E i)
  have H := blockTable_model (t i) (E i) (hOne i) (hMul i)
  letI : WordTable.Laws U := WordTable.laws_of_model U F H.1 H.2
  change F ((wordMulMatrix U (F.symm a)).mulVec (fun z => T z j)) = _
  rw [wordMulMatrix_mulVec,H.2,F.apply_symm_apply]

include hOne hMul in
/-- A scalar test on a rectangular restriction of finite-field multiplication
examines only native blocks supporting a nonzero column. Within a field
block, one nonzero vector suffices to force the multiplier. -/
theorem liveAction_mul_restriction_iff (i : Fin d) (a : ∀ v, A i v)
    (T : Matrix (LiveModeIndex C i) (Fin p) K) (c : K) :
    liveActionMatrix t E i a*T = c • T ↔
      ∀ v, (∃ (r : C i v) (j : Fin p), T ⟨v,r⟩ j ≠ 0) → a v = c • 1 := by
  let F := blockDecode (E i)
  have hm (j : Fin p) := decodeBlock_mul_column t E hOne hMul i a T j
  have hs (j : Fin p) : F (fun z => (c • T) z j)=c • F (fun z => T z j) :=
    F.map_smul c _
  constructor
  · intro h v hv
    obtain ⟨r,j,hEntry⟩ := hv
    let x : A i v := E i v (fun q => T ⟨v,q⟩ j)
    have hx : x ≠ 0 := by
      intro hz
      apply hEntry
      have hf : (fun q => T ⟨v,q⟩ j) = 0 :=
        (E i v).injective (hz.trans (E i v).map_zero.symm)
      exact congrFun hf r
    have he : a v*x=c • x := by
      have hj := hm j
      rw [h,hs] at hj
      exact congrFun hj.symm v
    apply mul_right_cancel₀ hx
    calc
      a v*x = c • x := he
      _ = (c • (1 : A i v))*x := by rw [smul_mul_assoc,one_mul]
  · intro h
    have he (j : Fin p) : F (fun z => (liveActionMatrix t E i a*T) z j) =
        F (fun z => (c • T) z j) := by
      rw [hm,hs]
      funext v
      let x : A i v := E i v (fun q => T ⟨v,q⟩ j)
      change a v*x=c • x
      by_cases hZero : x=0
      · rw [hZero,mul_zero,smul_zero]
      · have hEntry : ∃ r : C i v, T ⟨v,r⟩ j≠0 := by
          by_contra! hz
          apply hZero
          have hx : (fun q => T ⟨v,q⟩ j)=0 := funext hz
          dsimp only [x]
          rw [hx,map_zero]
        obtain ⟨r,hr⟩ := hEntry
        rw [h v ⟨r,j,hr⟩,smul_mul_assoc,one_mul]
    ext r j
    exact congrFun (F.injective (he j)) r

end BlockAction

section Coordinate

variable {K : Type} [Field K] {p w : ℕ} {R : Type} [Fintype R] [DecidableEq R]

/-- Move a rectangular source pad into chart coordinates. This formula
needs the invariant-subspace conclusion, but no ambient projector. -/
theorem stableCrop_conjugate_iff
    (P : Matrix (Fin w) (Fin p) K) (Q : Matrix (Fin p) (Fin w) K)
    (U : (Matrix (Fin w) (Fin w) K)ˣ) (B : Matrix (Fin w) (Fin w) K)
    (a : K) (hLeft : Q*P=1)
    (hInvariant : (U.val*B*U.inv)*P=P*(Q*(U.val*B*U.inv)*P)) :
    Q*(U.val*B*U.inv)*P=a • 1 ↔ B*(U.inv*P)=a • (U.inv*P) := by
  have hMove : U.inv*((U.val*B*U.inv)*P)=B*(U.inv*P) := by
    calc
      _ = (U.inv*U.val)*(B*(U.inv*P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [U.inv_val,Matrix.one_mul]
  constructor
  · intro h
    have hAct := hInvariant
    rw [h,Matrix.mul_smul,Matrix.mul_one] at hAct
    have hV := congrArg (fun X => U.inv*X) hAct
    simpa only [hMove,Matrix.mul_smul] using hV
  · intro h
    have hAct : (U.val*B*U.inv)*P=a • P := by
      have hv := congrArg (fun X => U.val*X) h
      have hl : U.val*(B*(U.inv*P))=(U.val*B*U.inv)*P := by
        simp only [Matrix.mul_assoc]
      have hr : U.val*(a • (U.inv*P))=a • P := by
        rw [Matrix.mul_smul,←Matrix.mul_assoc,U.val_inv,Matrix.one_mul]
      exact hl.symm.trans (hv.trans hr)
    rw [Matrix.mul_assoc,hAct,Matrix.mul_smul,hLeft]

/-- Move the square block matrix and the rectangular input through
the identical numbered mode indexing. -/
theorem reindexBlock_mul_iff (e : R ≃ Fin w) (B : Matrix R R K)
    (T : Matrix (Fin w) (Fin p) K) (a : K) :
    B.submatrix e.symm e.symm*T=a • T ↔
      B*T.submatrix e id=a • T.submatrix e id := by
  have hMove :
      (B.submatrix e.symm e.symm*T).submatrix e id=B*T.submatrix e id := by
    rw [←Matrix.submatrix_mul_equiv (B.submatrix e.symm e.symm) T e e id,
      Matrix.submatrix_submatrix,Equiv.symm_comp_self,Matrix.submatrix_id_id]
  have hScale : (a • T).submatrix e id=a • T.submatrix e id := rfl
  constructor
  · intro h
    rw [←hMove,h,hScale]
  · intro h
    ext i j
    have hj := congrFun (congrFun (hMove.trans (h.trans hScale.symm)) (e.symm i)) j
    simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,id_eq] using hj

end Coordinate

#print axioms decodeBlock_mul_column
#print axioms liveAction_mul_restriction_iff
#print axioms stableCrop_conjugate_iff
#print axioms reindexBlock_mul_iff
end EvenTI.P21Pad
