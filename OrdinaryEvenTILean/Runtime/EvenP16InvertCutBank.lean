import EvenP15ReciprocalCall
import EvenP12CompareRetainedLayout
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 25000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P15Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix address)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutSlotOrder (l n : ℕ) : Coord (l+1) n ≃ Fin (n*n^l) :=
  (inputCoordOrder n (l+1)).trans (finCongr (pow_succ' n l))

/-- Exact cut coordinates at one physical field bank. -/
noncomputable def cutSlotMatrix (F : FieldPresentation K) (s : Env) (l n base : ℕ) :
    Matrix (Coord (l+1) n) (Coord (l+1) n) K :=
  fun x y => val F canonical ws s (base+((inputCoordOrder n (l+1) x).val*(n*n^l)+(inputCoordOrder n (l+1) y).val))

private theorem matrix_eq_reindex_cutSlotMatrix (F : FieldPresentation K) (s : Env) (l n base : ℕ) :
    matrix F s (s.vars ws+base*F.e) (n*n^l) (n*n^l) =
      Matrix.reindexAlgEquiv K K (cutSlotOrder l n) (cutSlotMatrix F s l n base) := by
  let e := cutSlotOrder l n
  ext i j
  have eli : (inputCoordOrder n (l+1) (e.symm i)).val=i.val := by
    have h := congrArg Fin.val (e.apply_symm_apply i)
    simpa [e,cutSlotOrder] using h
  have elj : (inputCoordOrder n (l+1) (e.symm j)).val=j.val := by
    have h := congrArg Fin.val (e.apply_symm_apply j)
    simpa [e,cutSlotOrder] using h
  simp only [Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply]
  unfold matrix cutSlotMatrix val address
  change _ = _
  rw [show (inputCoordOrder n (l+1) ((cutSlotOrder l n).symm i)).val=i.val from eli,
    show (inputCoordOrder n (l+1) ((cutSlotOrder l n).symm j)).val=j.val from elj]
  rw [show s.vars ws+base*F.e+F.e*(i.val*(n*n^l)+j.val)=
      s.vars ws+(base+(i.val*(n*n^l)+j.val))*F.e by ring]

private theorem reindex_nonsing_inv {l n : ℕ} (A : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (hA : IsUnit A) :
    Matrix.reindexAlgEquiv K K (cutSlotOrder l n) A⁻¹ =
      (Matrix.reindexAlgEquiv K K (cutSlotOrder l n) A)⁻¹ := by
  let e := Matrix.reindexAlgEquiv K K (cutSlotOrder l n)
  let M := e A
  have hu : IsUnit M := hA.map e.toMonoidHom
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have hAA : A*A⁻¹=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hMC : M * e A⁻¹ = 1 := by change e A * e A⁻¹ = 1; rw [←map_mul,hAA,map_one]
  change e A⁻¹ = M⁻¹
  calc
    _ = (M⁻¹*M)*e A⁻¹ := by rw [Matrix.nonsing_inv_mul _ hd,one_mul]
    _ = _ := by rw [mul_assoc,hMC,mul_one]

/-- The paid inverse from the installed cut produces the reciprocal in
exactly the physical mixed-radix order used by the anchor grid. -/
theorem invertCutBank_run (F : FieldPresentation K) {l n input start S B : ℕ} {s : Env}
    (hn : 0 < n) (hB : 4 < B)
    (hApart : input+(n*n^l)*(n*n^l) ≤ start) (hFit : start+4*((n*n^l)*(n*n^l))+3 ≤ S)
    (hV : ValidMemory F B s) (hS : Slots F canonical ws S B s)
    (hN : s.vars inverseSizeWord=n*n^l) (hInput : s.vars inverseInputWord=input)
    (hOut : s.vars inverseOutputWord=start) (hMB : s.vars canonical.modBase+F.e ≤ s.vars ws)
    (hWord : Fintype.card K^((n*n^l)*(n*n^l)+n*n^l+2) < B)
    (hUnit : IsUnit (cutSlotMatrix F s l n input)) :
    ∃ t, Run B (invertLiveMatrix (Fintype.card K)) s t
      (47+loadedInverseCost (Fintype.card K) F.e (n*n^l)) ∧
      cutSlotMatrix F t l n start=(cutSlotMatrix F s l n input)⁻¹ ∧
      cutSlotMatrix F t l n input=cutSlotMatrix F s l n input ∧
      ValidMemory F B t ∧ Slots F canonical ws S B t ∧ Frame (invertLiveMatrix (Fintype.card K)) s t := by
  let e := Matrix.reindexAlgEquiv K K (cutSlotOrder l n)
  have hs := matrix_eq_reindex_cutSlotMatrix F s l n input
  have hu : IsUnit (matrix F s (s.vars ws+input*F.e) (n*n^l) (n*n^l)) := by
    rw [hs]
    exact hUnit.map e.toMonoidHom
  obtain ⟨t,hRun,hInv,hInput',hVt,hSt,hFrame⟩ := invertLiveMatrix_run F
    (Nat.mul_pos hn (pow_pos hn _)) hB hApart hFit hV hS hN hInput hOut hMB hWord hu
  have hf : scalarWrites (invertLiveMatrix (Fintype.card K)) = scalarWrites (invertLiveMatrix 0) := rfl
  have hw : t.vars ws=s.vars ws := hFrame.vars _ (by rw [hf]; decide)
  have hInv' : cutSlotMatrix F t l n start=(cutSlotMatrix F s l n input)⁻¹ := by
    apply e.injective
    rw [←matrix_eq_reindex_cutSlotMatrix,hw,hInv,hs,←reindex_nonsing_inv _ hUnit]
  have hIn : cutSlotMatrix F t l n input=cutSlotMatrix F s l n input := by
    apply e.injective
    rw [←matrix_eq_reindex_cutSlotMatrix,hw,hInput',hs]
  exact ⟨t,hRun,hInv',hIn,hVt,hSt,hFrame⟩

#print axioms invertCutBank_run
end EvenTI.P16Execution