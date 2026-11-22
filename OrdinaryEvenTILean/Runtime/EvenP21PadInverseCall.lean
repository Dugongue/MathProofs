import EvenP15ReciprocalCall
import EvenP21PadClosure
import Mathproof.Meta.IMPAutoTactics20261004

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 25000

namespace EvenTI.P21Pad

open EvenTI.Action EvenTI.Contract EvenTI.P15Execution EvenTI.P15Scalar
open EvenTI.P20Pad
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix address)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)
open Mathproof.Problem17Primary46ModePadding (start stop)
open Mathproof.Problem18PairBoundaryMatrixPower20261004
open EvenTI.P19Scalar.PrefixStencil (stencilChartBank)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def squareWidth : Expr := .mul (.var inverseSizeWord) (.var inverseSizeWord)

def installInverseLabelBounds (lower : Bool) : Com :=
  .seq (.assign (start lower) (.var inverseOutputWord))
    (.assign (stop lower) (.add (.var inverseOutputWord) squareWidth))

noncomputable def invertAndExportFrame (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) : Com :=
  .seq (invertLiveMatrix (Fintype.card K))
    (.seq (installInverseLabelBounds lower)
      (EvenTI.P19Scalar.LiveChart.materializeSweptChart D F lower))

private theorem matrix_eq_slot (F : FieldPresentation K) (s : Env) (b n : ℕ)
    (i j : Fin n) :
    matrix F s (s.vars ws+b*F.e) n n i j =
      val F canonical ws s (b+inverseAddress i j) := by
  unfold matrix address val inverseAddress
  congr 1
  ring

/-- Invert the source frame by a paid matrix call, then export its row-major
digits. The inverse-frame data itself is produced by this machine. -/
theorem invertAndExportFrame_run (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) {W S input a n : ℕ} {s : Env}
    (U : (Matrix (Fin n) (Fin n) K)ˣ)
    (hn : 0 < n) (hW : 4 < W)
    (hApart : input+n*n ≤ a) (hFit : a+4*(n*n)+3 ≤ S)
    (hMemory : ValidMemory F W s) (hSlots : Slots F canonical ws S W s)
    (hN : s.vars inverseSizeWord=n) (hIn : s.vars inverseInputWord=input)
    (hA : s.vars inverseOutputWord=a) (hMB : s.vars canonical.modBase+F.e ≤ s.vars ws)
    (hExp : Fintype.card K^(n*n+n+2)<W)
    (hInput : ∀ r c, val F canonical ws s (input+inverseAddress r c)=U.val r c)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W)
    (hTarget : n*n ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < W) :
    ∃ t, Run W (invertAndExportFrame D F lower) s t
        (63+loadedInverseCost (Fintype.card K) F.e n+installScalarLabelsCost F (n*n)) ∧
      Slots F canonical ws S W t ∧
      (∀ r c, (t.arrs stencilChartBank).getD (inverseAddress r c) 0=(D (U.inv r c)).val) ∧
      Frame (invertAndExportFrame D F lower) s t := by
  have hMat : matrix F s (s.vars ws+input*F.e) n n=U.val := by
    ext r c
    rw [matrix_eq_slot,hInput]
  obtain ⟨u,ru,hInv,_,_,hu,fu⟩ := invertLiveMatrix_run F hn hW hApart hFit
    hMemory hSlots hN hIn hA hMB hExp (by rw [hMat]; exact U.isUnit)
  have hSame : scalarWrites (invertLiveMatrix (Fintype.card K)) =
      scalarWrites (invertLiveMatrix 0) := rfl
  have huWS : u.vars ws=s.vars ws := fu.vars _ (by rw [hSame]; imp_frame)
  have huN : u.vars inverseSizeWord=n :=
    (fu.vars _ (by rw [hSame]; imp_frame)).trans hN
  have huA : u.vars inverseOutputWord=a :=
    (fu.vars _ (by rw [hSame]; imp_frame)).trans hA
  have hRef : ∀ r c, val F canonical ws u (a+inverseAddress r c)=U.inv r c := by
    intro r c
    rw [← matrix_eq_slot,huWS,hInv,hMat]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) K => M r c) (Matrix.inv_eq_left_inv U.inv_val)
  have hS := hu.slots_word
  have ha : a < W := by omega
  have hnW : n < W := (Nat.le_mul_of_pos_right n hn).trans_lt (by omega)
  have hEnd : a+n*n < W := by omega
  let v := u.setVar (start lower) a
  let z := v.setVar (stop lower) (a+n*n)
  have r0 : Run W (.assign (start lower) (.var inverseOutputWord)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨huA.symm,by rw [huA]; exact ha⟩)
  have sepA : inverseOutputWord≠start lower := by cases lower <;> decide
  have sepN : inverseSizeWord≠start lower := by cases lower <;> decide
  have hvA : v.vars inverseOutputWord=a := by simpa [v,vars_setVar,sepA] using huA
  have hvN : v.vars inverseSizeWord=n := by simpa [v,vars_setVar,sepN] using huN
  have evN : (Expr.var inverseSizeWord).evalB W v=some n :=
    evalB_var_iff.mpr ⟨hvN.symm,by rw [hvN]; exact hnW⟩
  have r1 : Run W (.assign (stop lower) (.add (.var inverseOutputWord) squareWidth)) v z 6 := by
    exact Run.assign (evalB_bin (op:=.add)
      (evalB_var_iff.mpr ⟨hvA.symm,by rw [hvA]; exact ha⟩)
      (evalB_bin (op:=.mul) evN evN (show n*n<W by omega)) hEnd)
  have hBnds : Run W (installInverseLabelBounds lower) u z 8 := r0.seq r1
  have hsne : start lower≠stop lower := by cases lower <;> decide
  have hStart : z.vars (start lower)=a := by simp [z,v,vars_setVar,hsne]
  have hStop : z.vars (stop lower)=a+n*n := by simp [z,vars_setVar]
  have hZ : Slots F canonical ws S W z := by
    apply (hu.setVar F canonical (by cases lower <;> decide) (by cases lower <;> decide) a).setVar F canonical
      (by cases lower <;> decide) (by cases lower <;> decide) (a+n*n)
  have hZRef (r c : Fin n) : val F canonical ws z (a+inverseAddress r c)=U.inv r c := by
    rw [val_setVar F canonical (by cases lower <;> decide),
      val_setVar F canonical (by cases lower <;> decide),hRef]
  have hZU : (z.arrs stencilChartBank).length=(s.arrs stencilChartBank).length := fu.len _
  obtain ⟨t,rt,ht,hLabels,_,_,_⟩ := materializeInverseGaugeLabels_run D F lower U.inv
    hZ hQ hP (by omega) hStart hStop (by omega) (by rwa [hZU]) (by rwa [hZU]) hZRef
  have rr : Run W (invertAndExportFrame D F lower) s t
      (63+loadedInverseCost (Fintype.card K) F.e n+installScalarLabelsCost F (n*n)) :=
    (ru.seq (hBnds.seq rt)).mono (by omega)
  exact ⟨t,rr,ht,hLabels,Frame.of_run rr⟩

#print axioms invertAndExportFrame_run
end EvenTI.P21Pad



