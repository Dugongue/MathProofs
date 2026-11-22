import EvenP19ScalarPrefixLabels
import Primary46ModeSweep

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace EvenTI.P19Scalar.LiveChart

open scoped BigOperators
open EvenTI.Contract EvenTI.P15Scalar
open EvenTI.P18Scalar (stencilChartBank)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem17Primary46ModePadding (start stop)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def chartControls (lower : Bool) : Com :=
  .seq (.assign scalarCopySource (.var (start lower)))
    (.seq (.assign scalarCopyTarget (.lit 0))
      (.assign scalarCopyLength (.sub (.var (stop lower)) (.var (start lower)))))

noncomputable def materializeSweptChart (D : FieldEncoding K)
    (F : FieldPresentation K) (lower : Bool) : Com :=
  .seq (chartControls lower) (PrefixLabels.installChartLabels D F qN.WS)

/-- Direct consumption of the start/stop ports returned by the complete old
Primary46ModeSweep driver. Code reads both live endpoints; neither the source
address nor the run-dependent row count is compiled as an input-specific literal. -/
theorem materializeSweptChart_run (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) {W S a L : ℕ} {s : Env}
    (hSlots : Slots F canonical qN.WS S W s)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W) (hOne : 1 < W)
    (hStart : s.vars (start lower)=a) (hStop : s.vars (stop lower)=a+L)
    (hRead : a+L ≤ S) (hTarget : L ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < W) :
    ∃ t, Run W (materializeSweptChart D F lower) s t
        (8+installScalarLabelsCost F L) ∧
      Slots F canonical qN.WS S W t ∧
      (∀ j < L, (t.arrs stencilChartBank).getD j 0=
        (D (val F canonical qN.WS s (a+j))).val) ∧
      (t.arrs stencilChartBank).length=(s.arrs stencilChartBank).length ∧
      (∀ k, L ≤ k → (t.arrs stencilChartBank).getD k 0=
        (s.arrs stencilChartBank).getD k 0) ∧
      (∀ b, b ≠ stencilChartBank → t.arrs b=s.arrs b) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hA : a < W := by have := hSlots.slots_word; omega
  have hEnd : a+L < W := hRead.trans_lt hSlots.slots_word
  have hL : L < W := by omega
  let u := s.setVar scalarCopySource a
  let v := u.setVar scalarCopyTarget 0
  let z := v.setVar scalarCopyLength L
  have r0 : Run W (.assign scalarCopySource (.var (start lower))) s u 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hStart.symm,by rw [hStart]; exact hA⟩)
  have r1 : Run W (.assign scalarCopyTarget (.lit 0)) u v 2 :=
    Run.assign (evalB_lit (by omega))
  have hStopV : v.vars (stop lower)=a+L := by
    have hs : stop lower ≠ scalarCopySource := by cases lower <;> decide
    have ht : stop lower ≠ scalarCopyTarget := by cases lower <;> decide
    simpa only [v,u,vars_setVar,hs,ht,if_false] using hStop
  have hStartV : v.vars (start lower)=a := by
    have hs : start lower ≠ scalarCopySource := by cases lower <;> decide
    have ht : start lower ≠ scalarCopyTarget := by cases lower <;> decide
    simpa only [v,u,vars_setVar,hs,ht,if_false] using hStart
  have r2 : Run W (.assign scalarCopyLength
      (.sub (.var (stop lower)) (.var (start lower)))) v z 4 := by
    apply Run.assign
    have e := evalB_bin (op:=.sub)
      (evalB_var_iff.mpr ⟨hStopV.symm,by rw [hStopV]; exact hEnd⟩)
      (evalB_var_iff.mpr ⟨hStartV.symm,by rw [hStartV]; exact hA⟩)
      (show a+L-a < W by simpa only [Nat.add_sub_cancel_left] using hL)
    simpa only [Bop.apply,Nat.add_sub_cancel_left] using e
  have hSz : Slots F canonical qN.WS S W z :=
    ((hSlots.setVar F canonical (by decide) (by decide) a).setVar F canonical
      (by decide) (by decide) 0).setVar F canonical (by decide) (by decide) L
  have hVal (b : ℕ) : val F canonical qN.WS z b=val F canonical qN.WS s b := by
    exact (val_setVar F canonical (by decide) v L b).trans
      ((val_setVar F canonical (by decide) u 0 b).trans
        (val_setVar F canonical (by decide) s a b))
  obtain ⟨t,rt,ht,hLabels,hLength,hTail,hOther,hIn,hOut⟩ :=
    PrefixLabels.installChartLabels_run D F (s:=z) (ws:=qN.WS) hSz (by decide) hQ hP hOne
      (by simp [z,v,u,scalarCopySource,scalarCopyTarget,scalarCopyLength])
      (by simp [z,v,scalarCopyTarget,scalarCopyLength]) (by simp [z])
      hRead hTarget hWord
  refine ⟨t,(r0.seq (r1.seq r2)).seq rt,ht,?_,hLength,hTail,hOther,hIn,hOut⟩
  intro j hj
  rw [hLabels j hj,hVal]

noncomputable def sweepAndMaterialize (D : FieldEncoding K)
    (F : FieldPresentation K) (lower : Bool) (array : String) : Com :=
  .seq (Mathproof.Problem17Primary46ModeSweep.program lower array)
    (materializeSweptChart D F lower)

/-- Full checked all-factor basis sweep followed by its live cursor-to-chart
handoff. Allocation is a source-degree bound; no exact realized rank is needed
at allocation time. Native site installation is a separate remaining contract. -/
theorem sweepAndMaterialize_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n : ℕ} (lower : Bool) (M : Mathproof.Problem17Primary46ModeSweep.Task K n)
    {s : Env} (A : Mathproof.Problem17Primary46ModeSweep.Layout M)
    (H : Mathproof.Problem17Primary46ModeSweep.Prepared F lower M s)
    (hQ : Fintype.card K ≤ M.R.B) (hP : F.p < M.R.B) (hOne : 1 < M.R.B)
    (hCap : M.factors.length*(Mathproof.Problem17Primary46Equations.dim n*
        Mathproof.Problem17Primary46Equations.dim n) ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < M.R.B) :
    ∃ u t, Run M.R.B (sweepAndMaterialize D F lower M.array) s t
        (Mathproof.Problem17Primary46ModeSweep.cost F M+
          (8+installScalarLabelsCost F (Mathproof.Problem17Primary46ModeSweep.rowCount M*
            Mathproof.Problem17Primary46Equations.dim n))) ∧
      Mathproof.Problem17Primary46FactorLoop.Stored F M.output M.S M.T M.f M.factors
        M.factors.length u ∧
      Slots F canonical qN.WS M.R.Sn M.R.B t ∧
      (∀ j < Mathproof.Problem17Primary46ModeSweep.rowCount M*
          Mathproof.Problem17Primary46Equations.dim n,
        (t.arrs stencilChartBank).getD j 0=
          (D (val F canonical qN.WS u (M.output+j))).val) ∧
      (t.arrs stencilChartBank).length=(s.arrs stencilChartBank).length ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let R := Mathproof.Problem17Primary46ModeSweep.rowCount M
  let w := Mathproof.Problem17Primary46Equations.dim n
  have hR : R ≤ M.factors.length*w := by
    unfold R Mathproof.Problem17Primary46ModeSweep.rowCount
      Mathproof.Problem17Primary46FactorLoop.rankPrefix
    calc
      _ ≤ ∑ i ∈ Finset.range M.factors.length, w :=
        Finset.sum_le_sum (fun i _ => Mathproof.Problem17Primary46FactorLoop.rankAt_le
          M.S M.T M.f M.factors i)
      _ = _ := by simp
  have hRows : R*w ≤ M.factors.length*(w*w) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right w hR
  have hRead : M.output+R*w ≤ M.R.Sn := by
    have hOut := A.outFit
    have hZS := A.geom.eqs.kernel.z_s
    change M.output+M.factors.length*(w*w) ≤ M.R.Z at hOut
    omega
  obtain ⟨u,ru,hu,hStart,hStop,hStored,hSafe,hFrame⟩ :=
    Mathproof.Problem17Primary46ModeSweep.run F lower M A H
  have hChart : u.arrs stencilChartBank=s.arrs stencilChartBank := hFrame.arrs _ (by
    apply not_mem_arrayWrites
    change writesArr stencilChartBank
      (Mathproof.Problem17Primary46ModeSweep.program lower "")=false
    cases lower <;> rfl)
  have hIn : u.inp=s.inp := hFrame.inp (by
    apply noRead_of_check
    change readsInp (Mathproof.Problem17Primary46ModeSweep.program lower "")=false
    cases lower <;> rfl)
  have hOut : u.out=s.out := hFrame.out (by
    apply noWrite_of_check
    change writesOut (Mathproof.Problem17Primary46ModeSweep.program lower "")=false
    cases lower <;> rfl)
  obtain ⟨t,rt,ht,hLabels,hLength,hTail,hOther,hInput,hOutput⟩ :=
    materializeSweptChart_run D F lower hu hQ hP hOne hStart hStop hRead
      (by rw [hChart]; exact hRows.trans hCap) (by rw [hChart]; exact hWord)
  exact ⟨u,t,ru.seq rt,hStored,ht,hLabels,hLength.trans (congrArg List.length hChart),
    hInput.trans hIn,hOutput.trans hOut⟩

#print axioms sweepAndMaterialize_run
#print axioms materializeSweptChart_run
end EvenTI.P19Scalar.LiveChart