import EvenP14CRTConstraints
import EvenP14CutNonzero
import EvenP12CompareRecoverLinear

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18PairBoundaryCopy20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)
open EvenTI.P12Compare (crtRhsBank recoverLinear recoverLinear_complete recoverLinear_sound)
open EvenTI.P12ComparePrep (coeffLength cutNonzero cutNonzeroProgram cutNonzeroProgram_run)

private abbrev rhsScanWords := EvenTI.P12ComparePrep.coefficientBank

private def copyRhsScanWords : Com :=
  copyBlock crtRhsBank rhsScanWords (.var baseRows) (.lit 0) (.lit 0)

def emptyCoordinateVerdict : Com :=
  .seq copyRhsScanWords (.seq (.assign coeffLength (.var baseRows)) (cutNonzeroProgram 0))

private theorem emptyColumnSolution {M m : ℕ}
    (A : Matrix (Fin m) (Fin 0) (ZMod M)) (b : Fin m → ZMod M) (w : Fin 0 → ZMod M) :
    A.mulVec w = b ↔ ∀ j, b j = 0 := by
  have h : A.mulVec w = 0 := by ext j; simp [Matrix.mulVec,dotProduct]
  rw [h]
  exact ⟨fun he j => (congrFun he j).symm,fun hb => funext fun j => (hb j).symm⟩

/-- For zero unknowns, verify every live right-hand side word and decide
whether the reference algorithm returns the unique empty solution. -/
theorem emptyCoordinateVerdict_run {M m B : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin 0) (ZMod M)) (b : Fin m → ZMod M)
    (hM : M < B) (hB : 1 < B) (hm : m < B) (hLive : s.vars baseRows = m)
    (hRhs : s.arrs crtRhsBank = List.ofFn fun j => (b j).val)
    (hBank : m ≤ (s.arrs rhsScanWords).length) :
    ∃ t, Run B emptyCoordinateVerdict s t (44*m+24) ∧
      t.vars cutNonzero ≤ 1 ∧
      (t.vars cutNonzero = 0 ↔ (recoverLinear A b).isSome = true) ∧
      Frame emptyCoordinateVerdict s t := by
  have hLen : (s.arrs crtRhsBank).length = m := by simp [hRhs]
  have hGet (i : ℕ) (hi : i < m) : (s.arrs crtRhsBank).getD i 0 = (b ⟨i,hi⟩).val := by
    rw [hRhs,List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have eLen : (Expr.var baseRows).evalB B s = some m := evalB_var_iff.mpr ⟨hLive.symm,hLive ▸ hm⟩
  obtain ⟨u,ru,hWords,_,_,_,_,_,_⟩ := copyBlock_run (src:=crtRhsBank)
    (dst:=rhsScanWords) (n:=m) (sourceBase:=0) (targetBase:=0) (B:=B) (sigma:=s)
    (by decide) eLen (evalB_lit (by omega)) (evalB_lit (by omega)) hm
    (by simpa using hm) (by simpa using hm) (by simp [hLen]) (by simpa using hBank)
    (by intro i hi; simp only [Nat.zero_add]; rw [hGet i hi]; exact (ZMod.val_lt _).trans hM)
  have mode : u.vars baseRows = m := by
    apply Eq.trans ((Frame.of_run ru).vars _ ?_) hLive
    decide
  let v := u.setVar coeffLength m
  have rv : Run B (.assign coeffLength (.var baseRows)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨mode.symm,mode ▸ hm⟩)
  have hFin : m ≤ (v.arrs rhsScanWords).length := (Frame.of_run (ru.seq rv)).len rhsScanWords |>.symm ▸ hBank
  have hV (i : ℕ) (hi : i < m) : (v.arrs rhsScanWords).getD i 0 = (b ⟨i,hi⟩).val := by
    change (u.arrs rhsScanWords).getD i 0 = (b ⟨i,hi⟩).val
    simpa only [Nat.zero_add] using (hWords i hi).trans (by simpa only [Nat.zero_add] using hGet i hi)
  obtain ⟨t,rt,hBit,hOut,_,_,_,_⟩ := cutNonzeroProgram_run 0 m B v hB hm (by omega)
    (by simp [v]) hFin (fun i hi => by rw [hV i hi]; exact (ZMod.val_lt _).trans hM)
  have run : Run B emptyCoordinateVerdict s t (44*m+24) :=
    (ru.seq (rv.seq rt)).mono (by simp [Expr.size] <;> omega)
  refine ⟨t,run,hBit,?_,Frame.of_run run⟩
  constructor
  · intro hf
    apply recoverLinear_complete A b
    let x : Fin 0 → ZMod M := Fin.elim0
    refine ⟨x,(emptyColumnSolution A b x).mpr fun j => ?_⟩
    by_contra hj
    have hv : (b j).val ≠ 0 := by simpa using hj
    have ht := hOut.mpr ⟨j.val,j.isLt,by rw [hV j.val j.isLt]; exact hv⟩
    omega
  · intro h
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h
    have hz := (emptyColumnSolution A b x).mp (recoverLinear_sound A b hx)
    have hne : t.vars cutNonzero ≠ 1 := by
      intro he
      obtain ⟨j,hj,hv⟩ := hOut.mp he
      rw [hV j hj,hz ⟨j,hj⟩,ZMod.val_zero] at hv
      exact hv rfl
    omega

#print axioms emptyCoordinateVerdict_run
end EvenTI.P14Recovery