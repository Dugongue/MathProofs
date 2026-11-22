import EvenP14CRTLoop

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery Matrix
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)

local macro "restoreLayout" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.RecoveryLayout.fromFrame))

def probeIndex : String := "even.scalar.probe.index"
def probeValue : String := "even.scalar.probe.value"

def pickProbeValue : Com :=
  .ite (.eq (.var coordinateSlot) (.var probeIndex))
    (.assign crtRepresentative (.var probeValue)) (.assign crtRepresentative (.lit 0))

def storeProbeCoordinate : Com :=
  .store coordinateBank (.var coordinateSlot) (.var crtRepresentative)

def nextProbeCoordinate : Com :=
  .assign coordinateSlot (.add (.var coordinateSlot) (.lit 1))

def probePrefixBody : Com :=
  .seq pickProbeValue (.seq installConstraint (.seq storeProbeCoordinate nextProbeCoordinate))

def probePrefixGuard : Cond :=
  .lt (.var coordinateSlot) (.add (.var probeIndex) (.lit 1))

def installKernelProbePrefix : Com := .while probePrefixGuard probePrefixBody

private def probeVector {M n : ℕ} (i : Fin n) (a : ZMod M) (k : ℕ) : Fin n → ZMod M :=
  if i.val < k then Function.update 0 i a else 0

private theorem probeVector_next {M n : ℕ} (i j : Fin n) (a : ZMod M) (hj : j.val  ≤  i.val) :
    Function.update (probeVector i a j.val) j (if j=i then a else 0) =
      probeVector i a (j.val+1) := by
  rw [show probeVector i a j.val = 0 by simp [probeVector,Nat.not_lt_of_ge hj]]
  by_cases h : j=i
  · subst j
    simp [probeVector]
  · have hne : j.val  ≠  i.val := fun he => h (Fin.ext he)
    simp [probeVector,h,show ¬i.val<j.val+1 by omega]

/-- Install the prescribed homogeneous prefix into the live CRT banks.
The coefficient rows, RHS and committed coordinate words agree. -/
theorem installKernelProbePrefix_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) (a : ZMod M)
    (hW : M+2 < W) (hSize : (m+n+1)*n+m+n+4 < W)
    (hs : RecoveryLayout M m n s) (hInit : ConstraintBanks A 0 0 0 s)
    (hSlot : s.vars coordinateSlot=0) (hI : s.vars probeIndex=i.val) (hA : s.vars probeValue=a.val) :
    ∃ t, Run W installKernelProbePrefix s t (64*(i.val+1)+8) ∧
      RecoveryLayout M m n t ∧ t.vars coordinateSlot=i.val+1 ∧
      ConstraintBanks A 0 (Function.update 0 i a) (i.val+1) t ∧
      CoordinatePrefix (Function.update 0 i a) (i.val+1) t := by
  let p := i.val+1
  let I (t : Env) := RecoveryLayout M m n t ∧ t.vars coordinateSlot ≤ p ∧
    t.vars probeIndex=i.val ∧ t.vars probeValue=a.val ∧
    ConstraintBanks A 0 (probeVector i a (t.vars coordinateSlot)) (t.vars coordinateSlot) t ∧
    CoordinatePrefix (probeVector i a (t.vars coordinateSlot)) (t.vars coordinateSlot) t
  let V (t : Env) := p-t.vars coordinateSlot
  have hp : p ≤ n := Nat.succ_le_of_lt i.isLt
  have one : 1 < W := by omega
  have hP : p < W := by omega
  have ha : a.val < W := (ZMod.val_lt a).trans (by omega)
  have hInitial : I s := by
    refine ⟨hs,by rw [hSlot]; omega,hI,hA,?_,?_⟩
    · simpa [hSlot,probeVector] using hInit
    · rw [hSlot]
      intro j hj
      exact False.elim (Nat.not_lt_zero _ hj)
  have hGuard (t : Env) (ht : I t) : probePrefixGuard.evalB W t =
      some (decide (t.vars coordinateSlot<p)) := by
    have e := ev_add (ev_var ht.2.2.1 (show i.val < W by omega)) (evalB_lit one) hP
    exact evalB_condLt (evalB_var (ht.2.1.trans_lt hP)) e
  have hStep (t : Env) (ht : I t) (hEntry : probePrefixGuard.evalB W t = some true) :
      ∃ u,Run W probePrefixBody t u 56 ∧ I u ∧ V u < V t := by
    rw [hGuard t ht] at hEntry
    have hi : t.vars coordinateSlot < p := by simpa using hEntry
    let j : Fin n := ⟨t.vars coordinateSlot,hi.trans_le hp⟩
    have hj : j.val ≤ i.val := by change t.vars coordinateSlot ≤ i.val; omega
    let x : ZMod M := if j=i then a else 0
    let u := t.setVar crtRepresentative x.val
    have hWordX : x.val < W := (ZMod.val_lt x).trans (by omega)
    have ei : (Expr.var probeIndex).evalB W t = some i.val :=
      ev_var ht.2.2.1 (show i.val < W by omega)
    have e := evalB_condEq (evalB_var (σ:=t) (x:=coordinateSlot) (hi.trans hP)) ei
    have hr : Run W pickProbeValue t u 6 := by
      by_cases he : j=i
      · have ee : (Cond.eq (.var coordinateSlot) (.var probeIndex)).evalB W t = some true := by
          have hVal : t.vars coordinateSlot=i.val := congrArg Fin.val he
          simpa only [hVal,beq_self_eq_true] using e
        have evalValue : (Expr.var probeValue).evalB W t = some a.val := ev_var ht.2.2.2.1 ha
        simpa only [pickProbeValue,u,x,if_pos he,Cond.size,Expr.size] using (Run.ite_true
          (d:=.assign crtRepresentative (.lit 0)) ee
          (Run.assign (x:=crtRepresentative) evalValue))
      · have hVal : t.vars coordinateSlot ≠ i.val := fun he' => he (Fin.ext he')
        have ee : (Cond.eq (.var coordinateSlot) (.var probeIndex)).evalB W t = some false := by
          simpa only [beq_eq_false_iff_ne.mpr hVal] using e
        simpa only [pickProbeValue,u,x,if_neg he,ZMod.val_zero,Cond.size,Expr.size] using
          (Run.ite_false (c:=.assign crtRepresentative (.var probeValue)) ee
            (Run.assign (x:=crtRepresentative) (evalB_lit (show 0 < W by omega))))
    have f := Frame.of_run hr
    have hPut : (m+j.val)*n+j.val < (m+n)*n := packed_lt
      (⟨m+j.val,Nat.add_lt_add_left j.isLt m⟩ : Fin (m+n)) j
    have hRhs : (t.arrs crtRhsBank).length=m+n := by rw [ht.2.2.2.2.1.rhs,List.length_ofFn]
    have hMat0 := ht.1.sourceLen
    have hEntryB : (m+j.val)*n+j.val < W := by
      have hge := Nat.mul_le_mul_right n (show m+n ≤ m+n+1 by omega)
      omega
    have hjW : j.val < W := (show j.val < p from hi).trans hP
    obtain ⟨v,r,hMat,hRhs',f'⟩ := installConstraint_run (M:=M) (m:=m) (n:=n) (i:=j.val) (s:=u)
      (by omega) one hWordX (by have := j.isLt; omega) hjW (by omega) (by omega) hEntryB
      ((f.vars _ (by decide)).trans ht.1.base) ((f.vars _ (by decide)).trans ht.1.cols)
      ((f.vars _ (by decide)).trans rfl) ((f.vars _ (by decide)).trans ht.1.modWord)
      (by simp [u]) (by rw [f.len _,hRhs]; exact Nat.add_lt_add_left j.isLt m)
      (by rw [f.len _]; have hge := Nat.mul_le_mul_right n (show m+n ≤ m+n+1 by omega); omega)
    have fr := Frame.of_run (hr.seq r)
    have hB := ht.2.2.2.2.1.advance j x hMat0
      (hMat.trans (by rw [f.arrs _ (by decide)]))
      (hRhs'.trans (by rw [f.arrs _ (by decide)]))
    let w := v.setArr coordinateBank j.val x.val
    let y := w.setVar coordinateSlot (j.val+1)
    have hV' : v.vars crtRepresentative=x.val := (f'.vars _ (by decide)).trans (by simp [u])
    have hv' : v.vars coordinateSlot=j.val := fr.vars _ (by decide)
    have hw : Run W storeProbeCoordinate v w 3 := Run.store
      (ev_var hv' hjW) (ev_var hV' hWordX) (j.isLt.trans_le (by rw [fr.len _]; exact ht.1.destLen))
    have hry : Run W nextProbeCoordinate w y 4 := Run.assign
      (ev_add (ev_var (show w.vars coordinateSlot=j.val from hv') hjW)
        (evalB_lit one) (show j.val+1 < W from (Nat.succ_le_of_lt hi).trans_lt hP))
    have rr : Run W probePrefixBody t y 56 := (hr.seq (r.seq (hw.seq hry))).mono (by decide)
    have fy := Frame.of_run rr
    have hY : y.vars coordinateSlot=j.val+1 := by simp [y]
    have hy : RecoveryLayout M m n y := restoreLayout ht.1 fy (by decide) (by decide)
      (by decide) (by decide) (by rw [fy.arrs matrixR (by decide)]; exact ht.1.workCanon)
    have hBanks := hB.congr_env
      ((Frame.of_run (hw.seq hry)).arrs _ (by decide))
      ((Frame.of_run (hw.seq hry)).arrs _ (by decide))
    have hPrev : CoordinatePrefix (probeVector i a j.val) j.val t := ht.2.2.2.2.2
    have hStore : y.arrs coordinateBank=(t.arrs coordinateBank).set j.val x.val := by
      change (v.arrs coordinateBank).set j.val x.val = _
      rw [fr.arrs _ (by decide)]
    have hCoords := hPrev.advance j x (j.isLt.trans_le ht.1.destLen) hStore
    have hvect := probeVector_next i j a hj
    refine ⟨y,rr,⟨hy,by rw [hY]; exact Nat.succ_le_of_lt hi,
      (fy.vars _ (by decide)).trans ht.2.2.1,(fy.vars _ (by decide)).trans ht.2.2.2.1,?_,?_⟩,?_⟩
    · rw [hY,← hvect]
      exact hBanks
    · rw [hY,← hvect]
      exact hCoords
    · simp only [V,hY]
      change p-(j.val+1) < p-j.val
      omega
  obtain ⟨t,r,ht,hstop⟩ := Run.while_count I V 56 (fun u hu => ⟨_,hGuard u hu⟩) hStep hInitial
  have hDone : t.vars coordinateSlot=p := by
    rw [hGuard t ht] at hstop
    have hh : ¬t.vars coordinateSlot < p := by simpa using hstop
    exact le_antisymm ht.2.1 (Nat.le_of_not_gt hh)
  have hEnd : probeVector i a p = Function.update (0 : Fin n → ZMod M) i a := by simp [probeVector,p]
  refine ⟨t,r.mono ?_,ht.1,hDone,?_,?_⟩
  · simp [V,hSlot,probePrefixGuard,Cond.size,Expr.size,p] <;> omega
  · simpa only [hDone,hEnd] using ht.2.2.2.2.1
  · simpa only [hDone,hEnd] using ht.2.2.2.2.2

#print axioms installKernelProbePrefix_run
end EvenTI.P15Scalar