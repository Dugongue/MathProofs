import EvenP12CompareLiveCRTRow
import EvenP12CompareLiveCRTInstall
import Mathproof.Meta.Problem18PairBoundaryCopy20261004

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18PairBoundaryCopy20261004
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open EvenTI.P12Compare

def constraintMatrix : String := "even_recovery_constraints"
def baseRows : String := "even_recovery_base_rows"

def constraintRow : Expr := .add (.var baseRows) (.var coordinateSlot)
def constraintEntry : Expr := .add (.mul constraintRow (.var inputColsR)) (.var coordinateSlot)

def unitWord : Expr :=
  .sub (.lit 1) (.mul (.div (.lit 1) (.var modR)) (.var modR))

def installConstraint : Com :=
  .seq (.store constraintMatrix constraintEntry unitWord)
    (.store crtRhsBank constraintRow (.var crtRepresentative))

private theorem evalLive {B v : ℕ} {s : Env} {x : String}
    (h : s.vars x=v) (hv : v<B) : (Expr.var x).evalB B s=some v :=
  evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩

/-- Install the equation obtained from the last successful coordinate run. The
existing rows stay in the persistent bank when the Smith workspace is reused. -/
theorem installConstraint_run {M B m n i r : Nat} {s : Env}
    (hM : M<B) (hB : 1<B) (hrB : r<B) (hRowB : m+i<B) (hiB : i<B)
    (hmB : m<B) (hnB : n<B) (hCell : (m+i)*n+i<B)
    (hm : s.vars baseRows=m) (hn : s.vars inputColsR=n) (hi : s.vars coordinateSlot=i)
    (hc : s.vars modR=M) (hr : s.vars crtRepresentative=r)
    (hRow : m+i < (s.arrs crtRhsBank).length)
    (hEntry : (m+i)*n+i < (s.arrs constraintMatrix).length) :
    ∃ t, Run B installConstraint s t 26 ∧
      t.arrs constraintMatrix=(s.arrs constraintMatrix).set ((m+i)*n+i) (1%M) ∧
      t.arrs crtRhsBank=(s.arrs crtRhsBank).set (m+i) r ∧ Frame installConstraint s t := by
  have eRow : constraintRow.evalB B s = some (m+i) :=
    evalB_bin (op:=.add) (evalLive hm hmB) (evalLive hi hiB) hRowB
  have eCell : constraintEntry.evalB B s = some ((m+i)*n+i) :=
    evalB_bin (op:=.add) (evalB_bin (op:=.mul) eRow (evalLive hn hnB)
      (by change (m+i)*n<B; omega)) (evalLive hi hiB) hCell
  have hDiv : 1/M ≤ 1 := Nat.div_le_self _ _
  have hProd : (1/M)*M ≤ 1 := Nat.div_mul_le_self _ _
  have eQuot : (Expr.div (.lit 1) (.var modR)).evalB B s = some (1/M) :=
    evalB_bin (op:=.div) (evalB_lit hB) (evalLive hc hM) (by change 1/M<B; omega)
  have eMul : (Expr.mul (.div (.lit 1) (.var modR)) (.var modR)).evalB B s = some ((1/M)*M) :=
    evalB_bin (op:=.mul) eQuot (evalLive hc hM) (by change (1/M)*M<B; omega)
  have eVal : unitWord.evalB B s = some (1%M) := by
    have e := evalB_bin (op:=.sub) (evalB_lit hB) eMul (by change 1-(1/M)*M<B; omega)
    simpa only [unitWord,Bop.apply,Nat.mod_def,Nat.mul_comm] using e
  let u := s.setArr constraintMatrix ((m+i)*n+i) (1%M)
  let t := u.setArr crtRhsBank (m+i) r
  have ru : Run B (.store constraintMatrix constraintEntry unitWord) s u
      (1+constraintEntry.size+unitWord.size) := Run.store eCell eVal hEntry
  have rt : Run B (.store crtRhsBank constraintRow (.var crtRepresentative)) u t 5 := by
    refine Run.store ?_ (evalLive (s:=u) (x:=crtRepresentative) (by exact hr) hrB) ?_
    · exact evalB_bin (op:=.add) (evalLive (s:=u) (x:=baseRows) (by exact hm) hmB)
        (evalLive (s:=u) (x:=coordinateSlot) (by exact hi) hiB) hRowB
    · simpa [u,arrs_setArr,show crtRhsBank ≠ constraintMatrix by decide] using hRow
  have rr : Run B installConstraint s t 26 := (ru.seq rt).mono (by decide)
  exact ⟨t,rr,by simp [t,u,arrs_setArr,show constraintMatrix ≠ crtRhsBank by decide],
    by simp [t,u,arrs_setArr,show crtRhsBank ≠ constraintMatrix by decide],Frame.of_run rr⟩

def smithInputLength : Expr := .mul (.var rowsR) (.var inputColsR)
def reloadSmithConstraints : Com :=
  copyBlock constraintMatrix matrixR smithInputLength (.lit 0) (.lit 0)

/-- Smith may overwrite its own buffer. Replaying the fixed-height coefficient
bank restores every logical input word, while preserving the RHS and assignments. -/
theorem reloadSmithConstraints_run {B m n : Nat} {s : Env}
    (hB : 1<B) (hmB : m<B) (hnB : n<B) (hLen : m*n<B)
    (hm : s.vars rowsR=m) (hn : s.vars inputColsR=n)
    (hs : m*n≤(s.arrs constraintMatrix).length) (ht : m*n≤(s.arrs matrixR).length)
    (hw : ∀ i < m*n,(s.arrs constraintMatrix).getD i 0<B) :
    ∃ t, Run B reloadSmithConstraints s t (20*(m*n)+14) ∧
      (∀ i < m*n,(t.arrs matrixR).getD i 0=(s.arrs constraintMatrix).getD i 0) ∧
      (∀ i, m*n ≤ i → (t.arrs matrixR).getD i 0=(s.arrs matrixR).getD i 0) ∧
      Frame reloadSmithConstraints s t := by
  have he : smithInputLength.evalB B s=some (m*n) :=
    evalB_bin (op:=.mul) (evalLive hm hmB) (evalLive hn hnB) hLen
  obtain ⟨t,hr,hWords,hTail,_,_,_,_,_⟩ := copyBlock_run (src:=constraintMatrix)
    (dst:=matrixR) (n:=m*n) (sourceBase:=0) (targetBase:=0) (B:=B) (sigma:=s)
    (by decide) he (evalB_lit (by omega)) (evalB_lit (by omega)) hLen
    (by simpa using hLen) (by simpa using hLen) (by simpa using hs) (by simpa using ht)
    (by simpa using hw)
  exact ⟨t,hr,by simpa using hWords,fun i hi => by simpa using hTail i (Or.inr (by simpa using hi)),
    Frame.of_run hr⟩

#print axioms installConstraint_run
#print axioms reloadSmithConstraints_run
end EvenTI.P14Recovery
