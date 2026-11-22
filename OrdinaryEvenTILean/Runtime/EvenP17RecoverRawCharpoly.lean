import EvenP17RecoverCharpoly
import EvenP17RecoverFront
import EvenP15TrialInputTail

set_option autoImplicit false
set_option maxHeartbeats 2350000
set_option maxRecDepth 12000

namespace EvenTI.P17Recover

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.P10Scan EvenTI.P15Execution EvenTI.P15Trial EvenTI.P12Compare EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots NoVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots)
open Mathproof.Problem17CharpolyExec
open Mathproof.Problem17CharpolyStage (dim)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def anchorCap (n : ℕ) : ℕ := n+n
def rawCharpolyBase (n : ℕ) : ℕ := anchorCap n * anchorCap n
def rawCharpolyWidth (n : ℕ) : ℕ := anchorCap n + 1
def rawCharpolyScratch (n : ℕ) : ℕ := rawCharpolyBase n + rawCharpolyWidth n
def rawCharpolySlots (n : ℕ) : ℕ :=
  rawCharpolyScratch n + 5*(dim (anchorCap n)*dim (anchorCap n))+5

private def capE : Expr := .add (.var requestWidth) (.var requestWidth)
private def baseE : Expr := .mul capE capE
private def widthE : Expr := .add capE (.lit 1)
private def scratchE : Expr := .add baseE widthE

private def rawCharpolyBindings : List (String × Expr) :=
  [(loadBase,.lit 0),(setupCoeff,baseE),(setupWidth,widthE),(setupScratch,scratchE)]

private theorem layoutBindingsSafe :
    ∀ p ∈ rawCharpolyBindings, ∀ q ∈ rawCharpolyBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [rawCharpolyBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl <;>
    simp [NoVar,capE,baseE,widthE,scratchE,requestWidth,loadBase,setupCoeff,setupWidth,setupScratch]

private def rawCharpolyState (n : ℕ) (s : Env) : Env :=
  install [(loadBase,0),(setupCoeff,rawCharpolyBase n),(setupWidth,rawCharpolyWidth n),
    (setupScratch,rawCharpolyScratch n)] s

private theorem rawCharpolyLayout_run (F : FieldPresentation K) {B S n : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) (hN : s.vars requestWidth=n)
    (hCap : rawCharpolyScratch n < B) :
    Run B (commands rawCharpolyBindings) s (rawCharpolyState n s) 31 ∧
      Slots F canonical qN.WS S B (rawCharpolyState n s) := by
  have hNcap : n ≤ anchorCap n := by simp [anchorCap]
  have hp := Nat.le_mul_self (anchorCap n)
  have hA : anchorCap n+1 < B := by unfold rawCharpolyScratch rawCharpolyWidth at hCap; omega
  have eb : (Expr.var requestWidth).evalB B s = some n := evalB_var_iff.mpr ⟨hN.symm,hN ▸ (by omega)⟩
  have ec : capE.evalB B s=some (anchorCap n) :=
    evalB_bin (op:=.add) eb eb (show anchorCap n < B by omega)
  have ed : baseE.evalB B s=some (rawCharpolyBase n) :=
    evalB_bin (op:=.mul) ec ec (show rawCharpolyBase n < B by unfold rawCharpolyScratch at hCap; omega)
  have ew : widthE.evalB B s=some (rawCharpolyWidth n) :=
    evalB_bin (op:=.add) ec (evalB_lit (by omega)) hA
  have es : scratchE.evalB B s=some (rawCharpolyScratch n) :=
    evalB_bin (op:=.add) ed ew hCap
  refine ⟨commands_run rawCharpolyBindings _ s (by rfl)
    (.cons (evalB_lit (by omega)) (.cons ed (.cons ew (.cons es .nil)))) layoutBindingsSafe,?_⟩
  apply installed_slots F _ s hS
  intro p hp'
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
  rcases hp' with rfl|rfl|rfl|rfl <;> simp only [Prod.fst] <;> decide

theorem rawCharpoly_contiguous {n t B : ℕ} (hw : t+1 ≤ anchorCap n)
    (hB : rawCharpolySlots n+rawCharpolyWidth n*dim (anchorCap n)+12 < B) :
    (contiguous t 0 (rawCharpolyBase n) (rawCharpolyWidth n) (rawCharpolyScratch n)).valid
      (rawCharpolySlots n) B := by
  have hDim : dim (t+1) ≤ dim (anchorCap n) := by
    unfold dim
    gcongr
  have hm := Nat.mul_le_mul hDim hDim
  have hMx := Nat.mul_le_mul hw hw
  have hWeighted := Nat.mul_le_mul_left (rawCharpolyWidth n) hDim
  apply contiguous_valid (by unfold rawCharpolyWidth; omega)
  · unfold rawCharpolyScratch rawCharpolyBase
    omega
  · exact le_rfl
  · unfold address chunk rawCharpolySlots
    omega
  · omega
  · unfold address chunk rawCharpolySlots at *
    omega

noncomputable def rawSelectedAnchorCharpoly (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  .seq (recoveryFront F) <| .seq (.read anchorWanted) <|
    .seq (commands rawCharpolyBindings) (selectedAnchorCharpoly D F right)

/-- Starting with the literal request and selected anchor index, the machine
parses both rows, computes the spectral scratch layout from the raw width,
and installs the chosen anchor's full characteristic polynomial. -/
theorem rawSelectedAnchorCharpoly_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n h B : ℕ} (d : ℕ) (raw : List ℕ) (P Q : PreparedTrial K l n)
    (right : Bool) (i : Fin (numberedAnchors (if right then Q else P)).length)
    (A : Matrix (Fin (h+1)) (Fin (h+1)) K)
    (hA : (numberedAnchors (if right then Q else P)).get i=⟨h+1,A⟩)
    (other : String → ℕ) :
    let z := pairW (d::n::raw) (pairW (preparedTrialWords D P) (preparedTrialWords D Q))
    let S := rawCharpolySlots n
    4<B → z.length<B → (∀ x ∈ z, x<B) → i.val<B →
    F.e+1+S*F.e<B → 16*(F.e+1)<B → (F.p+1)^2<B → (F.p+1)^(F.e+1)<B →
    S+rawCharpolyWidth n*dim (anchorCap n)+12<B →
    ∃ t, Run B (rawSelectedAnchorCharpoly D F right)
      (initEnv (recoveryExtent F S z.length other) (z.length::z++[i.val])) t
      ((13*z.length+215+3*F.e)+(1+(31+((19*i.val+22+
        (3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
        (7+fromBankCost F h (rawCharpolyWidth n)))))) ∧
      Slots F canonical qN.WS S B t ∧
      CoeffSlots F t (rawCharpolyWidth n) (rawCharpolyBase n) A.charpoly := by
  dsimp only
  intro hB hLen hWords hi hMF hSF hSquare hPower hBound
  let z := pairW (d::n::raw) (pairW (preparedTrialWords D P) (preparedTrialWords D Q))
  let S := rawCharpolySlots n
  have hSB : S < B := by change S+rawCharpolyWidth n*dim (anchorCap n)+12 < B at hBound; omega
  let la := listW ((numberedAnchors P).map (numberedAnchorWords D))
  let ra := listW ((numberedAnchors Q).map (numberedAnchorWords D))
  obtain ⟨u,ru,hReady,hLeft,hRight,hBank,_,hInp,_⟩ :=
    recoveryFront_run F S d n (trialKind P) (trialKind Q) raw la (trialFormWords D P)
      ra (trialFormWords D Q) other hB hLen hWords hMF hSF hSquare hPower hSB
  let u₀ := appendInput u [i.val]
  let u₁ := {u₀.setVar anchorWanted i.val with inp := []}
  have rFront := paidRun_appendInput [i.val] ru
  change Run B (recoveryFront F)
    (initEnv (recoveryExtent F S z.length other) (z.length::z++[i.val])) u₀
    (13*z.length+215+3*F.e) at rFront
  have rRead : Run B (.read anchorWanted) u₀ u₁ 1 :=
    Run.read (by simp [u₀,appendInput,hInp])
  have hSet : Slots F canonical qN.WS S B (u.setVar anchorWanted i.val) :=
    Slots.setVar F canonical hReady.field (by decide : anchorWanted ∉ regNames canonical)
      (by decide : anchorWanted ≠ qN.WS) i.val
  have h₁ : Slots F canonical qN.WS S B u₁ :=
    slots_frame F hSet rfl rfl (fun _ _ => rfl) rfl
  have hs : rawCharpolyScratch n<B := by
    have hSlots : rawCharpolyScratch n ≤ S := by unfold S rawCharpolySlots; omega
    omega
  obtain ⟨rc,hC⟩ := rawCharpolyLayout_run F h₁ (show u₁.vars requestWidth=n by
    simpa [u₁,u₀,appendInput,requestWidth,anchorWanted] using hReady.ndim) hs
  let v := rawCharpolyState n u₁
  have keep (r : String) (a : r≠loadBase) (b : r≠setupCoeff) (c : r≠setupWidth)
      (k : r≠setupScratch) (e : r≠anchorWanted) : v.vars r=u.vars r := by
    simp [v,rawCharpolyState,install,u₁,u₀,appendInput,a,b,c,k,e]
  have hSections : OperandSections z right
      (listW ((numberedAnchors (if right then Q else P)).map (numberedAnchorWords D)))
      (trialFormWords D (if right then Q else P)) v := by
    have hA' := keep (anchorListStart right) (by cases right <;> decide) (by cases right <;> decide)
      (by cases right <;> decide) (by cases right <;> decide) (by cases right <;> decide)
    have hB' := keep (formStart right) (by cases right <;> decide) (by cases right <;> decide)
      (by cases right <;> decide) (by cases right <;> decide) (by cases right <;> decide)
    have hC' := keep (formEnd right) (by cases right <;> decide) (by cases right <;> decide)
      (by cases right <;> decide) (by cases right <;> decide) (by cases right <;> decide)
    cases right
    · exact ⟨by rw [hA',hB',hC']; exact hLeft.ordered,
        by rw [hA',hB']; exact hLeft.anchors,by rw [hB',hC']; exact hLeft.forms⟩
    · exact ⟨by rw [hA',hB',hC']; exact hRight.ordered,
        by rw [hA',hB']; exact hRight.anchors,by rw [hB',hC']; exact hRight.forms⟩
  have hWidth : h+1 ≤ anchorCap n := by
    have hW := numberedAnchors_width_le (if right then Q else P)
      ((numberedAnchors (if right then Q else P)).get i) (List.get_mem _ i)
    rw [hA] at hW
    simpa [anchorCap,two_mul] using hW
  have hIndex : v.vars anchorWanted=i.val := by
    simp [v,rawCharpolyState,u₁,install,anchorWanted,loadBase,setupCoeff,setupWidth,setupScratch]
  obtain ⟨t,rt,ht,hCoeff,_⟩ := selectedAnchorCharpoly_run D F z _ right _ i A hA hSections hi
    hIndex hC (by
      rw [Mathproof.P15DecideRef20261007.card_eq_pow F]
      exact (Nat.pow_le_pow_left (by omega : F.p ≤ F.p+1) F.e).trans
        ((Nat.pow_le_pow_right (by omega : 0<F.p+1) (by omega : F.e≤F.e+1)).trans hPower.le))
    (by omega) hLen hBank
    (by simp [v,rawCharpolyState,install,loadBase,setupCoeff,setupWidth,setupScratch])
    (by simp [v,rawCharpolyState,install,loadBase,setupCoeff,setupWidth,setupScratch])
    (by simp [v,rawCharpolyState,install,loadBase,setupCoeff,setupWidth,setupScratch])
    (by simp [v,rawCharpolyState,install,loadBase,setupCoeff,setupWidth,setupScratch])
    (rawCharpoly_contiguous hWidth hBound)
  exact ⟨t,rFront.seq (rRead.seq (rc.seq rt)),ht,hCoeff⟩

#print axioms rawCharpoly_contiguous
#print axioms rawSelectedAnchorCharpoly_run
end EvenTI.P17Recover
