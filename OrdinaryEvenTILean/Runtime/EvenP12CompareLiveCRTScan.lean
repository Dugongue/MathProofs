import EvenP12CompareLiveCRTStep
import EvenP12CompareRecoverSmithRun

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (noRead)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def crtCursor : String := "even_recover_crt_cursor"
def crtRows : String := "even_recover_crt_rows"
def coefficientBank : String := "even_recover_crt_coefficients"
def targetBank : String := "even_recover_crt_targets"
def modulusBank : String := "even_recover_crt_moduli"

def CRTInputs (es : List UnaryEquation) (σ : Env) : Prop :=
  σ.vars crtRows = es.length ∧
  σ.arrs coefficientBank = es.map UnaryEquation.coefficient ∧
  σ.arrs targetBank = es.map UnaryEquation.value ∧
  σ.arrs modulusBank = es.map UnaryEquation.modulus

def PrefixSolutions (es : List UnaryEquation) (j x : ℕ) : Prop :=
  ∀ i : Fin es.length, i.val < j → (es.get i).Satisfied x

private theorem prefixSolutions_succ (es : List UnaryEquation) (i : Fin es.length) (x : ℕ) :
    PrefixSolutions es (i.val+1) x ↔ PrefixSolutions es i.val x ∧ (es.get i).Satisfied x := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ j hj
    by_cases hlt : j.val < i.val
    · exact h j hlt
    · have hEq : j = i := Fin.ext (by omega)
      simpa only [hEq] using hi

/-- A nonempty prefix is represented by one canonical class modulo a divisor
of the original M. A rejected prefix has no solution at any residue. -/
def CRTState (M : ℕ) (es : List UnaryEquation) (j : ℕ) (σ : Env) : Prop :=
  (σ.vars crtActive = 1 ∧ σ.vars crtRepresentative < σ.vars crtPeriod ∧
    σ.vars crtPeriod ∣ M ∧ ∀ x, PrefixSolutions es j x ↔
      x ≡ σ.vars crtRepresentative [MOD σ.vars crtPeriod]) ∨
  (σ.vars crtActive = 0 ∧ ∀ x, ¬ PrefixSolutions es j x)

private theorem crtState_congr {M j : ℕ} {es : List UnaryEquation} {σ τ : Env}
    (ha : τ.vars crtActive = σ.vars crtActive)
    (hr : τ.vars crtRepresentative = σ.vars crtRepresentative)
    (hp : τ.vars crtPeriod = σ.vars crtPeriod) (h : CRTState M es j σ) :
    CRTState M es j τ := by simpa only [CRTState,ha,hr,hp] using h

def loadCRTRow : Com :=
  .seq (.assign rowCoefficient (.get coefficientBank (.var crtCursor)))
    (.seq (.assign rowTarget (.get targetBank (.var crtCursor)))
      (.assign rowModulus (.get modulusBank (.var crtCursor))))

private theorem loadCRTRow_run (es : List UnaryEquation) (i : Fin es.length)
    {W : ℕ} {σ : Env} (h : CRTInputs es σ) (hCursor : σ.vars crtCursor = i.val)
    (hw : es.length < W) (ha : (es.get i).coefficient < W)
    (hb : (es.get i).value < W) (hd : (es.get i).modulus < W) :
    ∃ τ, Run W loadCRTRow σ τ 9 ∧
      τ.vars rowCoefficient = (es.get i).coefficient ∧
      τ.vars rowTarget = (es.get i).value ∧ τ.vars rowModulus = (es.get i).modulus ∧
      Frame loadCRTRow σ τ := by
  let x := es.get i
  have hiW : i.val < W := i.isLt.trans hw
  let ρ := σ.setVar rowCoefficient x.coefficient
  let η := ρ.setVar rowTarget x.value
  let τ := η.setVar rowModulus x.modulus
  have e₁ : (Expr.get coefficientBank (.var crtCursor)).evalB W σ = some x.coefficient := by
    apply evalB_get (ev_var hCursor hiW) ?_ ha
    rw [h.2.1,List.getElem?_map,List.getElem?_eq_getElem i.isLt]
    rfl
  have hCursorρ : ρ.vars crtCursor = i.val := by
    simpa [ρ,vars_setVar,show crtCursor ≠ rowCoefficient by decide] using hCursor
  have e₂ : (Expr.get targetBank (.var crtCursor)).evalB W ρ = some x.value := by
    apply evalB_get (ev_var hCursorρ hiW) ?_ hb
    rw [show ρ.arrs targetBank = es.map UnaryEquation.value from h.2.2.1,
      List.getElem?_map,List.getElem?_eq_getElem i.isLt]
    rfl
  have hCursorη : η.vars crtCursor = i.val := by
    simpa [η,vars_setVar,show crtCursor ≠ rowTarget by decide] using hCursorρ
  have e₃ : (Expr.get modulusBank (.var crtCursor)).evalB W η = some x.modulus := by
    apply evalB_get (ev_var hCursorη hiW) ?_ hd
    rw [show η.arrs modulusBank = es.map UnaryEquation.modulus from h.2.2.2,
      List.getElem?_map,List.getElem?_eq_getElem i.isLt]
    rfl
  have hRun : Run W loadCRTRow σ τ 9 := (Run.assign e₁).seq ((Run.assign e₂).seq (Run.assign e₃))
  refine ⟨τ,hRun,?_,?_,?_,Frame.of_run hRun⟩
  · simp [τ,η,ρ,vars_setVar,show rowCoefficient ≠ rowModulus by decide,
      show rowCoefficient ≠ rowTarget by decide,x]
  · simp [τ,η,vars_setVar,show rowTarget ≠ rowModulus by decide,x]
  · simp [τ,x]

def crtStep : Com :=
  .seq (.ite (.eq (.var crtActive) (.lit 1)) (.seq loadCRTRow intersectRow) .skip)
    (.assign crtCursor (.add (.var crtCursor) (.lit 1)))

def crtStepCost (M : ℕ) : ℕ := intersectRowCost M+24

private theorem crtInputs_of_frame {es : List UnaryEquation} {σ τ : Env}
    (h : CRTInputs es σ) (hv : τ.vars crtRows = σ.vars crtRows)
    (hc : τ.arrs coefficientBank = σ.arrs coefficientBank)
    (ht : τ.arrs targetBank = σ.arrs targetBank)
    (hd : τ.arrs modulusBank = σ.arrs modulusBank) : CRTInputs es τ :=
  ⟨hv.trans h.1,hc.trans h.2.1,ht.trans h.2.2.1,hd.trans h.2.2.2⟩

private theorem crtStep_run (es : List UnaryEquation) (i : Fin es.length)
    {W M : ℕ} {σ : Env} (hM : 0 < M) (hW : 4*M*M+4*M+10 < W)
    (hwords : es.length < W) (h : CRTInputs es σ) (hCursor : σ.vars crtCursor = i.val)
    (hData : ∀ j : Fin es.length, (es.get j).coefficient ≤ M ∧ (es.get j).value ≤ M ∧
      0 < (es.get j).modulus ∧ (es.get j).modulus ∣ M)
    (hs : CRTState M es i.val σ) :
    ∃ τ, Run W crtStep σ τ (crtStepCost M) ∧
      CRTInputs es τ ∧ τ.vars crtCursor = i.val+1 ∧ CRTState M es (i.val+1) τ := by
  let cond : Cond := .eq (.var crtActive) (.lit 1)
  let active : Com := .seq loadCRTRow intersectRow
  have hw : 1 < W := by omega
  have hgo : ∃ ρ, Run W (.ite cond active .skip) σ ρ (intersectRowCost M+16) ∧
      CRTState M es (i.val+1) ρ := by
    rcases hs with hyes | hno
    · obtain ⟨hAct,hCanon,hp,hPrefix⟩ := hyes
      obtain ⟨ha,hb,hd,hdM⟩ := hData i
      have hMod := Nat.le_of_dvd hM hdM
      obtain ⟨η,hload,hA,hB,hD,hf⟩ := loadCRTRow_run es i h hCursor hwords
        (by omega) (by omega) (by omega)
      have ha' : η.vars crtActive = 1 := (hf.vars _ (by decide)).trans hAct
      have hr' : η.vars crtRepresentative = σ.vars crtRepresentative := hf.vars _ (by decide)
      have hp' : η.vars crtPeriod = σ.vars crtPeriod := hf.vars _ (by decide)
      obtain ⟨ρ,hr,_,hc⟩ := intersectRow_run hM hW hCanon hp hd hdM ha hb hr' hp' ha' hA hB hD
      have eh : cond.evalB W σ = some true := by
        exact evalB_condEq (ev_var hAct hw) (evalB_lit hw)
      have rr : Run W (.ite cond active .skip) σ ρ (intersectRowCost M+16) :=
        (Run.ite_true eh (hload.seq hr)).mono (by simp [cond,Cond.size,Expr.size] <;> omega)
      refine ⟨ρ,rr,?_⟩
      rcases hc with ⟨h₁,h₂,h₃,hc⟩ | ⟨h₁,hc⟩
      · refine Or.inl ⟨h₁,h₂,h₃,fun x => ?_⟩
        rw [prefixSolutions_succ es i x,hPrefix x]
        exact hc x
      · refine Or.inr ⟨h₁,fun x hx => ?_⟩
        obtain ⟨hpx,hi⟩ := (prefixSolutions_succ es i x).mp hx
        exact hc x ⟨(hPrefix x).mp hpx,hi⟩
    · obtain ⟨hAct,hNo⟩ := hno
      have eh : cond.evalB W σ = some false := by
        exact evalB_condEq (ev_var hAct (by omega)) (evalB_lit (n := 1) hw)
      have rr : Run W (.ite cond active .skip) σ σ (intersectRowCost M+16) :=
        (Run.ite_false eh Run.skip).mono (by simp [cond,Cond.size,Expr.size] <;> omega)
      exact ⟨σ,rr,Or.inr ⟨hAct,fun x hx => hNo x ((prefixSolutions_succ es i x).mp hx).1⟩⟩
  obtain ⟨ρ,hRun,hNext⟩ := hgo
  let τ := ρ.setVar crtCursor (i.val+1)
  have hf := Frame.of_run hRun
  have hiρ : ρ.vars crtCursor = i.val := (hf.vars _ (by decide)).trans hCursor
  have hv : i.val+1 < W := (Nat.succ_le_of_lt i.isLt).trans_lt hwords
  have ei : (Expr.add (.var crtCursor) (.lit 1)).evalB W ρ = some (i.val+1) :=
    ev_add (ev_var hiρ (by omega)) (evalB_lit hw) hv
  have r₂ : Run W (.assign crtCursor (.add (.var crtCursor) (.lit 1))) ρ τ 4 := Run.assign ei
  have rr : Run W crtStep σ τ (crtStepCost M) :=
    (hRun.seq r₂).mono (by unfold crtStepCost; omega)
  have ff := Frame.of_run rr
  refine ⟨τ,rr,crtInputs_of_frame h (ff.vars _ (by decide)) (ff.arrs _ (by decide))
    (ff.arrs _ (by decide)) (ff.arrs _ (by decide)),by simp [τ],?_⟩
  exact crtState_congr (by simp [τ,vars_setVar,show crtActive ≠ crtCursor by decide])
    (by simp [τ,vars_setVar,show crtRepresentative ≠ crtCursor by decide])
    (by simp [τ,vars_setVar,show crtPeriod ≠ crtCursor by decide]) hNext

def crtGuard : Cond := .lt (.var crtCursor) (.var crtRows)

def crtScan : Com := .while crtGuard crtStep

def crtScanCost (M rows : ℕ) : ℕ := (crtStepCost M+4)*rows+4

/-- The live all-row scan. One normalization is charged for each row, the
failure case remains empty across the rest of the scan, and all source banks
are retained. -/
theorem crtScan_run (es : List UnaryEquation) {M W : ℕ} {σ : Env}
    (hM : 0 < M) (hW : 4*M*M+4*M+10 < W) (hl : es.length < W)
    (h : CRTInputs es σ) (hCursor : σ.vars crtCursor = 0)
    (hInitial : CRTState M es 0 σ)
    (hData : ∀ j : Fin es.length, (es.get j).coefficient ≤ M ∧ (es.get j).value ≤ M ∧
      0 < (es.get j).modulus ∧ (es.get j).modulus ∣ M) :
    ∃ τ, Run W crtScan σ τ (crtScanCost M es.length) ∧
      CRTInputs es τ ∧ τ.vars crtCursor = es.length ∧ CRTState M es es.length τ ∧
      Frame crtScan σ τ := by
  let I (τ : Env) := CRTInputs es τ ∧ τ.vars crtCursor ≤ es.length ∧ CRTState M es (τ.vars crtCursor) τ
  let V (τ : Env) := es.length - τ.vars crtCursor
  have hg (τ : Env) (hτ : I τ) :
      crtGuard.evalB W τ = some (decide (τ.vars crtCursor < es.length)) := by
    exact evalB_condLt (ev_var rfl (hτ.2.1.trans_lt hl)) (ev_var hτ.1.1 hl)
  have step (τ : Env) (hτ : I τ) (hTest : crtGuard.evalB W τ = some true) :
      ∃ η, Run W crtStep τ η (crtStepCost M) ∧ I η ∧ V η < V τ := by
    rw [hg τ hτ] at hTest
    have hi : τ.vars crtCursor < es.length := by simpa using hTest
    let i : Fin es.length := ⟨τ.vars crtCursor,hi⟩
    obtain ⟨η,hRun,hInputs,hC,hS⟩ :=
      crtStep_run es i hM hW hl hτ.1 rfl hData hτ.2.2
    refine ⟨η,hRun,⟨hInputs,by rw [hC]; exact Nat.succ_le_of_lt hi,?_⟩,?_⟩
    · rw [hC]; exact hS
    · simp only [V,hC,i]; omega
  have h0 : I σ := ⟨h,by rw [hCursor]; exact Nat.zero_le _,by rwa [hCursor]⟩
  obtain ⟨τ,hRun,hI,hStop⟩ :=
    Run.while_count I V (crtStepCost M) (fun ρ hρ => ⟨_,hg ρ hρ⟩) step h0
  rw [hg τ hI] at hStop
  have hDone : τ.vars crtCursor = es.length := by
    have hle := hI.2.1
    have hge : ¬ τ.vars crtCursor < es.length := by simpa using hStop
    omega
  have rr : Run W crtScan σ τ (crtScanCost M es.length) :=
    hRun.mono (by simp [crtScanCost,crtGuard,Cond.size,Expr.size,V,hCursor,Nat.add_comm 4])
  exact ⟨τ,rr,hI.1,hDone,by simpa only [hDone] using hI.2.2,Frame.of_run rr⟩

#print axioms crtScan_run

end EvenTI.P12Compare
