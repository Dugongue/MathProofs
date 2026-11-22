import EvenP12CompareLiveCRTStep
import Mathproof.Meta.P15GSSSmithWeight20261007

namespace EvenTI.P12Compare

open scoped BigOperators
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR TwoBank)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithWeight20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)
open Mathproof.Problem18IMPFieldLayout20261001 (noRead)

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def crtRhsBank : String := "even_recover_smith_rhs"
def crtDot : String := "even_recover_smith_dot"
def crtRhsWord : String := "even_recover_smith_rhs_word"

def CRTSmithInput {M m n : ℕ} [NeZero M] (st : ZDiag.State M (m+1) n)
    (b : Fin m → ZMod M) (σ : Env) : Prop :=
  σ.vars rowsR = m+1 ∧ σ.vars inputColsR = n ∧ σ.vars modR = M ∧
  (m+1)*n+(m+1)*(m+1) ≤ (σ.arrs matrixR).length ∧ Canonical M (σ.arrs matrixR) ∧
  TwoBank σ st ∧ σ.arrs crtRhsBank = List.ofFn (fun j => (b j).val)

theorem crtSmithInput_congr {M m n : ℕ} [NeZero M] {st : ZDiag.State M (m+1) n}
    {b : Fin m → ZMod M} {σ τ : Env} (h : CRTSmithInput st b σ)
    (hr : τ.vars rowsR = σ.vars rowsR) (hn : τ.vars inputColsR = σ.vars inputColsR)
    (hm : τ.vars modR = σ.vars modR) (hmat : τ.arrs matrixR = σ.arrs matrixR)
    (hb : τ.arrs crtRhsBank = σ.arrs crtRhsBank) : CRTSmithInput st b τ := by
  unfold CRTSmithInput TwoBank at *
  exact ⟨hr.trans h.1,hn.trans h.2.1,hm.trans h.2.2.1,
    by rw [hmat]; exact h.2.2.2.1,by rw [hmat]; exact h.2.2.2.2.1,
    by rw [hmat]; exact h.2.2.2.2.2.1,hb.trans h.2.2.2.2.2.2⟩

private def rhsTerm {M m : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M)
    (b : Fin m → ZMod M) (j : ℕ) : ZMod M :=
  if h : j < m then u ((⟨j,h⟩ : Fin m).castSucc) * b ⟨j,h⟩ else 0

private def rhsPrefix {M m : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M)
    (b : Fin m → ZMod M) (k : ℕ) : ZMod M :=
  ∑ j ∈ Finset.range k, rhsTerm u b j

private theorem rhsPrefix_full {M m : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M)
    (b : Fin m → ZMod M) :
    rhsPrefix u b m = ∑ j : Fin m, u j.castSucc * b j := by
  rw [rhsPrefix,Finset.sum_range]
  exact Finset.sum_congr rfl (fun j _ => dif_pos j.isLt)

private theorem rhsPrefix_step {M m : ℕ} [NeZero M] (u : Fin (m+1) → ZMod M)
    (b : Fin m → ZMod M) (j : Fin m) :
    rhsPrefix u b (j.val+1) = rhsPrefix u b j.val + u j.castSucc*b j := by
  rw [rhsPrefix,Finset.sum_range_succ,rhsTerm,dif_pos j.isLt]
  rfl

private def dotTotalExpr : Expr := .add (.var crtDot) (.mul (.var productWeightR) (.var crtRhsWord))
private def dotNextExpr : Expr :=
  .sub dotTotalExpr (.mul (.div dotTotalExpr (.var modR)) (.var modR))
private def dotLoad : Com := .assign crtRhsWord (.get crtRhsBank (.var productColR))
private def dotCompute : Com := .assign crtDot dotNextExpr
private def dotInc : Com := .assign productColR (.add (.var productColR) (.lit 1))
private def dotStep : Com := .seq loadWeightIMP (.seq dotLoad (.seq dotCompute dotInc))
private def dotGuard : Cond := .lt (.var productColR) (.sub (.var rowsR) (.lit 1))
private def dotInit : Com := .seq (.assign productColR (.lit 0)) (.assign crtDot (.lit 0))
def loadSmithDot : Com := .seq dotInit (.while dotGuard dotStep)

private theorem dotStep_run {M m n W : ℕ} [NeZero M] {σ : Env}
    (st : ZDiag.State M (m+1) n) (b : Fin m → ZMod M) (r : Fin (m+1)) (j : Fin m)
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+2 < W) (hW : 4*M*M+4*M+10 < W)
    (h : CRTSmithInput st b σ) (hR : σ.vars productRowR = r.val)
    (hJ : σ.vars productColR = j.val) (hD : σ.vars crtDot = (rhsPrefix (st.U r) b j.val).val) :
    ∃ τ, Run W dotStep σ τ 60 ∧ CRTSmithInput st b τ ∧
      τ.vars productRowR = r.val ∧ τ.vars productColR = j.val+1 ∧
      τ.vars crtDot = (rhsPrefix (st.U r) b (j.val+1)).val := by
  obtain ⟨hRows,hCols,hMod,hLen,hCanon,hBank,hRhs⟩ := h
  have hMW : M < W := by omega
  obtain ⟨ρ,r0,hWeight,hWeightB,hF⟩ := loadWeightIMP_run st r j.castSucc hL hMW
    hLen hCanon hRows hCols hR hJ hBank
  have hJR : ρ.vars productColR = j.val := (hF.vars _ (by decide)).trans hJ
  have hRhsR : ρ.arrs crtRhsBank = List.ofFn (fun j => (b j).val) :=
    (hF.arrs _ (by decide)).trans hRhs
  have hjw : j.val < W := j.isLt.trans (by omega)
  have hjw' : j.val+1 < W := by have := j.isLt; omega
  let η := ρ.setVar crtRhsWord (b j).val
  have rr : (ρ.arrs crtRhsBank)[j.val]? = some (b j).val := by
    rw [hRhsR]
    simp [j.isLt]
  have r1 : Run W dotLoad ρ η 3 := Run.assign
    (evalB_get (ev_var hJR hjw) rr ((ZMod.val_lt _).trans hMW))
  have hF1 := Frame.of_run r1
  let x := (rhsPrefix (st.U r) b j.val).val
  let y := (st.U r j.castSucc).val
  let z := (b j).val
  let v := x+y*z
  have hx : x < M := ZMod.val_lt _
  have hy : y < M := ZMod.val_lt _
  have hz : z < M := ZMod.val_lt _
  have hprod : y*z ≤ M*M := Nat.mul_le_mul hy.le hz.le
  have hquad : M*M ≤ (4*M)*M := Nat.mul_le_mul_right M (by omega)
  have htotal : x+y*z < W := by omega
  have hx' : η.vars crtDot = x := (hF1.vars _ (by decide)).trans ((hF.vars _ (by decide)).trans hD)
  have hy' : η.vars productWeightR = y := (hF1.vars _ (by decide)).trans hWeight
  have hz' : η.vars crtRhsWord = z := by simp [η,z]
  have hm' : η.vars modR = M :=
    (hF1.vars _ (by decide)).trans ((hF.vars _ (by decide)).trans hMod)
  have evV : dotTotalExpr.evalB W η = some v :=
    ev_add (ev_var hx' (hx.trans hMW)) (ev_mul (ev_var hy' (hy.trans hMW))
      (ev_var hz' (hz.trans hMW)) (hprod.trans_lt (by omega))) htotal
  have evM : (Expr.var modR).evalB W η = some M := ev_var hm' hMW
  have hvW := Expr.lt_of_evalB evV
  have hrem : dotNextExpr.evalB W η = some (v%M) := by
    unfold dotNextExpr
    exact (ev_sub evV (ev_mul (ev_div evV evM ((Nat.div_le_self ..).trans_lt hvW)) evM
      ((Nat.div_mul_le_self ..).trans_lt hvW)) ((Nat.sub_le ..).trans_lt hvW)).trans
      (congrArg some (hmdg v M))
  let ζ := η.setVar crtDot (v%M)
  have r2 : Run W dotCompute η ζ 19 := (Run.assign hrem).mono (by decide)
  have hJζ : ζ.vars productColR = j.val := ((Frame.of_run r2).vars _ (by decide)).trans
    ((hF1.vars _ (by decide)).trans hJR)
  let τ := ζ.setVar productColR (j.val+1)
  have r3 : Run W dotInc ζ τ 4 := Run.assign (ev_add (ev_var hJζ hjw)
    (evalB_lit (n := 1) (by omega)) hjw')
  have run : Run W dotStep σ τ 60 := (r0.seq (r1.seq (r2.seq r3))).mono (by decide)
  have hf := Frame.of_run run
  have hVal : (rhsPrefix (st.U r) b (j.val+1)).val = v%M := by
    rw [rhsPrefix_step,ZMod.val_add,ZMod.val_mul]
    simp only [v,x,y,z,Nat.add_mod_mod]
  refine ⟨τ,run,crtSmithInput_congr ⟨hRows,hCols,hMod,hLen,hCanon,hBank,hRhs⟩
    (hf.vars _ (by decide)) (hf.vars _ (by decide)) (hf.vars _ (by decide))
    (hf.arrs _ (by decide)) (hf.arrs _ (by decide)),
    (hf.vars _ (by decide)).trans hR,by simp [τ],?_⟩
  simp [τ,ζ,vars_setVar,show crtDot ≠ productColR by decide, hVal]

/-- Compute the actual finite-field RHS dot product from canonical Smith U
and the original RHS words. Every read, product and modular accumulation is paid. -/
theorem loadSmithDot_run {M m n W : ℕ} [NeZero M] {σ : Env}
    (st : ZDiag.State M (m+1) n) (b : Fin m → ZMod M) (r : Fin (m+1))
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+2 < W) (hW : 4*M*M+4*M+10 < W)
    (h : CRTSmithInput st b σ) (hR : σ.vars productRowR = r.val) :
    ∃ τ, Run W loadSmithDot σ τ (70*m+20) ∧ CRTSmithInput st b τ ∧
      τ.vars productRowR = r.val ∧ τ.vars productColR = m ∧
      τ.vars crtDot = (∑ j : Fin m, st.U r j.castSucc * b j : ZMod M).val ∧
      Frame loadSmithDot σ τ := by
  let η := (σ.setVar productColR 0).setVar crtDot 0
  have hw : 0 < W := by omega
  have r0 : Run W dotInit σ η 4 := (Run.assign (evalB_lit hw)).seq (Run.assign (evalB_lit hw))
  have f0 := Frame.of_run r0
  let I (τ : Env) := CRTSmithInput st b τ ∧ τ.vars productRowR = r.val ∧
    τ.vars productColR ≤ m ∧ τ.vars crtDot = (rhsPrefix (st.U r) b (τ.vars productColR)).val
  let V (τ : Env) := m-τ.vars productColR
  have hg (τ : Env) (hτ : I τ) : dotGuard.evalB W τ = some (decide (τ.vars productColR < m)) := by
    have right : (Expr.sub (.var rowsR) (.lit 1)).evalB W τ = some m := by
      exact (ev_sub (ev_var hτ.1.1 (by omega : m+1 < W))
        (evalB_lit (n := 1) (by omega)) (by omega : m+1-1 < W)).trans
        (congrArg some (by omega : m+1-1 = m))
    exact evalB_condLt (ev_var rfl (by have := hτ.2.2.1; omega)) right
  have hs (τ : Env) (hτ : I τ) (hgo : dotGuard.evalB W τ = some true) :
      ∃ ξ, Run W dotStep τ ξ 60 ∧ I ξ ∧ V ξ < V τ := by
    rw [hg τ hτ] at hgo
    have hi : τ.vars productColR < m := by simpa using hgo
    let j : Fin m := ⟨_,hi⟩
    obtain ⟨ξ,hr,hI,hRow,hCol,hDot⟩ := dotStep_run st b r j hL hW hτ.1 hτ.2.1 rfl hτ.2.2.2
    refine ⟨ξ,hr,⟨hI,hRow,by rw [hCol]; exact Nat.succ_le_of_lt hi,by rw [hCol]; exact hDot⟩,?_⟩
    simp only [V,hCol,j]; omega
  have h0 : η.vars productColR = 0 := by
    simp [η,vars_setVar,show productColR ≠ crtDot by decide]
  have hI : I η := ⟨crtSmithInput_congr h (f0.vars _ (by decide)) (f0.vars _ (by decide))
    (f0.vars _ (by decide)) (f0.arrs _ (by decide)) (f0.arrs _ (by decide)),
    (f0.vars _ (by decide)).trans hR,by simp [h0],by simp [η,rhsPrefix]⟩
  obtain ⟨τ,rr,hτ,hStop⟩ := Run.while_count I V 60 (fun ξ hx => ⟨_,hg ξ hx⟩) hs hI
  rw [hg τ hτ] at hStop
  have hd : τ.vars productColR = m := by
    have hl := hτ.2.2.1
    have hr : ¬ τ.vars productColR < m := by simpa using hStop
    omega
  have run : Run W loadSmithDot σ τ (70*m+20) := (r0.seq rr).mono (by
    simp [dotGuard,Cond.size,Expr.size,V,h0] <;> omega)
  refine ⟨τ,run,hτ.1,hτ.2.1,hd,?_,Frame.of_run run⟩
  simpa only [hd,rhsPrefix_full] using hτ.2.2.2

#print axioms loadSmithDot_run

end EvenTI.P12Compare
