import EvenP13SpectralAnchorLoad
import RecognizerWorkspace

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DH2Bank20261007 (rNin)
open Mathproof.Problem17CharpolyExec
open Mathproof.Problem17BudgetExec (dimReg cap budgetCost budgetCost_le)
open Mathproof.Problem17CharpolyStage (dim)
open Mathproof.Problem17RecognizerAllocation (width rawSlot_eq dim_le)
open Mathproof.Problem17RecognizerWorkspace (reserve wordLimit word_dominates fitted)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.Problem17PreparedCovariants (W)
open Mathproof.Problem17CovariantExecution (leftStart rightStart squareStart)
open Mathproof.P15FactorIMP20261007 (Snf)
open EvenTI.P12Compare

def squareE (e : Expr) : Expr := .mul e e
def anchorSide : Expr := .var dimReg
def anchorSize : Expr := .var loadLength
def anchorWidthE : Expr :=
  .add (.mul (.lit 16) (squareE (squareE (.add anchorSize (.lit 1))))) (.lit 16)
def anchorBaseE : Expr := .mul (.lit 3) (squareE anchorSize)

/-- Set the matrix and factor-bank addresses from the literal serialized
anchor's leading dimension, using only bounded arithmetic. -/
def anchorRegisters (bank : String) : Com :=
  .seq (.assign dimReg (.get bank (.lit 0)))
    (.seq (.assign loadLength (squareE anchorSide))
      (.seq (.assign rNin anchorWidthE)
        (.seq (.assign loadBase anchorBaseE) (.assign inputBase (.lit 1)))))

theorem anchorRegisters_run (bank : String) {B n : ℕ} {σ : Env}
    (hword : (σ.arrs bank)[0]? = some n) (hp : 0 < n) (hwidth : width n < B) :
    ∃ τ, Run B (anchorRegisters bank) σ τ 95 ∧
      τ.vars dimReg = n ∧ τ.vars loadLength = n*n ∧ τ.vars rNin = width n ∧
      τ.vars loadBase = covBase false n ∧ τ.vars inputBase = 1 ∧
      Frame (anchorRegisters bank) σ τ := by
  let x := n*n+1
  have hx : 1 ≤ x := by simp [x]
  have h₁ : x ≤ x^4 := Nat.le_self_pow (by decide) _
  have h₂ : x^2 ≤ x^4 := Nat.pow_le_pow_right hx (by decide)
  have hwidth' : width n = 16*x^4+16 := by
    unfold width
    rw [rawSlot_eq]
  have hn2 : n ≤ n*n := Nat.le_mul_self _
  have hX : x < B := by omega
  have hN : n*n < B := by dsimp [x] at hX; omega
  have hn : n < B := by omega
  have hB : 16 < B := by omega
  have hSq : (n*n)*(n*n) ≤ x^4 := by
    have hh := Nat.mul_le_mul (show n*n ≤ x by dsimp [x]; omega)
      (show n*n ≤ x by dsimp [x]; omega)
    exact (show (n*n)*(n*n) ≤ x^2 by simpa [pow_two] using hh).trans h₂
  let a := σ.setVar dimReg n
  let b := a.setVar loadLength (n*n)
  let c := b.setVar rNin (width n)
  let d := c.setVar loadBase (covBase false n)
  let τ := d.setVar inputBase 1
  have e0 : (Expr.get bank (.lit 0)).evalB B σ = some n :=
    evalB_get (evalB_lit (by omega)) hword hn
  have e1 : anchorSide.evalB B a = some n :=
    ev_var (by simp [a,vars_setVar]) hn
  have e2 : (squareE anchorSide).evalB B a = some (n*n) :=
    ev_mul e1 e1 hN
  have eLen : anchorSize.evalB B b = some (n*n) := ev_var (by simp [b,vars_setVar]) hN
  have eX : (Expr.add anchorSize (.lit 1)).evalB B b = some x :=
    ev_add eLen (evalB_lit (by omega)) hX
  have e2X : (squareE (.add anchorSize (.lit 1))).evalB B b = some (x*x) :=
    ev_mul eX eX (by rw [← pow_two]; omega)
  have e4X : (squareE (squareE (.add anchorSize (.lit 1)))).evalB B b = some (x^4) := by
    have he := ev_mul e2X e2X (show (x*x)*(x*x) < B by
      rw [show (x*x)*(x*x) = x^4 by ring]
      omega)
    simpa [squareE, show (x*x)*(x*x) = x^4 by ring] using he
  have eWidth : anchorWidthE.evalB B b = some (width n) := by
    rw [hwidth']
    exact ev_add (ev_mul (evalB_lit hB) e4X (by omega)) (evalB_lit hB) (by omega)
  have eLen' : anchorSize.evalB B c = some (n*n) :=
    ev_var (by simp [c,b,rNin,loadLength,vars_setVar]) hN
  have hBase : covBase false n = 3*((n*n)*(n*n)) := by
    unfold covBase leftStart squareStart W
    simp <;> ring
  have eBase : anchorBaseE.evalB B c = some (covBase false n) := by
    rw [hBase]
    exact ev_mul (evalB_lit (by omega)) (ev_mul eLen' eLen' (by omega)) (by omega)
  have hr : Run B (anchorRegisters bank) σ τ 95 := by
    have r := (Run.assign (x := dimReg) e0).seq ((Run.assign (x := loadLength) e2).seq
      ((Run.assign (x := rNin) eWidth).seq
        ((Run.assign (x := loadBase) eBase).seq
          (Run.assign (x := inputBase) (evalB_lit (show 1 < B by omega))))))
    exact r.mono (by norm_num [Expr.size,anchorWidthE,anchorBaseE,squareE,anchorSide,anchorSize])
  refine ⟨τ,hr,?_,?_,?_,?_,?_,Frame.of_run hr⟩ <;>
    simp [τ,d,c,b,a,inputBase,loadBase,rNin,loadLength,dimReg,
      Mathproof.Problem17ComparatorReader.rN,vars_setVar]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def anchorInputScale (F : FieldPresentation K) (L : ℕ) : ℕ :=
  (L+F.e+macroBudget F+12)^2

/-- The original matrix payload bounds all reserves used by the physical
anchor evaluator. The field is fixed, and this is a polynomial in the word
encoding's input bit length. -/
theorem anchorFits (F : FieldPresentation K) {t L : ℕ} (hL : (t+1)*(t+1)+1 ≤ L) :
    let x := anchorInputScale F L
    let N := width (t+1)
    OneAnchorLayout N (wordLimit x) t ∧
      (F.e+1+Snf N*F.e) < wordLimit x ∧
      16*(F.e+1) < wordLimit x ∧
      width (t+1) < wordLimit x ∧
      (reserve x ≥ macroBudget F ∧ reserve x ≥ dim (t+1)*dim (t+1)+2 ∧
        reserve x ≥ N+N+1 ∧ reserve x ≥ F.e+1 ∧ reserve x ≥ Nat.size t+1) := by
  let n := t+1
  let y := L+F.e+macroBudget F+12
  let x := anchorInputScale F L
  let u := reserve x
  have hy : 12 ≤ y := by dsimp [y]; omega
  have hx' : x = y^2 := rfl
  have hx : 1 ≤ x := by rw [hx']; exact Nat.one_le_pow _ _ (by omega)
  have hyx : y ≤ x := by rw [hx']; exact Nat.le_self_pow (by decide) _
  have hxu : x ≤ u := by
    have hm : x ≤ x^5 := Nat.le_self_pow (by decide) _
    have hU : x^5 ≤ u := by unfold u reserve; omega
    exact hm.trans hU
  have hn2 : n*n+1 ≤ y := by dsimp [n,y]; omega
  have hn : n+1 ≤ x := by
    have h := Nat.le_mul_self n
    omega
  have h4 : n^4 ≤ x := by
    rw [hx',show n^4=(n*n)^2 by ring]
    exact Nat.pow_le_pow_left (by omega) _
  have he : F.e+1 ≤ x := by dsimp [y] at hyx; omega
  have hM : macroBudget F ≤ u := by dsimp [y] at hyx; omega
  have hD : dim n ≤ x := (dim_le n).trans (by rw [hx']; exact Nat.pow_le_pow_left hn2 _)
  have hD2 : dim n * dim n ≤ x^2 := by simpa [pow_two] using Nat.mul_le_mul hD hD
  have hpx : x^2 ≤ x^5 := Nat.pow_le_pow_right hx (by decide)
  have hUp : 1000*x^2 ≤ u := by
    exact (Nat.mul_le_mul_left _ hpx).trans
      (Nat.mul_le_mul_right _ (by decide : 1000 ≤ 10000000))
  have hWidth : width n ≤ 32*x^2 := by
    have hp := Nat.pow_le_pow_left hn2 4
    rw [show y^4=x^2 by rw [hx',← pow_mul]] at hp
    have h1 : 1 ≤ x^2 := Nat.one_le_pow _ _ hx
    unfold width
    rw [rawSlot_eq]
    omega
  have hNX : width n+width n+1 ≤ u := by
    have h1 : 1 ≤ x^2 := Nat.one_le_pow _ _ hx
    omega
  have hDX : dim n * dim n + 2 ≤ u := by
    have h1 : 1 ≤ x^2 := Nat.one_le_pow _ _ hx
    omega
  obtain ⟨hFit,hExt⟩ := fitted hx hxu he hn h4 hNX
    (by simpa [pow_two] using hDX)
  have hnSize : Nat.size t ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
  have hH := hFit.upper
  have hW := hFit.address_fit
  have hsub : n-1 = t := by simp [n]
  rw [hsub] at hH hW
  have hMlen := hFit.mem
  have hScr : 16*(F.e+1) < wordLimit x := by
    have hh := hExt canonical.scratch
    simpa [Mathproof.Problem17RecognizerWorkspace.extents,
      show canonical.scratch ≠ Mathproof.Problem17RecognizerPrefix.src by decide,
      show canonical.scratch ≠ canonical.mem by decide] using hh
  have hWidth' : width n < wordLimit x := by
    have hh := hFit.bank
    have hsn : width n ≤ Snf (width n) := by
      unfold Snf Mathproof.P15FactorIMP20261007.wkf Mathproof.P15FactorIMP20261007.osf
        Mathproof.P15FactorIMP20261007.L0f
      omega
    omega
  have hWord : Snf (width n)+10 < wordLimit x := by have hFit := hFit.bank; omega
  have htSize : Nat.size t+1 ≤ u := by
    have ht : Nat.size t+1 ≤ n := Nat.succ_le_succ hnSize
    exact ht.trans ((Nat.le_succ n).trans (hn.trans hxu))
  exact ⟨⟨hFit.lower,hH,hWord,hW,hFit.budget,hFit.degree,hFit.width_min⟩,
    hMlen,hScr,hWidth',hM,hDX,hNX,he.trans hxu,htSize⟩

#print axioms anchorRegisters_run
#print axioms anchorFits
end EvenTI.P13Spectral
