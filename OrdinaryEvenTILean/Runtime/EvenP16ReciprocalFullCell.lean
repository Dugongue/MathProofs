import EvenP16ReciprocalAnchorGrid
import EvenP16InvertCutBank
import EvenP16AnchorUnits
import EvenP16AnchorCosts

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P15Execution EvenTI.P12ComparePrep EvenTI.P12Compare
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)
open scoped Matrix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def runReciprocalAnchor (D : FieldEncoding K) (F : FieldPresentation K) (mirror : Bool) : Com :=
  .seq (invertLiveMatrix (Fintype.card K)) (.seq (initializeAnchorUnits D F) (reciprocalAnchorGrid F mirror))

noncomputable def runReciprocalAnchorCost (F : FieldPresentation K) (mirror : Bool) (n a : ℕ) : ℕ :=
  (47+loadedInverseCost (Fintype.card K) F.e (n*a)) +
    (2*(4+installEncodedDigitCost F)+(crossGridCost F mirror n a+squareTraceCost F n))

/-- One complete reciprocal anchor from an installed nonsingular cut.
The inverse and the constant units are produced by executed commands. -/
theorem runReciprocalAnchor_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n B S src inv cross square o tt uu z one : ℕ} {s : Env}
    (T : Tensor K ((l+1)+(l+1)) n) (mode : HigherModes l) (hn : 0 < n)
    (hV : ValidMemory F B s) (hS : Slots F canonical qN.WS S B s)
    (hLoad : cutSlotMatrix F s l n src=flatten T) (hUnit : IsUnit (flatten T))
    (hMB : s.vars canonical.modBase+F.e ≤ s.vars qN.WS)
    (hWord : Fintype.card K^((n*n^l)*(n*n^l)+n*n^l+2) < B) (hB : 4 < B) (hQ : Fintype.card K ≤ B)
    (hN : n+1 < B) (hNN : n*n+1 < B) (hA : (n^l)*(n^l)+1 < B)
    (hApart : src+(n*n^l)*(n*n^l) ≤ inv) (hInvFit : inv+4*((n*n^l)*(n*n^l))+3 ≤ S)
    (hInvSep : inv+(n*n^l)*(n*n^l) ≤ cross)
    (hCross : cross+(n*n)*(n*n) ≤ square) (hSquare : square+(n*n)*(n*n) ≤ S) (hOut : o+n*n ≤ square)
    (hT : tt < src ∧ tt < o) (hU : uu < src ∧ uu < o) (hTU : tt≠uu)
    (hZ : z < src ∧ z < o ∧ z≠tt ∧ z≠uu) (hOne : one < src ∧ one < o ∧ one≠tt ∧ one≠uu) (hne : z≠one)
    (hI0 : s.vars inverseSizeWord=n*n^l) (hI1 : s.vars inverseInputWord=src) (hI2 : s.vars inverseOutputWord=inv)
    (hR : s.vars gRows=n*n) (hC : s.vars gCols=n*n) (hL : s.vars dL=(n^l)*(n^l))
    (hO : s.vars gOut=cross) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu) (hZR : s.vars dZ=z)
    (hNr : s.vars crossN=n) (hAr : s.vars crossA=n^l) (hStride : s.vars crossStride=n^(l-mode.2.val))
    (hSrc : s.vars crossSource=src) (hInv : s.vars crossInverse=inv)
    (hSide : s.vars anchorSideWord=n) (hCrossW : s.vars anchorCrossWord=cross)
    (hSquareW : s.vars anchorSquareWord=square) (hTraceW : s.vars anchorTraceWord=o)
    (hOneW : s.vars anchorUnitWord=one) :
    ∃ t, Run B (runReciprocalAnchor D F mode.1) s t (runReciprocalAnchorCost F mode.1 n (n^l)) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (o+(i.val*n+j.val)) =
        rawReciprocalAnchor T (flatten T)⁻¹ mode i j) := by
  obtain ⟨u,ru,hUinv,hUcut,_,hSu,hFu⟩ := invertCutBank_run F hn hB hApart hInvFit hV hS hI0 hI1 hI2 hMB hWord
    (by rwa [hLoad])
  have hWrite : scalarWrites (invertLiveMatrix (Fintype.card K)) = scalarWrites (invertLiveMatrix 0) := rfl
  have huReg (r : String) (h : r ∉ scalarWrites (invertLiveMatrix 0)) : u.vars r=s.vars r :=
    hFu.vars r (by rwa [hWrite])
  obtain ⟨v,rv,hSv,hZero,hUnit',hKeep,hVreg,_,_⟩ := initializeAnchorUnits_run D F hSu hQ
    (by omega : z < S) (by omega : one < S) hne
    ((huReg dZ (by decide)).trans hZR) ((huReg anchorUnitWord (by decide)).trans hOneW)
  have hf {r : String} {a : ℕ} (ha : s.vars r=a) (h : r ∉ scalarWrites (invertLiveMatrix 0))
      (h₁ : r≠inputLabel) (h₂ : r≠destination) (h₃ : r≠rCv) (h₄ : r≠rTd) : v.vars r=a :=
    (hVreg r h₁ h₂ h₃ h₄).trans ((huReg r h).trans ha)
  have dischargeLower (base : ℕ) (hb : src ≤ base) (x y : Coord (l+1) n) :
      val F canonical qN.WS v
        (base+((inputCoordOrder n (l+1) x).val*(n*n^l)+(inputCoordOrder n (l+1) y).val)) =
      cutSlotMatrix F u l n base x y := by
    change val F canonical qN.WS v _ = val F canonical qN.WS u _
    exact hKeep _ (by omega) (by omega)
  have hVload : InstalledCutMatrix F v l n src (flatten T) := by
    intro x y
    exact (dischargeLower src (Nat.le_refl _) x y).trans
      (congrFun (congrFun (hUcut.trans hLoad) x) y)
  have hVinv : InstalledCutMatrix F v l n inv (flatten T)⁻¹ := by
    intro x y
    rw [hLoad] at hUinv
    exact (dischargeLower inv (by omega) x y).trans (congrFun (congrFun hUinv x) y)
  obtain ⟨t,rt,hSt,hValue,_,_⟩ := reciprocalAnchorGrid_run F T (flatten T)⁻¹ mode hn hSv hN hNN hA
    (by omega) hInvSep hCross hSquare hOut
    ⟨hT.1,by omega,hT.2⟩ ⟨hU.1,by omega,hU.2⟩ hTU
    ⟨hZ.2.1,by omega,hZ.2.2⟩ ⟨hOne.2.1,by omega,hOne.2.2⟩
    (hf hR (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hC (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hL (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hO (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hTR (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hUR (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hZR (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hNr (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hAr (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hStride (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hSrc (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hInv (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hSide (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hCrossW (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hSquareW (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hTraceW (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf hOneW (by decide) (by decide) (by decide) (by decide) (by decide))
    hZero hUnit' hVload hVinv
  exact ⟨t,ru.seq (rv.seq rt),hSt,hValue⟩

open Polynomial Lax51.BinaryWordEncoding in
/-- One polynomial in the original pair bits bounds every retained mode's
paid inverse, crossed product, square and trace. -/
theorem runReciprocalAnchor_originalBitBudget (D : FieldEncoding K) (F : FieldPresentation K) (mirror : Bool) :
    ∃ p : Polynomial ℕ, ∀ {l n : ℕ} (T S : Tensor K ((l+1)+(l+1)) n), 2 ≤ n →
      runReciprocalAnchorCost F mirror n (n^l) ≤ p.eval (bitSize (comparisonInput D T S)) := by
  obtain ⟨p,hp⟩ := anchorGrid_originalBitBudget D F mirror
  refine ⟨C 47+inverseCostPolynomial (Fintype.card K) F.e+C (2*(4+installEncodedDigitCost F))+p,?_⟩
  intro l n T S hn
  have h := cutInput_side_bounds D T S (by omega : 1 ≤ l+1) hn
  have hDim : n*n^l ≤ bitSize (comparisonInput D T S) := by rw [←pow_succ']; exact h.2.1
  have hi := loadedInverseCost_le_bits (Fintype.card K) F.e _ _ hDim
  have hgrid := hp T S hn
  simp only [runReciprocalAnchorCost,eval_add,eval_C]
  omega

#print axioms runReciprocalAnchor_originalBitBudget
#print axioms runReciprocalAnchor_run
end EvenTI.P16Execution