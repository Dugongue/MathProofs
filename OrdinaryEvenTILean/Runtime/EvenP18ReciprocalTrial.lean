import EvenP17ReciprocalTrial
import EvenP16ReciprocalFullCell

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000

namespace EvenTI.P18Execution

open EvenTI.P17Execution EvenTI.P16Execution EvenTI.P17Trial EvenTI.P15Trial EvenTI.P15Execution EvenTI.P10Scan
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.P12Compare
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites noRead)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dZ)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def produceReciprocalTrial (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (invertLiveMatrix (Fintype.card K))
    (.seq (initializeAnchorUnits D F) (emitReciprocalTrial D F))

noncomputable def produceReciprocalTrialCost (F : FieldPresentation K) (l n : ℕ) : ℕ :=
  (47+loadedInverseCost (Fintype.card K) F.e (n*n^l)) +
    (2*(4+installEncodedDigitCost F) +
      (15+(12+(4+(((reciprocalVisitCost F true l n+12)*(l+1)+8)+
        ((reciprocalVisitCost F false l n+12)*(l+1)+8))))))

/-- Invert an installed nonsingular cut, produce the field units and serialize
the entire native reciprocal trial. -/
theorem produceReciprocalTrial_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n B S : ℕ} {s : Env} (T : Tensor K ((l+1)+(l+1)) n) (L : ReciprocalOffsets)
    (hn : 2 ≤ n) (hB : 4 < B) (hN : n+1 < B) (hNN : n*n+1 < B)
    (hA : (n^l)*(n^l)+1 < B) (hLim : l+1 < B) (hQ : Fintype.card K ≤ B)
    (hP : F.p < B)
    (hApart : L.src+(n*n^l)*(n*n^l) ≤ L.inv)
    (hInvFit : L.inv+4*((n*n^l)*(n*n^l))+3 ≤ S)
    (hInv : L.inv+(n*n^l)*(n*n^l) ≤ L.out)
    (hOut : L.out+n*n ≤ L.cross) (hCross : L.cross+(n*n)*(n*n) ≤ L.square)
    (hSquare : L.square+(n*n)*(n*n) ≤ S)
    (hT : L.tt < L.src) (hU : L.uu < L.src) (hTU : L.tt≠L.uu)
    (hZ : L.zero < L.src ∧ L.zero≠L.tt ∧ L.zero≠L.uu)
    (hOne : L.one < L.src ∧ L.one≠L.tt ∧ L.one≠L.uu) (hne : L.zero≠L.one)
    (hV : ValidMemory F B s) (hS : Slots F canonical qN.WS S B s)
    (hLoad : cutSlotMatrix F s l n L.src=flatten T) (hUnit : IsUnit (flatten T))
    (hI0 : s.vars inverseSizeWord=n*n^l) (hI1 : s.vars inverseInputWord=L.src)
    (hI2 : s.vars inverseOutputWord=L.inv)
    (hMB : s.vars canonical.modBase+F.e ≤ s.vars qN.WS)
    (hWord : Fintype.card K^((n*n^l)*(n*n^l)+n*n^l+2) < B)
    (hRegs : ReciprocalInstalled l n L s)
    (hCount : s.vars reciprocalCountWord=(l+1)+(l+1))
    (hCountB : (l+1)+(l+1)<B) (hPayloadB : n*n+2<B)
    (hFrameWord : 1+((l+1)+(l+1))*(n*n+2)<B) :
    ∃ t, Run B (produceReciprocalTrial D F) s t (produceReciprocalTrialCost F l n) ∧
      Slots F canonical qN.WS S B t ∧ t.inp=s.inp ∧
      t.out=s.out++preparedTrialWords D (.reciprocal (rawReciprocalAnchor T (flatten T)⁻¹)) := by
  obtain ⟨u,ru,hUinv,hUcut,_,hSu,hFu⟩ := invertCutBank_run F (by omega) hB hApart hInvFit
    hV hS hI0 hI1 hI2 hMB hWord (by rwa [hLoad])
  have hWrite : scalarWrites (invertLiveMatrix (Fintype.card K)) =
      scalarWrites (invertLiveMatrix 0) := rfl
  have huReg (r : String) (h : r ∉ scalarWrites (invertLiveMatrix 0)) : u.vars r=s.vars r :=
    hFu.vars r (by rwa [hWrite])
  have hui : u.inp=s.inp := hFu.inp (show noRead (invertLiveMatrix 0) by repeat' constructor)
  have huo : u.out=s.out := hFu.out (show (invertLiveMatrix 0).NoWrite by repeat' constructor)
  obtain ⟨v,rv,hSv,hZero,hUnit',hKeep,hVreg,hvi,hvo⟩ := initializeAnchorUnits_run D F hSu hQ
    (by omega : L.zero < S) (by omega : L.one < S) hne
    ((huReg dZ (by decide)).trans hRegs.zero)
    ((huReg anchorUnitWord (by decide)).trans hRegs.unit)
  have hNames : ∀ r ∈ reciprocalCountWord :: reciprocalPermanent,
      r ∉ scalarWrites (invertLiveMatrix 0) ∧ r≠inputLabel ∧ r≠destination ∧ r≠rCv ∧ r≠rTd := by
    decide
  have hf {r : String} {a : ℕ} (ha : s.vars r=a)
      (hr : r ∈ reciprocalCountWord :: reciprocalPermanent) : v.vars r=a := by
    obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := hNames r hr
    exact (hVreg r h₁ h₂ h₃ h₄).trans ((huReg r h₀).trans ha)
  have hVregs : ReciprocalInstalled l n L v :=
    ⟨hf hRegs.width (by decide), hf hRegs.power (by decide),
      hf hRegs.source (by decide), hf hRegs.inverse (by decide),
      hf hRegs.side (by decide), hf hRegs.crossed (by decide),
      hf hRegs.squared (by decide), hf hRegs.traced (by decide),
      hf hRegs.unit (by decide), hf hRegs.zero (by decide),
      hf hRegs.temp1 (by decide), hf hRegs.temp2 (by decide),
      hf hRegs.start (by decide), hf hRegs.length (by decide),
      hf hRegs.emitWidth (by decide)⟩
  have dischargeLower (base : ℕ) (hb : L.src ≤ base) (x y : Coord (l+1) n) :
      val F canonical qN.WS v
        (base+((inputCoordOrder n (l+1) x).val*(n*n^l)+(inputCoordOrder n (l+1) y).val)) =
      cutSlotMatrix F u l n base x y := by
    change val F canonical qN.WS v _ = val F canonical qN.WS u _
    exact hKeep _ (by omega) (by omega)
  have hVload : InstalledCutMatrix F v l n L.src (flatten T) := by
    intro x y
    exact (dischargeLower L.src (Nat.le_refl _) x y).trans
      (congrFun (congrFun (hUcut.trans hLoad) x) y)
  have hVinv : InstalledCutMatrix F v l n L.inv (flatten T)⁻¹ := by
    intro x y
    rw [hLoad] at hUinv
    exact (dischargeLower L.inv (by omega) x y).trans (congrFun (congrFun hUinv x) y)
  obtain ⟨t,rt,hSt,hti,hto⟩ := emitReciprocalTrial_run D F T (flatten T)⁻¹ L hn hN hNN hA
    hLim hQ hP (by omega) hInv hOut hCross hSquare
    ⟨hT,by omega,by omega⟩ ⟨hU,by omega,by omega⟩ hTU
    ⟨by omega,hZ.2.1,hZ.2.2⟩ ⟨by omega,hOne.2.1,hOne.2.2⟩
    hSv hVregs hZero hUnit' hVload hVinv (hf hCount (by decide)) hCountB hPayloadB hFrameWord
  exact ⟨t,ru.seq (rv.seq rt),hSt,hti.trans (hvi.trans hui),by rw [hto,hvo,huo]⟩

#print axioms produceReciprocalTrial_run
end EvenTI.P18Execution


