import EvenP18RawInit
import EvenP18RawCut
import EvenP18RawLayout
import EvenP18ReciprocalTrial
import Mathproof.Meta.Problem18PairBoundaryOddProducts20261004

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 2750000

namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Execution EvenTI.P16Execution EvenTI.P17Execution EvenTI.P10Scan
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P17Trial
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (install installed_arrays installed_scalar installed_slots)
open Mathproof.Problem18PairBoundaryPrefix20261004 (zeroGap)
open Mathproof.Problem18PairBoundaryOddProducts20261004 (gapFix_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawReciprocalTrialProgram (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) : Com :=
  .seq (comparisonInitProgram F) (.seq (reciprocalRawSetup target)
    (.seq (encodedBankLoad D F rawPairIO.array contiguousAddress)
      (.seq zeroGap (produceReciprocalTrial D F))))

noncomputable def rawReciprocalTrialCost (F : FieldPresentation K)
    (target : Bool) (l n len : ℕ) : ℕ :=
  (40*(len+1)+3*F.e+25)+(reciprocalRawSetupCost target+
    (encodedBankLoadCost F contiguousAddress (n^((l+1)+(l+1)))+
      (3+produceReciprocalTrialCost F l n)))

/-- Exact output from untouched dense binary-decoded input words on the
nonsingular branch. The given word and slot bounds can be chosen from the
input size. The command initializes, loads, inverts, and serializes. -/
theorem rawReciprocalTrialProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n B : ℕ} (T U : Tensor K ((l+1)+(l+1)) n) (target : Bool)
    (other : String → ℕ) (hl : 1 ≤ l) (hn : 2 ≤ n)
    (hUnit : IsUnit (flatten (if target then U else T)))
    (hLen : (comparisonInput D T U).length < B)
    (hWords : ∀ x ∈ comparisonInput D T U, x < B)
    (hMemFit : F.e+1+reciprocalRawSlots (n*n^l)*F.e < B)
    (hScratchFit : 16*(F.e+1) < B)
    (hSquare : (F.p+1)^2 < B) (hPower : (F.p+1)^(F.e+1) < B)
    (hSlotsFit : reciprocalRawSlots (n*n^l) < B)
    (hQ : Fintype.card K ≤ B) (hB : 4 < B)
    (hA : (n^l)*(n^l)+1 < B)
    (hWord : Fintype.card K^((n*n^l)*(n*n^l)+n*n^l+2) < B)
    (hFrame : 1+((l+1)+(l+1))*(n*n+2)<B) :
    let m := n*n^l
    let w := comparisonInput D T U
    let V := if target then U else T
    ∃ t, Run B (rawReciprocalTrialProgram D F target)
      (initEnv (comparisonInitExt F (reciprocalRawSlots m) w.length other) (w.length::w)) t
      (rawReciprocalTrialCost F target l n w.length) ∧
      t.inp=[] ∧
      t.out=preparedTrialWords D (.reciprocal (rawReciprocalAnchor V (flatten V)⁻¹)) := by
  dsimp only
  let m := n*n^l
  let d := (l+1)+(l+1)
  let w := comparisonInput D T U
  let V := if target then U else T
  let L := reciprocalRawOffsets m
  have hmPow : m = n^(l+1) := (pow_succ' n l).symm
  have hArea : m*m = n^d := by rw [hmPow]; exact (pow_add n (l+1) (l+1)).symm
  have hnPos : 0 < n := by omega
  have hmPos : 0 < m := Nat.mul_pos hnPos (pow_pos hnPos _)
  have hnM : n*n ≤ m := by
    rw [hmPow,←pow_two]
    exact Nat.pow_le_pow_right hnPos (by omega)
  have hSize : w.length=2+m*m+m*m := by
    rw [hArea]
    simp [w,d,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
  have hLenW : w.length < B := hLen
  have hAreaLt : m*m < B := by omega
  have hAreaNat : n^d < B := by rwa [←hArea]
  have hSlotsLt : 7+8*(m*m) < B := hSlotsFit
  have hWidth : n ≤ m := (Nat.le_mul_self n).trans hnM
  have hmB : m < B := (Nat.le_mul_self m).trans_lt hAreaLt
  have hnB : n < B := hWidth.trans_lt hmB
  have hdB : d < B := by
    have : d ≤ n^d := (Nat.lt_two_pow_self (n:=d)).le.trans (Nat.pow_le_pow_left hn _)
    omega
  have hFit := reciprocalRawOffsets_fit hnM
  have hValid := decodePair_encode D T U (by omega) (show Even d from ⟨l+1,rfl⟩) hn
  obtain ⟨s,r₀,hShape,hSlots,hWS,_,hin,hout,hMod,hMem⟩ :=
    comparisonInitLayout_run D F w hValid (reciprocalRawSlots m) B other hLen hWords
      hMemFit hScratchFit hSquare hPower hSlotsFit
  have hHalf : d/2=l+1 := by dsimp [d]; omega
  have hSide : s.vars shapePower.out=m := by simpa [hHalf,hmPow,d] using hShape.side
  let bs := reciprocalRawRegisters target m n d
  let u := install bs s
  have r₁ : Run B (reciprocalRawSetup target) s u (reciprocalRawSetupCost target) :=
    reciprocalRawSetup_run target hSide hShape.dimension hShape.order hmPos hmB hnB
      (reciprocalRawBindings_fit target hSlotsFit hdB hnM hnB)
  have hFrameSetup := installed_arrays bs s
  have safe : ∀ x ∈ (reciprocalRawBindings target).map Prod.fst,
      canonical.e≠x ∧ canonical.p≠x ∧ canonical.modBase≠x ∧ canonical.exp≠x ∧ qN.WS≠x := by
    cases target <;> decide
  have hFresh : ∀ p ∈ bs, canonical.e≠p.1 ∧ canonical.p≠p.1 ∧ canonical.modBase≠p.1 ∧
      canonical.exp≠p.1 ∧ qN.WS≠p.1 := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact safe a.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hUslots := installed_slots F bs s hSlots hFresh
  have hQReg {r : String} {a : RawBindWord} (hr : (r,a) ∈ reciprocalRawBindings target) :
      u.vars r=a.value m n d := reciprocalRawRegisters_at target m n d s hr
  have hLoadBase : u.vars loadBase=L.src := hQReg (a:=.address (.litSucc 3))
    (by simp [reciprocalRawBindings])
  have hLoadLen : u.vars loadLength=n^d :=
    (hQReg (a:=.address cutArea) (by simp [reciprocalRawBindings])).trans hArea
  have hInput : u.vars inputBase=tensorOffset (n^d) target := by
    have ha := hQReg (r:=inputBase) (a:=.address (inputOffset target)) (by simp [reciprocalRawBindings])
    rw [ha,←hArea]
    cases target <;> rfl
  have hOffset : tensorOffset (n^d) target+n^d < B := by
    rw [←hArea]
    cases target <;> simp [tensorOffset] <;> omega
  have hSrcFit : L.src+n^d ≤ reciprocalRawSlots m := by
    rw [←hArea]
    simp [L,reciprocalRawOffsets,reciprocalRawSlots]
    omega
  obtain ⟨v,r₂,hVs,hCut,hKeep,_,hvi,hvo⟩ := loadRawCut_run D F T U target
    rawPairIO.array (by decide) (by rw [hFrameSetup.1]; exact hShape.bank)
    hUslots hQ (by omega) hOffset hLoadBase hLoadLen hInput hSrcFit
  have hWSv : v.vars qN.WS=F.e+1 := (hKeep _ (by decide)).trans
    ((installed_scalar bs s qN.WS (fun _ h => (hFresh _ h).2.2.2.2)).trans hWS)
  have hModv : v.vars canonical.modBase=0 := (hKeep _ (by decide)).trans
    ((installed_scalar bs s canonical.modBase (fun _ h => (hFresh _ h).2.2.1)).trans hMod)
  have hMemv : (v.arrs canonical.mem).length=F.e+1+reciprocalRawSlots m*F.e := by
    rw [(Frame.of_run r₂).len,hFrameSetup.1,hMem]
  obtain ⟨a,r₃,hValidMem,hAs,hVal,hVars,_,_,hai,hao⟩ := gapFix_run F hVs hWSv hModv hMemv
  have hAload : cutSlotMatrix F a l n L.src=flatten V := by
    rw [←hCut]
    ext x y
    exact hVal _
  have hR {r : String} {p : RawBindWord} (hr : (r,p) ∈ reciprocalRawBindings target)
      (h : ¬loadChanges r) : a.vars r=p.value m n d := by
    rw [hVars,hKeep _ h]
    exact hQReg hr
  have hAreg : ReciprocalInstalled l n L a := by
    refine ⟨hR (p:=.width) (by simp [reciprocalRawBindings]) (by decide), ?_,
      hR (p:=.address (.litSucc 3)) (by simp [reciprocalRawBindings]) (by decide), ?_,
      hR (p:=.width) (by simp [reciprocalRawBindings]) (by decide), ?_, ?_, ?_,
      hR (p:=.address (.litSucc 0)) (by simp [reciprocalRawBindings]) (by decide),
      hR (p:=.zero) (by simp [reciprocalRawBindings]) (by decide),
      hR (p:=.address (.litSucc 1)) (by simp [reciprocalRawBindings]) (by decide),
      hR (p:=.address (.litSucc 2)) (by simp [reciprocalRawBindings]) (by decide), ?_,
      hR (p:=.widthSquare) (by simp [reciprocalRawBindings]) (by decide),
      hR (p:=.width) (by simp [reciprocalRawBindings]) (by decide)⟩
    · exact (hR (p:=.inner) (by simp [reciprocalRawBindings]) (by decide)).trans
        (Nat.mul_div_cancel_left (n^l) hnPos)
    · simpa [L,reciprocalRawOffsets,RawBindWord.value,layoutAddr,cutArea,Address.value] using
        hR (r:=crossInverse) (p:=.address (layoutAddr 3 0)) (by simp [reciprocalRawBindings]) (by decide)
    · exact hR (p:=.address (layoutAddr 6 5)) (by simp [reciprocalRawBindings]) (by decide)
    · exact hR (p:=.address (layoutAddr 6 6)) (by simp [reciprocalRawBindings]) (by decide)
    · exact hR (p:=.address (layoutAddr 6 4)) (by simp [reciprocalRawBindings]) (by decide)
    · exact hR (p:=.address (layoutAddr 6 4)) (by simp [reciprocalRawBindings]) (by decide)
  have hi₀ : a.vars inverseSizeWord=m :=
    hR (p:=.address .side) (by simp [reciprocalRawBindings]) (by decide)
  have hi₁ : a.vars inverseInputWord=L.src :=
    hR (p:=.address (.litSucc 3)) (by simp [reciprocalRawBindings]) (by decide)
  have hi₂ : a.vars inverseOutputWord=L.inv := by
    simpa [L,reciprocalRawOffsets,RawBindWord.value,layoutAddr,cutArea,Address.value] using
      hR (r:=inverseOutputWord) (p:=.address (layoutAddr 3 0)) (by simp [reciprocalRawBindings]) (by decide)
  have hCount : a.vars reciprocalCountWord=d :=
    hR (p:=.order) (by simp [reciprocalRawBindings]) (by decide)
  have hMB : a.vars canonical.modBase+F.e ≤ a.vars qN.WS := by rw [hVars,hModv,hWSv]; omega
  have hNN : n*n+2 < B := by
    have : n*n ≤ m*m := hnM.trans (Nat.le_mul_self m)
    omega
  have hnSq := Nat.le_mul_self n
  have hP : F.p < B := by
    have he : F.p+1 ≤ (F.p+1)^2 := by simpa [pow_two] using Nat.le_mul_self (F.p+1)
    omega
  obtain ⟨t,r₄,_,hti,hto⟩ := produceReciprocalTrial_run D F V L hn hB (by omega) (by omega)
    hA (by dsimp [d] at hdB; omega) hQ hP hFit.1 hFit.2.1 hFit.2.2.1 hFit.2.2.2.1
    hFit.2.2.2.2.1 hFit.2.2.2.2.2
    (by change 2 < 4; decide) (by change 3 < 4; decide) (by change 2 ≠ 3; decide)
    (by change 0 < 4 ∧ 0 ≠ 2 ∧ 0 ≠ 3; decide)
    (by change 1 < 4 ∧ 1 ≠ 2 ∧ 1 ≠ 3; decide) (by change 0 ≠ 1; decide)
    hValidMem hAs hAload hUnit hi₀ hi₁ hi₂
    hMB hWord hAreg hCount hdB hNN hFrame
  refine ⟨t,r₀.seq (r₁.seq (r₂.seq (r₃.seq r₄))),?_,?_⟩
  · exact hti.trans (hai.trans (hvi.trans (hFrameSetup.2.1.trans hin)))
  · rw [hto,hao,hvo,hFrameSetup.2.2,hout,List.nil_append]

#print axioms rawReciprocalTrialProgram_run
end EvenTI.P18Execution




