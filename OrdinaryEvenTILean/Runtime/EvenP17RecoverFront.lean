import EvenP17RecoverWindows
import EvenP15ScalarStorage
import EvenP12ComparePrepField
import EvenP14CutRawSetup

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace EvenTI.P17Recover

open EvenTI.Contract EvenTI.Action EvenTI.TrialProducer EvenTI.P10Scan EvenTI.P12ComparePrep
open EvenTI.P15Execution EvenTI.P15Scalar EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Lax51.BinaryWordEncoding Polynomial
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical arrayWrites)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def recoveryExtent (F : FieldPresentation K) (S length : ℕ) (other : String → ℕ) : String → ℕ :=
  canonicalInitExt F S (fun a => if a="data" then length+1 else other a)

noncomputable def recoveryFront (F : FieldPresentation K) : Com :=
  .seq requestLoadProgram (.seq requestHeaderProgram (.seq openPairedTrialSections (fieldInitProgram F)))

structure RecoveryFrontReady (F : FieldPresentation K) (B S d n lk rk : ℕ)
    (raw la lf ra rf : List ℕ) (s : Env) : Prop where
  ndim : s.vars requestWidth=n
  order : s.vars requestOrder=d
  ltag : s.vars requestLeftTag=lk
  rtag : s.vars requestRightTag=rk
  field : Slots F canonical qN.WS S B s

/-- The native constructor starts directly from the binary word loader's
length prefix and literal raw pair followed by the two trial records. It
keeps all original words, opens both trials, and initializes the field ABI. -/
theorem recoveryFront_run (F : FieldPresentation K) (S d n lk rk : ℕ)
    (raw la lf ra rf : List ℕ) (other : String → ℕ) {B : ℕ} :
    let w := d::n::raw
    let left := lk::pairW la lf
    let right := rk::pairW ra rf
    let z := pairW w (pairW left right)
    4 < B → z.length < B → (∀ x ∈ z, x < B) →
    F.e+1+S*F.e < B → 16*(F.e+1) < B → (F.p+1)^2 < B → (F.p+1)^(F.e+1) < B → S < B →
    ∃ t, Run B (recoveryFront F) (initEnv (recoveryExtent F S z.length other) (z.length::z)) t
        (13*z.length+215+3*F.e) ∧
      RecoveryFrontReady F B S d n lk rk raw la lf ra rf t ∧
      OperandSections z false la lf t ∧ OperandSections z true ra rf t ∧
      t.arrs "data"=sentinelWords z ∧
      slice z (t.vars requestRawStart) (t.vars requestRawEnd)=w ∧
      t.inp=[] ∧ t.out=[] := by
  dsimp only
  intro hB hZ hWords hMemFit hScratchFit hSquare hPower hSlots
  let w := d::n::raw
  let left := lk::pairW la lf
  let right := rk::pairW ra rf
  let z := pairW w (pairW left right)
  let ext := recoveryExtent F S z.length other
  have hext : ext "data"=z.length+1 := by simp [ext,recoveryExtent,canonicalInitExt,canonical]
  obtain ⟨u,ru,hU,huIn,huOut,huMem⟩ :=
    requestLoadWithStorage_run w left right ext hB hZ hWords hext
  obtain ⟨v,rv,hV,hd,hn,hkL,hkR,hvIn,hvOut⟩ :=
    requestHeaderProgram_run raw (pairW la lf) (pairW ra rf) hU (by omega) hZ hWords
  obtain ⟨r,rr,hLeft,hRight,hrArr,hrIn,hrOut,hrStart,hrEnd⟩ :=
    openPairedTrialSections_run w la lf ra rf lk rk hV (by omega) hZ hWords
  have hvFrame := Frame.of_run rv
  have hWrites : arrayWrites requestHeaderProgram = ∅ := by decide
  have hrMem : r.arrs canonical.mem=List.replicate (F.e+1+S*F.e) 0 := by
    rw [hrArr,hvFrame.arrs _ (by simp [hWrites]),huMem _ (by decide)]
    simp [ext,recoveryExtent,canonicalInitExt]
  have hrScratch : (r.arrs canonical.scratch).length=16*(F.e+1) := by
    rw [hrArr,hvFrame.arrs _ (by simp [hWrites]),huMem _ (by decide)]
    simp [ext,recoveryExtent,canonicalInitExt,canonical]
  obtain ⟨rt,htSlots,_,_,htArr,htVar,htIn,htOut⟩ :=
    fieldInitProgram_run F S B r hrMem hrScratch hMemFit hScratchFit hSquare hPower hSlots
  let t := fieldInitState F r
  have fr := Frame.of_run rr
  have heq {z₀ : String} (h : z₀ ≠ canonical.e) (h' : z₀ ≠ canonical.p)
      (h₃ : z₀ ≠ canonical.modBase) (h₄ : z₀ ≠ canonical.exp) (h₅ : z₀ ≠ qN.WS) :
      t.vars z₀ = r.vars z₀ := htVar _ h h' h₃ h₄ h₅
  have leftStable : OperandSections z false la lf t := by
    have ha := heq (z₀:=anchorListStart false) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hb := heq (z₀:=formStart false) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hc := heq (z₀:=formEnd false) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨by rw [ha,hb,hc]; exact hLeft.ordered,by rw [ha,hb]; exact hLeft.anchors,
      by rw [hb,hc]; exact hLeft.forms⟩
  have rightStable : OperandSections z true ra rf t := by
    have ha := heq (z₀:=anchorListStart true) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hb := heq (z₀:=formStart true) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hc := heq (z₀:=formEnd true) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨by rw [ha,hb,hc]; exact hRight.ordered,by rw [ha,hb]; exact hRight.anchors,
      by rw [hb,hc]; exact hRight.forms⟩
  have hReady : RecoveryFrontReady F B S d n lk rk raw la lf ra rf t := by
    refine ⟨?_,?_,?_,?_,htSlots⟩
    · exact (heq (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fr.vars _ (by decide)).trans hn)
    · exact (heq (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fr.vars _ (by decide)).trans hd)
    · exact (heq (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fr.vars _ (by decide)).trans hkL)
    · exact (heq (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fr.vars _ (by decide)).trans hkR)
  have hRun : Run B (recoveryFront F) (initEnv ext (z.length::z)) t (13*z.length+215+3*F.e) := by
    refine (ru.seq (rv.seq (rr.seq rt))).mono ?_
    change (13*z.length+90)+(15+(97+(3*F.e+13))) ≤ 13*z.length+215+3*F.e
    omega
  refine ⟨t,hRun,hReady,leftStable,rightStable,(htArr _ (by decide)).trans
    ((congrFun hrArr "data").trans hV.stored),?_,
    htIn.trans (hrIn.trans (hvIn.trans huIn)),htOut.trans (hrOut.trans (hvOut.trans huOut))⟩
  rw [(heq (z₀:=requestRawStart) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrStart,
    (heq (z₀:=requestRawEnd) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrEnd]
  exact hV.raw

noncomputable def recoveryRequestBitPoly (q : ℕ) : Polynomial ℕ :=
  C 2+2*X+3*trialPayloadPolynomial q

/-- Serialized trials increase the original dense input only polynomially,
including all length prefixes on both nested pairs. -/
theorem recoveryRequestBitPoly_bound (D : FieldEncoding K) {l n : ℕ}
    (T U : Tensor K ((l+1)+(l+1)) n) (P Q : PreparedTrial K l n) (hn : 2 ≤ n) :
    let w := comparisonInput D T U
    bitSize (pairW w (pairW (preparedTrialWords D P) (preparedTrialWords D Q))) ≤
      (recoveryRequestBitPoly (Fintype.card K)).eval (bitSize w) := by
  let w := comparisonInput D T U
  let L := bitSize w
  let q := Fintype.card K
  have hGrid : n^((l+1)+(l+1)) ≤ L := by
    have hLen : w.length=2+n^((l+1)+(l+1))+n^((l+1)+(l+1)) := by
      simp [w,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
    have hW := Lax51Proofs.Encoding.length_le_bitSize w
    change _ ≤ bitSize w
    omega
  have hd : (l+1)+(l+1) ≤ L :=
    ((Nat.lt_two_pow_self (n:=(l+1)+(l+1))).le.trans (Nat.pow_le_pow_left hn _)).trans hGrid
  have hP := preparedTrialWords_bits D P hn L hd hGrid
  have hQ := preparedTrialWords_bits D Q hn L hd hGrid
  have h0 := bitSize_pairW_le w (pairW (preparedTrialWords D P) (preparedTrialWords D Q))
  have h1 := bitSize_pairW_le (preparedTrialWords D P) (preparedTrialWords D Q)
  change bitSize (pairW w _) ≤ (recoveryRequestBitPoly q).eval L
  simp [recoveryRequestBitPoly,eval_add,eval_mul,eval_X,eval_trialPayloadPolynomial]
  dsimp only [q]
  omega

#print axioms recoveryFront_run
#print axioms recoveryRequestBitPoly_bound

end EvenTI.P17Recover
