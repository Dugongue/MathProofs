import EvenP12CompareLiveCRTTable
import Mathproof.Meta.P15GSSSmithMachine20261007
import Mathproof.Meta.P15GDHSmithBudget20261007

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithMachine20261007 (smithIMP smithCost smithIMP_run)

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

def smithRecoverAndCommit : Com := .seq smithIMP (.seq populateSmithCRT recoverAndCommitCoordinate)
def smithRecoverAndCommitCost (M m n : ℕ) : ℕ :=
  smithCost M (m+1) n + populateSmithCRTCost M m + crtScanCost M (m+1)+20

/-- Run physical Smith, extract the induced unary rows from its two output
banks, compute the least extending residue, and store that coordinate. The
installed source bank contains the logical trial matrix with one coordinate row. -/
theorem smithRecoverAndCommit_run {M m n W : ℕ} [NeZero M] {σ : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+4 < W)
    (hLen : (m+1)*n+(m+1)*(m+1)+n ≤ (σ.arrs matrixR).length)
    (hCanon : Canonical M (σ.arrs matrixR))
    (hM : σ.vars modR = M) (hRows : σ.vars rowsR = m+1) (hCols : σ.vars inputColsR = n)
    (hB : ∀ r : Fin (m+1), ∀ j : Fin n,
      decode M (σ.arrs matrixR) (r.val*n+j.val) = appendCoordinate A i r j)
    (hRhs : σ.arrs crtRhsBank = List.ofFn (fun j => (b j).val))
    (hLen₁ : (σ.arrs coefficientBank).length = m+1)
    (hLen₂ : (σ.arrs targetBank).length = m+1)
    (hLen₃ : (σ.arrs modulusBank).length = m+1)
    (hSlot : σ.vars coordinateSlot = i.val)
    (hDest : i.val < (σ.arrs coordinateBank).length) :
    ∃ τ, Run W smithRecoverAndCommit σ τ (smithRecoverAndCommitCost M m n) ∧
      Frame smithRecoverAndCommit σ τ ∧
      (match recoverCoordinate A b i with
       | some z => τ.vars crtActive = 1 ∧
           τ.arrs coordinateBank = (σ.arrs coordinateBank).set i.val z.val
       | none => τ.vars crtActive = 0 ∧ τ.arrs coordinateBank = σ.arrs coordinateBank) := by
  have hMp : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMul : (2*M)*M ≤ (4*M)*M := Nat.mul_le_mul_right M (by omega)
  obtain ⟨ρ,st,r0,hMatrixLen,hCanonical,hBank,hValid,hClr,hMono,_,hf⟩ :=
    smithIMP_run (appendCoordinate A i) (by omega : 2*M*M+M+3 < W)
      hL hLen hCanon hM hRows hCols hB
  have hψ : CRTSmithInput st b ρ := ⟨(hf.vars _ (by decide)).trans hRows,
    (hf.vars _ (by decide)).trans hCols,(hf.vars _ (by decide)).trans hM,
    by rw [hMatrixLen]; omega,hCanonical,hBank,(hf.arrs _ (by decide)).trans hRhs⟩
  obtain ⟨η,r1,hIRC,_,hf1⟩ := populateSmithCRT_run st b (by omega : (m+1)+n+(m+1)*n+(m+1)*(m+1)+2 < W)
    hW hψ hClr ((congrArg List.length (hf.arrs _ (by decide))).trans hLen₁)
    ((congrArg List.length (hf.arrs _ (by decide))).trans hLen₂)
    ((congrArg List.length (hf.arrs _ (by decide))).trans hLen₃)
  have hF01 := Frame.of_run (r0.seq r1)
  have hSlotη : η.vars coordinateSlot = i.val := (hF01.vars _ (by decide)).trans hSlot
  have hDestη : η.arrs coordinateBank = σ.arrs coordinateBank := hF01.arrs _ (by decide)
  let es := coordinateEquations st.B st.U b
  have he : es.length = m+1 := coordinateEquations_length st.B st.U b
  have hData := coordinateEquations_words st b
  obtain ⟨τ,r2,_,hOutput⟩ :=
    recoverAndCommitCoordinate_run es hMp hW (by rw [he]; omega) hIRC hSlotη
      (i.isLt.trans (by omega)) (by rwa [hDestη]) hData
  obtain ⟨hU₁,hU₂,hV₁,hV₂,hEq,hD⟩ := ZDiag.zmodDiag_spec (appendCoordinate A i)
  have hv : valueFromBanks st.B st.U b = recoverCoordinate A b i :=
    valueFromBanks_eq A b i hValid hMono ⟨hEq,hU₁,hU₂,hV₁,hV₂⟩ hD
  have run : Run W smithRecoverAndCommit σ τ (smithRecoverAndCommitCost M m n) :=
    (r0.seq (r1.seq r2)).mono (by unfold smithRecoverAndCommitCost; rw [he]; omega)
  refine ⟨τ,run,Frame.of_run run,?_⟩
  rw [← hv]
  change (match (solveUnaryList es).map (fun z => (z.1 : ZMod M)) with
    | some z => τ.vars crtActive = 1 ∧ τ.arrs coordinateBank = (σ.arrs coordinateBank).set i.val z.val
    | none => τ.vars crtActive = 0 ∧ τ.arrs coordinateBank = σ.arrs coordinateBank)
  cases hs : solveUnaryList es with
  | none => simpa [hs,hDestη] using hOutput
  | some w =>
    have hw := solveUnaryList_bounds es hMp
      (fun e he' => by
        obtain ⟨j,hj⟩ := List.mem_iff_get.mp he'
        rw [←hj]
        exact (hData j).2.2.2) hs
    have hb : w.1 < M := hw.2.2.trans_le (Nat.le_of_dvd hMp hw.2.1)
    have hr : ((w.1 : ℕ) : ZMod M).val = w.1 := by simp [ZMod.val_natCast,Nat.mod_eq_of_lt hb]

    simpa [hs,hDestη,hr] using hOutput

/-- The complete coordinate run has a uniform quartic word bound in the
Smith dimensions and the binary length of the modulus. -/
theorem smithRecoverAndCommitCost_le (M m n : ℕ) :
    smithRecoverAndCommitCost M m n ≤ 52000*(Nat.size M+m+n+2)^4 := by
  let X := Nat.size M+m+n+2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hm : m+1 ≤ X := by dsimp [X]; omega
  have hM : Nat.size M ≤ X := by dsimp [X]; omega
  have h₂ : X^2 ≤ X^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₄ : 1 ≤ X^4 := one_le_pow₀ hX
  have hS := Mathproof.P15GDHSmithBudget20261007.diagonal_cost M (m+1) n
  rw [show Nat.size M+(m+1)+n+1 = X by dsimp [X]; omega] at hS
  have hSS := Nat.mul_le_mul hm hm
  rw [← pow_two X] at hSS
  have hT : loadSmithRowCost M m+28 ≤ 250*X := by unfold loadSmithRowCost; omega
  have hT' := Nat.mul_le_mul hT hm
  rw [show 250*X*X = 250*X^2 by ring] at hT'
  have hC : crtStepCost M+4 ≤ 864*X := by
    unfold crtStepCost intersectRowCost
    omega
  have hC' := Nat.mul_le_mul hC hm
  rw [show 864*X*X = 864*X^2 by ring] at hC'
  change smithRecoverAndCommitCost M m n ≤ 52000*X^4
  unfold smithRecoverAndCommitCost smithCost populateSmithCRTCost crtScanCost
  omega

#print axioms smithRecoverAndCommit_run
#print axioms smithRecoverAndCommitCost_le

end EvenTI.P12Compare
