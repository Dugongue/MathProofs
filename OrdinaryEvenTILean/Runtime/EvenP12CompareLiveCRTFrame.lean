import EvenP12CompareLiveCRTMachine

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithMachine20261007 (smithIMP smithIMP_run)

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

/-- A bounded execution of the coordinate command preserves canonical Smith
words, array lengths and the original dimension and modulus registers. -/
theorem smithRecoverAndCommit_state {M m n W K : ℕ} [NeZero M] {σ τ : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+4 < W)
    (hLen : (m+1)*n+(m+1)*(m+1)+n ≤ (σ.arrs matrixR).length)
    (hCanon : Canonical M (σ.arrs matrixR))
    (hM : σ.vars modR = M) (hRows : σ.vars rowsR = m+1) (hCols : σ.vars inputColsR = n)
    (hB : ∀ r : Fin (m+1), ∀ j : Fin n,
      decode M (σ.arrs matrixR) (r.val*n+j.val) = appendCoordinate A i r j)
    (hRun : Run W smithRecoverAndCommit σ τ K) :
    Canonical M (τ.arrs matrixR) ∧ (τ.arrs matrixR).length = (σ.arrs matrixR).length ∧
      τ.vars rowsR = m+1 ∧ τ.vars inputColsR = n ∧ τ.vars modR = M := by
  have hx : (2*M)*M ≤ (4*M)*M := Nat.mul_le_mul_right M (by omega)
  obtain ⟨ρ,_,hR,_,hCan,_,_,_,_,_,_⟩ :=
    smithIMP_run (appendCoordinate A i) (by omega : 2*M*M+M+3 < W)
      hL hLen hCanon hM hRows hCols hB
  have hf := Frame.of_run hRun
  refine ⟨?_,hf.len _,(hf.vars _ (by decide)).trans hRows,
    (hf.vars _ (by decide)).trans hCols,(hf.vars _ (by decide)).trans hM⟩
  obtain ⟨_,_,hr⟩ := hR
  obtain ⟨k,_,hb⟩ := hRun
  change BigStepB W (.seq smithIMP (.seq populateSmithCRT recoverAndCommitCoordinate)) σ τ k at hb
  cases hb with
  | seq ha hb =>
    have he := (ha.bigStep.unique hr.bigStep).1
    have hS := (Frame.of_run (Run.of_bigStepB hb)).arrs matrixR (by decide)
    rw [hS,he]
    exact hCan

#print axioms smithRecoverAndCommit_state

end EvenTI.P12Compare
