import EvenP12CompareRecoverLinear
import Mathproof.Meta.P15GSSSmithMachine20261007

namespace EvenTI.P12Compare

open scoped Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithArray20261007
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithMachine20261007 (smithIMP smithCost smithIMP_run)

variable {M m n : ℕ} [NeZero M]

def readSmithB (τ : Env) : Matrix (Fin (m+1)) (Fin n) (ZMod M) :=
  fun r j => decode M (τ.arrs matrixR) (r.val*n+j.val)

def readSmithU (τ : Env) : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M) :=
  fun r j => decode M (τ.arrs matrixR) ((m+1)*n+r.val*(m+1)+j.val)

/-- Run the existing two-bank Smith routine on one installed appended system.
The reference recovery value is exactly the result of reading its B and U
banks and solving the induced unary system. -/
theorem paidCoordinateSmith_run (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (i : Fin n) {W : ℕ} {σ : Env}
    (hW : 2*M*M+M+3 < W) (hLayout : (m+1)+n+(m+1)*n+(m+1)*(m+1)+4 < W)
    (hLen : (m+1)*n+(m+1)*(m+1)+n ≤ (σ.arrs matrixR).length)
    (hCanon : Canonical M (σ.arrs matrixR))
    (hm : σ.vars modR = M) (hr : σ.vars rowsR = m+1) (hn : σ.vars inputColsR = n)
    (hB : ∀ r : Fin (m+1), ∀ j : Fin n,
      decode M (σ.arrs matrixR) (r.val*n+j.val) = appendCoordinate A i r j) :
    ∃ τ, Run W smithIMP σ τ (smithCost M (m+1) n) ∧
      (τ.arrs matrixR).length = (σ.arrs matrixR).length ∧
      Canonical M (τ.arrs matrixR) ∧
      valueFromBanks (readSmithB (n := n) τ) (readSmithU (n := n) τ) b = recoverCoordinate A b i ∧
      Frame smithIMP σ τ := by
  obtain ⟨τ,st,hRun,hℓ,hcan,hbank,hvalid,_,hD,_,hFrame⟩ :=
    smithIMP_run (appendCoordinate A i) hW hLayout hLen hCanon hm hr hn hB
  have hReadB : readSmithB τ = st.B := Matrix.ext hbank.1
  have hReadU : readSmithU τ = st.U := Matrix.ext hbank.2
  obtain ⟨hU₁,hU₂,hV₁,hV₂,hEq,hD'⟩ := ZDiag.zmodDiag_spec (appendCoordinate A i)
  refine ⟨τ,hRun,hℓ,hcan,?_,hFrame⟩
  rw [hReadB,hReadU,recoverCoordinate]
  exact valueFromBanks_eq A b i hvalid hD ⟨hEq,hU₁,hU₂,hV₁,hV₂⟩ hD'

#print axioms paidCoordinateSmith_run

end EvenTI.P12Compare
