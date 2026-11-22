import EvenP21ScalarScanPublish
import EvenP21ScalarScanSelected

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1000000

namespace EvenTI.P21ScalarScan

open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open EvenTI.P17Scalar (scalarProbeLimit activeSlotBank)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)

local macro "keepLayout" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.RecoveryLayout.fromFrame))

/-- Footprint needed to run a mode producer beside the committed CRT solver.
The frame always preserves allocation lengths. Only the CRT data and control
words actually read by the scanner need write protection here. -/
structure KeepsSharedScan (cmd : Com) : Prop where
  rows : rowsR ∉ scalarWrites cmd
  columns : inputColsR ∉ scalarWrites cmd
  modulus : modR ∉ scalarWrites cmd
  base : baseRows ∉ scalarWrites cmd
  probeLimit : scalarProbeLimit ∉ scalarWrites cmd
  matrix : matrixR ∉ arrayWrites cmd
  constraint : constraintMatrix ∉ arrayWrites cmd
  incidence : incidenceBank ∉ arrayWrites cmd
  coordinate : coordinateBank ∉ arrayWrites cmd

theorem SharedScanInput.ofFrame {M W m n capacity : ℕ} {s t : Env} {cmd : Com}
    {src : Fin m → Fin 3 → Fin n} (h : SharedScanInput M W capacity src s)
    (f : Frame cmd s t) (keep : KeepsSharedScan cmd) : SharedScanInput M W capacity src t := by
  have canon : Canonical M (t.arrs matrixR) := (f.arrs matrixR keep.matrix).symm ▸ h.recovery.workCanon
  have recovery : RecoveryLayout M m n t := keepLayout h.recovery f keep.rows keep.columns keep.modulus keep.base canon
  exact ⟨recovery,h.incidence.congr_env (f.arrs _ keep.incidence),
    (f.arrs constraintMatrix keep.constraint).symm ▸ h.canonical,
    (f.len _).trans_lt h.limit,(f.len _).trans h.rhs,(f.len _).symm ▸ h.active,
    (f.len _).trans_lt h.coordLength,(f.arrs coordinateBank keep.coordinate).symm ▸ h.coordWords,
    (f.vars _ keep.probeLimit).trans h.probeLimit⟩

theorem publishScanMode_keepsShared : KeepsSharedScan publishScanMode := by
  constructor <;> decide

theorem SharedScanInput.afterPublish {M W m n capacity : ℕ} {s t : Env}
    {src : Fin m → Fin 3 → Fin n} (h : SharedScanInput M W capacity src s)
    (f : Frame publishScanMode s t) : SharedScanInput M W capacity src t :=
  h.ofFrame f publishScanMode_keepsShared

#print axioms SharedScanInput.afterPublish
end EvenTI.P21ScalarScan
