import EvenP13SpectralAnchorLoad

set_option autoImplicit false
set_option maxRecDepth 22000
set_option maxHeartbeats 500000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (noRead)
open Mathproof.Problem17CharpolyExec (config fromBank)
open Mathproof.Problem17BudgetExec (budgetScan)
open Mathproof.P15DH2Bank20261007 (bankInstall)
open Mathproof.P15RecogIMPDot20261007 (qN)

private theorem fromBank_noRead : noRead fromBank := by imp_frame
private theorem fromBank_noWrite : fromBank.NoWrite := by imp_frame
private theorem budget_noRead : noRead budgetScan := by imp_frame
private theorem budget_noWrite : budgetScan.NoWrite := by imp_frame

theorem oneAnchor_noRead : noRead oneAnchorCode := by
  exact And.intro (by imp_frame : noRead (config false))
    ⟨fromBank_noRead, (by imp_frame : noRead (bankInstall qN.WS)),budget_noRead⟩

theorem oneAnchor_noWrite : oneAnchorCode.NoWrite := by
  exact And.intro (by imp_frame : (config false).NoWrite)
    ⟨fromBank_noWrite, (by imp_frame : (bankInstall qN.WS).NoWrite),budget_noWrite⟩

#print axioms oneAnchor_noRead
#print axioms oneAnchor_noWrite
end EvenTI.P13Spectral
