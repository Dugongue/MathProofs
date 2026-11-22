import EvenP12CompareRightKernel
import EvenP16InvertCutBank

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P16Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The existing raw word loader installs exactly the original balanced cut
used by the reciprocal and singular inverse interfaces. -/
theorem loadRawCut_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n B S src : ℕ} {s : Env} (T U : Tensor K ((l+1)+(l+1)) n) (target : Bool)
    (bank : String) (hBankMem : bank ≠ canonical.mem)
    (hBank : s.arrs bank = comparisonInput D T U)
    (hS : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B)
    (hB : 1 < B)
    (hOffset : tensorOffset (n^((l+1)+(l+1))) target + n^((l+1)+(l+1)) < B)
    (hBase : s.vars loadBase=src) (hLength : s.vars loadLength=n^((l+1)+(l+1)))
    (hInput : s.vars inputBase=tensorOffset (n^((l+1)+(l+1))) target)
    (hFit : src+n^((l+1)+(l+1)) ≤ S) :
    ∃ t, Run B (encodedBankLoad D F bank contiguousAddress) s t
      (encodedBankLoadCost F contiguousAddress (n^((l+1)+(l+1)))) ∧
      Slots F canonical qN.WS S B t ∧
      cutSlotMatrix F t l n src=flatten (if target then U else T) ∧
      (∀ r, ¬loadChanges r → t.vars r=s.vars r) ∧
      (∀ a, a ≠ canonical.mem → t.arrs a=s.arrs a) ∧ t.inp=s.inp ∧ t.out=s.out := by
  let V := if target then U else T
  obtain ⟨t,r,ht,hMatrix,_,hvars,harr,hinp,hout⟩ :=
    contiguousBankLoad_run D F bank (flatEntry V) hBankMem hS hQ hB
      (by omega) hOffset hBase hLength hInput hFit
      (fun k hk => by rw [hBank]; exact comparisonInput_getElem?_flat D T U target k hk)
  refine ⟨t,r,ht,?_,hvars,harr,hinp,hout⟩
  ext x y
  let i := inputCoordOrder n (l+1) x
  let j := inputCoordOrder n (l+1) y
  have hlt : i.val*n^(l+1)+j.val < n^((l+1)+(l+1)) := by
    rw [pow_add n (l+1) (l+1)]
    calc i.val*n^(l+1)+j.val < (i.val+1)*n^(l+1) := by rw [Nat.succ_mul]; omega
      _ ≤ n^(l+1)*n^(l+1) := Nat.mul_le_mul_right _ i.isLt
  have hEq := (hMatrix _ hlt).trans (flatEntry_index V i j)
  change val F canonical qN.WS t _ = flatten V x y
  simpa [i,j,pow_succ'] using hEq

#print axioms loadRawCut_run
end EvenTI.P18Execution

