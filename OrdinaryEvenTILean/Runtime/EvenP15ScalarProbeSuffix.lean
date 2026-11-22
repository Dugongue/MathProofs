import EvenP14CRTLoop

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

local macro "loopProgress" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.Progress))
local macro "loopGuard" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.recoverOuterGuard))
local macro "loopBody" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.recoverOuterStep))
local macro "loopStep" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.recoverOuterStep_run))

def recoverRemainingCoordinates : Com := .while loopGuard loopBody

/-- Continue the same checked CRT driver from any genuinely installed
prefix. The caller checks feasibility separately when the prefix already
includes every coordinate. -/
theorem recoverRemainingCoordinates_run {M m n W p : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (w : Fin n → ZMod M)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hp : p ≤ n) (hSlot : s.vars coordinateSlot = p)
    (ha : s.vars crtActive = 1) (hInit : ConstraintBanks A b w p s)
    (hPrefix : CoordinatePrefix w p s) :
    let result := fixPaddedCoordinates A b ((List.finRange n).drop p) w p
    ∃ t, Run W recoverRemainingCoordinates s t ((recoverRoundCost M m n+54)*(n-p)+4) ∧
      RecoveryLayout M m n t ∧ t.vars coordinateSlot = n ∧
      Frame recoverRemainingCoordinates s t ∧
      match result with
      | some z => t.vars crtActive = 1 ∧
        (∀ i, (t.arrs coordinateBank).getD i.val 0 = (z i).val) ∧ Canonical M (t.arrs constraintMatrix)
      | none => t.vars crtActive = 0 := by
  let result := fixPaddedCoordinates A b ((List.finRange n).drop p) w p
  let I (t : Env) := RecoveryLayout M m n t ∧ t.vars coordinateSlot ≤ n ∧
    loopProgress A b result (t.vars coordinateSlot) t
  let V (t : Env) := n-t.vars coordinateSlot
  have hI : I s := ⟨hs,by simpa only [hSlot] using hp,by
    rw [hSlot]
    exact Or.inl ⟨ha,w,hInit,hPrefix,rfl⟩⟩
  have guard (t : Env) (ht : I t) : (loopGuard).evalB W t =
      some (decide (t.vars coordinateSlot < n)) :=
    evalB_condLt (ev_var rfl (ht.2.1.trans_lt (by omega))) (ev_var ht.1.cols (by omega))
  have step (t : Env) (ht : I t) (hg : (loopGuard).evalB W t = some true) :
      ∃ u, Run W loopBody t u (recoverRoundCost M m n+50) ∧ I u ∧ V u < V t := by
    rw [guard t ht] at hg
    have hi : t.vars coordinateSlot < n := by simpa using hg
    let i : Fin n := ⟨_,hi⟩
    obtain ⟨u,r,hu,hiu,hP⟩ := loopStep A b i result hW hL ht.1 rfl ht.2.2
    refine ⟨u,r,⟨hu,by rw [hiu]; exact Nat.succ_le_of_lt hi,by rw [hiu]; exact hP⟩,?_⟩
    simp only [V,hiu,i]
    omega
  obtain ⟨t,r,ht,hStop⟩ := Run.while_count I V (recoverRoundCost M m n+50)
    (fun q hq => ⟨_,guard q hq⟩) step hI
  rw [guard t ht] at hStop
  have hDone : t.vars coordinateSlot=n := by
    have hge : ¬t.vars coordinateSlot < n := by simpa using hStop
    have hle := ht.2.1
    omega
  have rr : Run W recoverRemainingCoordinates s t ((recoverRoundCost M m n+54)*(n-p)+4) := by
    have hSize : (loopGuard).size=3 := rfl
    simpa only [recoverRemainingCoordinates,V,hSlot,hSize,
      show 1+3+(recoverRoundCost M m n+50)=recoverRoundCost M m n+54 by omega] using r
  have hFinal : loopProgress A b result n t := by simpa only [hDone] using ht.2.2
  refine ⟨t,rr,ht.1,hDone,Frame.of_run rr,?_⟩
  have hSame : fixPaddedCoordinates A b ((List.finRange n).drop p) w p = result := rfl
  rw [hSame]
  rcases hFinal with ⟨hv,z,hBank,hx,hRest⟩ | ⟨hv,hRest⟩
  · have hDrop : (List.finRange n).drop n = [] := by simp
    have he : some z = result := by rw [hDrop] at hRest; exact hRest
    rw [← he]
    exact ⟨hv,fun j => hx j j.isLt,hBank.canonical⟩
  · rw [hRest]
    exact hv

local macro "fixComplete" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP12CompareRecoverLinear
    `EvenTI.P12Compare.fixCoordinates_complete))

/-- After one successful feasibility query, the tail of the in-place
prefix probe returns a genuine solution, including an empty tail. -/
theorem probeSuffix_feasible {M m n p : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (w : Fin n → ZMod M)
    (h : ∃ x, (fixedCoordinateMatrix A p).mulVec x = fixedCoordinateRhs b w p) :
    ∃ y, fixPaddedCoordinates A b ((List.finRange n).drop p) w p = some y ∧
      (fixedCoordinateMatrix A p).mulVec y = fixedCoordinateRhs b w p := by
  let is := (List.finRange n).drop p
  let C := fixedCoordinateMatrix A p
  let c := fixedCoordinateRhs b w p
  have hSeq (t : Fin is.length) : (is.get t).val = p+t.val := by
    change (((List.finRange n).drop p)[t.val]).val = _
    rw [List.getElem_drop,List.getElem_finRange]; rfl
  have hNodup : is.Nodup := (List.nodup_finRange n).sublist (List.drop_sublist p _)
  obtain ⟨y,hy,z,hz,hIn,hOut⟩ := fixComplete is hNodup w C c h
  have hEqual : y = z := by
    funext j
    by_cases hj : j ∈ is
    · exact hIn j hj
    · rw [hOut j hj]
      symm
      apply ((fixedCoordinate_solutions A b w z p).mp hz).2
      by_contra hh
      have hGe : p ≤ j.val := Nat.le_of_not_gt hh
      have hi : j.val-p < is.length := by
        simp only [is,List.length_drop,List.length_finRange]
        have hj' := j.isLt
        omega
      have hget : is.get ⟨j.val-p,hi⟩ = j := by
        apply Fin.ext
        rw [hSeq]
        change p+(j.val-p)=j.val
        omega
      exact hj (hget ▸ List.get_mem is ⟨j.val-p,hi⟩)
  have hRef := fixPaddedCoordinates_eq A b is p w C c hSeq
    (fun z => fixedCoordinate_solutions A b w z p)
  exact ⟨y,hRef.trans hy,by simpa only [hEqual] using hz⟩

#print axioms probeSuffix_feasible

#print axioms recoverRemainingCoordinates_run
end EvenTI.P15Scalar