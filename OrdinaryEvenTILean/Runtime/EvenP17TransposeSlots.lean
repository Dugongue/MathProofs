import EvenP16TrialCrossShuffle

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace EvenTI.P17Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007 Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)

def transposeSourceSlot : String := "even.transpose.source"
def transposeOneSlot : String := "even.transpose.one"

private def transposeSourceExpr : Expr :=
  (Expr.var transposeSourceSlot).add (((Expr.var gV).mul (.var gRows)).add (.var gU))

private def transposeKeep : List String := [dL,dT,dU,dZ,gRows,gCols,gOut,transposeSourceSlot,transposeOneSlot]

variable {K : Type} [Field K] [Fintype K]

noncomputable def transposeSlots (F : FieldPresentation K) : Com :=
  gridProg (fieldMacros F) (.var transposeOneSlot) transposeSourceExpr

noncomputable def transposeSlotsCost (F : FieldPresentation K) (m n : ℕ) : ℕ :=
  gridCost (fieldMacros F) (.var transposeOneSlot) transposeSourceExpr 1 n m

/-- A row-major slot bank is transposed by the existing grid with dot
length one. The original bank and all protected slots remain available. -/
theorem transposeSlots_run (F : FieldPresentation K) {B S m n src dst z tt uu one : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) (hBefore : src+m*n ≤ dst) (hFit : dst+n*m ≤ S)
    (hN : n+1 < B) (hM : m+1 < B) (hSmall : 2 < B)
    (hT : tt < S) (hU : uu < S) (hTU : tt ≠ uu)
    (hTs : dst+n*m ≤ tt ∨ tt < src) (hUs : dst+n*m ≤ uu ∨ uu < src)
    (hZ : z < S) (hZkeep : ¬ Written dst n m tt uu z) (hZero : val F canonical qN.WS s z=0)
    (hOne : one < S) (hOneKeep : ¬ Written dst n m tt uu one)
    (hOneVal : val F canonical qN.WS s one=1)
    (hL : s.vars dL=1) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu) (hZR : s.vars dZ=z)
    (hR : s.vars gRows=n) (hC : s.vars gCols=m) (hO : s.vars gOut=dst)
    (hSR : s.vars transposeSourceSlot=src) (hOR : s.vars transposeOneSlot=one) :
    ∃ t, Run B (transposeSlots F) s t (transposeSlotsCost F m n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i < n, ∀ j < m, val F canonical qN.WS t (dst+(i*m+j)) =
        val F canonical qN.WS s (src+(j*n+i))) ∧
      (∀ k < S, ¬ Written dst n m tt uu k → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r ∉ regNames canonical → r ≠ dI → r ≠ gU → r ≠ gV → r ≠ dO → t.vars r=s.vars r) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hs := hS.slots_word
  let fa := fun (_ _ _ : ℕ) => one
  let fb := fun (i j _ : ℕ) => src+(j*n+i)
  obtain ⟨t,hr,hSlot,hAt,hKeep,hVars,_,hi,ho⟩ :=
    grid_run (fieldMacros F) transposeKeep (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (.var transposeOneSlot) transposeSourceExpr
      (by simp [VarsIn,transposeKeep]) (by simp [transposeSourceExpr,VarsIn,transposeKeep])
      hS hL hTR hUR hZR hR hC hO (fa:=fa) (fb:=fb)
      (by
        intro u hk i hi j hj x hx hri hrj hrx
        exact ev_var ((hk _ (by decide)).trans hOR) (show one < B by omega))
      (by
        intro u hk i hi j hj x hx hri hrj hrx
        have hiB : i < B := by omega
        have hjB : j < B := by omega
        have eb := ev_var ((hk _ (by decide)).trans hSR) (show src < B by omega)
        have en := ev_var ((hk _ (by decide)).trans hR) (show n < B by omega)
        have endAt : src+(j*n+i) < src+m*n := out_lt (o0:=src) hj hi
        exact ev_add eb (ev_add (ev_mul (ev_var hrj hjB) en (by omega))
          (ev_var hri hiB) (by omega)) (by omega))
      (fun _ _ _ _ _ _ => ⟨hOne,hOneKeep⟩)
      (by
        intro i hi j hj x hx
        have endAt : src+(j*n+i) < src+m*n := out_lt (o0:=src) hj hi
        refine ⟨by dsimp [fb]; omega,?_⟩
        dsimp [fb]
        rintro (⟨_,_⟩ | h | h) <;> omega)
      hFit hT hU hZ hTU hZkeep (by omega) (by omega) hZero hSmall hN hM (by omega)
  refine ⟨t,hr,hSlot,?_,hKeep,hVars,hi,ho⟩
  intro i hi j hj
  rw [hAt i hi j hj,Finset.sum_range_one]
  simp [fa,fb,hOneVal]

#print axioms transposeSlots_run
end EvenTI.P17Execution
