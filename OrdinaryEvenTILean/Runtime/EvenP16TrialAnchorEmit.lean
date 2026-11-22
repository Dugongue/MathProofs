import EvenP15TrialFieldVector
import EvenP10TrialPayload

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace EvenTI.P16Trial

open EvenTI.Contract EvenTI.P10Scan EvenTI.P15Trial EvenTI.PrimaryAlignment
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def emitAnchorWidth : String := "even.trial.emit.anchor-width"

private def blockLength : Expr := .add (.var fieldVectorLength) (.lit 1)

noncomputable def emitAnchorBlock (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.write blockLength) (.seq (.write (.var emitAnchorWidth)) (fieldVectorProgram D F))

noncomputable def emitAnchorBlockCost (F : FieldPresentation K) (n : ℕ) : ℕ :=
  6+((emitFieldLabelCost F+16)*(n*n)+6)

/-- Serialize one actually computed anchor in the literal length-prefixed
format used in the prepared trial's anchor list. -/
theorem emitAnchorBlock_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn start : ℕ} {σ : Env} (A : NumberedAnchor K)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hW : A.width*A.width+1 < B)
    (hFit : start+A.width*A.width ≤ Sn)
    (hStart : σ.vars fieldVectorStart=start)
    (hLen : σ.vars fieldVectorLength=A.width*A.width)
    (hWidth : σ.vars emitAnchorWidth=A.width)
    (hRead : ∀ i : Fin (A.width*A.width),
      val F canonical qN.WS σ (start+i.val)=A.matrix (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) :
    ∃ τ, Run B (emitAnchorBlock D F) σ τ (emitAnchorBlockCost F A.width) ∧
      τ.out=σ.out++blockW (numberedAnchorWords D A) ∧ τ.arrs=σ.arrs ∧ τ.inp=σ.inp := by
  let n := A.width
  let m := n*n
  change m+1 < B at hW
  have hN : n < B := by
    by_cases hz : n=0
    · omega
    · have hn : 0 < n := Nat.pos_of_ne_zero hz
      have hh : n ≤ m := Nat.le_mul_of_pos_right n hn
      omega
  have hL : (Expr.var fieldVectorLength).evalB B σ=some m :=
    evalB_var_iff.mpr ⟨hLen.symm,hLen ▸ (show m < B by omega)⟩
  have hb : blockLength.evalB B σ=some (m+1) :=
    evalB_bin (op := .add) hL (evalB_lit (by omega)) hW
  let ρ := {σ with out := σ.out++[m+1]}
  have hρ : Run B (.write blockLength) σ ρ 4 := Run.write hb
  have hn : (Expr.var emitAnchorWidth).evalB B ρ=some n :=
    evalB_var_iff.mpr ⟨hWidth.symm,hWidth ▸ hN⟩
  let α := {ρ with out := ρ.out++[n]}
  have hα : Run B (.write (.var emitAnchorWidth)) ρ α 2 := Run.write hn
  have hs : Slots F canonical qN.WS Sn B α := slots_frame F hSlots rfl rfl (fun _ _ => rfl) rfl
  obtain ⟨τ,hR,hO,hA,hI,_⟩ := fieldVectorProgram_run D F hs hQ hP (by omega) hFit hStart hLen
  have hWords : ((List.range m).map fun i => (D (val F canonical qN.WS α (start+i))).val) =
      List.ofFn (fun i : Fin m => (D (A.matrix (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2)).val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hm : i < m := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact congrArg (fun x => (D x).val) (hRead ⟨i,hm⟩)
  refine ⟨τ,?_,?_,hA,hI⟩
  · exact (hρ.seq (hα.seq hR)).mono (by unfold emitAnchorBlockCost; omega)
  · rw [hO,hWords]
    simp [α,ρ,blockW,numberedAnchorWords,m,n,List.append_assoc]

#print axioms emitAnchorBlock_run
end EvenTI.P16Trial