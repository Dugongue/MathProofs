import EvenP15TrialFieldVector
import EvenP15TrialFormOrder
import EvenP14CutRankOne
import EvenP14CutRawSetup
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 2050000

namespace EvenTI.P15Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
open Mathproof.P15RecogIMPGrid20261007 (gridProg gRows gCols gOut)
open Mathproof.P15RecogIMPProgram20261007 (Mac copyAE rOs)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def orderFourDestination : Expr := .add (.var cutFormStart) (.var shapePower.out)

def orderFourBindings : List (String × Expr) :=
  [(retainedSrc,.var cutFormStart),(retainedStride,.var cutChoiceBudget),
   (dL,.lit 1),(rOs,.add (.var dZ) (.lit 1)),
   (gRows,.var cutChoiceBudget),(gCols,.var cutChoiceBudget),
   (gOut,orderFourDestination),(fieldVectorStart,orderFourDestination),
   (fieldVectorLength,.var shapePower.out)]

def orderFourConfigCost : ℕ := (orderFourBindings.map fun p => p.2.size+1).sum+1

noncomputable def orderFourFormWriter (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (cutRankMakeOne D F) <|
    .seq (commands orderFourBindings) <|
      .seq (gridProg Mac copyAE retainedIndex) (fieldVectorProgram D F)

def orderFourFormCost (F : FieldPresentation K) (m : ℕ) : ℕ :=
  cutRankMakeOneCost F+orderFourConfigCost+
    (300*(macroBudget F*(m+2)^4)+((emitFieldLabelCost F+16)*m+6))

private theorem orderFourSafe : ∀ p ∈ orderFourBindings, ∀ q ∈ orderFourBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [orderFourBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Prod.fst,Prod.snd,orderFourDestination,NoVar,Expr.add] <;> decide

private def orderFourValues (o m n z : ℕ) : List (String × ℕ) :=
  [(retainedSrc,o),(retainedStride,n),(dL,1),(rOs,z+1),(gRows,n),(gCols,n),
   (gOut,o+m),(fieldVectorStart,o+m),(fieldVectorLength,m)]

private theorem orderFourFieldsFixed : ∀ x ∈ (orderFourValues 0 0 0 0).map Prod.fst,
    canonical.e ≠ x ∧ canonical.p ≠ x ∧ canonical.modBase ≠ x ∧ canonical.exp ≠ x ∧ qN.WS ≠ x :=
  by decide

private theorem reverseModeNumber_two {n i : ℕ} (hn : 0 < n) (hi : i < n^2) :
    reverseModeNumber n 2 i=(i%n)*n+i/n := by
  have hq : i/n < n := Nat.div_lt_of_lt_mul (by simpa [pow_two] using hi)
  simp [reverseModeNumber,Nat.mod_eq_of_lt hq]

/-- Emit a selected live form in the exact decoder order. One existing
paid retained-mode gather performs the transpose between the native field
bank and the public cut-coordinate order. -/
theorem orderFourFormWriter_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n o z Sn B : ℕ} {σ : Env} (form : Coord 2 n → K) (hn : 2 ≤ n)
    (hWork : o+n*n+n*n ≤ z) (hScratch : z+4 ≤ Sn) (hB : Sn+3 < B)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hs : Slots F canonical qN.WS Sn B σ)
    (hWidth : σ.vars cutChoiceBudget=n) (hSide : σ.vars shapePower.out=n*n)
    (hBase : σ.vars cutFormStart=o)
    (hZ : σ.vars dZ=z) (hT : σ.vars dT=z+2) (hU : σ.vars dU=z+3)
    (hZero : val F canonical qN.WS σ z=0)
    (hRead : ∀ x, val F canonical qN.WS σ (o+(inputCoordOrder n 2 x).val)=form x)
    (hConst : constantsBase.value (n*n)=z) :
    ∃ τ, Run B (orderFourFormWriter D F) σ τ (orderFourFormCost F (n*n)) ∧
      τ.out=σ.out++cutFormWords D form ∧ τ.inp=σ.inp := by
  let m := n*n
  let dst := o+m
  have hnPos : 0 < n := by omega
  have hM : n ≤ m := Nat.le_mul_of_pos_right n hnPos
  have hmPos : 0 < m := Nat.mul_pos hnPos hnPos
  obtain ⟨ρ,r₀,hρ,hOne,hM₀,hV₀,hA₀,hI₀,hO₀⟩ :=
    cutRankMakeOne_run D F hSide hmPos hs (by rw [hConst]; omega) hQ
  have hV (r : String) (h₁ : r ≠ inputLabel) (h₂ : r ≠ destination) (h₃ : r ≠ rCv)
      (h₄ : r ≠ rTd) : ρ.vars r=σ.vars r := hV₀ r h₁ h₂ h₃ h₄
  have hv {r : String} {v : ℕ} (h : ρ.vars r=v) (hvb : v < B) :
      (Expr.var r).evalB B ρ=some v := evalB_var_iff.mpr ⟨h.symm,h ▸ hvb⟩
  have hSrc := hv ((hV _ (by decide) (by decide) (by decide) (by decide)).trans hBase) (by omega)
  have hN := hv ((hV _ (by decide) (by decide) (by decide) (by decide)).trans hWidth) (by omega)
  have hMval := hv ((hV _ (by decide) (by decide) (by decide) (by decide)).trans hSide) (by omega)
  have hZeroReg := hv ((hV _ (by decide) (by decide) (by decide) (by decide)).trans hZ) (by omega)
  have hLit : (Expr.lit 1).evalB B ρ=some 1 := evalB_lit (by omega)
  have hD : orderFourDestination.evalB B ρ=some dst :=
    evalB_bin (op := .add) hSrc hMval (show o+m < B by omega)
  have hOp : (Expr.add (.var dZ) (.lit 1)).evalB B ρ=some (z+1) :=
    evalB_bin (op := .add) hZeroReg hLit (show z+1 < B by omega)
  let vals := orderFourValues o m n z
  let η := install vals ρ
  have hList : List.Forall₂ (fun (p : String×Expr) (v : ℕ) => p.2.evalB B ρ=some v)
      orderFourBindings (vals.map Prod.snd) :=
    .cons hSrc (.cons hN (.cons hLit (.cons hOp (.cons hN (.cons hN (.cons hD (.cons hD (.cons hMval .nil))))))))
  have r₁ : Run B (commands orderFourBindings) ρ η orderFourConfigCost :=
    commands_run orderFourBindings (vals.map Prod.snd) ρ (by rfl) hList orderFourSafe
  have hSlot : Slots F canonical qN.WS Sn B η := installed_slots F vals ρ hρ <|
    fun p hp => orderFourFieldsFixed p.1 (by
      change p.1 ∈ vals.map Prod.fst
      exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hVal (i : ℕ) : val F canonical qN.WS η i=val F canonical qN.WS ρ i :=
    cutSlot_value_frame F rfl rfl _
  have hKeep (r : String) (h₁ : r ≠ inputLabel) (h₂ : r ≠ destination)
      (h₃ : r ≠ rCv) (h₄ : r ≠ rTd) (hN : r ∉ vals.map Prod.fst) : η.vars r=σ.vars r := by
    have hv := installed_scalar vals ρ r (fun p hp he => hN (List.mem_map.mpr ⟨p,hp,he.symm⟩))
    exact hv.trans (hV r h₁ h₂ h₃ h₄)
  have hZ' : η.vars dZ=z := (hKeep dZ (by decide) (by decide) (by decide) (by decide) (by
    change dZ ∉ (orderFourValues 0 0 0 0).map Prod.fst
    decide)).trans hZ
  have hT' : η.vars dT=z+2 := (hKeep dT (by decide) (by decide) (by decide) (by decide) (by
    change dT ∉ (orderFourValues 0 0 0 0).map Prod.fst
    decide)).trans hT
  have hU' : η.vars dU=z+3 := (hKeep dU (by decide) (by decide) (by decide) (by decide) (by
    change dU ∉ (orderFourValues 0 0 0 0).map Prod.fst
    decide)).trans hU
  have hz₁ : val F canonical qN.WS η z=0 :=
    (hVal z).trans ((hM₀ z (by rw [hConst]; omega)).trans hZero)
  have ho₁ : val F canonical qN.WS η (z+1)=1 :=
    (hVal (z+1)).trans (by rwa [hConst] at hOne)
  obtain ⟨α,r₂,hα,hCopy,_,hFrame,hIn,hOut⟩ :=
    paidRetainedLoad_run F (a := 1) (s := n) (n := n) (src := o) (dst := dst) (L := m)
      hnPos hnPos (by decide)
      (by simp [m]) (by simp [dst,m]) (by simpa [dst,m] using hWork)
      hScratch hB hSlot rfl rfl rfl hT' hU' hZ' rfl (by change n = 1*n; simp)
      rfl rfl hz₁ ho₁
  have hA : α.vars fieldVectorStart=dst := hFrame _ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hLen : α.vars fieldVectorLength=m := hFrame _ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨τ,r₃,ho,_,hi,_⟩ := fieldVectorProgram_run D F hα hQ hP (by omega)
    (show dst+m ≤ Sn by dsimp [dst,m]; omega) hA hLen
  have hGather (i : Fin (n^2)) :
      val F canonical qN.WS α (dst+i.val) =
        val F canonical qN.WS σ (o+reverseModeNumber n 2 i.val) := by
    let q := i.val/n
    let r := i.val%n
    have hq : q < n := Nat.div_lt_of_lt_mul (by simpa [pow_two] using i.isLt)
    have hr : r < n := Nat.mod_lt _ hnPos
    have hQR : q*n+r=i.val := by simpa [q,r,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div i.val n
    have hIdx : retainedOffset n n q r=reverseModeNumber n 2 i.val := by
      rw [reverseModeNumber_two hnPos i.isLt]
      simp [retainedOffset,Nat.div_eq_of_lt hq,Nat.mod_eq_of_lt hq,q,r]
    have hCopy' := hCopy q (by simpa using hq) r hr
    rw [hQR,hIdx] at hCopy'
    have hx : o+reverseModeNumber n 2 i.val ≠ constantsBase.value m+1 := by
      rw [hConst,reverseModeNumber_two hnPos i.isLt]
      have hh : r*n+q < m := by
        have ht := Nat.mul_le_mul_right n (show r+1 ≤ n from Nat.succ_le_of_lt hr)
        rw [Nat.succ_mul] at ht
        change _ < n*n
        omega
      change o+(r*n+q) ≠ z+1
      dsimp [m] at hh
      omega
    exact hCopy'.trans ((hVal _).trans (hM₀ _ hx))
  have hWord : ((List.range m).map fun i => (D (val F canonical qN.WS α (dst+i))).val)
      = cutFormWords D form := by
    rw [cutFormWords_as_gather hnPos D form (fun i => val F canonical qN.WS σ (o+i)) hRead]
    apply List.ext_getElem
    · simp [m,pow_two]
    · intro i hi₁ hi₂
      have hx : i < n^2 := by simpa [m,pow_two] using hi₁
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact congrArg (fun x => (D x).val) (hGather ⟨i,hx⟩)
  refine ⟨τ,?_,?_,hi.trans (hIn.trans hI₀)⟩
  · simpa only [orderFourFormWriter,orderFourFormCost,Nat.add_assoc] using
      r₀.seq (r₁.seq (r₂.seq r₃))
  · rw [ho,hWord,hOut,show η.out=ρ.out from rfl,hO₀]

#print axioms orderFourFormWriter_run
end EvenTI.P15Trial
