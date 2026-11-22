import EvenP16TrialHigherEmit
import EvenP14CutRawSetup
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace EvenTI.P16Trial

open EvenTI.P15Trial EvenTI.P12ComparePrep EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)

private def halfInputOrder : Expr := .div (.get rawPairIO.array (.lit 0)) (.lit 2)

def emitFormBindings : List (String×Expr) :=
  [(emitFormModes,halfInputOrder),(reverseDigitBase,.var cutChoiceBudget),
    (fieldVectorStart,.var cutFormStart),(fieldVectorLength,.var shapePower.out)]

def emitFormInit : Com := commands emitFormBindings

def emitFormInitCost : ℕ := (emitFormBindings.map (fun p => p.2.size+1)).sum+1

def emitFormTargets : List String :=
  [emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]

private theorem safeBindings : ∀ p∈emitFormBindings, ∀ q∈emitFormBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [emitFormBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl <;>
    simp only [Prod.fst,Prod.snd,halfInputOrder,NoVar,Expr.div] <;> decide

private def values (d n src m : ℕ) : List (String×ℕ) :=
  [(emitFormModes,d),(reverseDigitBase,n),(fieldVectorStart,src),(fieldVectorLength,m)]

private theorem safeFields : ∀ x∈emitFormTargets,
    canonical.e ≠ x ∧ canonical.p ≠ x ∧ canonical.modBase ≠ x ∧ canonical.exp ≠ x ∧ qN.WS ≠ x := by
  decide

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Install the serialization order, radix, field interval and length
using the actual original header and selected live cut metadata. -/
theorem emitFormInit_run (F : FieldPresentation K) {B Sn d n m src : ℕ} {σ : Env}
    (rest : List ℕ) (hB : d+d < B) (hTwo : 2 < B) (hN : n < B) (hM : m < B)
    (hPtr : src < B) (hHead : σ.arrs rawPairIO.array=(d+d)::rest)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hWidth : σ.vars cutChoiceBudget=n)
    (hSource : σ.vars cutFormStart=src) (hLength : σ.vars shapePower.out=m) :
    ∃ τ, Run B emitFormInit σ τ emitFormInitCost ∧ Slots F canonical qN.WS Sn B τ ∧
      τ.vars emitFormModes=d ∧ τ.vars reverseDigitBase=n ∧
      τ.vars fieldVectorStart=src ∧ τ.vars fieldVectorLength=m ∧
      (∀ x, x ∉ emitFormTargets → τ.vars x=σ.vars x) ∧
      (∀ s, val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  have hRead : (Expr.get rawPairIO.array (.lit 0)).evalB B σ = some (d+d) :=
    evalB_get (evalB_lit (by omega)) (by rw [hHead]; rfl) hB
  have hh : halfInputOrder.evalB B σ=some d := by
    have h := evalB_bin (op := .div) hRead (evalB_lit hTwo) (show (d+d)/2 < B by omega)
    simpa [halfInputOrder,show (d+d)/2=d by omega] using h
  have hVar (x : String) (i : ℕ) (hx : σ.vars x=i) (hi : i<B) :
      (Expr.var x).evalB B σ=some i := evalB_var_iff.mpr ⟨hx.symm,hx ▸ hi⟩
  let v := values d n src m
  let τ := install v σ
  have hr : Run B emitFormInit σ τ emitFormInitCost :=
    commands_run emitFormBindings (v.map Prod.snd) σ rfl
      (.cons hh (.cons (hVar _ _ hWidth hN) (.cons (hVar _ _ hSource hPtr)
       (.cons (hVar _ _ hLength hM) .nil)))) safeBindings
  have hS : Slots F canonical qN.WS Sn B τ := installed_slots F v σ hSlots <| fun p hp =>
    safeFields p.1 (by
      change p.1 ∈ v.map Prod.fst
      exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hR (x : String) (hx : x ∉ emitFormTargets) : τ.vars x=σ.vars x :=
    installed_scalar v σ x (fun p hp e => hx (List.mem_map.mpr ⟨p,hp,e.symm⟩))
  obtain ⟨hA,hI,hO⟩ := installed_arrays v σ
  refine ⟨τ,hr,hS,?_,?_,?_,?_,hR,?_,hA,hI,hO⟩
  · simp [τ,v,values,install,emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]
  · simp [τ,v,values,install,emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]
  · simp [τ,v,values,install,emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]
  · simp [τ,v,values,install,emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]
  · intro s
    exact cutSlot_value_frame F (congrFun hA canonical.mem) (hR _ (by decide)) s

#print axioms emitFormInit_run
end EvenTI.P16Trial