import EvenP14CutScanEngine
import EvenP14CutRankLayout
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical run_frame)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def choiceFormAddress : Address := .add augmentedMatrixBase .side
def choiceTemp1 : Address := .add constantsBase (.litSucc 1)
def choiceTemp2 : Address := .add constantsBase (.litSucc 2)

def cutSetupBindings (j : Fin 4) : List (String × Expr) :=
  [(cutCoeffStart,augmentedMatrixBase.expr),(cutBasisStart,(outputBase j).expr),
   (cutFormStart,choiceFormAddress.expr),(dL,.var (nullityAt j)),
   (dZ,constantsBase.expr),(dT,choiceTemp1.expr),(dU,choiceTemp2.expr),
   (coeffLength,.var (nullityAt j)),(loadBase,augmentedMatrixBase.expr),
   (loadLength,.var (nullityAt j)),(cutChoiceBudget,.get rawPairIO.array (.lit 1))]

def cutSetupProgram (j : Fin 4) : Com := commands (cutSetupBindings j)

def cutSetupCost (j : Fin 4) : ℕ := ((cutSetupBindings j).map fun p => p.2.size+1).sum+1

private def cutSetupValues (j : Fin 4) (m c n : ℕ) : List (String × ℕ) :=
  [(cutCoeffStart,augmentedMatrixBase.value m),(cutBasisStart,(outputBase j).value m),
   (cutFormStart,placedRankSource m),(dL,c),
   (dZ,constantsBase.value m),(dT,constantsBase.value m+2),(dU,constantsBase.value m+3),
   (coeffLength,c),(loadBase,augmentedMatrixBase.value m),
   (loadLength,c),(cutChoiceBudget,n)]

private theorem setup_inputs_fresh : ∀ j : Fin 4, ∀ r ∈ (cutSetupBindings j).map Prod.fst,
    r ≠ shapePower.out ∧ r ≠ nullityAt j ∧ r ≠ qN.WS := by decide

private theorem setup_fields_fresh : ∀ r ∈ (cutSetupValues 0 0 0 0).map Prod.fst,
    canonical.e ≠ r ∧ canonical.p ≠ r ∧ canonical.modBase ≠ r ∧
      canonical.exp ≠ r ∧ qN.WS ≠ r := by decide

/-- Read width from the raw pair bank and selected nullity from its persisted
register. The cut scan consumes the resulting live coefficient layout. -/
theorem cutSetupProgram_run (FP : FieldPresentation K) {B m c n : ℕ} {σ : Env}
    (j : Fin 4) (d : ℕ) (tail : List ℕ) (hm : 0 < m) (hn : n ≤ m) (hc : c ≤ m)
    (hB : pairCutSlotCount.value m + m + m + 10 < B)
    (hS : Slots FP canonical qN.WS (pairCutSlotCount.value m) B σ)
    (hSide : σ.vars shapePower.out = m) (hC : σ.vars (nullityAt j)=c)
    (hHead : σ.arrs rawPairIO.array = d::n::tail)
    (hBank : m ≤ (σ.arrs coefficientBank).length)
    (hZ : val FP canonical qN.WS σ (constantsBase.value m)=0) :
    ∃ τ, Run B (cutSetupProgram j) σ τ (cutSetupCost j) ∧
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) FP τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m (constantsBase.value m)
        (constantsBase.value m+2) (constantsBase.value m+3) ∧
      τ.vars cutChoiceBudget=n ∧ τ.vars (nullityAt j)=c ∧
      (∀ s, val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      (∀ r, r ∉ (cutSetupBindings j).map Prod.fst → τ.vars r=σ.vars r) ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  let a := augmentedMatrixBase.value m
  let b := (outputBase j).value m
  let o := placedRankSource m
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  have h1 : a+c ≤ o := by simp only [o,placedRankSource]; omega
  have h2 : o+m ≤ b := by
    have hh : m ≤ m*m := Nat.le_mul_of_pos_right _ hm
    rw [show b = _ from outputBase_value m j]
    simp only [o,placedRankSource,firstOutputBase,Address.value,cutArea_value]
    omega
  have h3 : b+m*m ≤ z := outputBank_point_upper m j
  have h4 : z+4=Sn := rfl
  have hLay : CutDotLayout a b o c m z (z+2) (z+3) Sn :=
    ⟨h1,h2,h3,by omega,by omega,by omega,hc⟩
  have hv (x : Address) (hx : x.value m<B) : x.expr.evalB B σ=some (x.value m) :=
    Address.eval hSide hm x hx
  have ha := hv augmentedMatrixBase (by change a<B; omega)
  have hb := hv (outputBase j) (by change b<B; omega)
  have ho : choiceFormAddress.expr.evalB B σ=some o := hv _ (show o<B by omega)
  have hz := hv constantsBase (by change z<B; omega)
  have ht : choiceTemp1.expr.evalB B σ=some (z+2) := hv _ (show z+2<B by omega)
  have hu : choiceTemp2.expr.evalB B σ=some (z+3) := hv _ (show z+3<B by omega)
  have hcc : (Expr.var (nullityAt j)).evalB B σ=some c :=
    evalB_var_iff.mpr ⟨hC.symm,hC ▸ (show c<B by omega)⟩
  have hnn : (Expr.get rawPairIO.array (.lit 1)).evalB B σ=some n :=
    evalB_get (evalB_lit (by omega)) (by rw [hHead]; rfl) (by omega)
  let xs := cutSetupBindings j
  let vals := cutSetupValues j m c n
  let τ := install vals σ
  have hEval : List.Forall₂ (fun (p : String × Expr) v => p.2.evalB B σ=some v)
      xs (vals.map Prod.snd) :=
    .cons ha (.cons hb (.cons ho (.cons hcc (.cons hz (.cons ht (.cons hu
      (.cons hcc (.cons ha (.cons hcc (.cons hnn .nil))))))))))
  have hNoVar : ∀ p ∈ xs, ∀ q ∈ xs, NoVar p.1 q.2 := by
    intro p hp q hq
    have hf := setup_inputs_fresh j p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩)
    simp only [xs,cutSetupBindings,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with e|e|e|e|e|e|e|e|e|e|e <;> rw [e] <;> simp only [Prod.snd]
    all_goals first
      | exact Address.noVar _ hf.1
      | simp [NoVar,hf.2.1,Ne.symm hf.2.1]
  have hh : List.zip (xs.map Prod.fst) (vals.map Prod.snd)=vals := rfl
  have hRun := commands_run xs (vals.map Prod.snd) σ (by rfl) hEval hNoVar
  rw [hh] at hRun
  have hKeep (r : String) (hr : r ∉ xs.map Prod.fst) : τ.vars r=σ.vars r :=
    installed_scalar _ _ _ (fun p hp he => hr (show r ∈ xs.map Prod.fst from
      (show xs.map Prod.fst=vals.map Prod.fst from rfl).symm ▸ List.mem_map.mpr ⟨p,hp,he.symm⟩))
  have hfresh {r : String} (hr : r ∈ (vals.map Prod.fst)) :
      canonical.e ≠ r ∧ canonical.p ≠ r ∧ canonical.modBase ≠ r ∧
        canonical.exp ≠ r ∧ qN.WS ≠ r := setup_fields_fresh r (show r ∈ _ from hr)
  have hw : τ.vars qN.WS=σ.vars qN.WS := hKeep _
    (fun hr => (setup_inputs_fresh _ _ hr).2.2 rfl)
  have hArr := installed_arrays vals σ
  have hVal (s : ℕ) : val FP canonical qN.WS τ s=val FP canonical qN.WS σ s :=
    cutSlot_value_frame FP (congrFun hArr.1 canonical.mem) hw s
  have hRep : CutVisitInput (B := B) (Sn := Sn) FP τ a b o c m z (z+2) (z+3) := by
    refine ⟨⟨installed_slots FP vals σ hS (fun p hp => hfresh (List.mem_map.mpr ⟨p,hp,rfl⟩)),
      hLay,by omega,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,(hVal _).trans hZ⟩,?_,rfl,rfl,rfl⟩
    · exact (hKeep shapePower.out (fun hr => (setup_inputs_fresh _ _ hr).1 rfl)).trans hSide
    · rw [hArr.1]
      exact hc.trans hBank
  refine ⟨τ,hRun,hRep,rfl,?_,hVal,hKeep,hArr.1,hArr.2.1,hArr.2.2⟩
  exact (hKeep (nullityAt j) (fun hr => (setup_inputs_fresh _ _ hr).2.1 rfl)).trans hC

theorem coefficientBank_length_frame {P : Com} {σ τ : Env} {B C : ℕ}
    (h : Run B P σ τ C) :
    (τ.arrs coefficientBank).length = (σ.arrs coefficientBank).length :=
  (run_frame h).2.2.1 _

#print axioms cutSetupProgram_run
#print axioms coefficientBank_length_frame
end EvenTI.P12ComparePrep
