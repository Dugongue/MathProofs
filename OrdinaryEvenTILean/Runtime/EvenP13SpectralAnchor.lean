import Comparator46CharpolyFactor
import CharpolyExecPairCost
import EvenP11SpectralCost

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5500000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Contract EvenTI.PrimaryAlignment
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPPolynomialProductCall20261002 (WS)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15FactorIMP20261007
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.Problem17CharpolyExec
open Mathproof.Problem17BudgetExec (budgetScan budgetScan_run budgetCost budgetCost_le valueReg cap)
open Mathproof.Problem17RepeatedBudget (repeatedBudget)
open Mathproof.Problem17CharpolyStage (dim)
open Problem17Factor46 Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Compute the characteristic polynomial from the live matrix bank and peel
its successive radicals with the checked Problem 1.7 register programs. -/
noncomputable def anchorBudgetCode : Com := .seq fromBank budgetScan

noncomputable def anchorBudgetCost (F : FieldPresentation K) (t N : Nat) : Nat :=
  fromBankCost F t (N+N) + budgetCost F N

structure AnchorReady (F : FieldPresentation K) (N B t ab tb : Nat)
    (A : Matrix (Fin (t+1)) (Fin (t+1)) K) (σ : Env) : Prop where
  bank : Bank F N B σ
  ws : σ.vars qN.WS = σ.vars WS
  layout : (contiguous t ab (L0f N) (N+N) tb).valid (Snf N) B
  input : σ.vars setupInput = ab
  coeff : σ.vars setupCoeff = L0f N
  width : σ.vars setupWidth = N+N
  scratch : σ.vars setupScratch = tb
  exponent : σ.vars setupExp = t
  matrix : MatBlock F σ ab A
  capacity : t+3 ≤ N
  minimum : 4 ≤ N
  word : cap N * N + (N+N+4) < B

theorem anchorBudget_run (F : FieldPresentation K)
    {N B t ab tb : Nat} {A : Matrix (Fin (t+1)) (Fin (t+1)) K} {σ : Env}
    (h : AnchorReady F N B t ab tb A σ) :
    ∃ τ, Run B anchorBudgetCode σ τ (anchorBudgetCost F t N) ∧
      Bank F N B τ ∧ τ.vars valueReg = repeatedBudget A.charpoly ∧
      Frame anchorBudgetCode σ τ := by
  have hSlots := slots_ws F h.bank.slots h.ws (by decide)
  obtain ⟨η,hr,hS,hCoeff,_,fr⟩ :=
    fromBank_run F A hSlots h.layout h.input h.coeff h.width h.scratch h.exponent h.matrix
  have hws' : η.vars qN.WS = η.vars WS :=
    (fr.vars qN.WS (by apply not_mem_scalarWrites; rfl)).trans
      (h.ws.trans (fr.vars WS (by apply not_mem_scalarWrites; rfl)).symm)
  have hb : Bank F N B η := bank_from_alias_frame F h.bank hS hws' fr
    (by unfold keep; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> apply not_mem_scalarWrites <;> rfl)
    (by apply not_mem_scalarWrites; rfl)
  have hd : A.charpoly.natDegree+2 ≤ N := by
    rw [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
    exact h.capacity
  obtain ⟨τ,hs,hτ,_,hBudget,_⟩ := budgetScan_run F hb h.minimum h.word
    A.charpoly_monic hd (coeffSlots_holds F (by simpa only [Nat.zero_mul,Nat.add_zero] using hCoeff) hws')
  have run : Run B anchorBudgetCode σ τ (anchorBudgetCost F t N) := hr.seq hs
  exact ⟨τ,run,hτ,hBudget,Frame.of_run run⟩

theorem anchorBudgetCost_le (F : FieldPresentation K) {t N X : Nat}
    (hM : macroBudget F ≤ X) (hDim : dim (t+1)*dim (t+1)+2 ≤ X)
    (hSize : Nat.size t+1 ≤ X) (hN : N+N+1 ≤ X) (hE : F.e+1 ≤ X) :
    anchorBudgetCost F t N ≤ (fromBankFactor+5000000)*X^7 := by
  have hX : 1 ≤ X := by omega
  have hp : X^6 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h₁ := (fromBank_cost_le F hM hDim hSize (show N+N ≤ X by omega) hE).trans
    (Nat.mul_le_mul_left fromBankFactor hp)
  have h₂ := budgetCost_le F hX hM (show N+1 ≤ X by omega)
  unfold anchorBudgetCost
  rw [Nat.add_mul]
  exact Nat.add_le_add h₁ h₂

/-- The register produced by the paid kernel is the exact spectral exponent
contribution recorded for a numbered anchor. -/
theorem numberedAnchorBudget_run (D : FieldEncoding K) (F : FieldPresentation K)
    (A : NumberedAnchor K) {t N B ab tb : Nat} (ht : A.width = t+1)
    {σ : Env}
    (h : AnchorReady F N B t ab tb
      ((Matrix.reindexAlgEquiv K K (finCongr ht)) A.matrix) σ) :
    ∃ τ, Run B anchorBudgetCode σ τ (anchorBudgetCost F t N) ∧
      Bank F N B τ ∧ τ.vars valueReg = storedAnchorExponent D A ∧
      Frame anchorBudgetCode σ τ := by
  obtain ⟨τ,hr,hb,hv,hf⟩ := anchorBudget_run F h
  refine ⟨τ,hr,hb,?_,hf⟩
  rw [hv,storedAnchorExponent_eq]
  congr 1
  exact Matrix.charpoly_reindex _ _

#print axioms anchorBudget_run
#print axioms anchorBudgetCost_le
#print axioms numberedAnchorBudget_run
end EvenTI.P13Spectral
