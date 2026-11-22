import EvenP13SpectralAnchor
import EvenP12CompareBankLoad
import EvenP10TrialPayloadDecode

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 7000000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Contract EvenTI.P12Compare EvenTI.PrimaryAlignment EvenTI.P10Scan
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPPolynomialProductCall20261002 (WS)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15FactorIMP20261007
open Mathproof.P15DH2Bank20261007 (rNin bankInstall bankInstall_run bankRegs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.Problem17CharpolyExec
open Mathproof.Problem17BudgetExec (budgetScan budgetScan_run budgetCost valueReg cap dimReg)
open Mathproof.Problem17RepeatedBudget (repeatedBudget)
open Mathproof.Problem17CharpolyStage (dim)
open Mathproof.Problem17PreparedCovariants (W)
open Mathproof.Problem17CovariantExecution (leftStart rightStart)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- One reusable anchor evaluation. Reinstall the common polynomial bank
from the slots already used for the live matrix. -/
noncomputable def oneAnchorCode : Com :=
  .seq (config false) (.seq fromBank (.seq (bankInstall qN.WS) budgetScan))

noncomputable def oneAnchorCost (F : FieldPresentation K) (t N : Nat) : Nat :=
  configCost false + (fromBankCost F t (N+N) + (60+budgetCost F N))

/-- Layout shared by matrix loading and the polynomial arithmetic. -/
structure OneAnchorLayout (N B t : Nat) : Prop where
  low : rightStart (t+1) (W (t+1))+(t+1)*(t+1) ≤ fBase N
  high : address t (pairScratch N) 5+5 ≤ Snf N
  word : Snf N+10 < B
  wide : address t (pairScratch N) 4+(N+N)*dim (t+1) < B
  budget : cap N*N+(N+N+4) < B
  degree : t+3 ≤ N
  minimum : 4 ≤ N

structure OneAnchorState (F : FieldPresentation K) (N B t : Nat) (σ : Env) : Prop where
  slots : Slots F canonical qN.WS (Snf N) B σ
  ws : σ.vars qN.WS = F.e+1
  modulus : σ.vars canonical.modBase = 0
  length : (σ.arrs canonical.mem).length = F.e+1+Snf N*F.e
  width : σ.vars rNin = N
  order : σ.vars dimReg = t+1

theorem oneAnchor_run (F : FieldPresentation K)
    {N B t : ℕ} {σ : Env} (A : Matrix (Fin (t+1)) (Fin (t+1)) K)
    (h : OneAnchorLayout N B t) (hs : OneAnchorState F N B t σ)
    (hA : MatBlock F σ (covBase false (t+1)) A) :
    ∃ τ, Run B oneAnchorCode σ τ (oneAnchorCost F t N) ∧
      Bank F N B τ ∧ τ.vars valueReg = repeatedBudget A.charpoly ∧
      Frame oneAnchorCode σ τ := by
  have hBase : covBase false (t+1)+(t+1)*(t+1) ≤ fBase N := by
    have hl := h.low
    unfold rightStart at hl
    change leftStart (t+1) (W (t+1)) + (t+1)*(t+1) ≤ fBase N
    omega
  have hfg : fBase N+(N+N) ≤ pairScratch N := by unfold pairScratch gBase fBase; omega
  have ht : pairScratch N ≤ address t (pairScratch N) 5 := by unfold address; omega
  have hB := h.word
  have hHi := h.high
  have hScratch : pairScratch N < B := by omega
  have hn : t+1 < B := by
    have hh := h.degree
    have hcap := h.budget
    have hm : N ≤ cap N*N := by
      have hpos : 0 < cap N := by
        unfold cap
        exact Nat.mul_pos (by have := h.minimum; omega) (by omega)
      exact Nat.le_mul_of_pos_left _ hpos
    omega
  have hvalid :
      (contiguous t (covBase false (t+1)) (outBase false N) (N+N) (pairScratch N)).valid (Snf N) B := by
    apply contiguous_valid (by have := h.minimum; omega) (by omega) ?_ h.high h.word h.wide
    exact hfg
  obtain ⟨ρ,r₁,hρ,hcfg,hmem,f₁⟩ := config_run F false hs.slots hs.order hs.width
    (by omega) hn (by have := h.minimum; omega) h.low hScratch
  have hA' : MatBlock F ρ (covBase false (t+1)) A := by
    intro i j
    rw [hmem]
    exact hA i j
  obtain ⟨ν,r₂,hν,hcoeff,_,f₂⟩ := fromBank_run F A hρ hvalid hcfg.input hcfg.output
    hcfg.width hcfg.scratch hcfg.exp hA'
  have keep (r : String) (h₁ : r ∉ scalarWrites (config false)) (h₂ : r ∉ scalarWrites fromBank) :
      ν.vars r = σ.vars r := (f₂.vars _ h₂).trans (f₁.vars _ h₁)
  have hLen := (f₂.len canonical.mem).trans ((f₁.len canonical.mem).trans hs.length)
  obtain ⟨η,r₃,hη,hVal,_,_,_,_⟩ := bankInstall_run F (show 1 ≤ N by have := h.minimum; omega)
    qN.WS (by decide) (by decide) hν
    ((keep _ (by imp_frame) (by imp_frame)).trans hs.ws)
    ((keep _ (by imp_frame) (by imp_frame)).trans hs.modulus) hLen
    ((keep _ (by imp_frame) (by imp_frame)).trans hs.width)
  have hc : Holds F η (N+N) (L0f N+0*(N+N)) A.charpoly := by
    intro i hi
    simp only [Nat.zero_mul,Nat.add_zero]
    rw [hVal]
    exact hcoeff i hi
  have hd : A.charpoly.natDegree+2 ≤ N := by
    rw [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
    exact h.degree
  obtain ⟨τ,r₄,hbank,_,hval,_⟩ := budgetScan_run F hη h.minimum h.budget A.charpoly_monic hd hc
  have hr : Run B oneAnchorCode σ τ (oneAnchorCost F t N) := r₁.seq (r₂.seq (r₃.seq r₄))
  exact ⟨τ,hr,hbank,hval,Frame.of_run hr⟩

noncomputable def oneAnchorFromLabels (D : FieldEncoding K) (F : FieldPresentation K)
    (input : String) : Com :=
  .seq (encodedBankLoad D F input contiguousAddress) oneAnchorCode

/-- Physically load the finite-field labels in a row-major serialized anchor
and run the complete characteristic-polynomial and repeated-budget kernel. -/
theorem oneAnchorFromLabels_run (D : FieldEncoding K) (F : FieldPresentation K)
    {N B t offset : ℕ} {σ : Env} (A : Matrix (Fin (t+1)) (Fin (t+1)) K)
    (input : String) (hInput : input ≠ canonical.mem)
    (h : OneAnchorLayout N B t) (hs : OneAnchorState F N B t σ)
    (hF : Fintype.card K ≤ B) (hOffset : offset+(t+1)*(t+1) < B)
    (hBase : σ.vars loadBase = covBase false (t+1))
    (hLen : σ.vars loadLength = (t+1)*(t+1)) (hOff : σ.vars inputBase = offset)
    (hData : ∀ j : Fin ((t+1)*(t+1)),
      (σ.arrs input)[offset+j.val]? = some
        (D (A (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)).val) :
    ∃ τ, Run B (oneAnchorFromLabels D F input) σ τ
      (encodedBankLoadCost F contiguousAddress ((t+1)*(t+1))+oneAnchorCost F t N) ∧
      Bank F N B τ ∧ τ.vars valueReg = repeatedBudget A.charpoly ∧
      Frame (oneAnchorFromLabels D F input) σ τ := by
  let el (j : ℕ) : K := if hj : j < (t+1)*(t+1) then
    A (finProdFinEquiv.symm ⟨j,hj⟩).1 (finProdFinEquiv.symm ⟨j,hj⟩).2 else 0
  have hFit : covBase false (t+1)+(t+1)*(t+1) ≤ Snf N := by
    have hh := h.low
    unfold rightStart at hh
    change leftStart (t+1) (W (t+1))+(t+1)*(t+1) ≤ Snf N
    have hSn : fBase N ≤ Snf N := by unfold fBase Snf wkf osf; omega
    omega
  obtain ⟨ρ,hr,hSlots,hval,_,hvars,_,_,_⟩ := contiguousBankLoad_run D F input el hInput
    hs.slots hF (by have := h.word; omega) (by omega) hOffset hBase hLen hOff hFit
    (fun j hj => by simpa only [el,dif_pos hj] using hData ⟨j,hj⟩)
  have hρ : OneAnchorState F N B t ρ := ⟨hSlots,
    (hvars _ (by decide)).trans hs.ws, (hvars _ (by decide)).trans hs.modulus,
    ((Frame.of_run hr).len _).trans hs.length, (hvars _ (by decide)).trans hs.width,
    (hvars _ (by decide)).trans hs.order⟩
  have hM : MatBlock F ρ (covBase false (t+1)) A := by
    intro i j
    let ij := finProdFinEquiv (i,j)
    have hindex : ij.val = i.val*(t+1)+j.val := by simp [ij,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    change val F canonical qN.WS ρ (covBase false (t+1)+(i.val*(t+1)+j.val)) = A i j
    rw [← hindex,hval ij.val ij.isLt]
    simp only [el,dif_pos ij.isLt]
    change A (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2 = A i j
    rw [show finProdFinEquiv.symm ij = (i,j) from Equiv.symm_apply_apply _ _]
  obtain ⟨τ,ht,hBank,hBudget,_⟩ := oneAnchor_run F A h hρ hM
  have r : Run B (oneAnchorFromLabels D F input) σ τ _ := hr.seq ht
  exact ⟨τ,r,hBank,hBudget,Frame.of_run r⟩

#print axioms oneAnchor_run
#print axioms oneAnchorFromLabels_run
end EvenTI.P13Spectral
