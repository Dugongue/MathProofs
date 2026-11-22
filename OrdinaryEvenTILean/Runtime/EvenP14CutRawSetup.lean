import EvenP14CutScanSetup
import EvenP14CutRawBudget

set_option autoImplicit false
set_option maxHeartbeats 1850000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutChoiceExt (L : ℕ) (name : String) : ℕ := if name=coefficientBank then L else 0

noncomputable def rawCutSetupProgram (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (comparisonFourReadyProgram D F) (cutSetupProgram j)

def rawCutSetupBitCost (F : FieldPresentation K) (L : ℕ) (j : Fin 4) : ℕ :=
  40*(L+1)+3*F.e+26+4*oneCutCostBound F L+cutSetupCost j

theorem cutInput_side_bounds (D : FieldEncoding K) {a n : ℕ}
    (T S : Tensor K (a+a) n) (ha : 1 ≤ a) (hn : 2 ≤ n) :
    let L := bitSize (comparisonInput D T S)
    n ≤ n^a ∧ n^a ≤ L ∧ a ≤ L := by
  let w := comparisonInput D T S
  have hW : w.length ≤ bitSize w := Lax51Proofs.Encoding.length_le_bitSize w
  have hLen : w.length = 2+n^(a+a)+n^(a+a) := by
    simp [w,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have hN : n ≤ n^a := by
    simpa using Nat.pow_le_pow_right (by omega : 0<n) ha
  have hA : a ≤ n^a := (Nat.lt_two_pow_self (n := a)).le.trans (Nat.pow_le_pow_left hn _)
  have hM : n^a ≤ n^(a+a) := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hN,by change n^a≤bitSize w; omega,by change a≤bitSize w; omega⟩

/-- Raw input through four checked bases and the selected scan initializer,
with capacity and word bounds derived from original comparison bits. -/
theorem rawCutSetupProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (j : Fin 4) (ha : 2 ≤ a) (hn : 2 ≤ n) :
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (cutWordPoly F).eval L
    let m := n^a
    let Sn := pairCutSlotCount.value m
    let z := constantsBase.value m
    let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
    ∃ τ, Run B (rawCutSetupProgram D F j) (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L))
        (w.length::w)) τ (rawCutSetupBitCost F L j) ∧
      CutVisitInput (B := B) (Sn := Sn) F τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      (∀ i : Fin 4, InstalledCut F T S i τ) ∧ τ.vars (nullityAt j)=c ∧
      τ.vars cutChoiceBudget=n ∧ τ.vars qN.WS=F.e+1 ∧
      τ.arrs rawPairIO.array=w ∧ τ.inp=[] ∧ τ.out=[] ∧
      Sn+m+m+10<B ∧ (m+Fintype.card K+1)*(m+Fintype.card K+1)<B := by
  dsimp only
  let w := comparisonInput D T S
  let L := bitSize w
  let B := (cutWordPoly F).eval L
  let m := n^a
  let Sn := pairCutSlotCount.value m
  let z := constantsBase.value m
  let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
  have hBounds := cutInput_side_bounds D T S (by omega) hn
  have hFit : Sn+m+m+10<B := by
    have h : pairCutSlotCount.value m ≤ pairCutSlotCount.value L :=
      Address.monotone_value pairCutSlotCount hBounds.2.1
    have hh : pairCutSlotCount.value L ≤ pairCutSlotCount.value L*(F.e+1) := by
      rw [Nat.mul_add,Nat.mul_one]; omega
    unfold B Sn
    rw [cutWordPoly_eval]
    unfold cutWordBudget comparisonWordBudget fixedMetadataCap
    have hm : m≤L := hBounds.2.1
    omega
  have hC : c ≤ m := kernelFinrank_le _
  obtain ⟨ρ,hρ,hS,hm,hRaw,hABI,hZero,hCuts,hIn,hOut⟩ :=
    comparisonFourCutSized_run D F T S (cutChoiceExt L) ha hn
  have hLen : m ≤ (ρ.arrs coefficientBank).length := by
    rw [coefficientBank_length_frame hρ]
    have hBank : (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L))
      (w.length::w)).arrs coefficientBank = List.replicate L 0 := by
      simp [initEnv,comparisonInitExt,canonicalInitExt,canonical,rawPairIO,cutChoiceExt,coefficientBank]
    rw [hBank,List.length_replicate]
    exact hBounds.2.1
  have hh : ρ.arrs rawPairIO.array = (a+a)::n::(tensorWords D T ++ tensorWords D S) := by
    simpa [comparisonInput,w,List.append_assoc] using hRaw
  obtain ⟨τ,hτ,hW,hBudget,hNull,hV,hVars,hArr,hi,ho⟩ :=
    cutSetupProgram_run F j _ _ (pow_pos (by omega) _) hBounds.1 hC hFit hS hm
      (hCuts j).nullity hh hLen hZero
  have hInputFresh (v : String) (hv : v ∉ (cutSetupBindings j).map Prod.fst) :
      τ.vars v=ρ.vars v := hVars v hv
  have hABI' : τ.vars qN.WS=F.e+1 := by
    rw [hInputFresh _ (by fin_cases j <;> decide),hABI]
  refine ⟨τ,hρ.seq hτ,hW,?_,hNull,hBudget,hABI',?_,hi.trans hIn,ho.trans hOut,
    hFit,cutWordBudget_choice F hBounds.2.1⟩
  · intro i
    have hN : τ.vars (nullityAt i)=ρ.vars (nullityAt i) := hInputFresh _ (by fin_cases i <;> fin_cases j <;> decide)
    refine ⟨hN.trans (hCuts i).nullity,?_⟩
    rw [hN]
    obtain ⟨xs,hInd,hSpan,hAt⟩ := (hCuts i).basis
    exact ⟨xs,hInd,hSpan,fun v x => (hV _).trans (hAt v x)⟩
  · rw [hArr,hRaw]

#print axioms rawCutSetupProgram_run
end EvenTI.P12ComparePrep
