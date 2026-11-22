import EvenP12ComparePrepFour

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def fixedMetadataCap (F : FieldPresentation K) : ℕ :=
  F.e+1+16*(F.e+1)+(F.p+1)^2+(F.p+1)^(F.e+1)+Fintype.card K+16

def comparisonWordBudget (F : FieldPresentation K) (L : ℕ) : ℕ :=
  pairCutSlotCount.value L*(F.e+1)+2*L+fixedMetadataCap F

noncomputable def comparisonWordPoly (F : FieldPresentation K) : Polynomial ℕ :=
  pairCutSlotCount.rangePoly * Polynomial.C (F.e+1) +
    Polynomial.C 2 * Polynomial.X + Polynomial.C (fixedMetadataCap F)

theorem comparisonWordPoly_eval (F : FieldPresentation K) (L : ℕ) :
    (comparisonWordPoly F).eval L = comparisonWordBudget F L := by
  simp [comparisonWordPoly,comparisonWordBudget,Address.evaluate_rangePoly]

/-- Allocate the four complete live kernels using a single explicit polynomial
in the original input bits. The machine consumes the exact raw input tape. -/
theorem comparisonFourBinarySized_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (other : String → Nat)
    (ha : 2 ≤ a) (hn : 2 ≤ n) :
    let m := n^a
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (comparisonWordPoly F).eval L
    ∃ τ, Run B (comparisonFourReadyProgram D F)
        (initEnv (comparisonInitExt F (pairCutSlotCount.value m) w.length other) (w.length::w)) τ
        (40*(L+1)+3*F.e+26+4*oneCutCostBound F L) ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars shapePower.out = m ∧ τ.arrs rawPairIO.array = w ∧ τ.vars qN.WS = F.e+1 ∧
      val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      (∀ j : Fin 4, InstalledCut F T S j τ) ∧ τ.inp = [] ∧ τ.out = [] := by
  dsimp only
  rw [comparisonWordPoly_eval]
  let m := n^a
  let w := comparisonInput D T S
  let L := bitSize w
  let B := comparisonWordBudget F L
  have hLen : w.length ≤ L := Lax51Proofs.Encoding.length_le_bitSize w
  have hN : n ≤ n^(a+a) := by
    simpa using Nat.pow_le_pow_right (by omega : 0<n) (by omega : 1≤a+a)
  have hD : a+a ≤ n^(a+a) :=
    (Nat.lt_two_pow_self (n := a+a)).le.trans (Nat.pow_le_pow_left hn _)
  have hRaw : w.length = 2+n^(a+a)+n^(a+a) := by
    simp [w,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have hm : m ≤ L := (Nat.pow_le_pow_right (by omega : 0 < n) (show a ≤ a+a by omega)).trans (by omega)
  have hS : pairCutSlotCount.value m ≤ pairCutSlotCount.value L :=
    Address.monotone_value pairCutSlotCount hm
  have ha' : pairCutSlotCount.value L ≤ pairCutSlotCount.value L*(F.e+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hfm : pairCutSlotCount.value m*F.e ≤ pairCutSlotCount.value L*F.e :=
    Nat.mul_le_mul_right _ hS
  have hfit : pairCutSlotCount.value m + m+m+10 < B := by
    unfold B comparisonWordBudget fixedMetadataCap
    omega
  have hInp : w.length < B := by unfold B comparisonWordBudget fixedMetadataCap; omega
  have hMem : F.e+1+pairCutSlotCount.value m*F.e < B := by
    unfold B comparisonWordBudget fixedMetadataCap
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hWords : ∀ x ∈ w, x<B := by
    have hQ : Fintype.card K < B := by unfold B comparisonWordBudget fixedMetadataCap; omega
    have hW (U : Tensor K (a+a) n) (x : ℕ) (hx : x ∈ tensorWords D U) : x < B := by
      rw [tensorWords_eq_inputCoordOrder] at hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact (D _).isLt.trans hQ
    intro x hx
    simp only [w,comparisonInput,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hx
    rcases hx with rfl | rfl | ht | hs
    · unfold B comparisonWordBudget fixedMetadataCap; omega
    · unfold B comparisonWordBudget fixedMetadataCap; omega
    · exact hW T x ht
    · exact hW S x hs
  obtain ⟨τ,hRun,hSlots,hM,hBank,hWS,hZero,hCuts,hi,ho⟩ :=
    comparisonFourReadyProgram_run D F T S other ha hn (B:=B)
      hInp hWords hMem
      (by unfold B comparisonWordBudget fixedMetadataCap; omega)
      (by unfold B comparisonWordBudget fixedMetadataCap; omega)
      (by unfold B comparisonWordBudget fixedMetadataCap; omega)
      (fun i t r hr => (kernelBindings_le m t i (pow_pos (by omega) _) r hr).trans_lt (by omega))
      (by unfold B comparisonWordBudget fixedMetadataCap; omega)
      (by unfold B comparisonWordBudget fixedMetadataCap; omega) hfit
  exact ⟨τ,hRun.mono (comparisonFourReadyCost_le D F T S (by omega) hLen),hSlots,hM,hBank,hWS,hZero,hCuts,hi,ho⟩

#print axioms comparisonFourBinarySized_run
end EvenTI.P12ComparePrep
