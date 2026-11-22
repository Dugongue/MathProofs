import EvenP12ComparePrepBounds

import EvenP12ComparePrepCut

import EvenP12ComparePrepInit

import Mathproof.Meta.P15DecideIMPCost20261007


set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPProgram20261007
open Mathproof.P15DecideIMPKerBasis20261007
open Mathproof.P15DecideIMPRowKer20261007
open Mathproof.P15DecideIMPEGens20261007 (hmdg ev_var ev_add ev_mul ev_div)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Slots above the augmented working matrix and outside the chosen output
interval are unaffected by loading and eliminating one cut. -/
def OutsidePlacedCut (nr d AM OUT Z Sn j : ℕ) : Prop :=
  j < Sn ∧ AM+d*(nr+d) ≤ j ∧ (j < OUT ∨ OUT+d*d ≤ j) ∧ j ≠ Z+2 ∧ j ≠ Z+3

private theorem transposeIndex_lt {rows columns k : ℕ} (hr : 0 < rows)
    (hk : k < rows * columns) : transposeIndex rows columns k < rows * columns := by
  have hq : k / rows < columns := (Nat.div_lt_iff_lt_mul hr).2 (by rwa [Nat.mul_comm])
  have hrem : k % rows < rows := Nat.mod_lt _ hr
  calc
    transposeIndex rows columns k < (k % rows + 1) * columns := by
      rw [Nat.add_mul, one_mul]
      unfold transposeIndex
      omega
    _ ≤ rows * columns := Nat.mul_le_mul_right _ hrem

private theorem transposeIndex_pair {rows columns : ℕ} (hr : 0 < rows)
    (i : Fin columns) (j : Fin rows) :
    transposeIndex rows columns (i.val*rows+j.val) = j.val*columns+i.val := by
  have hSum : i.val*rows+j.val = j.val+i.val*rows := Nat.add_comm _ _
  rw [transposeIndex,hSum,Nat.add_mul_mod_self_right,Nat.add_mul_div_right _ _ hr,
    Nat.mod_eq_of_lt j.isLt,Nat.div_eq_of_lt j.isLt,Nat.zero_add]

private theorem transposeAddress_eval {B rows columns k off : ℕ} {σ : Env}
    (hr : 0 < rows) (hc : 0 < columns) (hk : k < rows*columns) (hb : off+rows*columns < B)
    (hidx : σ.vars loadIndex = k) (hrow : σ.vars originalRows = rows)
    (hcol : σ.vars originalColumns = columns) (hoff : σ.vars inputBase = off) :
    transposeAddress.evalB B σ = some (off+transposeIndex rows columns k) := by
  have hrB : rows ≤ rows*columns := Nat.le_mul_of_pos_right _ hc
  have hcB : columns ≤ rows*columns := Nat.le_mul_of_pos_left _ hr
  have hq := Nat.div_le_self k rows
  have hqr := Nat.div_mul_le_self k rows
  have ht := transposeIndex_lt hr hk
  unfold transposeIndex at ht
  have ek := ev_var hidx (show k < B by omega)
  have er := ev_var hrow (show rows < B by omega)
  have ec := ev_var hcol (show columns < B by omega)
  have eo := ev_var hoff (show off < B by omega)
  have eq := ev_div ek er (show k / rows < B by omega)
  have em := ev_sub ek (ev_mul eq er (show k / rows * rows < B by omega)) (by omega)
  rw [hmdg] at em
  unfold transposeAddress transposeIndex
  have hsumB : k % rows * columns + k / rows < B := ht.trans (by omega)
  have hmulB : k % rows * columns < B :=
    (Nat.le_add_right _ _).trans_lt hsumB
  have hoffB := (Nat.add_lt_add_left ht off).trans hb
  exact ev_add eo (ev_add (ev_mul em ec hmulB) eq hsumB) hoffB

theorem comparisonRightKernel_preserving_run (D : FieldEncoding K) (FP : FieldPresentation K)
    {a b n AM OUT Z Sn B RB : ℕ} (T S : Tensor K (a+b) n) (target : Bool)
    (bank : String) (L : KBLay (n^a) (n^b) AM OUT Z Sn B) {σ : Env}
    (hS : Slots FP canonical qN.WS Sn B σ)
    (hBankMem : bank ≠ canonical.mem) (hBank : σ.arrs bank = comparisonInput D T S)
    (hField : Fintype.card K ≤ B) (hB : 1 < B)
    (hOffset : tensorOffset (n^(a+b)) target + n^(a+b) < B)
    (hBase : σ.vars loadBase = RB) (hLength : σ.vars loadLength = n^(a+b))
    (hInputBase : σ.vars inputBase = tensorOffset (n^(a+b)) target)
    (hR : σ.vars tNR = n^a) (hD : σ.vars tD = n^b) (hRBv : σ.vars tRB = RB)
    (hAM : σ.vars kAM = AM) (hOUT : σ.vars kOUT = OUT)
    (hZ : σ.vars dZ = Z) (hO : σ.vars rOs = Z + 1)
    (hT : σ.vars dT = Z + 2) (hU : σ.vars dU = Z + 3)
    (hws : σ.vars qN.WS = FP.e + 1)
    (hlo : (n^b + 1) * XBs (n^a) (n^b) ≤ RB) (hhi : RB + n^(a+b) ≤ AM)
    (hz : val FP canonical qN.WS σ Z = 0)
    (ho : val FP canonical qN.WS σ (Z + 1) = 1) :
    ∃ τ, Run B (comparisonRightKernel D FP bank) σ τ
      (encodedBankLoadCost FP contiguousAddress (n^(a+b)) + rkCost FP (n^a) (n^b)) ∧
      Slots FP canonical qN.WS Sn B τ ∧
      τ.vars kK = Module.finrank K (flatten (if target then S else T)).mulVecLin.ker ∧
      (∃ xs : Fin (τ.vars kK) → Coord b n → K,
        LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = (flatten (if target then S else T)).mulVecLin.ker ∧
        ∀ (k : Fin (τ.vars kK)) (j : Coord b n),
          val FP canonical qN.WS τ (OUT+(k.val*n^b+(inputCoordOrder n b j).val)) = xs k j) ∧
      (∀ s, OutsidePlacedCut (n^a) (n^b) AM OUT Z Sn s →
        val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let U := if target then S else T
  obtain ⟨ρ,hr,hslots,hmatrix,houtside,hrvars,_,hi₀,ho₀⟩ :=
    contiguousBankLoad_run D FP bank (flatEntry U) hBankMem hS hField hB (by omega)
      hOffset hBase hLength hInputBase (show RB+n^(a+b) ≤ Sn by
        have h₁ := L.am_out; have h₂ := L.out_z; have h₃ := L.z_s; omega)
      (fun k hk => by rw [hBank]; exact comparisonInput_getElem?_flat D T S target k hk)
  have hρ (r : String) (hr : ¬loadChanges r) : ρ.vars r = σ.vars r := hrvars r hr
  have hfit : RB + n^a * n^b ≤ AM := by rwa [← pow_add]
  have houtside₀ : RB + n^(a+b) ≤ Z := by
    have h₁ := L.am_out; have h₂ := L.out_z; omega
  have hrows (i : Fin (n^a)) (j : Fin (n^b)) :
      val FP canonical qN.WS ρ (RB+(i.val*n^b+j.val)) =
        flatten U ((inputCoordOrder n a).symm i) ((inputCoordOrder n b).symm j) := by
    have hlt : i.val*n^b+j.val < n^(a+b) := by
      rw [pow_add]
      calc i.val*n^b+j.val < (i.val+1)*n^b := by rw [Nat.succ_mul]; omega
        _ ≤ n^a*n^b := Nat.mul_le_mul_right _ i.isLt
    rw [hmatrix _ hlt,flatEntry_index]
  let M := flatten U
  let rOrder := inputCoordOrder n a
  let cOrder := inputCoordOrder n b
  obtain ⟨τ,hRun,hS',_,⟨xs,hBankAt,hInd,hSpan⟩,hFrame,_,hi,ho'⟩ :=
    rk_run FP L (kernelInputMatrix M rOrder cOrder) hslots
    ((hρ _ (by decide)).trans hR) ((hρ _ (by decide)).trans hD)
    ((hρ _ (by decide)).trans hRBv) ((hρ _ (by decide)).trans hAM)
    ((hρ _ (by decide)).trans hOUT) ((hρ _ (by decide)).trans hZ)
    ((hρ _ (by decide)).trans hO) ((hρ _ (by decide)).trans hT)
    ((hρ _ (by decide)).trans hU) ((hρ _ (by decide)).trans hws) hlo hfit hrows
    ((houtside Z (Or.inr houtside₀)).trans hz)
    ((houtside (Z+1) (Or.inr (by omega))).trans ho)
  obtain ⟨hI,hsp⟩ := kernelInputMatrix_basis M rOrder cOrder xs hInd hSpan
  let e := frameFromVectors M.mulVecLin (fun i j => xs i (cOrder j)) hI hsp
  have hd : τ.vars kK = Module.finrank K M.mulVecLin.ker := by simpa using e.finrank_eq
  refine ⟨τ,hr.seq hRun,hS',hd,
    ⟨fun i j => xs i (cOrder j),hI,hsp,fun i j => hBankAt i (cOrder j)⟩,
    ?_,hi.trans hi₀,ho'.trans ho₀⟩
  intro s hs
  rcases hs with ⟨hSn,hAM,hOut,hZ₂,hZ₃⟩
  exact (hFrame s hSn (by omega)
    (hOut.elim (fun h => Or.inr (Or.inl ⟨hAM,h⟩)) (fun h => Or.inr (Or.inr h)))
    hZ₂ hZ₃).trans (houtside s (Or.inr (by omega)))

theorem comparisonLeftKernel_preserving_run (D : FieldEncoding K) (FP : FieldPresentation K)
    {a b n AM OUT Z Sn B RB : ℕ} (hn : 0 < n) (T S : Tensor K (a+b) n) (target : Bool)
    (bank : String) (L : KBLay (n^b) (n^a) AM OUT Z Sn B) {σ : Env}
    (hS : Slots FP canonical qN.WS Sn B σ)
    (hBankMem : bank ≠ canonical.mem) (hBank : σ.arrs bank = comparisonInput D T S)
    (hField : Fintype.card K ≤ B) (hB : 1 < B)
    (hOffset : tensorOffset (n^(a+b)) target + n^(a+b) < B)
    (hBase : σ.vars loadBase = RB) (hLength : σ.vars loadLength = n^(a+b))
    (hInputBase : σ.vars inputBase = tensorOffset (n^(a+b)) target)
    (hM : σ.vars originalRows = n^a) (hN : σ.vars originalColumns = n^b)
    (hR : σ.vars tNR = n^b) (hD : σ.vars tD = n^a) (hRBv : σ.vars tRB = RB)
    (hAM : σ.vars kAM = AM) (hOUT : σ.vars kOUT = OUT)
    (hZ : σ.vars dZ = Z) (hO : σ.vars rOs = Z + 1)
    (hT : σ.vars dT = Z + 2) (hU : σ.vars dU = Z + 3)
    (hws : σ.vars qN.WS = FP.e + 1)
    (hlo : (n^a + 1) * XBs (n^b) (n^a) ≤ RB) (hhi : RB + n^(a+b) ≤ AM)
    (hz : val FP canonical qN.WS σ Z = 0)
    (ho : val FP canonical qN.WS σ (Z + 1) = 1) :
    ∃ τ, Run B (comparisonLeftKernel D FP bank) σ τ
      (encodedBankLoadCost FP transposeAddress (n^(a+b)) + rkCost FP (n^b) (n^a)) ∧
      Slots FP canonical qN.WS Sn B τ ∧
      τ.vars kK = Module.finrank K (leftCutKernel (if target then S else T)).ker ∧
      (∃ xs : Fin (τ.vars kK) → Coord a n → K,
        LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = (leftCutKernel (if target then S else T)).ker ∧
        ∀ (k : Fin (τ.vars kK)) (j : Coord a n),
          val FP canonical qN.WS τ (OUT+(k.val*n^a+(inputCoordOrder n a j).val)) = xs k j) ∧
      (∀ s, OutsidePlacedCut (n^b) (n^a) AM OUT Z Sn s →
        val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let U := if target then S else T
  let offset := tensorOffset (n^(a+b)) target
  let index := transposeIndex (n^a) (n^b)
  have hPow : n^a*n^b = n^(a+b) := (pow_add n a b).symm
  have hp : 0 < n^a := pow_pos hn _
  have haddr (ρ : Env) (k : ℕ) (hk : ρ.vars loadIndex = k)
      (hs : ∀ r, ¬loadChanges r → ρ.vars r = σ.vars r) (hkl : k < n^(a+b)) :
      transposeAddress.evalB B ρ = some (offset+index k) := by
    exact transposeAddress_eval hp (pow_pos hn _) (by rwa [hPow]) (by rwa [hPow])
      hk ((hs _ (by decide)).trans hM) ((hs _ (by decide)).trans hN)
      ((hs _ (by decide)).trans hInputBase)
  have hf : RB+n^(a+b) ≤ Sn := by
    have h₁ := L.am_out; have h₂ := L.out_z; have h₃ := L.z_s; omega
  obtain ⟨ρ,hr,hslots,hmatrix,houtside,hrvars,_,hi₀,ho₀⟩ :=
    encodedBankLoad_run D FP bank transposeAddress (fun k => offset+index k)
      (fun k => flatEntry U (index k)) hBankMem hS hField hB (by omega)
      hBase hLength hf haddr (fun k hk => by
        rw [hBank]
        exact comparisonInput_getElem?_flat D T S target (index k)
          (by have he := transposeIndex_lt hp (show k<n^a*n^b by rwa [hPow]); rwa [hPow] at he))
  have hρ (r : String) (hr : ¬loadChanges r) : ρ.vars r = σ.vars r := hrvars r hr
  have hfit : RB + n^b * n^a ≤ AM := by rwa [Nat.mul_comm (n^b) (n^a), hPow]
  have houtside₀ : RB + n^(a+b) ≤ Z := by
    have h₁ := L.am_out; have h₂ := L.out_z; omega
  let M := (flatten U).transpose
  let rOrder := inputCoordOrder n b
  let cOrder := inputCoordOrder n a
  have hrows (i : Fin (n^b)) (j : Fin (n^a)) :
      val FP canonical qN.WS ρ (RB+(i.val*n^a+j.val)) = M (rOrder.symm i) (cOrder.symm j) := by
    have hlt : i.val*n^a+j.val < n^(a+b) := by
      rw [← hPow,Nat.mul_comm (n^a) (n^b)]
      calc i.val*n^a+j.val < (i.val+1)*n^a := by rw [Nat.succ_mul]; omega
        _ ≤ n^b*n^a := Nat.mul_le_mul_right _ i.isLt
    rw [hmatrix _ hlt]
    change flatEntry U (transposeIndex (n^a) (n^b) (i.val*n^a+j.val)) = _
    exact (congrArg (flatEntry U) (transposeIndex_pair hp i j)).trans (flatEntry_index U j i)
  obtain ⟨τ,hRun,hS',_,⟨xs,hBankAt,hInd,hSpan⟩,hFrame,_,hi,ho'⟩ :=
    rk_run FP L (kernelInputMatrix M rOrder cOrder) hslots
      ((hρ _ (by decide)).trans hR) ((hρ _ (by decide)).trans hD)
      ((hρ _ (by decide)).trans hRBv) ((hρ _ (by decide)).trans hAM)
      ((hρ _ (by decide)).trans hOUT) ((hρ _ (by decide)).trans hZ)
      ((hρ _ (by decide)).trans hO) ((hρ _ (by decide)).trans hT)
      ((hρ _ (by decide)).trans hU) ((hρ _ (by decide)).trans hws) hlo hfit hrows
      ((houtside Z (Or.inr houtside₀)).trans hz)
      ((houtside (Z+1) (Or.inr (by omega))).trans ho)
  obtain ⟨hI,hsp⟩ := kernelInputMatrix_basis M rOrder cOrder xs hInd hSpan
  let e := frameFromVectors M.mulVecLin (fun i j => xs i (cOrder j)) hI hsp
  have hd : τ.vars kK = Module.finrank K M.mulVecLin.ker := by simpa using e.finrank_eq
  refine ⟨τ,hr.seq hRun,hS',hd,
    ⟨fun i j => xs i (cOrder j),hI,hsp,fun i j => hBankAt i (cOrder j)⟩,
    ?_,hi.trans hi₀,ho'.trans ho₀⟩
  intro s hs
  rcases hs with ⟨hSn,hAM,hOut,hZ₂,hZ₃⟩
  exact (hFrame s hSn (by omega)
    (hOut.elim (fun h => Or.inr (Or.inl ⟨hAM,h⟩)) (fun h => Or.inr (Or.inr h)))
    hZ₂ hZ₃).trans (houtside s (Or.inr (by omega)))


#print axioms comparisonRightKernel_preserving_run
#print axioms comparisonLeftKernel_preserving_run
end EvenTI.P12ComparePrep


set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites run_frame)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15FactorIMP20261007 (rCv)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15DecideIMPRowKer20261007 (rkProg)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def nullityAt (i : Fin 4) : String := "even_compare_nullity_" ++ toString i.val

theorem nullityAt_injective : Function.Injective nullityAt := by decide

private theorem dispatch_arrays (xs : List (Nat × Nat)) :
    arrayWrites (literalDispatch xs) = ∅ := by
  induction xs with
  | nil => simp [literalDispatch,arrayWrites]
  | cons x xs ih => rcases x with ⟨a,b⟩; simp [literalDispatch,arrayWrites,ih]

private theorem dispatch_scalars (xs : List (Nat × Nat)) :
    scalarWrites (literalDispatch xs) = {rCv} := by
  induction xs with
  | nil => simp [literalDispatch,scalarWrites]
  | cons x xs ih => rcases x with ⟨a,b⟩; simp [literalDispatch,scalarWrites,ih]

private theorem assignList_arrays (xs : List (String × Expr)) :
    arrayWrites (commands xs) = ∅ := by
  induction xs with
  | nil => simp [commands,arrayWrites]
  | cons x xs ih => simp [commands,arrayWrites,ih]

private theorem assignList_scalars (xs : List (String × Expr)) (v : String)
    (h : ∀ x ∈ xs, v ≠ x.1) : v ∉ scalarWrites (commands xs) := by
  induction xs with
  | nil => simp [commands,scalarWrites]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [commands,scalarWrites,hh,ht]

theorem runOneCut_rawBank_preserved (D : FieldEncoding K) (F : FieldPresentation K)
    (left target : Bool) (idx : Fin 4) {B c : Nat} {σ τ : Env}
    (h : Run B (runOneCut D F left target idx) σ τ c) :
    τ.arrs rawPairIO.array = σ.arrs rawPairIO.array := by
  have hDigit : rawPairIO.array ∉
      arrayWrites Mathproof.P15GEDigitLoad20261007.prog := by decide
  have hKernel : rawPairIO.array ∉ arrayWrites rkProg := by decide
  apply (run_frame h).2.1
  cases left <;>
    simp [runOneCut,oneCutSetup,comparisonLeftKernel,comparisonRightKernel,
      kernelAssignment,encodedBankLoad,encodedBankLoadStep,installEncodedDigit,
      arrayWrites,dispatch_arrays,assignList_arrays,hDigit,hKernel]

theorem runOneCut_register_preserved (D : FieldEncoding K) (F : FieldPresentation K)
    (left target : Bool) (idx : Fin 4) {B c : Nat} {σ τ : Env}
    (h : Run B (runOneCut D F left target idx) σ τ c)
    (v : String) (hv : v = shapePower.out ∨ v = qN.WS ∨ ∃ j : Fin 4, v = nullityAt j) :
    τ.vars v = σ.vars v := by
  have allRegs {P : String → Prop} (p : P shapePower.out) (q : P qN.WS)
      (j : ∀ i : Fin 4, P (nullityAt i)) : P v := by
    rcases hv with rfl | rfl | ⟨i,rfl⟩
    · exact p
    · exact q
    · exact j i
  have hdr : v ≠ rCv ∧ v ≠ destination ∧ v ≠ inputLabel ∧ v ≠ loadIndex := by
    exact allRegs (P := fun x => x ≠ rCv ∧ x ≠ destination ∧ x ≠ inputLabel ∧ x ≠ loadIndex) (by decide) (by decide) (by decide)
  have hDigit : v ∉ scalarWrites Mathproof.P15GEDigitLoad20261007.prog := by
    exact allRegs (P := fun x => x ∉ scalarWrites Mathproof.P15GEDigitLoad20261007.prog) (by decide) (by decide) (by decide)
  have hKernel : v ∉ scalarWrites rkProg :=
    allRegs (P := fun x => x ∉ scalarWrites rkProg) (by decide) (by decide) (by decide)
  have ha : v ∉ scalarWrites (kernelAssignment target idx) := by
    apply assignList_scalars
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    simp only [kernelBindings,List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      rw [h] <;> simp only [Prod.fst]
    all_goals
      rcases hv with rfl | rfl | ⟨j,rfl⟩
      · decide
      · decide
      · fin_cases j <;> decide
  apply (run_frame h).1
  cases left <;>
    simp [runOneCut,oneCutSetup,comparisonLeftKernel,comparisonRightKernel,
      encodedBankLoad,encodedBankLoadStep,installEncodedDigit,
      scalarWrites,dispatch_scalars,hdr.1,hdr.2.1,hdr.2.2.1,hdr.2.2.2,ha,hDigit,hKernel]

#print axioms runOneCut_rawBank_preserved
#print axioms runOneCut_register_preserved
end EvenTI.P12ComparePrep



namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (install installed_arrays installed_scalar installed_slots)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB rkCost)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs KBLay kAM kOUT kK)
open Mathproof.P15FactorIMP20261007 (rCv rTd)
open Mathproof.P15RecogIMPDot20261007 (dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15GEDigitLoad20261007 (destination)
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem oneCutSetup_preserving_run (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) (idx : Fin 4) (m : Nat) {Sn B : Nat} {σ : Env}
    (hm : σ.vars shapePower.out = m) (hPos : 0 < m)
    (hS : Slots F canonical qN.WS Sn B σ) (hWS : σ.vars qN.WS = F.e+1)
    (hFits : ∀ v ∈ kernelBindings target idx, v.2.value m < B)
    (hCard : Fintype.card K ≤ B) (hO : constantsBase.value m+1 < Sn)
    (hz : val F canonical qN.WS σ (constantsBase.value m) = 0) :
    ∃ τ, Run B (oneCutSetup D F target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+installEncodedDigitCost F) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars qN.WS = F.e+1 ∧
      CutRegisters τ target idx m ∧
      val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      val F canonical qN.WS τ (constantsBase.value m+1) = 1 ∧
      (∀ j, j ≠ constantsBase.value m+1 → val F canonical qN.WS τ j = val F canonical qN.WS σ j) ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let r := kernelState target idx m σ
  have hr := kernelAssignment_run target idx m hm hPos hFits
  have hRegs := kernelState_registers σ target idx m
  obtain ⟨hS',hWS',hFrame⟩ := kernelState_slots F target idx m hS hWS
  let x := r.setVar inputLabel (D 1).val
  let y := x.setVar destination (constantsBase.value m+1)
  have r₁ : Run B (.assign inputLabel (.lit (D 1).val)) r x 2 :=
    Run.assign (evalB_lit ((D 1).isLt.trans_le hCard))
  have hOx : x.vars rOs = constantsBase.value m+1 := by
    rw [show x.vars rOs = r.vars rOs by rfl]
    exact hRegs.hO
  have r₂ : Run B (.assign destination (.var rOs)) x y 2 := by
    apply Run.assign
    rw [evalB_var_iff,hOx]
    exact ⟨rfl,hO.trans hS.slots_word⟩
  have hSy : Slots F canonical qN.WS Sn B y :=
    Slots.setVar F canonical (Slots.setVar F canonical hS' (by decide) (by decide) _)
      (by decide) (by decide) _
  obtain ⟨τ,r₃,hSτ,hOne,hOutside,hVars,hArrays,hInp,hOut⟩ :=
    installEncodedDigit_run D F (σ := y) 1 hSy hCard (by simp [y,x,show inputLabel ≠ destination by decide])
      (by simp [y]) hO
  have hKeep (v : String) (h₁ : v ≠ rCv) (h₂ : v ≠ rTd)
      (h₃ : v ≠ inputLabel) (h₄ : v ≠ destination) : τ.vars v = r.vars v := by
    rw [hVars v h₁ h₂]
    simp [y,x,h₃,h₄]
  have hFrameArr := kernelState_frame σ target idx m
  have hRun : Run B (oneCutSetup D F target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+installEncodedDigitCost F) :=
    (hr.seq (r₁.seq (r₂.seq r₃))).mono (by omega)
  refine ⟨τ,hRun,hSτ,(hKeep _ (by decide) (by decide) (by decide) (by decide)).trans hWS',
    ?_,?_,hOne,?_,?_,?_,?_⟩
  · exact ⟨(hKeep originalRows (by decide) (by decide) (by decide) (by decide)).trans hRegs.hRows,
      (hKeep originalColumns (by decide) (by decide) (by decide) (by decide)).trans hRegs.hCols,
      (hKeep tNR (by decide) (by decide) (by decide) (by decide)).trans hRegs.hNR,
      (hKeep tD (by decide) (by decide) (by decide) (by decide)).trans hRegs.hD,
      (hKeep loadBase (by decide) (by decide) (by decide) (by decide)).trans hRegs.hBase,
      (hKeep tRB (by decide) (by decide) (by decide) (by decide)).trans hRegs.hRB,
      (hKeep loadLength (by decide) (by decide) (by decide) (by decide)).trans hRegs.hLength,
      (hKeep kAM (by decide) (by decide) (by decide) (by decide)).trans hRegs.hAM,
      (hKeep kOUT (by decide) (by decide) (by decide) (by decide)).trans hRegs.hOUT,
      (hKeep inputBase (by decide) (by decide) (by decide) (by decide)).trans hRegs.hInpBase,
      (hKeep dZ (by decide) (by decide) (by decide) (by decide)).trans hRegs.hZ,
      (hKeep rOs (by decide) (by decide) (by decide) (by decide)).trans hRegs.hO,
      (hKeep dT (by decide) (by decide) (by decide) (by decide)).trans hRegs.hT,
      (hKeep dU (by decide) (by decide) (by decide) (by decide)).trans hRegs.hU⟩
  · rw [hOutside _ (by omega),show y = x.setVar destination _ from rfl,
      val_setVar F canonical (by decide),show x = r.setVar inputLabel _ from rfl,
      val_setVar F canonical (by decide)]
    exact (hFrame _).trans hz
  · intro j hj
    rw [hOutside j hj,show y = x.setVar destination _ from rfl,
      val_setVar F canonical (by decide),show x = r.setVar inputLabel _ from rfl,
      val_setVar F canonical (by decide)]
    exact hFrame j
  · intro a ha
    rw [hArrays a ha]
    exact congrFun hFrameArr.1 a
  · exact hInp.trans hFrameArr.2.1
  · exact hOut.trans hFrameArr.2.2

theorem runOneCut_preserving_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n B : Nat} (T S : Tensor K (a+a) n) (left target : Bool) (idx : Fin 4) {σ : Env}
    (hn : 0 < n) (hm : σ.vars shapePower.out = n^a)
    (hBank : σ.arrs rawPairIO.array = comparisonInput D T S)
    (hS : Slots F canonical qN.WS (pairCutSlotCount.value (n^a)) B σ)
    (hWS : σ.vars qN.WS = F.e+1)
    (hFits : ∀ v ∈ kernelBindings target idx, v.2.value (n^a) < B)
    (hCard : Fintype.card K ≤ B) (hB : 1 < B)
    (hMemory : pairCutSlotCount.value (n^a)+(n^a)+(n^a)+10 < B)
    (hInput : (comparisonInput D T S).length < B)
    (hz : val F canonical qN.WS σ (constantsBase.value (n^a)) = 0) :
    let m := n^a
    let cost := (((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+
      installEncodedDigitCost F+encodedBankLoadCost F
       (if left then transposeAddress else contiguousAddress) (n^(a+a))+rkCost F m m
    ∃ τ, Run B (runOneCut D F left target idx) σ τ cost ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars kK = Module.finrank K (selectedKernel left (if target then S else T)) ∧
      (∃ xs : Fin (τ.vars kK) → Coord a n → K, LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = selectedKernel left (if target then S else T) ∧
          ∀ i j, val F canonical qN.WS τ ((outputBase idx).value m+
              (i.val*m+(inputCoordOrder n a j).val)) = xs i j) ∧
      (∀ j, OutsidePlacedCut m m (augmentedMatrixBase.value m) ((outputBase idx).value m)
          (constantsBase.value m) (pairCutSlotCount.value m) j → j ≠ constantsBase.value m+1 →
        val F canonical qN.WS τ j = val F canonical qN.WS σ j) ∧
      τ.arrs rawPairIO.array = comparisonInput D T S ∧ τ.vars shapePower.out = m ∧
      τ.vars qN.WS = F.e+1 ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let m := n^a
  have hPos : 0 < m := pow_pos hn _
  have lay := concreteKernelLayout m idx hPos hMemory
  have hO : constantsBase.value m+1 < pairCutSlotCount.value m := by have := lay.z_s; omega
  obtain ⟨r,hr,hR,hWS',hRegs,hZ,hOne,hSlotFrame,hArr,hIn,hOut⟩ :=
    oneCutSetup_preserving_run D F target idx m hm hPos hS hWS hFits hCard hO hz
  have hMem : rawPairIO.array ≠ canonical.mem := by decide
  have hRaw : r.arrs rawPairIO.array = comparisonInput D T S :=
    (hArr _ hMem).trans hBank
  have hSquare : m*m = n^(a+a) := (pow_add ..).symm
  have hOffset : tensorOffset (n^(a+a)) target+n^(a+a) < B := by
    have hLen : (comparisonInput D T S).length = 2+n^(a+a)+n^(a+a) := by
      simp [comparisonInput,tensorWords_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hLen] at hInput
    cases target <;> simp [tensorOffset] <;> omega
  have hLoad := hRegs.hLength.trans hSquare
  have hInBase : r.vars inputBase = tensorOffset (n^(a+a)) target := by
    rw [← hSquare]
    exact hRegs.hInpBase
  have hBase : (m+1)*XBs m m ≤ rawMatrixBase.value m := by
    simp [rawMatrixBase,Address.value,rowKernelBlock_value]
  have hAm : rawMatrixBase.value m+n^(a+a) ≤ augmentedMatrixBase.value m := by
    rw [← hSquare]
    simp [augmentedMatrixBase,Address.value,cutArea_value]
  cases left
  · obtain ⟨τ,rr,hRun,hNull,hBasis,hFrame,hi,ho⟩ := comparisonRightKernel_preserving_run D F T S target
      rawPairIO.array lay hR hMem hRaw hCard hB hOffset hRegs.hBase hLoad hInBase
      hRegs.hNR hRegs.hD hRegs.hRB hRegs.hAM hRegs.hOUT hRegs.hZ hRegs.hO hRegs.hT
      hRegs.hU hWS' hBase hAm hZ hOne
    have hFull : Run B (runOneCut D F false target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+
        installEncodedDigitCost F+encodedBankLoadCost F contiguousAddress (n^(a+a))+rkCost F m m) :=
      (hr.seq rr).mono (by simp [m]; omega)
    refine ⟨τ,hFull,hRun,by exact hNull,by exact hBasis,?_,?_,?_,?_,hi.trans hIn,ho.trans hOut⟩
    · exact fun j hj hOne => (hFrame j hj).trans (hSlotFrame j hOne)
    · exact (runOneCut_rawBank_preserved D F _ target idx hFull).trans hBank
    · exact (runOneCut_register_preserved D F _ target idx hFull _ (Or.inl rfl)).trans hm
    · exact (runOneCut_register_preserved D F _ target idx hFull _ (Or.inr (Or.inl rfl))).trans hWS
  · obtain ⟨τ,rr,hRun,hNull,hBasis,hFrame,hi,ho⟩ := comparisonLeftKernel_preserving_run D F hn T S target
      rawPairIO.array lay hR hMem hRaw hCard hB hOffset hRegs.hBase hLoad hInBase
      hRegs.hRows hRegs.hCols hRegs.hNR hRegs.hD hRegs.hRB hRegs.hAM hRegs.hOUT
      hRegs.hZ hRegs.hO hRegs.hT hRegs.hU hWS' hBase hAm hZ hOne
    have hFull : Run B (runOneCut D F true target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+
        installEncodedDigitCost F+encodedBankLoadCost F transposeAddress (n^(a+a))+rkCost F m m) :=
      (hr.seq rr).mono (by simp [m]; omega)
    refine ⟨τ,hFull,hRun,by exact hNull,by exact hBasis,?_,?_,?_,?_,hi.trans hIn,ho.trans hOut⟩
    · exact fun j hj hOne => (hFrame j hj).trans (hSlotFrame j hOne)
    · exact (runOneCut_rawBank_preserved D F _ target idx hFull).trans hBank
    · exact (runOneCut_register_preserved D F _ target idx hFull _ (Or.inl rfl)).trans hm
    · exact (runOneCut_register_preserved D F _ target idx hFull _ (Or.inr (Or.inl rfl))).trans hWS

#print axioms oneCutSetup_preserving_run
#print axioms runOneCut_preserving_run
end EvenTI.P12ComparePrep


set_option maxHeartbeats 1500000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical arrayWrites run_frame)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPKerBasis20261007 (kK)
open Mathproof.P15DecideIMPRowKer20261007 (rkCost)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def leftOf (i : Fin 4) : Bool := decide (i.val % 2 = 0)
def targetOf (i : Fin 4) : Bool := decide (2 ≤ i.val)

noncomputable def actualCutCost (F : FieldPresentation K) (i : Fin 4) (m : ℕ) : ℕ :=
  ((kernelBindings (targetOf i) i).map fun v => v.2.expr.size+1).sum+5+
    installEncodedDigitCost F+encodedBankLoadCost F
      (if leftOf i then transposeAddress else contiguousAddress) (m*m)+rkCost F m m+2

noncomputable def allCutProgram (D : FieldEncoding K) (F : FieldPresentation K) : ℕ → Com
  | 0 => .skip
  | i+1 =>
    if hi : i < 4 then
      let j : Fin 4 := ⟨i,hi⟩
      .seq (allCutProgram D F i)
        (.seq (runOneCut D F (leftOf j) (targetOf j) j) (.assign (nullityAt j) (.var kK)))
    else allCutProgram D F i

noncomputable def allCutCost (F : FieldPresentation K) (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => if hi : i < 4 then allCutCost F m i + actualCutCost F ⟨i,hi⟩ m
      else allCutCost F m i

structure InstalledCut {a n : Nat} (F : FieldPresentation K)
    (T S : Tensor K (a+a) n) (i : Fin 4) (σ : Env) : Prop where
  nullity : σ.vars (nullityAt i) =
    Module.finrank K (selectedKernel (leftOf i) (if targetOf i then S else T))
  basis : ∃ xs : Fin (σ.vars (nullityAt i)) → Coord a n → K, LinearIndependent K xs ∧
    Submodule.span K (Set.range xs) = selectedKernel (leftOf i) (if targetOf i then S else T) ∧
    ∀ h j, val F canonical qN.WS σ ((outputBase i).value (n^a)
        +(h.val*(n^a)+(inputCoordOrder n a j).val)) = xs h j

theorem outputBank_point_upper (m : ℕ) (i : Fin 4) :
    (outputBase i).value m + m*m ≤ constantsBase.value m := by
  rw [outputBase_value]
  have h := Nat.mul_le_mul_right (m*m) i.isLt
  rw [Nat.succ_mul] at h
  simp only [constantsBase,Address.value,cutArea_value]
  omega

theorem outputBank_point_outside (m : ℕ) {i j : Fin 4} (hi : i < j)
    (s : ℕ) (hs : (outputBase i).value m ≤ s)
    (ht : s < (outputBase i).value m+m*m) :
    OutsidePlacedCut m m (augmentedMatrixBase.value m) ((outputBase j).value m)
      (constantsBase.value m) (pairCutSlotCount.value m) s ∧ s ≠ constantsBase.value m+1 := by
  have hU := outputBank_point_upper m i
  have hS : constantsBase.value m < pairCutSlotCount.value m := by simp [pairCutSlotCount,Address.value]
  have hlo : augmentedMatrixBase.value m+m*(m+m) ≤ (outputBase i).value m := by
    rw [outputBase_value]
    simp only [firstOutputBase,Address.value,cutArea_value]
    ring_nf
    omega
  have hs' : s < (outputBase j).value m := by
    rw [outputBase_value] at ht ⊢
    have hM := Nat.mul_le_mul_right (m*m) (show i.val+1 ≤ j.val from hi)
    rw [Nat.succ_mul] at hM
    omega
  exact ⟨⟨by omega,by omega,Or.inl hs',by omega,by omega⟩,by omega⟩

theorem kernelFinrank_le {a n : ℕ} (V : Submodule K (Coord a n → K)) :
    Module.finrank K V ≤ n^a := by
  calc
    Module.finrank K V ≤ Module.finrank K (Coord a n → K) := Submodule.finrank_le V
    _ = n^a := by
      rw [Module.finrank_fintype_fun_eq_card, ← Fintype.card_fin (n^a)]
      exact Fintype.card_congr (inputCoordOrder n a)

theorem outputPoint_lt {m k : ℕ} (hk : k ≤ m)
    (i : Fin k) (j : Fin m) : i.val*m+j.val < m*m := by
  calc
    i.val*m+j.val < (i.val+1)*m := by rw [Nat.succ_mul]; omega
    _ ≤ m*m := Nat.mul_le_mul_right _ (i.isLt.trans_le hk)

#print axioms outputBank_point_outside
#print axioms kernelFinrank_le
end EvenTI.P12ComparePrep



set_option maxHeartbeats 1500000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPKerBasis20261007 (kK)
open Mathproof.P15DecideIMPRowKer20261007 (rkCost)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem allCutProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n B : Nat} (T S : Tensor K (a+a) n) (steps : Nat) {σ : Env}
    (hn : 0 < n) (hm : σ.vars shapePower.out = n^a)
    (hBank : σ.arrs rawPairIO.array = comparisonInput D T S)
    (hS : Slots F canonical qN.WS (pairCutSlotCount.value (n^a)) B σ)
    (hWS : σ.vars qN.WS = F.e+1)
    (hFits : ∀ (idx : Fin 4) target v, v ∈ kernelBindings target idx → v.2.value (n^a) < B)
    (hCard : Fintype.card K ≤ B) (hB : 1 < B)
    (hMemory : pairCutSlotCount.value (n^a)+(n^a)+(n^a)+10 < B)
    (hInput : (comparisonInput D T S).length < B)
    (hz : val F canonical qN.WS σ (constantsBase.value (n^a)) = 0) :
    let m := n^a
    ∃ τ, Run B (allCutProgram D F steps) σ τ (allCutCost F m steps) ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars shapePower.out = m ∧ τ.arrs rawPairIO.array = comparisonInput D T S ∧
      τ.vars qN.WS = F.e+1 ∧ val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      (∀ j : Fin 4, j.val < steps → InstalledCut F T S j τ) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  dsimp only
  let m := n^a
  have hSquare : m*m = n^(a+a) := (pow_add ..).symm
  induction steps with
  | zero =>
    refine ⟨σ,Run.skip,hS,hm,hBank,hWS,hz,?_,rfl,rfl⟩
    intro j hj
    exact (Nat.not_lt_zero _ hj).elim
  | succ steps ih =>
    obtain ⟨ρ,r₀,hS₀,hm₀,hBank₀,hWS₀,hz₀,hOld,hin₀,hout₀⟩ := ih
    by_cases hI : steps < 4
    · let i : Fin 4 := ⟨steps,hI⟩
      obtain ⟨υ,r₁,hS₁,hK,hNew,hFrame,hBank₁,hm₁,hWS₁,hin₁,hout₁⟩ :=
        runOneCut_preserving_run D F T S (leftOf i) (targetOf i) i hn hm₀ hBank₀
          hS₀ hWS₀ (hFits i _) hCard hB hMemory hInput hz₀
      let τ := υ.setVar (nullityAt i) (υ.vars kK)
      have hk : υ.vars kK ≤ m := by rw [hK]; exact kernelFinrank_le _
      have hbK : υ.vars kK < B := by omega
      have r₂ : Run B (.assign (nullityAt i) (.var kK)) υ τ 2 :=
        Run.assign (evalB_var hbK)
      have r : Run B (allCutProgram D F (steps+1)) σ τ (allCutCost F m (steps+1)) := by
        rw [allCutProgram,dif_pos hI,allCutCost,dif_pos hI]
        simpa only [actualCutCost, hSquare, i] using (r₀.seq (r₁.seq r₂))
      have hNames : ∀ j : Fin 4, nullityAt j ∉ regNames canonical ∧
          nullityAt j ≠ qN.WS ∧ nullityAt j ≠ shapePower.out := by decide
      have hVar := hNames i
      have vFrame (j : Nat) :
          val F canonical qN.WS τ j = val F canonical qN.WS υ j :=
        val_setVar F canonical hVar.2.1 υ _ j
      have hPos : 0 < m := pow_pos hn _
      have hiLay := concreteKernelLayout m i hPos hMemory
      have hZOut : OutsidePlacedCut m m (augmentedMatrixBase.value m) ((outputBase i).value m)
          (constantsBase.value m) (pairCutSlotCount.value m) (constantsBase.value m) := by
        refine ⟨(show constantsBase.value m < constantsBase.value m+4 by omega).trans_le hiLay.z_s,
          hiLay.am_out.trans ((Nat.le_add_right _ _).trans hiLay.out_z),
          Or.inr hiLay.out_z,by omega,by omega⟩
      have hZ : val F canonical qN.WS τ (constantsBase.value m) = 0 := by
        exact (vFrame _).trans ((hFrame _ hZOut (Nat.ne_of_lt (Nat.lt_succ_self (constantsBase.value (n^a))))).trans hz₀)
      refine ⟨τ,r,Slots.setVar F canonical hS₁ hVar.1 hVar.2.1 _,
        ?_,hBank₁,?_,hZ,?_,hin₁.trans hin₀,hout₁.trans hout₀⟩
      · simpa [τ,Ne.symm hVar.2.2] using hm₁
      · simpa [τ,Ne.symm hVar.2.1] using hWS₁
      · intro j hj
        by_cases hji : j = i
        · subst j
          have hEq : τ.vars (nullityAt i) = υ.vars kK := by simp [τ]
          refine ⟨hEq.trans hK,?_⟩
          rw [hEq]
          obtain ⟨xs,hI,hSpan,hAt⟩ := hNew
          refine ⟨xs,hI,hSpan,?_⟩
          intro u v
          exact (vFrame _).trans (hAt u v)
        · have hj' : j < i := by
            change j.val < steps
            have hn : j.val ≠ steps := fun h => hji (Fin.ext h)
            omega
          obtain ⟨hOldDim,hOldBasis⟩ := hOld j hj'
          have hPres : υ.vars (nullityAt j) = ρ.vars (nullityAt j) :=
            runOneCut_register_preserved D F (leftOf i) (targetOf i) i r₁ (nullityAt j)
              (Or.inr (Or.inr ⟨j,rfl⟩))
          have hSame : τ.vars (nullityAt j) = ρ.vars (nullityAt j) := by
            simp [τ,show nullityAt j ≠ nullityAt i from fun h => hji (nullityAt_injective h),hPres]
          refine ⟨hSame.trans hOldDim,?_⟩
          rw [hSame]
          obtain ⟨xs,hInd,hSpan,hAt⟩ := hOldBasis
          have hDim : ρ.vars (nullityAt j) ≤ m := by rw [hOldDim]; exact kernelFinrank_le _
          refine ⟨xs,hInd,hSpan,?_⟩
          intro u v
          let s := (outputBase j).value m + (u.val*m+(inputCoordOrder n a v).val)
          have hs₀ : (outputBase j).value m ≤ s := by omega
          have ho := outputPoint_lt hDim u (inputCoordOrder n a v)
          have hs₁ : s < (outputBase j).value m+m*m := by omega
          obtain ⟨hOut,hOne⟩ := outputBank_point_outside m hj' s hs₀ hs₁
          exact (vFrame s).trans ((hFrame s hOut hOne).trans (hAt u v))
    · refine ⟨ρ,?_,hS₀,hm₀,hBank₀,hWS₀,hz₀,?_,hin₀,hout₀⟩
      · rw [allCutProgram,dif_neg hI,allCutCost,dif_neg hI]
        exact r₀
      · intro j _
        exact hOld j (by have := j.isLt; omega)

#print axioms allCutProgram_run
end EvenTI.P12ComparePrep



set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def comparisonFourReadyProgram (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (comparisonInitProgram F) (allCutProgram D F 4)

/-- Start with the literal raw pair on the input tape and no populated field
or matrix arrays; compute all four complete kernel bases in shared memory. -/
theorem comparisonFourReadyProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n B : Nat} (T S : Tensor K (a+a) n) (other : String → Nat)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hInput : (comparisonInput D T S).length < B)
    (hWords : ∀ x ∈ comparisonInput D T S, x < B)
    (hMemFit : F.e+1+pairCutSlotCount.value (n^a)*F.e < B)
    (hScratchFit : 16*(F.e+1) < B)
    (hSquare : (F.p+1)^2 < B) (hPower : (F.p+1)^(F.e+1) < B)
    (hFits : ∀ (idx : Fin 4) target v, v ∈ kernelBindings target idx → v.2.value (n^a) < B)
    (hCard : Fintype.card K ≤ B) (hB : 1 < B)
    (hMemory : pairCutSlotCount.value (n^a)+(n^a)+(n^a)+10 < B) :
    let m := n^a
    let w := comparisonInput D T S
    ∃ τ, Run B (comparisonFourReadyProgram D F)
      (initEnv (comparisonInitExt F (pairCutSlotCount.value m) w.length other) (w.length::w)) τ
      (40*(w.length+1)+3*F.e+25+allCutCost F m 4) ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars shapePower.out = m ∧ τ.arrs rawPairIO.array = w ∧
      τ.vars qN.WS = F.e+1 ∧ val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      (∀ j : Fin 4, InstalledCut F T S j τ) ∧ τ.inp = [] ∧ τ.out = [] := by
  dsimp only
  let m := n^a
  let w := comparisonInput D T S
  have he : Even (a+a) := ⟨a,rfl⟩
  have hValid := decodePair_encode D T S (by omega) he hn
  obtain ⟨ρ,r₀,hShape,hSlots,hABI,hZeros,hin,hout⟩ :=
    comparisonInitProgram_run D F w hValid (pairCutSlotCount.value m) B other hInput hWords
      hMemFit hScratchFit hSquare hPower (by change pairCutSlotCount.value (n^a) < B; omega)
  have hHalf : (a+a)/2 = a := by omega
  have hm : ρ.vars shapePower.out = m := by simpa only [hHalf,m] using hShape.side
  have hZero : val F canonical qN.WS ρ (constantsBase.value m) = 0 :=
    hZeros _ (by simp [pairCutSlotCount,Address.value])
  obtain ⟨τ,r,hSlots',hm',hBank,hABI',hz,hCuts,hi,ho⟩ :=
    allCutProgram_run D F T S 4 (by omega) hm hShape.bank hSlots hABI hFits hCard hB hMemory hInput hZero
  exact ⟨τ,r₀.seq r,hSlots',hm',hBank,hABI',hz,fun j => hCuts j j.isLt,hi.trans hin,ho.trans hout⟩

#print axioms comparisonFourReadyProgram_run
end EvenTI.P12ComparePrep



set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.P15DecideIMPCost20261007 (rkCost_le)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def oneCutCostBound (F : FieldPresentation K) (L : ℕ) : ℕ :=
  (78+installEncodedDigitCost F)*L +
  34500*(macroBudget F * (4*L+2)^5) + 4096 + installEncodedDigitCost F

private theorem kernelAssignment_cost_bound :
    ∀ (target : Bool) (i : Fin 4),
      ((kernelBindings target i).map fun v => v.2.expr.size+1).sum ≤ 2048 := by decide

private theorem cutAddress_size (left : Bool) :
    (if left then transposeAddress else contiguousAddress).size ≤ 64 := by cases left <;> decide

theorem actualCutCost_le (F : FieldPresentation K) (i : Fin 4) {m L : ℕ}
    (hm : m ≤ L) (hSq : m*m ≤ L) : actualCutCost F i m ≤ oneCutCostBound F L := by
  have hAssign := kernelAssignment_cost_bound (targetOf i) i
  have hAddr := cutAddress_size (leftOf i)
  have hRK := rkCost_le F (nr := m) (d := m) (X := 4*L+2) (by rw [Nat.mul_add]; omega)
  have hBank := Nat.mul_le_mul
    (show (if leftOf i then transposeAddress else contiguousAddress).size+10+
      installEncodedDigitCost F+4 ≤ 78+installEncodedDigitCost F by omega) hSq
  unfold actualCutCost oneCutCostBound encodedBankLoadCost encodedBankLoadStepCost
  omega

theorem allCutCost_le (F : FieldPresentation K) {m L : ℕ} (hm : m ≤ L)
    (hSq : m*m ≤ L) (steps : ℕ) :
    allCutCost F m steps ≤ 1+steps*oneCutCostBound F L := by
  induction steps with
  | zero => simp [allCutCost]
  | succ i ih =>
    by_cases hi : i < 4
    · rw [allCutCost,dif_pos hi,Nat.succ_mul]
      have hh := actualCutCost_le F ⟨i,hi⟩ hm hSq
      omega
    · rw [allCutCost,dif_neg hi,Nat.succ_mul]
      omega

theorem comparisonFourReadyCost_le (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (hn : 0 < n) {L : ℕ}
    (hLen : (comparisonInput D T S).length ≤ L) :
    40*((comparisonInput D T S).length+1)+3*F.e+25+allCutCost F (n^a) 4 ≤
      40*(L+1)+3*F.e+26+4*oneCutCostBound F L := by
  have hT : (comparisonInput D T S).length = 2+n^(a+a)+n^(a+a) := by
    simp [comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have hM : 0 < n^a := pow_pos hn _
  have hSq : n^a*n^a ≤ L := by rw [← pow_add]; omega
  have hm : n^a ≤ L := (Nat.le_mul_of_pos_right _ hM).trans hSq
  have hCost := allCutCost_le F hm hSq 4
  omega

#print axioms comparisonFourReadyCost_le
end EvenTI.P12ComparePrep



set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def leftCutAt (target : Bool) : Fin 4 := if target then 2 else 0
def rightCutAt (target : Bool) : Fin 4 := if target then 3 else 1

theorem leftOf_leftCutAt (target : Bool) : leftOf (leftCutAt target) = true := by cases target <;> decide
theorem leftOf_rightCutAt (target : Bool) : leftOf (rightCutAt target) = false := by cases target <;> decide
theorem targetOf_leftCutAt (target : Bool) : targetOf (leftCutAt target) = target := by cases target <;> decide
theorem targetOf_rightCutAt (target : Bool) : targetOf (rightCutAt target) = target := by cases target <;> decide

noncomputable def placedFormPairs {a n : ℕ} (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) (σ : Env) (goodL goodR : (Coord a n → K) → Bool) :
    List (CutFormPair K a a n) :=
  let i := leftCutAt target
  let j := rightCutAt target
  bankCutFormPairs (c := σ.vars (nullityAt i)) (e := σ.vars (nullityAt j)) D
    (inputCoordOrder n a) (inputCoordOrder n a) (val F canonical qN.WS σ)
    (val F canonical qN.WS σ) ((outputBase i).value (n^a)) ((outputBase j).value (n^a)) goodL goodR

/-- Membership agrees with the original comparison plan directly from the live
field slots, independently of how the paid elimination orders its basis. -/
theorem mem_placedFormPairs {a n : ℕ} (D : FieldEncoding K) (F : FieldPresentation K)
    (T S : Tensor K (a+a) n) (target : Bool) (σ : Env)
    (hL : InstalledCut F T S (leftCutAt target) σ)
    (hR : InstalledCut F T S (rightCutAt target) σ)
    (goodL goodR : (Coord a n → K) → Bool) (p : CutFormPair K a a n) :
    p ∈ placedFormPairs D F target σ goodL goodR ↔
      p ∈ rawCutBankForms D (if target then S else T) goodL goodR := by
  let U := if target then S else T
  have hLD : σ.vars (nullityAt (leftCutAt target)) = Module.finrank K (leftCutKernel U).ker := by
    have h := hL.nullity
    change _ = Module.finrank K (selectedKernel (leftOf (leftCutAt target)) (if targetOf (leftCutAt target) then S else T)) at h
    rw [leftOf_leftCutAt,targetOf_leftCutAt] at h
    exact h
  have hRD : σ.vars (nullityAt (rightCutAt target)) = Module.finrank K (rightCutKernel U).ker := by
    have h := hR.nullity
    change _ = Module.finrank K (selectedKernel (leftOf (rightCutAt target)) (if targetOf (rightCutAt target) then S else T)) at h
    rw [leftOf_rightCutAt,targetOf_rightCutAt] at h
    exact h
  obtain ⟨L,hLI,hLS,hLP⟩ := hL.basis
  obtain ⟨R,hRI,hRS,hRP⟩ := hR.basis
  have hLS' : Submodule.span K (Set.range L) = (leftCutKernel U).ker := by
    simpa only [leftOf_leftCutAt,targetOf_leftCutAt,selectedKernel,if_true] using hLS
  have hRS' : Submodule.span K (Set.range R) = (rightCutKernel U).ker := by
    simpa only [leftOf_rightCutAt,targetOf_rightCutAt,selectedKernel,Bool.false_eq_true,if_false,rightCutKernel]
      using hRS
  obtain ⟨x,y⟩ := p
  unfold placedFormPairs
  rw [bankCutFormPairs_eq D U _ _ _ _ _ _ goodL goodR L R hLP hRP hLI hRI hLS' hRS',
    mem_rawCutBankForms,cutFormPairs]
  refine List.mem_product.trans ?_
  simp only [mem_kernelForms,hLD,hRD] <;> rfl

#print axioms mem_placedFormPairs
end EvenTI.P12ComparePrep
