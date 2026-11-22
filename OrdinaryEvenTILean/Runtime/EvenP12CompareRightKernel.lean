import EvenP12CompareBankLoad
import EvenP11RawKernelMachine

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPProgram20261007
open Mathproof.P15DecideIMPKerBasis20261007
open Mathproof.P15DecideIMPRowKer20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def flatEntry {a b n : ℕ} (T : Tensor K (a+b) n) (j : ℕ) : K :=
  if hj : j < n^(a+b) then T ((inputCoordOrder n (a+b)).symm ⟨j,hj⟩) else 0

def tensorOffset (N : ℕ) (target : Bool) : ℕ := 2 + if target then N else 0

theorem comparisonInput_getElem?_flat {a b n : ℕ} (F : FieldEncoding K)
    (T S : Tensor K (a+b) n) (target : Bool) (j : ℕ) (hj : j < n^(a+b)) :
    (comparisonInput F T S)[tensorOffset (n^(a+b)) target+j]? =
      some (F (flatEntry (if target then S else T) j)).val := by
  have hsrc := tensorWords_length F T
  cases target
  · unfold comparisonInput
    rw [List.append_assoc]
    rw [show tensorOffset (n^(a+b)) false+j = j+1+1 by simp [tensorOffset]; omega]
    simp only [List.cons_append,List.nil_append,List.getElem?_cons_succ,Bool.false_eq_true,dif_pos hj,
      flatEntry,ite_false]
    rw [List.getElem?_append_left (by omega),tensorWords_eq_inputCoordOrder,List.getElem?_ofFn,dif_pos hj]
  · unfold comparisonInput
    rw [List.append_assoc]
    rw [show tensorOffset (n^(a+b)) true+j = n^(a+b)+j+1+1 by simp [tensorOffset]; omega]
    simp only [List.cons_append,List.nil_append,List.getElem?_cons_succ,flatEntry,dif_pos hj,ite_true]
    rw [List.getElem?_append_right (by omega),hsrc,Nat.add_sub_cancel_left,
      tensorWords_eq_inputCoordOrder,List.getElem?_ofFn,dif_pos hj]

theorem flatEntry_index {a b n : ℕ} (T : Tensor K (a+b) n)
    (i : Fin (n^a)) (j : Fin (n^b)) :
    flatEntry T (i.val * n^b+j.val) =
      flatten T ((inputCoordOrder n a).symm i) ((inputCoordOrder n b).symm j) := by
  let x := (inputCoordOrder n a).symm i
  let y := (inputCoordOrder n b).symm j
  have hxy : cutAddress n a b x y = i.val * n^b+j.val := by
    simp [cutAddress,x,y]
  have hlt := cutAddress_lt n a b x y
  rw [hxy] at hlt
  simp only [flatEntry,dif_pos hlt]
  change T ((inputCoordOrder n (a+b)).symm ⟨_,hlt⟩) = T (Fin.append x y)
  congr 1
  apply (inputCoordOrder n (a+b)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [inputCoord_append]
  exact hxy.symm

noncomputable def comparisonRightKernel (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) : Com :=
  .seq (encodedBankLoad D FP bank contiguousAddress) rkProg

/-- Load the right cut directly from the original comparison word list, then
run the checked row-kernel machine. No pre-installed matrix is supplied. -/
theorem comparisonRightKernel_run (D : FieldEncoding K) (FP : FieldPresentation K)
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
  obtain ⟨τ,hRun,hS',_,⟨xs,hBankAt,hInd,hSpan⟩,_,_,hi,ho'⟩ :=
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
  exact ⟨τ,hr.seq hRun,hS',hd,
    ⟨fun i j => xs i (cOrder j),hI,hsp,fun i j => hBankAt i (cOrder j)⟩,
    hi.trans hi₀,ho'.trans ho₀⟩

#print axioms comparisonInput_getElem?_flat
#print axioms comparisonRightKernel_run

end EvenTI.P12Compare
