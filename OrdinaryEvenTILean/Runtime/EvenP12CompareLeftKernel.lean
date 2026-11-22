import EvenP12CompareRightKernel

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
open Mathproof.P15DecideIMPEGens20261007 (hmdg ev_var ev_add ev_mul ev_div)

def originalRows : String := "even_compare_original_rows"
def originalColumns : String := "even_compare_original_columns"

def transposeIndex (rows columns k : ℕ) : ℕ := (k % rows) * columns + k / rows

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

def transposeAddress : Expr :=
  let k := Expr.var loadIndex
  let rows := Expr.var originalRows
  let quo := Expr.bin .div k rows
  let rem := Expr.bin .sub k (Expr.bin .mul quo rows)
  .add (.var inputBase) (.add (.bin .mul rem (.var originalColumns)) quo)

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

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def comparisonLeftKernel (D : FieldEncoding K) (FP : FieldPresentation K)
    (bank : String) : Com :=
  .seq (encodedBankLoad D FP bank transposeAddress) rkProg

/-- Form the transpose of the original source or target cut during the paid
bank load and leave a complete left kernel basis at the designated output. -/
theorem comparisonLeftKernel_run (D : FieldEncoding K) (FP : FieldPresentation K)
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

#print axioms comparisonLeftKernel_run

end EvenTI.P12Compare
