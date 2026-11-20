import CellCRT46TableWrite
import EvenNextSmithMatrix

/-! Narrow replay of the existing Problem 1.7 `CellCRT46Smith` command
and proof. The four input/output names and the command body are unchanged.
This avoids pulling the full tensor comparator in merely to read string
constants. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8500000
namespace EvenOrdinaryTI.LiveRows.Physical
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001

open Problem17CellCRT46

-- The old namespaces define these same hardware port names.
def source3 : String := "CellCRT.source3"
def inputColsR : String := "P15.GSS.smith.inputCols"
def matrixR : String := "P15.GSS.smith.matrix"
def modR : String := "P15.GSS.smith.modulus"

def eqRows := "CellCRT.smith.equations"
def gaugeWords := "CellCRT.smith.gauge"
def orderWords := "CellCRT.smith.orders"

def rowE : Expr := .bin .div (.var writeIndex) (.var inputColsR)
def colE : Expr := remE (.var writeIndex) (.var inputColsR)
def edgeE (k : ℕ) : Expr := .bin .add (.bin .mul (.lit 3) rowE) (.lit k)

def eqBitE (a b : Expr) : Expr :=
  .bin .sub (.lit 1) (.bin .add (.bin .sub a b) (.bin .sub b a))

def weightE (k : ℕ) : Expr := .get gaugeWords (edgeE k)

def signedTermE (k : ℕ) : Expr :=
  .bin .mul (eqBitE (.get source3 (edgeE k)) colE)
    (if k = 0 then weightE k else .bin .sub (.var modR) (weightE k))

def equationsE : Expr :=
  remE (.bin .add (.bin .add (signedTermE 0) (signedTermE 1)) (signedTermE 2)) (.var modR)

def orderRowE : Expr :=
  remE (.bin .mul (eqBitE (.bin .sub rowE (.var eqRows)) colE) (.get orderWords colE)) (.var modR)

def inEquations : Cond := .lt rowE (.var eqRows)
def loadSmith : Com := .ite inEquations (.assign writeValue equationsE) (.assign writeValue orderRowE)
def packSmith : Com := writeTable matrixR loadSmith

def signedTerm (M : ℕ) (src weights : ℕ → ℕ) (r c k : ℕ) : ℕ :=
  if src (3*r+k) = c then (if k = 0 then weights (3*r+k) else M-weights (3*r+k)) else 0

def transferWord (M J V : ℕ) (src weights orders : ℕ → ℕ) (i : ℕ) : ℕ :=
  let r := i/V
  let c := i%V
  if r < J then
    (signedTerm M src weights r c 0+signedTerm M src weights r c 1+signedTerm M src weights r c 2)%M
  else (if r-J = c then orders c else 0)%M

theorem eqBit_eval {B a b : ℕ} {ρ : Env} {u v : Expr} (hB : 1 < B)
    (hu : u.evalB B ρ = some a) (hv : v.evalB B ρ = some b) (ha : a < B) (hb : b < B) :
    (eqBitE u v).evalB B ρ = some (if a = b then 1 else 0) := by
  have hsum : a-b+(b-a) < B := by omega
  have er : (Expr.bin .add (.bin .sub u v) (.bin .sub v u)).evalB B ρ = some (a-b+(b-a)) :=
    evalB_bin (evalB_bin hu hv (by change a-b < B; omega))
      (evalB_bin hv hu (by change b-a < B; omega)) (by change _ < B; exact hsum)
  have hx : 1-(a-b+(b-a)) = (if a=b then 1 else 0) := by
    split_ifs with h <;> omega
  rw [← hx]
  exact evalB_bin (evalB_lit hB) er (by change 1-(a-b+(b-a)) < B; omega)

private theorem evalRead {B i v : ℕ} {ρ : Env} {a : String} {E : Expr}
    (e : E.evalB B ρ = some i) (hi : i < (ρ.arrs a).length)
    (hv : (ρ.arrs a).getD i 0 = v) (hb : v < B) :
    (Expr.get a E).evalB B ρ = some v :=
  evalB_get e (List.getElem?_eq_some_iff.mpr ⟨hi,by rw [← List.getD_eq_getElem _ _ hi,hv]⟩) hb

private theorem evalVar {B v : ℕ} {ρ : Env} {a : String} (hv : ρ.vars a = v) (hb : v < B) :
    (Expr.var a).evalB B ρ = some v :=
  (evalB_var (hv ▸ hb)).trans (congrArg some hv)

theorem loadSmith_run {B M J V i : ℕ} {ρ : Env} (src weights orders : ℕ → ℕ)
    (hV0 : 0 < V) (hM0 : 0 < M) (hB : 4 < B) (hJV : J+V < B) (hJ : 3*J < B)
    (hM : 3*M < B) (hAll : (J+V)*V < B) (hi : i < (J+V)*V)
    (hI : ρ.vars writeIndex = i) (hVR : ρ.vars inputColsR = V) (hJR : ρ.vars eqRows = J)
    (hMR : ρ.vars modR = M)
    (hSrc : ∀ k < 3*J, k < (ρ.arrs source3).length ∧
      (ρ.arrs source3).getD k 0 = src k ∧ src k < V)
    (hWeight : ∀ k < 3*J, k < (ρ.arrs gaugeWords).length ∧
      (ρ.arrs gaugeWords).getD k 0 = weights k ∧ weights k < M)
    (hOrder : ∀ k < V, k < (ρ.arrs orderWords).length ∧
      (ρ.arrs orderWords).getD k 0 = orders k ∧ orders k < B) :
    Run B loadSmith ρ (ρ.setVar writeValue (transferWord M J V src weights orders i)) 500 := by
  let r := i/V
  let c := i%V
  have hr : r < J+V := (Nat.div_lt_iff_lt_mul hV0).2 hi
  have hc : c < V := Nat.mod_lt _ hV0
  have ei := evalVar hI (hi.trans hAll)
  have ev := evalVar hVR (by omega : V < B)
  have er : rowE.evalB B ρ = some r := evalB_bin ei ev (by change r < B; omega)
  have ec : colE.evalB B ρ = some c := remE_eval ei ev (hi.trans hAll)
  have ej := evalVar hJR (by omega : J < B)
  have em := evalVar hMR (by omega : M < B)
  unfold loadSmith transferWord
  change Run B (.ite inEquations (.assign writeValue equationsE) (.assign writeValue orderRowE)) ρ
    (ρ.setVar writeValue (if r<J then
      (signedTerm M src weights r c 0+signedTerm M src weights r c 1+signedTerm M src weights r c 2)%M
      else (if r-J=c then orders c else 0)%M)) 500
  by_cases hlt : r < J
  · rw [if_pos hlt]
    have term (k : ℕ) (hk : k < 3) :
        (signedTermE k).evalB B ρ = some (signedTerm M src weights r c k) ∧
          signedTerm M src weights r c k ≤ M := by
      have hs : 3*r+k < 3*J := by omega
      obtain ⟨hls,hrs,hsV⟩ := hSrc _ hs
      obtain ⟨hlw,hrw,hwM⟩ := hWeight _ hs
      have ee : (edgeE k).evalB B ρ = some (3*r+k) :=
        evalB_bin (evalB_bin (evalB_lit (by omega)) er (by change 3*r<B; omega))
          (evalB_lit (by omega)) (by change 3*r+k<B; omega)
      have es := evalRead ee hls hrs (by omega)
      have ew : (weightE k).evalB B ρ = some (weights (3*r+k)) := evalRead ee hlw hrw (by omega)
      have ebit := eqBit_eval (by omega : 1 < B) es ec (by omega) (by omega)
      let w := if k = 0 then weights (3*r+k) else M-weights (3*r+k)
      have ew' : (if k = 0 then weightE k else .bin .sub (.var modR) (weightE k) : Expr).evalB B ρ = some w := by
        by_cases he : k = 0
        · simpa [w,he] using ew
        · simp only [if_neg he,w]
          exact evalB_bin em ew (by change M-weights (3*r+k)<B; omega)
      have hW : w ≤ M := by dsimp [w]; split_ifs <;> omega
      have hd : (if src (3*r+k) = c then 1 else 0)*w = signedTerm M src weights r c k := by
        by_cases he : src (3*r+k) = c <;> simp [he,signedTerm,w]
      have hb : signedTerm M src weights r c k ≤ M := by
        rw [← hd]
        by_cases hs : src (3*r+k) = c
        · simpa only [if_pos hs,one_mul] using hW
        · simp only [if_neg hs,zero_mul,Nat.zero_le]
      exact ⟨by unfold signedTermE; rw [← hd]; exact evalB_bin ebit ew' (by rw [Bop.apply_mul,hd]; omega),hb⟩
    have t0 := term 0 (by decide)
    have t1 := term 1 (by decide)
    have t2 := term 2 (by decide)
    have eAns : equationsE.evalB B ρ = some
        ((signedTerm M src weights r c 0+signedTerm M src weights r c 1+signedTerm M src weights r c 2)%M) :=
      remE_eval (evalB_bin (evalB_bin t0.1 t1.1 (by simp only [Bop.apply_add]; have := t0.2; have := t1.2; omega))
        t2.1 (by simp only [Bop.apply_add]; have := t0.2; have := t1.2; have := t2.2; omega)) em
          (by have := t0.2; have := t1.2; have := t2.2; omega)
    have eCond : inEquations.evalB B ρ = some true := by rw [inEquations,evalB_condLt er ej]; simp [hlt]
    exact (Run.ite_true eCond (Run.assign eAns)).mono (by decide)
  · rw [if_neg hlt]
    have hs : r-J < V := by omega
    have eo : (.bin .sub rowE (.var eqRows) : Expr).evalB B ρ = some (r-J) :=
      evalB_bin er ej (by change r-J<B; omega)
    have h1 : 1 < B := by omega
    have eb := eqBit_eval h1 eo ec (by omega) (by omega)
    obtain ⟨hl,ho,hob⟩ := hOrder _ hc
    have ed : (Expr.get orderWords colE).evalB B ρ = some (orders c) := evalRead ec hl ho hob
    have hw : (if r-J=c then 1 else 0)*orders c = (if r-J=c then orders c else 0) := by
      split_ifs <;> simp
    have en : orderRowE.evalB B ρ = some ((if r-J=c then orders c else 0)%M) := by
      rw [← hw]
      exact remE_eval (evalB_bin eb ed (by rw [Bop.apply_mul,hw]; split_ifs <;> omega)) em
        (by rw [hw]; split_ifs <;> omega)
    have eCond : inEquations.evalB B ρ = some false := by rw [inEquations,evalB_condLt er ej]; simp [hlt]
    exact (Run.ite_false eCond (Run.assign en)).mono (by decide)

theorem packSmith_run {B M J V : ℕ} {σ : Env} (src weights orders : ℕ → ℕ)
    (hV0 : 0 < V) (hM0 : 0 < M) (hB : 4 < B) (hJV : J+V < B) (hJ : 3*J < B)
    (hM : 3*M < B) (hAll : (J+V)*V < B)
    (hC : σ.vars writeCount = (J+V)*V) (hVR : σ.vars inputColsR = V)
    (hJR : σ.vars eqRows = J) (hMR : σ.vars modR = M)
    (hOut : (J+V)*V ≤ (σ.arrs matrixR).length)
    (hSrc : ∀ k < 3*J, k < (σ.arrs source3).length ∧
      (σ.arrs source3).getD k 0 = src k ∧ src k < V)
    (hWeight : ∀ k < 3*J, k < (σ.arrs gaugeWords).length ∧
      (σ.arrs gaugeWords).getD k 0 = weights k ∧ weights k < M)
    (hOrder : ∀ k < V, k < (σ.arrs orderWords).length ∧
      (σ.arrs orderWords).getD k 0 = orders k ∧ orders k < B) :
    ∃ τ, Run B packSmith σ τ (writeTableCost 500 ((J+V)*V)) ∧
      SegInv (σ.arrs matrixR) (τ.arrs matrixR) 0 ((J+V)*V) (transferWord M J V src weights orders) ∧
      Frame packSmith σ τ := by
  apply writeTable_run matrixR loadSmith (transferWord M J V src weights orders) hAll hC hOut (by imp_frame)
  · intro i _
    dsimp only [transferWord]
    split_ifs <;> exact (Nat.mod_lt _ hM0).trans (by omega)
  · intro i hi ρ hI hfr
    have hv : ρ.vars inputColsR = V := by rw [hfr.vars _ (by imp_frame),vars_setVar,if_neg (by decide),hVR]
    have hj : ρ.vars eqRows = J := by rw [hfr.vars _ (by imp_frame),vars_setVar,if_neg (by decide),hJR]
    have hm : ρ.vars modR = M := by rw [hfr.vars _ (by imp_frame),vars_setVar,if_neg (by decide),hMR]
    exact loadSmith_run src weights orders hV0 hM0 hB hJV hJ hM hAll hi hI hv hj hm
      (fun k hk => by rw [hfr.arrs source3 (by imp_frame)]; exact hSrc k hk)
      (fun k hk => by rw [hfr.arrs gaugeWords (by imp_frame)]; exact hWeight k hk)
      (fun k hk => by rw [hfr.arrs orderWords (by imp_frame)]; exact hOrder k hk)

#print axioms packSmith_run
end EvenOrdinaryTI.LiveRows.Physical




namespace EvenOrdinaryTI.LiveRows.Physical

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001
open Problem17CellCRT46

variable {s t d M B : Nat}

theorem prefix_packSmith_run (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat)
    (orders : Fin (VarCount s t d) → Nat) (σ : Env)
    (hV0 : 0 < VarCount s t d) (hM0 : 0 < M)
    (hB : 4 < B) (hJV : RowCount t d + VarCount s t d < B) (hJ : 3*RowCount t d < B)
    (hM : 3*M < B) (hAll : (RowCount t d + VarCount s t d)*VarCount s t d < B)
    (hC : σ.vars writeCount = (RowCount t d + VarCount s t d)*VarCount s t d)
    (hVR : σ.vars inputColsR = VarCount s t d)
    (hJR : σ.vars eqRows = RowCount t d) (hMR : σ.vars modR = M)
    (hOut : (RowCount t d + VarCount s t d)*VarCount s t d ≤ (σ.arrs matrixR).length)
    (hSrc : σ.arrs source3 = SmithSourceBank orig)
    (hWeight : σ.arrs gaugeWords = SmithGaugeBank M gauge)
    (hOrder : σ.arrs orderWords = SmithOrderBank orders)
    (hOrderFit : ∀ v, orders v < B) :
    ∃ τ, Run B packSmith σ τ (writeTableCost 500 ((RowCount t d + VarCount s t d)*VarCount s t d)) ∧
      Frame packSmith σ τ ∧
      ∀ r : Fin (RowCount t d + VarCount s t d), ∀ c : Fin (VarCount s t d),
        ((τ.arrs matrixR).getD (r.val*VarCount s t d+c.val) 0 : ZMod M) =
          SmithMatrix M orig gauge orders r c := by
  obtain ⟨τ,hr,hSeg,hFr⟩ := packSmith_run (sourceWord orig)
    (boundedWord (gaugeWord M gauge)) (boundedWord orders)
    hV0 hM0 hB hJV hJ hM hAll hC hVR hJR hMR hOut
    (fun _ hi => hSrc ▸ sourceBank_mem orig hi)
    (fun _ hi => hWeight ▸ gaugeBank_mem M gauge hM0 hi)
    (fun _ hi => hOrder ▸ orderBank_mem orders hOrderFit hi)
  refine ⟨τ,hr,hFr,?_⟩
  intro r c
  have hi : r.val*VarCount s t d+c.val < (RowCount t d + VarCount s t d)*VarCount s t d := by
    calc
      _ < r.val * VarCount s t d + VarCount s t d := Nat.add_lt_add_left c.isLt _
      _ = (r.val + 1) * VarCount s t d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ r.isLt
  have hw := hSeg.inside _ hi
  have hGiven := (smithMatrixWord_mem M orig gauge orders hi).2
  simp only [Nat.zero_add] at hw
  rw [hw]
  change (smithEntry M (RowCount t d) (VarCount s t d) (sourceWord orig)
    (boundedWord (gaugeWord M gauge)) (boundedWord orders) _ : ZMod M) = _
  rw [← hGiven]
  exact smithMatrixWords_decode M hM0 orig gauge orders r c

#print axioms prefix_packSmith_run

end EvenOrdinaryTI.LiveRows.Physical
