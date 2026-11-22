import EvenP15ReciprocalExponent
import Mathproof.Meta.Problem18PairBoundaryModeC2Calls20261004
import Mathproof.Meta.Problem18PairBoundaryOddProductsRun20261004

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites noRead)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)
open Mathproof.Problem18PairBoundaryModeC2Calls20261004 (valid_of_vars)
open Mathproof.Problem18PairBoundaryOddRun20261004 (slots_of_vars)
open Mathproof.Problem18PairBoundaryMatrixPower20261004
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def loadedInverseProgram (q : ℕ) : Com := .seq (installGLExponent q) program

def loadedInverseCost (q e m : ℕ) : ℕ :=
  26*m+20+programCost e m (q*(m*m+m+2)+1)

/-- Execute a uniform inverse from a live matrix bank. The same checked
matrix-power implementation handles every dimension and field presentation. -/
theorem loadedInverseProgram_run (F : FieldPresentation K) (L : Layout) {B S : ℕ} {s : Env}
    (h : L.Ok S) (hR : Regs L s) (hV : ValidMemory F B s) (hs : Slots F canonical ws S B s)
    (hMB : s.vars canonical.modBase+F.e ≤ s.vars ws) (hWide : L.n < B)
    (hWord : Fintype.card K^(L.n*L.n+L.n+2)<B)
    (hUnit : IsUnit (matrix F s (s.vars ws+L.input*F.e) L.n L.n)) :
    ∃ t, Run B (loadedInverseProgram (Fintype.card K)) s t (loadedInverseCost (Fintype.card K) F.e L.n) ∧
      matrix F t (s.vars ws+L.acc*F.e) L.n L.n=(matrix F s (s.vars ws+L.input*F.e) L.n L.n)⁻¹ ∧
      matrix F t (s.vars ws+L.input*F.e) L.n L.n=matrix F s (s.vars ws+L.input*F.e) L.n L.n ∧
      ValidMemory F B t ∧ Slots F canonical ws S B t ∧ Frame (loadedInverseProgram (Fintype.card K)) s t := by
  let q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  obtain ⟨u,ru,he,f⟩ := installGLExponent_run hq hWide hWord hR.n
  have hArrays : u.arrs=s.arrs := funext fun x => f.arrs x (by
    have h : arrayWrites (installGLExponent q) = ∅ := rfl
    simp [h])
  have hWrt : scalarWrites (installGLExponent q) = scalarWrites (installGLExponent 0) := rfl
  have hKeep (x : String) (hx : x ∉ scalarWrites (installGLExponent 0)) : u.vars x = s.vars x :=
    f.vars x (by rwa [hWrt])
  have hws : u.vars ws = s.vars ws := hKeep _ (by decide)
  have hMod : u.vars canonical.modBase = s.vars canonical.modBase := hKeep _ (by decide)
  have hReg : Regs L u := hR.transfer (fun r hr => hKeep _ (by
    simp only [layoutRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e|e|e|e|e|e|e|e|e <;> subst r <;> decide))
  have hVu := valid_of_vars F hV hArrays (hKeep _ (by decide)) (hKeep _ (by decide)) hMod
  have hSu := slots_of_vars F hs hArrays (fun r hr => hKeep _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e|e|e|e|e <;> subst r <;> decide))
  have hUmat : matrix F u (u.vars ws+L.input*F.e) L.n L.n =
      matrix F s (s.vars ws+L.input*F.e) L.n L.n := by
    rw [hws]
    apply matrix_of_cells F
    intro k _
    rw [hArrays]
  have hExp : u.vars exponentReg < B := by
    rw [he]
    exact (Nat.sub_le _ _).trans_lt ((glCount_le q L.n).trans_lt
      ((Nat.pow_le_pow_right (by omega) (by omega : L.n*L.n ≤ L.n*L.n+L.n+2)).trans_lt hWord))
  obtain ⟨t,rt,ht,htKeep,hValid,hSlot,_,_,_,_,_,_,_,_,_⟩ := program_run F L u h hReg hVu hSu
    (by rwa [hMod,hws]) hExp
  have ht' : matrix F t (s.vars ws+L.acc*F.e) L.n L.n =
      (matrix F s (s.vars ws+L.input*F.e) L.n L.n)⁻¹ := by
    calc
      matrix F t (s.vars ws+L.acc*F.e) L.n L.n = matrix F t (u.vars ws+L.acc*F.e) L.n L.n := by rw [hws]
      _ = (matrix F u (u.vars ws+L.input*F.e) L.n L.n)^(u.vars exponentReg) := ht
      _ = _ := by rw [hUmat,he]; exact inverse_eq_glPower _ hUnit
  have hTime : programCost F.e L.n (Nat.size (u.vars exponentReg)) ≤
      programCost F.e L.n (q*(L.n*L.n+L.n+2)+1) := by
    rw [he]
    unfold programCost
    exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left _ (glExponent_size hq _)) _ ) _
  have run : Run B (loadedInverseProgram q) s t (loadedInverseCost q F.e L.n) :=
    ru.seq (rt.mono hTime)
  refine ⟨t,run,ht',?_,hValid,hSlot,Frame.of_run run⟩
  calc
    matrix F t (s.vars ws+L.input*F.e) L.n L.n = matrix F t (u.vars ws+L.input*F.e) L.n L.n := by rw [hws]
    _ = _ := htKeep.trans hUmat

open Polynomial in
/-- Uniform word-operation cost of the inverse, as a univariate polynomial
for each fixed field degree and cardinality. -/
noncomputable def inverseCostPolynomial (q e : ℕ) : Polynomial ℕ :=
  let c := C (38+10000*(e+1)^2+2000*(e+1))
  let d := C (2000*(e+1)+110)
  let product := C 43 + X*X*(c*X+d)+C 150
  let copy := C 26*(X*X*C e)+C 8
  let body := C 20+C 2*product+C 3*copy
  let width := C q*(X*X+X+C 2)+C 1
  C 26*X+C 20+ (copy+(C 31*(X*X*C e)+C 8)+((C 4+body)*width+C 4))

theorem inverseCostPolynomial_eval (q e n : ℕ) :
    (inverseCostPolynomial q e).eval n=loadedInverseCost q e n := by
  simp only [inverseCostPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,loadedInverseCost,programCost,productCost,copyCost,bodyCost,
    Mathproof.Problem18IMPMatrixProductLoop20261001.cost,Nat.add_assoc]

/-- The registered power call uses a polynomial budget in the original size
whenever the flattening side is bounded by that size. -/
theorem loadedInverseCost_le_bits (q e m L : ℕ) (hm : m ≤ L) :
    loadedInverseCost q e m ≤ (inverseCostPolynomial q e).eval L := by
  rw [inverseCostPolynomial_eval]
  simp only [loadedInverseCost,programCost,bodyCost,productCost,copyCost,
    Mathproof.Problem18IMPMatrixProductLoop20261001.cost]
  gcongr

#print axioms loadedInverseProgram_run
#print axioms loadedInverseCost_le_bits
end EvenTI.P15Execution