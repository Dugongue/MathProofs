import Mathproof.Meta.P15RecogIMPParse20261007
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldAddition20261001 (writeValues writeValues_length writeValues_inside writeValues_outside)
open Mathproof.Problem18IMPFieldPresentation20261001 (decode slice)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Base Slots val NoVar)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands install commands_run installed_arrays installed_scalar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15RecogIMPParse20261007 (priv_canonical)
set_option autoImplicit false

private def literalStores (array : String) (start : Nat) (values : Nat → Nat) : Nat → Com
  | 0 => .skip
  | j+1 => .seq (literalStores array start values j)
      (.store array (.lit (start+j)) (.lit (values j)))

private def literalStored (array : String) (start : Nat) (values : Nat → Nat) (width : Nat)
    (σ : Env) : Env :=
  {σ with arrs := fun a => if a = array then writeValues (σ.arrs a) start values width else σ.arrs a}

private theorem literalStores_run (array : String) (start : Nat) (values : Nat → Nat)
    (width : Nat) {B : Nat} (σ : Env)
    (hFit : start+width ≤ (σ.arrs array).length) (hSize : (σ.arrs array).length < B)
    (hValues : ∀ j < width, values j < B) :
    Run B (literalStores array start values width) σ (literalStored array start values width σ)
      (3*width+1) := by
  induction width with
  | zero =>
    have hs : literalStored array start values 0 σ = σ := by
      cases σ
      simp only [literalStored,writeValues]
      congr 1
      funext a
      simp
    simpa [literalStores,hs] using (Run.skip (B := B) (σ := σ))
  | succ j ih =>
    let mid := literalStored array start values j σ
    let fin := literalStored array start values (j+1) σ
    have hIdx : start+j < (mid.arrs array).length := by
      simp [mid,literalStored,writeValues_length]
      omega
    have rr : Run B (.store array (.lit (start+j)) (.lit (values j))) mid
        (mid.setArr array (start+j) (values j)) 3 :=
      Run.store (evalB_lit (by omega)) (evalB_lit (hValues _ (by omega))) hIdx
    have he : mid.setArr array (start+j) (values j) = fin := by
      cases σ
      simp only [mid,fin,literalStored,Env.setArr,writeValues]
      congr 1
      funext a
      by_cases h : a = array <;> simp [h]
    rw [he] at rr
    have r := (ih (by omega) (fun k hk => hValues k (by omega))).seq rr
    exact r.mono (by omega)

variable {K : Type} [Field K] [Fintype K]

def fieldRegisterValues (F : FieldPresentation K) : List (String × Nat) :=
  [(canonical.e,F.e),(canonical.p,F.p),(canonical.modBase,0),(canonical.exp,0),(qN.WS,F.e+1)]

def modulusWord (F : FieldPresentation K) (j : Nat) : Nat :=
  if h : j < F.e then (F.modulus ⟨j,h⟩).val else 0

/-- The fixed field metadata is written by real IMP operations into a newly
allocated bank. The command leaves the incoming raw input and other banks intact. -/
def fieldInitProgram (F : FieldPresentation K) : Com :=
  .seq (commands ((fieldRegisterValues F).map fun p => (p.1,.lit p.2)))
    (literalStores canonical.mem 0 (modulusWord F) F.e)

def canonicalInitExt (F : FieldPresentation K) (slots : Nat) (ext : String → Nat) : String → Nat :=
  fun a => if a = canonical.mem then F.e+1+slots*F.e else
    if a = canonical.scratch then 16*(F.e+1) else ext a

def fieldInitState (F : FieldPresentation K) (σ : Env) : Env :=
  literalStored canonical.mem 0 (modulusWord F) F.e (install (fieldRegisterValues F) σ)

theorem fieldInitProgram_run (F : FieldPresentation K) (Sn B : Nat) (σ : Env)
    (hMemory : σ.arrs canonical.mem = List.replicate (F.e+1+Sn*F.e) 0)
    (hScratch : (σ.arrs canonical.scratch).length = 16*(F.e+1))
    (hMemFit : F.e+1+Sn*F.e < B) (hScratchFit : 16*(F.e+1) < B)
    (hSquare : (F.p+1)^2 < B) (hPower : (F.p+1)^(F.e+1) < B)
    (hSlotFit : Sn < B) :
    let τ := fieldInitState F σ
    Run B (fieldInitProgram F) σ τ (3*F.e+13) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars qN.WS = F.e+1 ∧
      (∀ j < Sn, val F canonical qN.WS τ j = 0) ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧
      (∀ r, r ≠ canonical.e → r ≠ canonical.p → r ≠ canonical.modBase →
        r ≠ canonical.exp → r ≠ qN.WS → τ.vars r = σ.vars r) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let regs := fieldRegisterValues F
  let mid := install regs σ
  let τ := fieldInitState F σ
  have hm := (installed_arrays regs σ).1
  have hFlt : F.p < B := by
    have hh : F.p+1 ≤ (F.p+1)^2 := by have := Nat.le_mul_self (F.p+1); simpa only [pow_two] using this
    omega
  have hE : F.e+1 < B := by omega
  have hR := commands_run (regs.map fun x => (x.1,.lit x.2)) (regs.map Prod.snd) σ
    (by simp) (by
      simp only [regs,fieldRegisterValues,List.map_cons,List.map_nil]
      refine .cons (evalB_lit (by omega)) (.cons (evalB_lit hFlt) (.cons (evalB_lit (by omega))
        (.cons (evalB_lit (by omega)) (.cons (evalB_lit hE) .nil)))))
    (by simp [regs,fieldRegisterValues,NoVar])
  have hZip : List.zip ((regs.map fun x => (x.1,Expr.lit x.2)).map Prod.fst) (regs.map Prod.snd) = regs := by
    simp [regs,fieldRegisterValues]
  rw [hZip] at hR
  have hMid : (mid.arrs canonical.mem).length = F.e+1+Sn*F.e := by
    rw [hm,hMemory,List.length_replicate]
  have ho := literalStores_run canonical.mem 0 (modulusWord F) F.e mid
    (by rw [hMid]; omega) (by rwa [hMid])
    (fun j hj => by
      simp only [modulusWord,dif_pos hj]
      exact (F.modulus ⟨j,hj⟩).isLt.trans hFlt)
  have hRun : Run B (fieldInitProgram F) σ τ (3*F.e+13) := by
    refine (hR.seq ho).mono ?_
    simp [regs,fieldRegisterValues,Expr.size]
    omega
  have he : τ.vars canonical.e = F.e := by
    simp [τ,fieldInitState,fieldRegisterValues,literalStored,install,canonical,qN,Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hp : τ.vars canonical.p = F.p := by
    simp [τ,fieldInitState,fieldRegisterValues,literalStored,install,canonical,qN,Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hmb : τ.vars canonical.modBase = 0 := by
    simp [τ,fieldInitState,fieldRegisterValues,literalStored,install,canonical,qN,Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hx : τ.vars canonical.exp = 0 := by
    simp [τ,fieldInitState,fieldRegisterValues,literalStored,install,canonical,qN,Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hws : τ.vars qN.WS = F.e+1 := by
    simp [τ,fieldInitState,fieldRegisterValues,literalStored,install,canonical,qN,Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hτMem : τ.arrs canonical.mem = writeValues (mid.arrs canonical.mem) 0 (modulusWord F) F.e := by
    simp [τ,fieldInitState,literalStored,mid,regs]
  have hτSize : (τ.arrs canonical.mem).length = F.e+1+Sn*F.e := by
    rw [hτMem,writeValues_length,hMid]
  have hτa (a : String) (ha : a ≠ canonical.mem) : τ.arrs a = σ.arrs a := by
    change (if a = canonical.mem then _ else _) = _
    rw [if_neg ha,hm]
  have hτScratch : (τ.arrs canonical.scratch).length = 16*(F.e+1) := by
    rw [hτa _ (by decide),hScratch]
  have hZero (i : Nat) (hi : F.e ≤ i) (hj : i < (τ.arrs canonical.mem).length) :
      (τ.arrs canonical.mem).getD i 0 = 0 := by
    rw [hτMem,writeValues_outside _ _ _ _ _ (by rw [hMid,←hτSize]; exact hj)
      (Or.inr (by omega)),hm,hMemory]
    simp [List.getD_eq_getElem?_getD]
  have hSzero (j : Nat) (hj : j < Sn) (i : Fin F.e) :
      slice F τ canonical (τ.vars qN.WS+j*F.e) i = 0 := by
    rw [slice,hws]
    apply hZero
    · omega
    · rw [hτSize]
      have hMul := Nat.mul_le_mul_right F.e (show j+1≤Sn by omega)
      rw [Nat.add_mul,Nat.one_mul] at hMul
      have := i.isLt
      omega
  have hSlots : Slots F canonical qN.WS Sn B τ := by
    refine ⟨⟨canonical_valid,he,hp,hSquare,hPower,by rwa [hτSize],by rwa [hτScratch],
      by rw [hτScratch],?_,?_,by rw [hx]; omega,priv_canonical⟩,by decide,?_,?_,?_,hSlotFit⟩
    · rw [hmb,hτSize]; omega
    · intro i
      rw [hmb,hτMem,writeValues_inside _ 0 F.e i.val _ (by rw [hMid]; omega) i.isLt]
      simp [modulusWord,i.isLt]
    · rw [hws,hτSize]
    · left; rw [hmb,hws]; simp
    · intro j hj i
      rw [hSzero j hj i]
      exact F.prime.pos
  refine ⟨hRun,hSlots,hws,?_,hτa,?_,rfl,rfl⟩
  · intro j hj
    change val F canonical qN.WS τ j = 0
    unfold val decode
    simp only [hSzero j hj,Nat.cast_zero,zero_mul,Finset.sum_const_zero]
  · intro r he hp hm hx hw
    change (install regs σ).vars r = σ.vars r
    apply installed_scalar
    intro p h
    simp only [regs,fieldRegisterValues,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h <;> rw [h] <;> assumption

#print axioms fieldInitProgram_run
end EvenTI.P12ComparePrep
