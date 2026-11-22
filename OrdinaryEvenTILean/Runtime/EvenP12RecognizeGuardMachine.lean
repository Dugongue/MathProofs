import EvenP11OracleOffset
import Mathproof.Meta.Problem18IMPFieldIO20261001
import Mathproof.Meta.Problem18RootValidatorHeaderIMP20261001

namespace EvenTI.P12Guard

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPFieldIO20261001 Mathproof.Problem18IMPFieldAddition20261001
open Mathproof.Problem18RootValidatorHeaderIMP20261001 (guards guardsCost)
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000

def readIO : Names := ⟨"bank", "base", "idx", "size", "value"⟩
def writeIO : Names := { readIO with limit := "prefix" }
def reject : Com := .write (.lit 0)
def checks (route : Bool) : List Cond :=
  [.eq (.get "bank" (.var "prefix")) (.lit 0),
   .eq (.get "bank" (.add (.var "prefix") (.lit 1))) (.lit 2),
   .eq (.get "bank" (.add (.var "prefix") (.lit 2))) (.lit 0)] ++
  (if route then [] else [.eq (.var "size") (.lit 3)])
def success (route : Bool) : Com :=
  if route then .seq reject (.seq (writeBlock writeIO) reject) else .write (.lit 1)
def branch (route : Bool) : Com :=
  .ite (.lt (.var "size") (.lit 3)) reject
    (.seq (.assign "prefix" (.sub (.var "size") (.lit 3))) (guards (checks route) (success route)))
def program (route : Bool) : Com := .seq (.read "size") (.seq (readBlock readIO) (branch route))
def layout : Layout := ⟨["base","idx","size","value","prefix"], ["bank"], 10⟩

def routeOutput (route : Bool) (xs : List Nat) : List Nat :=
  if 3 ≤ xs.length ∧ (route = true ∨ xs.length = 3) ∧ xs.drop (xs.length - 3) = [0,2,0]
  then if route then 0 :: xs.take (xs.length - 3) ++ [0] else [1]
  else [0]

theorem program_ok (route : Bool) : Com.Ok layout (program route) := by
  cases route <;> simp [program, branch, checks, success, reject, layout, readIO, writeIO, guards,
    readBlock, readBody, writeBlock, writeBody, Mathproof.Problem18IMPFieldAddition20261001.address,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr]

private theorem array_at_read (r : Names) (σ : Env) (xs : List Nat)
    (hb : σ.vars r.base = 0) (hlen : (σ.arrs r.array).length = xs.length) :
    (readState r σ xs [] xs.length).arrs r.array = xs := by
  have harray : (readState r σ xs [] xs.length).arrs r.array =
      writeValues (σ.arrs r.array) (σ.vars r.base) (fun j => xs.getD j 0) xs.length := by
    simp [readState,pointState,Names.point]
  have ho : ((readState r σ xs [] xs.length).arrs r.array).length = xs.length := by
    rw [harray,writeValues_length,hlen]
  apply List.ext_getElem ho
  intro j hj hj'
  have hd : ((readState r σ xs [] xs.length).arrs r.array).getD j 0 = xs.getD j 0 := by
    rw [harray,hb]
    simpa only [Nat.zero_add] using writeValues_inside (σ.arrs r.array) 0 xs.length j
      (fun k => xs.getD k 0) (by rw [hlen]; omega) hj'
  simpa only [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hj'] using hd

private theorem checks_run {B : Nat} {σ : Env} (cs : List Cond) (bs : List Bool)
    (he : List.Forall₂ (fun c b => c.evalB B σ = some b) cs bs) (hB : 0 < B)
    (yes : Com) (T : Nat) (vs : List Nat)
    (hy : bs.all id = true → ∃ τ, Run B yes σ τ T ∧ τ.out = σ.out ++ vs) :
    ∃ τ, Run B (guards cs yes) σ τ (guardsCost cs + T + 2) ∧
      τ.out = σ.out ++ if bs.all id then vs else [0] := by
  induction he with
  | nil =>
    obtain ⟨τ,hr,ho⟩ := hy rfl
    exact ⟨τ,hr.mono (by simp [guardsCost]),ho⟩
  | cons hc ht ih =>
    rename_i c b cs bs
    cases b with
    | false =>
      have hw := Run.write (σ := σ) (evalB_lit (n := 0) hB)
      refine ⟨_,(Run.ite_false hc hw).mono ?_,?_⟩
      · simp [guardsCost,Expr.size]; omega
      · simp
    | true =>
      obtain ⟨τ,hr,ho⟩ := ih (by simpa using hy)
      refine ⟨τ,(Run.ite_true hc hr).mono ?_,?_⟩
      · simp [guardsCost]; omega
      · simpa using ho

private theorem suffix_words (xs : List Nat) (h : 3 ≤ xs.length) :
    xs.drop (xs.length - 3) =
      [xs.getD (xs.length-3) 0, xs.getD (xs.length-3+1) 0, xs.getD (xs.length-3+2) 0] := by
  let j := xs.length - 3
  have h0 : j < xs.length := by dsimp [j]; omega
  have h1 : j+1 < xs.length := by dsimp [j]; omega
  have h2 : j+2 < xs.length := by dsimp [j]; omega
  have h3 : j+2+1 = xs.length := by dsimp [j]; omega
  change xs.drop j = [xs.getD j 0,xs.getD (j+1) 0,xs.getD (j+2) 0]
  rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
  rw [show (j+1)+1 = j+2 by omega, List.drop_eq_getElem_cons h2, h3]
  simp only [List.drop_length, List.getD_eq_getElem _ _ h0, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2]

theorem program_run (route : Bool) (xs : List Nat) {B : Nat}
    (hl : xs.length < B) (hb : 3 < B) (hv : ∀ a ∈ xs, a < B) :
    ∃ τ, Run B (program route)
      (initEnv (fun a => if a = "bank" then xs.length else 0) (xs.length :: xs)) τ
      (80 * xs.length + 500) ∧ τ.out = routeOutput route xs := by
  let σ := initEnv (fun a => if a = "bank" then xs.length else 0) (xs.length :: xs)
  let ρ := {σ.setVar "size" xs.length with inp := xs}
  have hin : Run B (.read "size") σ ρ 1 := Run.read rfl
  have hbase : ρ.vars readIO.base = 0 := by simp [ρ,σ,readIO,Env.setVar,initEnv]
  have hsize : ρ.vars readIO.limit = xs.length := by simp [ρ,readIO,Env.setVar]
  have hlen : (ρ.arrs readIO.array).length = xs.length := by simp [ρ,σ,readIO,Env.setVar,initEnv]
  have hvIO : readIO.Valid := by simp [Names.Valid,readIO]
  let η := readState readIO ρ xs [] xs.length
  have hr := readBlock_run readIO hvIO (B := B) ρ xs [] (by simp [ρ]) hl hsize
    (by rw [hbase,hlen]; omega) (by rwa [hlen]) hv
  have ha : η.arrs "bank" = xs := array_at_read readIO ρ xs hbase hlen
  have hsizeη : η.vars "size" = xs.length :=
    (readState_vars readIO ρ xs [] xs.length "size" (by decide) (by decide)).trans hsize
  have hbaseη : η.vars "base" = 0 :=
    (readState_vars readIO ρ xs [] xs.length "base" (by decide) (by decide)).trans hbase
  have houtη : η.out = [] := by rfl
  have hsmall := evalB_condLt (σ := η) (e := .var "size") (f := .lit 3)
    (evalB_var (hsizeη ▸ hl)) (evalB_lit hb)
  rw [hsizeη] at hsmall
  by_cases hh : xs.length < 3
  · have hbRun := Run.write (σ := η) (evalB_lit (n := 0) (by omega : 0 < B))
    have ht : Run B (branch route) η _ _ :=
      Run.ite_true (by simpa only [hh, decide_true] using hsmall) hbRun
    refine ⟨_, (hin.seq (hr.seq ht)).mono ?_, ?_⟩
    · simp [size_condLt,size_var,size_lit]; omega
    · simp [routeOutput,houtη,show ¬ 3 ≤ xs.length by omega]
  · let j := xs.length - 3
    have hj : j + 2 < xs.length := by dsimp [j]; omega
    let ξ := η.setVar "prefix" j
    have hassign : (Expr.sub (.var "size") (.lit 3)).evalB B η = some j := by
      simp [evalB_bin_iff,hsizeη,j,hl,hb]; omega
    have hset := Run.assign (x := "prefix") hassign
    have hp : ξ.vars "prefix" = j := by simp [ξ,Env.setVar]
    have hBnk : ξ.arrs "bank" = xs := ha
    have hSx : ξ.vars "size" = xs.length := hsizeη
    have hBase : ξ.vars "base" = 0 := hbaseη
    have hOut : ξ.out = [] := houtη
    have dial (k : ℕ) (hk : k < xs.length) (e : Expr)
        (he : e.evalB B ξ = some k) :
        (Expr.get "bank" e).evalB B ξ = some (xs.getD k 0) := by
      rw [List.getD_eq_getElem _ _ hk]
      exact evalB_get he (by rw [hBnk]; simp [hk]) (hv _ (List.getElem_mem hk))
    have e0 : (Expr.var "prefix").evalB B ξ = some j := by
      simpa only [hp] using (evalB_var (σ := ξ) (x := "prefix") (by rw [hp]; omega))
    have eplus (v : ℕ) (hv2 : v ≤ 2) :
        (Expr.add (.var "prefix") (.lit v)).evalB B ξ = some (j + v) :=
      evalB_bin e0 (evalB_lit (by omega)) (by simp; omega)
    have b0 := evalB_condEq (dial j (by omega) _ e0) (evalB_lit (n := 0) (by omega : 0 < B))
    have b1 := evalB_condEq (dial (j+1) (by omega) _ (eplus 1 (by decide)))
      (evalB_lit (n := 2) (by omega : 2 < B))
    have b2 := evalB_condEq (dial (j+2) hj _ (eplus 2 (by decide)))
      (evalB_lit (n := 0) (by omega : 0 < B))
    have b3 : (Cond.eq (.var "size") (.lit 3)).evalB B ξ = some (xs.length == 3) := by
      simpa only [hSx] using evalB_condEq (σ := ξ) (e := .var "size") (f := .lit 3)
        (evalB_var (hSx ▸ hl)) (evalB_lit hb)
    let bs := [xs.getD j 0 == 0,xs.getD (j+1) 0 == 2,xs.getD (j+2) 0 == 0] ++
      (if route then [] else [xs.length == 3])
    have hbs : List.Forall₂ (fun c b => c.evalB B ξ = some b) (checks route) bs := by
      cases route
      · exact .cons b0 (.cons b1 (.cons b2 (.cons b3 .nil)))
      · exact .cons b0 (.cons b1 (.cons b2 .nil))
    let ys := xs.take j
    have hyLen : ys.length = j := by simp [ys,List.length_take]; omega
    let good := if route then 0 :: ys ++ [0] else [1]
    have yes : bs.all id = true →
        ∃ τ, Run B (success route) ξ τ (20 * (xs.length+1)+10) ∧ τ.out = ξ.out ++ good := by
      intro _
      cases route
      · exact ⟨_, (Run.write (σ := ξ) (evalB_lit (n := 1) (by omega : 1 < B))).mono (by simp <;> omega), rfl⟩
      · let ξ' := {ξ with out := ξ.out ++ [0]}
        have hz : Run B reject ξ ξ' 2 := Run.write (evalB_lit (by omega))
        obtain ⟨hw,ho⟩ := writeBlock_run writeIO (by simp [Names.Valid,writeIO,readIO]) (B := B) ξ' ys
          (by rw [hyLen]; omega) (by simpa [ξ',writeIO] using hp.trans hyLen.symm)
          (by change ξ.vars "base" + ys.length ≤ (ξ.arrs "bank").length
              rw [hBase,hyLen,hBnk]; omega)
          (by change (ξ.arrs "bank").length < B; rwa [hBnk])
          (fun v h => hv v (List.mem_of_mem_take h))
          (by intro k hk
              change (ξ.arrs "bank").getD (ξ.vars "base"+k) 0 = ys.getD k 0
              rw [hBase, Nat.zero_add, hBnk]
              have hx : k < xs.length := by rw [hyLen] at hk; omega
              simp only [ys, List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hk, List.getElem_take])
        have hf := Run.write (σ := writeState writeIO ξ' ys ys.length) (evalB_lit (n := 0) (by omega : 0 < B))
        refine ⟨_, (hz.seq (hw.seq hf)).mono ?_, ?_⟩
        · simp [hyLen]; omega
        · simp [good,ho,ξ',List.append_assoc]
    obtain ⟨τ, hgo, hout⟩ := checks_run (checks route) bs hbs (by omega) (success route) _ good yes
    have ht : Run B (branch route) η τ _ :=
      Run.ite_false (by simpa only [hh, decide_false] using hsmall) (hset.seq hgo)
    refine ⟨τ, (hin.seq (hr.seq ht)).mono ?_, ?_⟩
    · cases route <;> simp [checks,guardsCost,size_condLt,size_var,size_lit,size_sub,size_get,size_condEq,size_add] <;> omega
    · have he : bs.all id = true ↔ (route = true ∨ xs.length = 3) ∧ xs.drop j = [0,2,0] := by
        rw [show xs.drop j = _ from suffix_words xs (by omega)]
        cases route <;> simp [bs,j,List.all_cons,and_assoc,and_left_comm,and_comm]
      simp only [hout, hOut, List.nil_append, routeOutput, show 3 ≤ xs.length by omega, true_and]
      change (if bs.all id = true then good else [0]) =
        if (route = true ∨ xs.length = 3) ∧ xs.drop j = [0,2,0] then good else [0]
      by_cases hgood : bs.all id = true
      · simp only [if_pos hgood, if_pos (he.mp hgood)]
      · simp only [if_neg hgood, if_neg (fun hh => hgood (he.mpr hh))]

theorem routeOutput_ramPolytime (route : Bool) : RamPolytime (routeOutput route) := by
  apply ramPolytime_of_bounded_imp layout (program route) (routeOutput route)
    (Polynomial.C 3) (80 * Polynomial.X + 500) (program_ok route)
  intro xs
  let B := 2 ^ ((3 : Nat) + bitSize xs + 1)
  have hx := Lax51Proofs.Encoding.length_le_bitSize xs
  have hl : xs.length < B := by
    exact (Nat.lt_two_pow_self (n := xs.length)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : 3 < B := by
    exact lt_of_lt_of_le (by decide : 3 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hv : ∀ a ∈ xs, a < B := fun a h =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one h).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨τ, hr, ho⟩ := program_run route xs hl hb hv
  refine ⟨fun a => if a = "bank" then xs.length else 0, τ, ?_, ho⟩
  simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat]
  exact hr.mono (by omega)

theorem routeOutput_time (route : Bool) : TuringPolytime (routeOutput route) :=
  Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime (routeOutput_ramPolytime route)

#print axioms routeOutput_time
end EvenTI.P12Guard
