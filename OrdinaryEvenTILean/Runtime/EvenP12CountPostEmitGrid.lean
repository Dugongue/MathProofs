import EvenP12CountPostClassify
import EvenP12CountPreSegments

namespace EvenTI.P12CountPost

open EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
set_option autoImplicit false
set_option maxHeartbeats 500000

def flagAt (xs : List ℕ) (a : ℕ) : ℕ := if xs.getD a 0 = 2 then 1 else 0

def emitFlag (addr : Expr) : Com :=
  .ite (.lt addr (.var "length"))
    (.ite (.eq (.get "data" addr) (.lit 2)) (.write (.lit 1)) (.write (.lit 0)))
    (.write (.lit 0))

theorem emitFlag_run (xs : List ℕ) {B : ℕ} {σ : Env} (addr : Expr) (a : ℕ)
    (hB : 2 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hL : σ.vars "length" = xs.length) (hdata : σ.arrs "data" = sentinelWords xs)
    (he : addr.evalB B σ = some a) :
    Run B (emitFlag addr) σ {σ with out := σ.out ++ [flagAt xs a]} (20 + 2*addr.size) := by
  have hL' : (Expr.var "length").evalB B σ = some xs.length := by
    simpa only [hL] using evalB_var (B := B) (σ := σ) (x := "length") (by rwa [hL])
  have eg := evalB_condLt he hL'
  by_cases ha : a < xs.length
  · have hg : (Cond.lt addr (.var "length")).evalB B σ = some true := by simpa [ha] using eg
    have hget : (Expr.get "data" addr).evalB B σ = some xs[a] := by
      refine evalB_get he ?_ (hv _ (List.getElem_mem ha))
      rw [hdata,sentinelWords,List.getElem?_append_left ha, List.getElem?_eq_getElem ha]
    have e := evalB_condEq hget (evalB_lit hB)
    by_cases ht : xs[a] = 2
    · have e' : (Cond.eq (.get "data" addr) (.lit 2)).evalB B σ = some true := by simpa [ht] using e
      have r := Run.ite_true (d := .write (.lit 0)) e'
        (Run.write (evalB_lit (by omega : 1 < B)))
      have rr := Run.ite_true (d := .write (.lit 0)) hg r
      simp only [flagAt, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha,Option.getD_some,ht,if_true]
      exact rr.mono (by simp; omega)
    · have e' : (Cond.eq (.get "data" addr) (.lit 2)).evalB B σ = some false := by simpa [ht] using e
      have r := Run.ite_false (c := .write (.lit 1)) e'
        (Run.write (evalB_lit (by omega : 0 < B)))
      have rr := Run.ite_true (d := .write (.lit 0)) hg r
      simp only [flagAt, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha,Option.getD_some,ht,if_false]
      exact rr.mono (by simp; omega)
  · have hg : (Cond.lt addr (.var "length")).evalB B σ = some false := by simpa [ha] using eg
    have rr := Run.ite_false (c := .ite (.eq (.get "data" addr) (.lit 2)) (.write (.lit 1)) (.write (.lit 0)))
      hg (Run.write (evalB_lit (by omega : 0 < B)))
    simp only [flagAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (Nat.le_of_not_gt ha), Option.getD_none, show (0:ℕ) ≠ 2 by decide, if_false]
    exact rr.mono (by simp; omega)

def emitFlagRow : ℕ → Com
  | 0 => .skip
  | q+1 => .seq (emitFlagRow q) (emitFlag (.add (.var "cell") (.lit (2*q))))

theorem emitFlagRow_run (q : ℕ) (xs : List ℕ) {B : ℕ} {σ : Env} (base : ℕ)
    (hB : 2 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hL : σ.vars "length" = xs.length) (hdata : σ.arrs "data" = sentinelWords xs)
    (hcell : σ.vars "cell" = base) (hCap : base + 2*q < B) :
    Run B (emitFlagRow q) σ
      {σ with out := σ.out ++ (List.range q).map (fun k => flagAt xs (base+2*k))}
      (26*q+1) := by
  induction q with
  | zero => simpa [emitFlagRow] using (Run.skip (B := B) (σ := σ))
  | succ q ih =>
    let ws := (List.range q).map (fun k => flagAt xs (base + 2*k))
    let t := {σ with out := σ.out ++ ws}
    have hprev : Run B (emitFlagRow q) σ t (26*q+1) := ih (by omega)
    have eC : (Expr.var "cell").evalB B t = some base := by
      have hx : t.vars "cell" = base := hcell
      simpa only [hx] using evalB_var (B := B) (σ := t) (x := "cell") (by rw [hx]; omega)
    have ea : (Expr.add (.var "cell") (.lit (2*q))).evalB B t = some (base+2*q) :=
      evalB_bin (op := .add) eC (evalB_lit (by omega)) (by simp; omega)
    have hr := emitFlag_run xs (σ := t) (.add (.var "cell") (.lit (2*q))) (base+2*q) hB hlen hv hL hdata ea
    rw [emitFlagRow,List.range_succ,List.map_append,List.map_singleton,← List.append_assoc]
    exact (hprev.seq hr).mono (by simp only [size_add,size_var,size_lit]; omega)

def reverseFlags (q : ℕ) (xs : List ℕ) (base : ℕ) : ℕ → List ℕ
  | 0 => []
  | r+1 => (List.range q).map (fun k => flagAt xs (base+(2*q*r+2*k))) ++
    reverseFlags q xs base r

def gridGuard : Cond := .lt (.lit 0) (.var "rows")

def gridBody (q : ℕ) : Com :=
  .seq (.assign "rows" (.sub (.var "rows") (.lit 1)))
    (.seq (.assign "cell" (.add (.var "base") (.mul (.lit (2*q)) (.var "rows"))))
      (emitFlagRow q))

def emitGrid (q : ℕ) : Com := .while gridGuard (gridBody q)

theorem emitGrid_run (q : ℕ) (xs : List ℕ) {B : ℕ} {σ : Env} (base rows : ℕ)
    (hB : 2 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hQ : 2*q < B) (hRows : rows < B)
    (hL : σ.vars "length" = xs.length) (hdata : σ.arrs "data" = sentinelWords xs)
    (hBase : σ.vars "base" = base) (hR : σ.vars "rows" = rows)
    (hCap : base + 2*q*rows < B) :
    ∃ τ, Run B (emitGrid q) σ τ ((26*q+15)*rows+4) ∧
      τ.out = σ.out ++ reverseFlags q xs base rows := by
  let I (t : Env) : Prop := t.vars "rows" ≤ rows ∧ t.vars "length" = xs.length ∧
    t.arrs "data" = sentinelWords xs ∧ t.vars "base" = base ∧
    t.out ++ reverseFlags q xs base (t.vars "rows") = σ.out ++ reverseFlags q xs base rows
  let V (t : Env) : ℕ := t.vars "rows"
  have eg (t : Env) (ht : I t) :
      gridGuard.evalB B t = some (decide (0 < t.vars "rows")) :=
    evalB_condLt (evalB_lit (by omega)) (evalB_var (ht.1.trans_lt hRows))
  have estep (t : Env) (ht : I t) (hg : gridGuard.evalB B t = some true) :
      ∃ u, Run B (gridBody q) t u (26*q+11) ∧ I u ∧ V u < V t := by
    rw [eg t ht] at hg
    have hpos : 0 < t.vars "rows" := by simpa using hg
    let r := t.vars "rows" - 1
    have hr : r+1 = t.vars "rows" := by omega
    have hrle : r+1 ≤ rows := hr ▸ ht.1
    have hMul := Nat.mul_le_mul_left (2*q) hrle
    have hbr : base + 2*q*r + 2*q < B := by
      rw [show base + 2*q*r + 2*q = base + 2*q*(r+1) by ring]
      omega
    let s := t.setVar "rows" r
    let v := s.setVar "cell" (base+2*q*r)
    let u := {v with out := v.out ++ (List.range q).map (fun k => flagAt xs (base+2*q*r + 2*k))}
    have er : (Expr.sub (.var "rows") (.lit 1)).evalB B t = some r :=
      evalB_bin (op := .sub) (evalB_var (ht.1.trans_lt hRows))
        (evalB_lit (by omega)) (by change r < B; omega)
    have eb : (Expr.var "base").evalB B s = some base := by
      have h : s.vars "base" = base := by simpa [s] using ht.2.2.2.1
      simpa only [h] using evalB_var (B := B) (σ := s) (x := "base") (by rw [h]; omega)
    have en : (Expr.var "rows").evalB B s = some r := by
      have h : s.vars "rows" = r := by simp [s]
      simpa only [h] using evalB_var (B := B) (σ := s) (x := "rows") (by rw [h]; omega)
    have em : (Expr.mul (.lit (2*q)) (.var "rows")).evalB B s = some (2*q*r) :=
      evalB_bin (op := .mul) (evalB_lit hQ) en (by simp; omega)
    have ec : (Expr.add (.var "base") (.mul (.lit (2*q)) (.var "rows"))).evalB B s =
        some (base+2*q*r) := evalB_bin (op := .add) eb em (by simp; omega)
    have r₁ : Run B (.assign "rows" (.sub (.var "rows") (.lit 1))) t s 4 := Run.assign er
    have r₂ : Run B (.assign "cell" (.add (.var "base") (.mul (.lit (2*q)) (.var "rows")))) s v 6 :=
      Run.assign ec
    have r₃ : Run B (emitFlagRow q) v u (26*q+1) :=
      emitFlagRow_run q xs (base+2*q*r) hB hlen hv (by simpa [v,s] using ht.2.1)
        (by simpa [v,s] using ht.2.2.1) (by simp [v]) hbr
    refine ⟨u,(r₁.seq (r₂.seq r₃)).mono (by omega),⟨?_,?_,?_,?_,?_⟩,?_⟩
    · simp [u,v,s]; omega
    · simpa [u,v,s] using ht.2.1
    · simpa [u,v,s] using ht.2.2.1
    · simpa [u,v,s] using ht.2.2.2.1
    · have hh := ht.2.2.2.2
      rw [← hr,reverseFlags] at hh
      simpa [u,v,s,List.append_assoc,Nat.add_assoc] using hh
    · simp [u,v,s,V]; omega
  obtain ⟨τ, hrun, hI, hfalse⟩ := Run.while_count I V (26*q+11)
    (fun t h => ⟨_,eg t h⟩) estep ⟨by rw [hR],hL,hdata,hBase,by rw [hR]⟩
  rw [eg τ hI] at hfalse
  have hz : τ.vars "rows" = 0 := by
    have : ¬ 0 < τ.vars "rows" := by simpa using hfalse
    omega
  refine ⟨τ, hrun.mono ?_, ?_⟩
  · simp [gridGuard,V,hR,show 4+(26*q+11) = 26*q+15 by omega]
  · simpa [hz,reverseFlags] using hI.2.2.2.2

#print axioms emitFlag_run
#print axioms emitFlagRow_run
#print axioms emitGrid_run
end EvenTI.P12CountPost
