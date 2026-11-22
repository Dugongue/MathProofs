import EvenP12CountPreSegments
import Mathproof.Meta.Problem18IMPFieldLayout20261001

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open EvenTI.P12CountPre (sentinelWords)
set_option autoImplicit false
set_option maxHeartbeats 580000

/-- Linear positions of the diagonal in an n-by-n row-major matrix are
exactly the multiples of n+1 below n². -/
theorem diagonal_offset_iff (n i j : ℕ) (hi : i < n) (hj : j < n) :
    (i*n+j) / (n+1) * (n+1) = i*n+j ↔ i=j := by
  let a := (i*n+j)/(n+1)
  have hPos : 0 < n := by omega
  have quot (x y : ℕ) (hy : y < n) : (x*n+y)/n = x := by
    rw [Nat.add_comm, Nat.mul_comm x n, Nat.add_mul_div_left _ _ hPos, Nat.div_eq_of_lt hy, Nat.zero_add]
  constructor
  · intro h
    change a*(n+1)=i*n+j at h
    have hh : a*n+a = i*n+j := by simpa only [Nat.mul_succ] using h
    have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hm
    have ha : a < n := by
      by_contra! hw
      have hmul := Nat.mul_le_mul_right n hw
      omega
    have hx := congrArg (fun k : ℕ => k/n) hh
    change (a*n+a)/n=(i*n+j)/n at hx
    rw [quot a a ha,quot i j hj] at hx
    have hh' : i*n+i = i*n+j := by simpa only [hx] using hh
    omega
  · intro h
    subst j
    rw [show i*n+i = i*(n+1) by rw [Nat.mul_succ]]
    rw [Nat.mul_div_cancel _ (Nat.succ_pos _)]
def scalarExpected (stride diagonal zero j : ℕ) : ℕ :=
  if j / stride * stride = j then diagonal else zero

private def onDiagonal : Cond :=
  .eq (.mul (.div (.var "index") (.var "stride")) (.var "stride")) (.var "index")

private def selectExpected (zero : ℕ) : Com :=
  .ite onDiagonal (.assign "expect" (.var "diag")) (.assign "expect" (.lit zero))

private def entryEqual : Cond :=
  .eq (.get "data" (.add (.var "base") (.var "index"))) (.var "expect")

private def keepBit : Com := .ite entryEqual .skip (.assign "good" (.lit 0))

private def nextIndex : Com := .assign "index" (.add (.var "index") (.lit 1))

private def checkBody (zero : ℕ) : Com := .seq (selectExpected zero) (.seq keepBit nextIndex)

private def checkGuard : Cond := .lt (.var "index") (.var "count")

def scalarMatrixScan (zero : ℕ) : Com := .while checkGuard (checkBody zero)

def scalarMatrixScanLayout : Layout :=
  ⟨["index","count","stride","diag","expect","base","good"],["data"],5⟩

theorem scalarMatrixScan_ok (zero : ℕ) : Com.Ok scalarMatrixScanLayout (scalarMatrixScan zero) := by
  simp [scalarMatrixScan,checkGuard,checkBody,selectExpected,onDiagonal,entryEqual,keepBit,
    nextIndex,scalarMatrixScanLayout,Com.Ok,Expr.Ok,Cond.Ok,condExpr]

theorem scalarMatrixScan_run (xs : List ℕ) (zero n base diagonal : ℕ)
    {B : ℕ} {σ : Env} (hB : 1 < B) (hLen : xs.length < B)
    (hn : n+1 < B) (hz : zero < B) (hd : diagonal < B)
    (hWords : ∀ a ∈ xs, a < B) (hFit : base+n*n ≤ xs.length)
    (hi : σ.vars "index" = 0) (hc : σ.vars "count" = n*n)
    (hStride : σ.vars "stride" = n+1) (hBase : σ.vars "base" = base)
    (hDiag : σ.vars "diag" = diagonal) (hGood : σ.vars "good" = 1)
    (hData : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B (scalarMatrixScan zero) σ τ (60*(n*n)+8) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      (τ.vars "good" = 1 ↔ ∀ j < n*n, xs.getD (base+j) 0 = scalarExpected (n+1) diagonal zero j) := by
  let ok (j : ℕ) : Prop := xs.getD (base+j) 0 = scalarExpected (n+1) diagonal zero j
  let I (t : Env) : Prop :=
    t.vars "index" ≤ n*n ∧ t.vars "count" = n*n ∧
    t.vars "stride" = n+1 ∧ t.vars "base" = base ∧ t.vars "diag" = diagonal ∧
    t.arrs = σ.arrs ∧ t.inp = σ.inp ∧ t.out = σ.out ∧
    (t.vars "good" = 1 ↔ ∀ j < t.vars "index", ok j)
  let V (t : Env) := n*n - t.vars "index"
  have hg (t : Env) (ht : I t) : checkGuard.evalB B t = some (decide (t.vars "index" < n*n)) := by
    have ee := evalB_condLt (σ := t) (B := B) (e := .var "index") (f := .var "count")
      (evalB_var (ht.1.trans_lt (by omega))) (evalB_var (by rw [ht.2.1]; omega))
    simpa only [checkGuard,ht.2.1] using ee
  have step (t : Env) (ht : I t) (he : checkGuard.evalB B t = some true) :
      ∃ u, Run B (checkBody zero) t u 50 ∧ I u ∧ V u < V t := by
    let j := t.vars "index"
    rw [hg t ht] at he
    have hj : j < n*n := by simpa [j] using he
    have hread : base+j < xs.length := by omega
    have hJ : j+1 < B := by omega
    have hStrideT : t.vars "stride" = n+1 := ht.2.2.1
    have hBaseT : t.vars "base" = base := ht.2.2.2.1
    have hDiagT : t.vars "diag" = diagonal := ht.2.2.2.2.1
    have ev : (Expr.var "index").evalB B t = some j := evalB_var (by omega)
    have es : (Expr.var "stride").evalB B t = some (n+1) := by
      simpa only [hStrideT] using evalB_var (σ := t) (B := B) (x := "stride") (hStrideT ▸ hn)
    have hmul := Nat.div_mul_le_self j (n+1)
    have hDiv : (Expr.div (.var "index") (.var "stride")).evalB B t = some (j/(n+1)) := by
      apply evalB_bin (op := .div) ev es
      change j / (n+1) < B
      exact (Nat.div_le_self _ _).trans_lt (by omega)
    have em : (Expr.mul (.div (.var "index") (.var "stride")) (.var "stride")).evalB B t =
        some (j/(n+1)*(n+1)) := evalB_bin (op := .mul) hDiv es (by simp; omega)
    have ed := evalB_condEq em ev
    let expected := scalarExpected (n+1) diagonal zero j
    let s := t.setVar "expect" expected
    have hExpected : expected < B := by
      unfold expected scalarExpected
      split <;> assumption
    have hSel : Run B (selectExpected zero) t s 16 := by
      by_cases hh : j/(n+1)*(n+1)=j
      · have e : onDiagonal.evalB B t = some true := by simpa [onDiagonal,hh] using ed
        have edg : (Expr.var "diag").evalB B t = some diagonal := by
          simpa only [hDiagT] using evalB_var (σ := t) (B := B) (x := "diag") (hDiagT ▸ hd)
        have hr := Run.ite_true (d := .assign "expect" (.lit zero)) e (Run.assign (x := "expect") edg)
        have hS : expected = diagonal := if_pos hh
        simpa only [s,hS,selectExpected] using hr.mono (by simp [onDiagonal] <;> omega : _ ≤ 16)
      · have e : onDiagonal.evalB B t = some false := by simpa [onDiagonal,hh] using ed
        have hr := Run.ite_false (c := .assign "expect" (.var "diag")) e (Run.assign (x := "expect") (evalB_lit hz))
        have hS : expected = zero := if_neg hh
        simpa only [s,hS,selectExpected] using hr.mono (by simp [onDiagonal] <;> omega : _ ≤ 16)
    have eBase : (Expr.var "base").evalB B s = some base := by
      have h : s.vars "base" = base := by simpa [s] using hBaseT
      simpa only [h] using evalB_var (σ := s) (B := B) (x := "base") (by rw [h]; omega)
    have eIndex : (Expr.var "index").evalB B s = some j :=
      evalB_var (by change j < B; omega)
    have eAddress : (Expr.add (.var "base") (.var "index")).evalB B s = some (base+j) :=
      evalB_bin (op := .add) eBase eIndex (by simp; omega)
    have eWord : (Expr.get "data" (.add (.var "base") (.var "index"))).evalB B s =
        some (xs.getD (base+j) 0) := by
      rw [List.getD_eq_getElem _ _ hread]
      refine evalB_get eAddress ?_ (hWords _ (List.getElem_mem hread))
      change (t.arrs "data")[base+j]? = _
      rw [ht.2.2.2.2.2.1,hData,sentinelWords,List.getElem?_append_left hread,
        List.getElem?_eq_getElem hread]
    have eExpect : (Expr.var "expect").evalB B s = some expected := by
      have h : s.vars "expect" = expected := by simp [s]
      simpa only [h] using evalB_var (σ := s) (B := B) (x := "expect") (h ▸ hExpected)
    have eEq : entryEqual.evalB B s = some (decide (ok j)) := evalB_condEq eWord eExpect
    let v := if ok j then s else s.setVar "good" 0
    have hBit : Run B keepBit s v 12 := by
      by_cases hp : ok j
      · have ep : entryEqual.evalB B s = some true := by simpa only [hp,decide_true] using eEq
        simpa only [v,if_pos hp,keepBit] using
          (Run.ite_true (d := .assign "good" (.lit 0)) ep Run.skip).mono (by simp [entryEqual] <;> omega : _ ≤ 12)
      · have ep : entryEqual.evalB B s = some false := by simpa only [hp,decide_false] using eEq
        simpa only [v,if_neg hp,keepBit] using
          (Run.ite_false (c := .skip) ep (Run.assign (x := "good") (evalB_lit (by omega : 0 < B)))).mono
            (by simp [entryEqual] <;> omega : _ ≤ 12)
    have hIdx : v.vars "index" = j := by by_cases hp : ok j <;> simp [v,hp,s,j]
    let u := v.setVar "index" (j+1)
    have eNext : (Expr.add (.var "index") (.lit 1)).evalB B v = some (j+1) := by
      have ei : (Expr.var "index").evalB B v = some j := by
        simpa only [hIdx] using evalB_var (σ := v) (B := B) (x := "index") (by rw [hIdx]; omega)
      exact evalB_bin (op := .add) ei (evalB_lit hB) hJ
    have hNext : Run B nextIndex v u 4 := Run.assign eNext
    refine ⟨u,(hSel.seq (hBit.seq hNext)).mono (by decide),⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · simpa [u] using Nat.succ_le_of_lt hj
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using ht.2.1
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using hStrideT
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using hBaseT
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using hDiagT
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using ht.2.2.2.2.2.1
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using ht.2.2.2.2.2.2.1
    · by_cases hp : ok j <;> simpa [u,v,s,hp] using ht.2.2.2.2.2.2.2.1
    · have hh := ht.2.2.2.2.2.2.2.2
      have heq : (∀ k < j+1, ok k) ↔ (∀ k < j, ok k) ∧ ok j := by
        constructor
        · intro h
          exact ⟨fun k hk => h k (by omega),h j (by omega)⟩
        · intro h k hk
          by_cases hkj : k < j
          · exact h.1 k hkj
          · simpa [show k=j by omega] using h.2
      change (v.vars "good" = 1 ↔ ∀ k < j+1, ok k)
      rw [heq]
      by_cases hp : ok j
      · have hv : v.vars "good" = t.vars "good" := by simp [v,s,hp]
        rw [hv,and_iff_left hp]
        exact hh
      · simp [v,hp]
    · change n*n-(j+1) < n*n-j
      omega
  have hI : I σ := by simp [I,hi,hc,hStride,hBase,hDiag,hGood]
  obtain ⟨τ,hr,ht,hfalse⟩ := Run.while_count I V 50 (fun t ht => ⟨_,hg t ht⟩) step hI
  rw [hg τ ht] at hfalse
  have hend : τ.vars "index" = n*n := by
    have hh := ht.1
    have hf : ¬τ.vars "index" < n*n := by simpa using hfalse
    omega
  refine ⟨τ,hr.mono ?_,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,?_⟩
  · simp [V,hi,checkGuard] <;> omega
  · simpa only [hend] using ht.2.2.2.2.2.2.2.2

#print axioms diagonal_offset_iff
#print axioms scalarMatrixScan_run
end EvenTI.P15Scalar
