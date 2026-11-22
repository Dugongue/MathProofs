import EvenP15ReciprocalPower
import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairBoundaryMatrixPower20261004 (nReg exponentReg)

private def glI : String := "even.reciprocal.order.index"
private def glP : String := "even.reciprocal.order.qpower"
private def glN : String := "even.reciprocal.order.group"
private def glGuard : Cond := .lt (.var glI) (.var nReg)
private def glMulPrefix : Com := .assign glN (.mul (.var glN) (.var glP))
private def glAdvancePower (q : ℕ) : Com := .assign glP (.mul (.var glP) (.lit q))
private def glMulFactor : Com := .assign glN (.mul (.var glN) (.sub (.var glP) (.lit 1)))
private def glAdvanceIndex : Com := .assign glI (.add (.var glI) (.lit 1))
private def glBody (q : ℕ) : Com := .seq glMulPrefix (.seq (glAdvancePower q) (.seq glMulFactor glAdvanceIndex))
private def glInit : Com := .seq (.assign glI (.lit 0)) (.seq (.assign glP (.lit 1)) (.assign glN (.lit 1)))
private def glFinish : Com := .assign exponentReg (.sub (.var glN) (.lit 1))

/-- Compute the exact inverse exponent in `n` group-cardinality updates. -/
def installGLExponent (q : ℕ) : Com := .seq glInit (.seq (.while glGuard (glBody q)) glFinish)

private theorem live {B a : ℕ} {s : Env} {x : String} (h : s.vars x=a) (hb : a<B) :
    (Expr.var x).evalB B s = some a := evalB_var_iff.mpr ⟨h.symm,h ▸ hb⟩

private theorem qpower_lt {q n B k : ℕ} (hq : 1 < q) (hk : k ≤ n*n+n+2)
    (hCap : q^(n*n+n+2) < B) : q^k < B :=
  (Nat.pow_le_pow_right (by omega) hk).trans_lt hCap

private theorem one_lt_bound {q n B : ℕ} (hq : 1 < q) (hCap : q^(n*n+n+2)<B) : 1<B := by
  have hqB := qpower_lt hq (by omega : 1≤n*n+n+2) hCap
  rw [pow_one] at hqB
  omega

private theorem glStep_run {q n B k : ℕ} {s : Env} (hq : 1 < q) (hk : k < n) (hn : n < B)
    (hCap : q^(n*n+n+2) < B) (hi : s.vars glI = k)
    (hp : s.vars glP = q^k) (hG : s.vars glN = glCount q k) :
    ∃ t, Run B (glBody q) s t 18 ∧ t.vars glI=k+1 ∧ t.vars glP=q^(k+1) ∧
      t.vars glN=glCount q (k+1) ∧ t.vars nReg=s.vars nReg := by
  let a := glCount q k*q^k
  let p := q^(k+1)
  have hpp : 1 < p := by
    exact (show 1 < q^1 by simpa using hq).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hpCap : p < B := qpower_lt hq (by omega) hCap
  have hGCap : glCount q (k+1)<B := by
    exact (glCount_le q _).trans_lt (qpower_lt hq
      ((Nat.mul_le_mul (by omega : k+1 ≤ n) (by omega : k+1 ≤ n)).trans (by omega)) hCap)
  have hG₀ : glCount q k<B := (glCount_le q k).trans_lt (qpower_lt hq
    ((Nat.mul_le_mul hk.le hk.le).trans (by omega)) hCap)
  have ha : a < B := by
    calc
      a ≤ a*(p-1) := Nat.le_mul_of_pos_right _ (by omega)
      _ = glCount q (k+1) := (glCount_succ q k).symm
      _ < B := hGCap
  have hP₀ : q^k<B := qpower_lt hq (by omega) hCap
  have hqB : q<B := by simpa using qpower_lt hq (by omega : 1 ≤ n*n+n+2) hCap
  have h1 := one_lt_bound hq hCap
  let s₁ := s.setVar glN a
  let s₂ := s₁.setVar glP p
  let s₃ := s₂.setVar glN (glCount q (k+1))
  let s₄ := s₃.setVar glI (k+1)
  have r₁ : Run B glMulPrefix s s₁ 4 := Run.assign (evalB_bin (op:=.mul) (live hG hG₀) (live hp hP₀) ha)
  have ep : (Expr.mul (.var glP) (.lit q)).evalB B s₁ = some p := by
    have hpm : q^k*q = p := (pow_succ q k).symm
    rw [←hpm]
    exact evalB_bin (op:=.mul) (live (by simpa [s₁,glP,glN] using hp) hP₀)
      (evalB_lit hqB) (show q^k*q < B by rwa [hpm])
  have r₂ : Run B (glAdvancePower q) s₁ s₂ 4 := Run.assign ep
  have eg : (Expr.mul (.var glN) (.sub (.var glP) (.lit 1))).evalB B s₂ = some (glCount q (k+1)) := by
    have he : a*(p-1) = glCount q (k+1) := (glCount_succ q k).symm
    rw [←he]
    exact evalB_bin (op:=.mul) (live (by simp [s₂,s₁,glP,glN]) ha)
      (evalB_bin (op:=.sub) (live (by simp [s₂]) hpCap) (evalB_lit h1) (by change p-1<B; omega))
      (show a*(p-1) < B by rwa [he])
  have r₃ : Run B glMulFactor s₂ s₃ 6 := Run.assign eg
  have r₄ : Run B glAdvanceIndex s₃ s₄ 4 := Run.assign (evalB_bin (op:=.add)
    (live (by simpa [s₃,s₂,s₁,glI,glN,glP] using hi) (hk.trans hn))
    (evalB_lit h1) (by change k+1<B; omega))
  refine ⟨s₄,r₁.seq (r₂.seq (r₃.seq r₄)),by simp [s₄],?_,?_,?_⟩
  · simp [s₄,s₃,s₂,glI,glN,glP,p]
  · simp [s₄,s₃,glI,glN]
  · simp [s₄,s₃,s₂,s₁,glI,glN,glP,nReg]

/-- Exact paid exponent computation, including the zero-dimensional group.
The compiler word length needed for the result is quadratic in the dimension. -/
theorem installGLExponent_run {q n B : ℕ} {s : Env} (hq : 1 < q)
    (hn : n<B) (hCap : q^(n*n+n+2)<B) (hLive : s.vars nReg=n) :
    ∃ t, Run B (installGLExponent q) s t (26*n+20) ∧
      t.vars exponentReg=glCount q n-1 ∧ Frame (installGLExponent q) s t := by
  let I (t : Env) := t.vars glI ≤ n ∧ t.vars glP = q^(t.vars glI) ∧
    t.vars glN = glCount q (t.vars glI) ∧ t.vars nReg=n
  let V (t : Env) := n-t.vars glI
  have h1 := one_lt_bound hq hCap
  let s₁ := s.setVar glI 0
  let s₂ := s₁.setVar glP 1
  let u := s₂.setVar glN 1
  have r₁ : Run B (.assign glI (.lit 0)) s s₁ 2 := Run.assign (evalB_lit (by omega))
  have r₂ : Run B (.assign glP (.lit 1)) s₁ s₂ 2 := Run.assign (evalB_lit h1)
  have r₃ : Run B (.assign glN (.lit 1)) s₂ u 2 := Run.assign (evalB_lit h1)
  have hu : I u := by
    simpa [I,u,s₂,s₁,glI,glP,glN,nReg] using hLive
  have hg (t : Env) (ht : I t) : glGuard.evalB B t = some (decide (t.vars glI<n)) :=
    evalB_condLt (evalB_var (ht.1.trans_lt hn)) (live ht.2.2.2 hn)
  have step (t : Env) (ht : I t) (he : glGuard.evalB B t=some true) :
      ∃ t',Run B (glBody q) t t' 18 ∧ I t' ∧ V t'<V t := by
    rw [hg t ht] at he
    have hlt : t.vars glI < n := by simpa using he
    obtain ⟨t',r,hi,hp,hg,hn'⟩ := glStep_run hq hlt hn hCap rfl ht.2.1 ht.2.2.1
    refine ⟨t',r,⟨by omega,by rw [hi,hp],by rw [hi,hg],hn'.trans ht.2.2.2⟩,?_⟩
    simp only [V,hi]
    omega
  obtain ⟨v,rv,hv,hStop⟩ := Run.while_count I V 18 (fun t ht => ⟨_,hg t ht⟩) step hu
  have hi : v.vars glI=n := by
    rw [hg v hv] at hStop
    have := hv.1
    have hNot : ¬ v.vars glI<n := by simpa using hStop
    omega
  have hG : v.vars glN=glCount q n := hv.2.2.1.trans (congrArg (glCount q) hi)
  have hGCap : glCount q n<B := (glCount_le q n).trans_lt (qpower_lt hq (by omega) hCap)
  let t := v.setVar exponentReg (glCount q n-1)
  have rt : Run B glFinish v t 4 := Run.assign (evalB_bin (op:=.sub) (live hG hGCap)
    (evalB_lit h1) (by change glCount q n-1<B; omega))
  have run : Run B (installGLExponent q) s t (26*n+20) :=
    (r₁.seq (r₂.seq r₃)).seq (rv.seq rt) |>.mono (by simp [V,u,s₂,s₁,glI,glP,glN,glGuard,Cond.size,Expr.size] <;> omega)
  exact ⟨t,run,by simp [t],Frame.of_run run⟩

#print axioms installGLExponent_run
end EvenTI.P15Execution