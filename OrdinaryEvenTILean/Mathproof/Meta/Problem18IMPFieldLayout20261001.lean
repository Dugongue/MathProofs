import Mathproof.Meta.Problem18IMPModularArithmetic20261001
import Mathproof.Meta.Problem18RAMLax13ProofsReasoning20261001

set_option backward.isDefEq.respectTransparency false
namespace Mathproof.Problem18IMPFieldLayout20261001
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- Names are static program parameters, never runtime callbacks. -/
structure FieldNames where
  mem : String
  scratch : String
  p : String
  e : String
  modBase : String
  aBase : String
  bBase : String
  outBase : String
  exp : String
  i : String
  j : String
  k : String
  value : String
  exponent : String
  flag : String
  deriving DecidableEq

def canonical : FieldNames :=
  ⟨"P18.mem","P18.scratch","P18.p","P18.e","P18.modBase",
    "P18.aBase","P18.bBase","P18.outBase","P18.exp",
    "P18.tmp.i","P18.tmp.j","P18.tmp.k","P18.tmp.value","P18.tmp.exponent","P18.flag"⟩

def scalarNames (r : FieldNames) : List String :=
  [r.p,r.e,r.modBase,r.aBase,r.bBase,r.outBase,r.exp,r.i,r.j,r.k,r.value,r.exponent,r.flag]

def ValidNames (r : FieldNames) : Prop := (scalarNames r).Nodup ∧ r.mem ≠ r.scratch

theorem canonical_valid : ValidNames canonical := by
  unfold ValidNames scalarNames canonical
  decide

def scalarWrites : Com → Finset String
  | .assign x _ => {x}
  | .read x => {x}
  | .seq c d => scalarWrites c ∪ scalarWrites d
  | .ite _ c d => scalarWrites c ∪ scalarWrites d
  | .while _ c => scalarWrites c
  | _ => ∅

def arrayWrites : Com → Finset String
  | .store a _ _ => {a}
  | .seq c d => arrayWrites c ∪ arrayWrites d
  | .ite _ c d => arrayWrites c ∪ arrayWrites d
  | .while _ c => arrayWrites c
  | _ => ∅

def noRead : Com → Prop
  | .read _ => False
  | .seq c d => noRead c ∧ noRead d
  | .ite _ c d => noRead c ∧ noRead d
  | .while _ c => noRead c
  | _ => True

theorem bigStep_vars_frame {c : Com} {σ τ : Env} {t : Nat} (h : BigStep c σ τ t) :
    ∀x,x ∉ scalarWrites c → τ.vars x=σ.vars x := by
  induction h with
  | skip => intro x hx; rfl
  | assign _ => intro x hx; simp only [scalarWrites,Finset.mem_singleton] at hx; simp [hx]
  | store _ _ _ => intro x hx; rfl
  | seq _ _ ih ih' =>
    intro x hx
    simp only [scalarWrites,Finset.mem_union,not_or] at hx
    exact (ih' x hx.2).trans (ih x hx.1)
  | ite_true _ _ ih => intro x hx; simp only [scalarWrites,Finset.mem_union,not_or] at hx; exact ih x hx.1
  | ite_false _ _ ih => intro x hx; simp only [scalarWrites,Finset.mem_union,not_or] at hx; exact ih x hx.2
  | while_true _ _ _ ih ih' => intro x hx; exact (ih' x hx).trans (ih x hx)
  | while_false _ => intro x hx; rfl
  | read _ => intro x hx; simp only [scalarWrites,Finset.mem_singleton] at hx; simp [Env.setVar,hx]
  | write _ => intro x hx; rfl

theorem bigStep_arrays_frame {c : Com} {σ τ : Env} {t : Nat} (h : BigStep c σ τ t) :
    ∀a,a ∉ arrayWrites c → τ.arrs a=σ.arrs a := by
  induction h with
  | skip => intro a ha; rfl
  | assign _ => intro a ha; rfl
  | store _ _ _ => intro a ha; simp only [arrayWrites,Finset.mem_singleton] at ha; simp [ha]
  | seq _ _ ih ih' =>
    intro a ha
    simp only [arrayWrites,Finset.mem_union,not_or] at ha
    exact (ih' a ha.2).trans (ih a ha.1)
  | ite_true _ _ ih => intro a ha; simp only [arrayWrites,Finset.mem_union,not_or] at ha; exact ih a ha.1
  | ite_false _ _ ih => intro a ha; simp only [arrayWrites,Finset.mem_union,not_or] at ha; exact ih a ha.2
  | while_true _ _ _ ih ih' => intro a ha; exact (ih' a ha).trans (ih a ha)
  | while_false _ => intro a ha; rfl
  | read _ => intro a ha; rfl
  | write _ => intro a ha; rfl

theorem bigStep_lengths {c : Com} {σ τ : Env} {t : Nat} (h : BigStep c σ τ t) :
    ∀a,(τ.arrs a).length=(σ.arrs a).length := by
  induction h with
  | skip => intro a; rfl
  | assign _ => intro a; rfl
  | store _ _ _ => intro a; exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => intro a; exact (ih' a).trans (ih a)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => intro a; exact (ih' a).trans (ih a)
  | while_false _ => intro a; rfl
  | read _ => intro a; rfl
  | write _ => intro a; rfl

theorem bigStep_input_frame {c : Com} {σ τ : Env} {t : Nat} (h : BigStep c σ τ t) :
    noRead c → τ.inp=σ.inp := by
  induction h with
  | skip => intro h; rfl
  | assign _ => intro h; rfl
  | store _ _ _ => intro h; rfl
  | seq _ _ ih ih' => intro h; exact (ih' h.2).trans (ih h.1)
  | ite_true _ _ ih => intro h; exact ih h.1
  | ite_false _ _ ih => intro h; exact ih h.2
  | while_true _ _ _ ih ih' => intro h; exact (ih' h).trans (ih h)
  | while_false _ => intro h; rfl
  | read _ => intro h; exact False.elim h
  | write _ => intro h; rfl

theorem run_frame {B cost : Nat} {c : Com} {σ τ : Env} (h : Run B c σ τ cost) :
    (∀x,x ∉ scalarWrites c → τ.vars x=σ.vars x) ∧
    (∀a,a ∉ arrayWrites c → τ.arrs a=σ.arrs a) ∧
    (∀a,(τ.arrs a).length=(σ.arrs a).length) ∧
    (noRead c → τ.inp=σ.inp) ∧ (c.NoWrite → τ.out=σ.out) := by
  obtain ⟨t,ht,hb⟩:=h.bigStep
  exact ⟨bigStep_vars_frame hb,bigStep_arrays_frame hb,bigStep_lengths hb,
    bigStep_input_frame hb,hb.out_eq⟩

/-- An actual bounded loop, specialized to a deterministic family of successive states. -/
theorem countedLoop_run {B n cost : Nat} (idx lim : String) (body : Com) (states : Nat→Env)
    (hidx : ∀i ≤ n,(states i).vars idx=i) (hlim : ∀i ≤ n,(states i).vars lim=n)
    (hn : n<B) (hbody : ∀i<n,Run B body (states i) (states (i+1)) cost) :
    Run B (.while (.lt (.var idx) (.var lim)) body) (states 0) (states n) ((cost+4)*n+4) := by
  let I : Env→Prop:=fun σ=>∃i ≤ n,σ=states i
  let V : Env→Nat:=fun σ=>n-σ.vars idx
  have hdef : ∀σ,I σ → ∃v,(Cond.lt (.var idx) (.var lim)).evalB B σ=some v := by
    rintro σ ⟨i,hi,rfl⟩
    exact evalB_condLt_vars (by rw [hidx i hi]; omega) (by rw [hlim i hi]; exact hn)
  have hs : ∀σ,I σ → (Cond.lt (.var idx) (.var lim)).evalB B σ=some true →
      ∃τ,Run B body σ τ cost ∧ I τ ∧ V τ<V σ := by
    rintro σ ⟨i,hi,rfl⟩ hc
    have htest:=evalB_condLt (evalB_var (by rw [hidx i hi]; omega : (states i).vars idx<B))
      (evalB_var (by rw [hlim i hi]; exact hn : (states i).vars lim<B))
    rw [hidx i hi,hlim i hi,hc] at htest
    have hin:i<n := by simpa using htest.symm
    refine ⟨states (i+1),hbody i hin,⟨i+1,by omega,rfl⟩,?_⟩
    dsimp [V]
    rw [hidx i hi,hidx (i+1) (by omega)]
    omega
  obtain ⟨τ,hr,⟨i,hi,rfl⟩,hf⟩:=Run.while_count I V cost hdef hs ⟨0,by omega,rfl⟩
  have htest:=evalB_condLt (evalB_var (by rw [hidx i hi]; omega : (states i).vars idx<B))
    (evalB_var (by rw [hlim i hi]; exact hn : (states i).vars lim<B))
  rw [hidx i hi,hlim i hi,hf] at htest
  have hin:¬i<n := by simpa using htest.symm
  have hin':i=n:=by omega
  subst i
  apply hr.mono
  simp only [V,hidx 0 (by omega),Nat.sub_zero,Cond.size,Expr.size]
  nlinarith

end Mathproof.Problem18IMPFieldLayout20261001
