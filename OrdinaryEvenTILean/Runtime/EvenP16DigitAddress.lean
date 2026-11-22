import EvenP12CompareRetainedLayout
import Mathproof.Meta.P15DecideIMPEGens20261007

set_option autoImplicit false

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15DecideIMPEGens20261007 (ev_bin ev_add ev_mul ev_div hmdg)

def remainderExpr (x y : Expr) : Expr := .sub x (.mul (.div x y) y)

theorem remainderExpr_eval {B x y : ℕ} {s : Env} {a b : Expr}
    (ha : a.evalB B s=some x) (hb : b.evalB B s=some y) (hx : x<B) :
    (remainderExpr a b).evalB B s=some (x%y) :=
  ev_bin ha (ev_mul (ev_div ha hb ((Nat.div_le_self _ _).trans_lt hx)) hb
    ((Nat.div_mul_le_self _ _).trans_lt hx)) (hmdg x y) ((Nat.mod_le _ _).trans_lt hx)

def digitInsertExpr (n b x c : Expr) : Expr :=
  .add (.mul (.add (.mul (.div c b) n) x) b) (remainderExpr c b)

theorem digitInsertExpr_eval {B n b x c : ℕ} {s : Env} {en eb ex ec : Expr}
    (hn : en.evalB B s=some n) (hb : eb.evalB B s=some b) (hx : ex.evalB B s=some x)
    (hc : ec.evalB B s=some c) (_hn0 : 0<n) (hb0 : 0<b) (hcB : c<B)
    (ho : insertWordIndex n b x c < B) :
    (digitInsertExpr en eb ex ec).evalB B s=some (insertWordIndex n b x c) := by
  have h₁ : (c/b)*n ≤ (c/b)*n+x := Nat.le_add_right _ _
  have h₂ : (c/b)*n+x ≤ ((c/b)*n+x)*b := Nat.le_mul_of_pos_right _ hb0
  have h₃ : ((c/b)*n+x)*b < B := by unfold insertWordIndex at ho; omega
  exact ev_add (ev_mul (ev_add (ev_mul
    (ev_div hc hb ((Nat.div_le_self _ _).trans_lt hcB)) hn ((h₁.trans h₂).trans_lt h₃)) hx
    (h₂.trans_lt h₃)) hb h₃) (remainderExpr_eval hc hb hcB) ho

/-- The numeric address sent to the instrumented gather is a valid index
for every choice of retained digit, including either endpoint of the mode range. -/
theorem insertWordIndex_lt (n d : ℕ) (hn : 0 < n) (i : Fin (d+1))
    {x c : ℕ} (hx : x<n) (hc : c<n^d) :
    insertWordIndex n (n^(d-i.val)) x c < n^(d+1) := by
  let a : Coord d n := (inputCoordOrder n d).symm ⟨c,hc⟩
  have h := inputCoord_retained n d hn i ⟨x,hx⟩ a
  simp only [a,Equiv.apply_symm_apply] at h
  rw [←h]
  exact (inputCoordOrder n (d+1) (retainedMode i (⟨x,hx⟩,a))).isLt

def orientedIndex (mirror : Bool) (base width row col : ℕ) : ℕ :=
  if mirror then base+(col*width+row) else base+(row*width+col)

def orientedIndexExpr (mirror : Bool) (base width row col : Expr) : Expr :=
  if mirror then .add base (.add (.mul col width) row) else .add base (.add (.mul row width) col)

theorem orientedIndexExpr_eval {B base width row col : ℕ} {s : Env} {eb ew er ec : Expr}
    (mirror : Bool) (hb : eb.evalB B s=some base) (hw : ew.evalB B s=some width)
    (hr : er.evalB B s=some row) (hc : ec.evalB B s=some col)
    (hW : orientedIndex mirror base width row col < B) :
    (orientedIndexExpr mirror eb ew er ec).evalB B s=some (orientedIndex mirror base width row col) := by
  cases mirror <;> simp only [orientedIndex,orientedIndexExpr,Bool.false_eq_true,if_false,if_true] at hW ⊢
  · exact ev_add hb (ev_add (ev_mul hr hw (by omega)) hc (by omega)) hW
  · exact ev_add hb (ev_add (ev_mul hc hw (by omega)) hr (by omega)) hW

#print axioms digitInsertExpr_eval
#print axioms insertWordIndex_lt
#print axioms orientedIndexExpr_eval
end EvenTI.P16Execution