import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel

open scoped BigOperators

namespace PairedGroupEpimorphism

/-- The one-parent cancellation in Alpöge–Buckmaster's `signedTreeLowerBound`,
    for exact residuals with values in an additive commutative group. -/
theorem exactTreeTelescoping {Node Leaf A : Type*} [Fintype Node] [Fintype Leaf]
    [AddCommGroup A] [DecidableEq Node] (root : Node) (parent : Node → Option Node)
    (owner : Leaf → Node) (front : Node → A) (load : Leaf → A)
    (rootParent : parent root = none)
    (onlyRoot : ∀ node, parent node = none → node = root)
    (nodeEquation : ∀ node, front node =
      (∑ leaf, if owner leaf = node then load leaf else 0) +
      ∑ child, if parent child = some node then front child else 0) :
    front root = ∑ leaf, load leaf := by
  classical
  have leafSum : (∑ node, ∑ leaf, if owner leaf = node then load leaf else 0) =
      ∑ leaf, load leaf := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun leaf _ => ?_
    simp
  have childSum : (∑ node, ∑ child, if parent child = some node then front child else 0) =
      (∑ node, front node) - front root := by
    rw [Finset.sum_comm]
    have oneParent (child : Node) :
        (∑ node, if parent child = some node then front child else 0) =
          front child - if child = root then front child else 0 := by
      by_cases childRoot : child = root
      · subst child
        simp [rootParent]
      · cases parentEq : parent child with
        | none => exact (childRoot (onlyRoot child parentEq)).elim
        | some node => simp [childRoot, eq_comm]
    rw [Finset.sum_congr rfl (fun child _ => oneParent child), Finset.sum_sub_distrib]
    simp
  have sumEq : (∑ node, front node) = (∑ leaf, load leaf) + ((∑ node, front node) - front root) := by
    calc
      (∑ node, front node) = ∑ node, ((∑ leaf, if owner leaf = node then load leaf else 0) +
          ∑ child, if parent child = some node then front child else 0) :=
        Finset.sum_congr rfl fun node _ => nodeEquation node
      _ = _ := by rw [Finset.sum_add_distrib, leafSum, childSum]
  calc
    front root = (∑ node, front node) - ((∑ node, front node) - front root) := by abel
    _ = (∑ leaf, load leaf) + ((∑ node, front node) - front root) -
        ((∑ node, front node) - front root) := congrArg
          (fun value : A => value - ((∑ node, front node) - front root)) sumEq
    _ = ∑ leaf, load leaf := by abel

end PairedGroupEpimorphism

#print axioms PairedGroupEpimorphism.exactTreeTelescoping
