import EvenP5InvAnchor

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P15Execution

open EvenTI.Action EvenTI.Contract
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open scoped BigOperators Matrix

variable {K : Type} [Field K]

private def reciprocalOrient {X : Type} (mirror : Bool) (A : Matrix X X K) : Matrix X X K :=
  if mirror then A.transpose else A

/-- First rectangular panel of the reciprocal contraction. Its rows are the
pair of retained coordinates and its columns are the contracted coordinates. -/
def reciprocalFront {l n : ℕ} (A : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (mode : HigherModes l) : Matrix (Fin n × Fin n) (Coord l n × Coord l n) K :=
  fun u v => reciprocalOrient mode.1 A (retainedMode 0 (u.1,v.1)) (retainedMode mode.2 (u.2,v.2))

/-- Second panel, from the reciprocal in transposed panel order. -/
def reciprocalBack {l n : ℕ} (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (mode : HigherModes l) : Matrix (Coord l n × Coord l n) (Fin n × Fin n) K :=
  fun v u => reciprocalOrient mode.1 N (retainedMode mode.2 (u.2,v.2)) (retainedMode 0 (u.1,v.1))

/-- Exact rectangular-product, square, and diagonal-block sum implementation
of the reference reciprocal anchor. All reshuffles are coordinate permutations. -/
theorem rawReciprocalAnchor_eq_products {l n : ℕ}
    (T : Tensor K ((l+1)+(l+1)) n) (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (mode : HigherModes l) :
    rawReciprocalAnchor T N mode =
      fun i j => ∑ a : Fin n, (((reciprocalFront (flatten T) mode * reciprocalBack N mode : Matrix (Fin n × Fin n) (Fin n × Fin n) K) ^ (2 : ℕ)) : Matrix (Fin n × Fin n) (Fin n × Fin n) K) (a,i) (a,j) := by
  let X : Matrix (Fin n × Fin n) (Fin n × Fin n) K := fun u v =>
    ∑ a : Coord l n, ∑ b : Coord l n,
      reciprocalFront (flatten T) mode u (a,b) * reciprocalBack N mode (a,b) v
  have hX : X = reciprocalFront (flatten T) mode * reciprocalBack N mode := by
    ext u v
    simp [X,Matrix.mul_apply,Fintype.sum_prod_type]
  change (fun i j => ∑ a : Fin n, (X*X) (a,i) (a,j)) = _
  rw [hX,pow_two]

#print axioms rawReciprocalAnchor_eq_products
end EvenTI.P15Execution