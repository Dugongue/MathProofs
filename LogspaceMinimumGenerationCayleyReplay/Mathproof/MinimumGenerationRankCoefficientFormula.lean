import Mathproof.MinimumGenerationRankFormula

namespace Mathproof.MinimumGeneration.RankBerkowitz.Formula

open Berkowitz

def powerTerm {n : Nat} (offset e : Nat) (i j : Fin n) : Expr :=
  productEntry (fun _ a b => .input (a.val+offset) (b.val+offset)) e.size 0 e i j

private theorem product_const {R : Type*} [CommRing R] {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) (s e : Nat) :
    MatrixProduct.product (fun _ => A) s e = A ^ e := by
  induction e generalizing s with
  | zero => simp [MatrixProduct.product]
  | succ e ih => simp [MatrixProduct.product, ih, pow_succ']

theorem powerTerm_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    {n : Nat} (offset e : Nat) (i j : Fin n) :
    (powerTerm offset e i j).eval read = (sourceWindow read n offset ^ e) i j := by
  unfold powerTerm
  rw [productEntry_eval]
  change MatrixProduct.entry (fun _ => sourceWindow read n offset) e.size 0 e i j = _
  rw [MatrixProduct.entry_size_eq_product]
  exact congrFun (congrFun (product_const (sourceWindow read n offset) 0 e) i) j

theorem powerTerm_depth {n : Nat} (offset e : Nat) (i j : Fin n) :
    (powerTerm offset e i j).depth ≤ e.size*(n.size+1) := by
  simpa only [powerTerm, Nat.zero_add] using
    productEntry_depth (K := 0) (fun _ a b => .input (a.val+offset) (b.val+offset))
      (fun _ _ _ => Nat.le_refl 0) e.size 0 e i j

def momentTerm (offset n e : Nat) : Expr :=
  finiteSum fun i : Fin n =>
    finiteSum fun j : Fin n =>
      .mul (.input offset (i.val+offset+1))
        (.mul (powerTerm (offset+1) e i j) (.input (j.val+offset+1) offset))

theorem momentTerm_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    (offset n e : Nat) :
    (momentTerm offset n e).eval read =
      borderMoment (fun i : Fin n => read offset (i.val+offset+1))
        (fun j : Fin n => read (j.val+offset+1) offset) (sourceWindow read n (offset+1)) e := by
  rw [← momentEntry_eq]
  simp only [momentTerm, momentEntry, finiteSum_eval,Expr.eval,powerTerm_eval,
    MatrixPower.entry_size_eq_pow]

theorem momentTerm_depth (offset n e : Nat) :
    (momentTerm offset n e).depth ≤ e.size*(n.size+1)+2+n.size+n.size := by
  apply finiteSum_depth
  intro i
  apply finiteSum_depth
  intro j
  simp only [Expr.depth, Nat.zero_max, Nat.max_zero]
  exact Nat.succ_le_succ (Nat.succ_le_succ (powerTerm_depth _ _ _ _))

/-- A factor entry uses only arithmetic operations and explicit coordinates
of a trailing principal window. -/
def factorTerm {w : Nat} (length offset stage : Nat) (d k : Fin w) : Expr :=
  if stage < length then
    let anchor := offset+stage
    let tail := length-stage-1
    .sub (.sub (if k.val+1=d.val then .one else .zero)
      (if k.val=d.val then .input anchor anchor else .zero))
      (if d.val<k.val ∧ k.val≤tail then momentTerm anchor tail (k.val-(d.val+1)) else .zero)
  else delta d k

private theorem eval_one_or_zero {R : Type*} [CommRing R] (read : Nat → Nat → R)
    (p : Prop) [Decidable p] :
    (if p then Expr.one else .zero).eval read = if p then 1 else 0 := by
  split_ifs <;> rfl

private theorem depth_one_or_zero (p : Prop) [Decidable p] :
    (if p then Expr.one else .zero).depth = 0 := by
  split_ifs <;> rfl

private theorem depth_input_or_zero (p : Prop) [Decidable p] (r c : Nat) :
    (if p then Expr.input r c else .zero).depth = 0 := by
  split_ifs <;> rfl

private theorem tailWindow_eq {R : Type*} [CommRing R] (read : Nat → Nat → R) (n off : Nat) :
    (sourceWindow read (n+1) off).submatrix Fin.succ Fin.succ = sourceWindow read n (off+1) := by
  ext i j
  simp [Matrix.submatrix_apply, sourceWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
theorem factorTerm_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    {w : Nat} (n off stage : Nat) (d k : Fin w) :
    (factorTerm n off stage d k).eval read = offsetFactor read w n off stage d k := by
  by_cases hs : stage < n
  · rw [factorTerm, if_pos hs, offsetFactor, if_pos hs]
    simp only [Expr.eval, eval_one_or_zero, momentFactor, sourceWindow, Fin.val_zero,
      Fin.val_succ, Nat.zero_add]
    split_ifs <;>
      simp [Expr.eval, momentTerm_eval, tailWindow_eq, momentEntry_eq,
        sourceWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp only [factorTerm, offsetFactor, hs, if_false]
    by_cases h : d = k <;> simp [delta,h,Expr.eval,Matrix.one_apply]

def factorDepth (n : Nat) : Nat := n.size*(n.size+1)+2+n.size+n.size+2

theorem factorTerm_depth {w : Nat} (n off stage : Nat) (d k : Fin w) :
    (factorTerm n off stage d k).depth ≤ factorDepth n := by
  by_cases hs : stage < n
  · rw [factorTerm, if_pos hs]
    simp only [Expr.depth]
    rw [depth_one_or_zero, depth_input_or_zero]
    have ht : (n-stage-1).size ≤ n.size := Nat.size_le_size (by omega)
    have hm : k.val - (d.val+1) ≤ n-stage-1 → (momentTerm (off+stage) (n-stage-1) (k.val-(d.val+1))).depth ≤
        n.size*(n.size+1)+2+n.size+n.size := by
      intro he
      have hp := Nat.mul_le_mul ((Nat.size_le_size he).trans ht) (Nat.add_le_add_right ht 1)
      have hb := momentTerm_depth (off+stage) (n-stage-1) (k.val-(d.val+1))
      omega
    split_ifs with h
    · have hb := hm (by omega)
      unfold factorDepth
      omega
    · unfold factorDepth
      simp [Expr.depth]
  · rw [factorTerm, if_neg hs]
    unfold delta
    split_ifs <;> simp [Expr.depth]

/-- The complete balanced coefficient formula, with matrix coordinates at
the leaves and depth logarithmic squared in the matrix dimension. -/
def coefficientTerm (n : Nat) (d : Fin (n+1)) : Expr :=
  productEntry (factorTerm n 0) n.size 0 n d 0

theorem coefficientTerm_eval {R : Type*} [CommRing R] {n : Nat}
    (A : Matrix (Fin n) (Fin n) R) (d : Fin (n+1)) :
    (coefficientTerm n d).eval (matrixSource A) = A.charpoly.coeff d.val := by
  unfold coefficientTerm
  rw [productEntry_eval]
  have h : (fun t r c => (factorTerm n 0 t r c).eval (matrixSource A)) =
      offsetFactor (matrixSource A) (n+1) n 0 := by
    funext t r c
    exact factorTerm_eval _ _ _ _ _ _
  rw [h]
  exact offsetBalancedCoefficient_eq A d

theorem coefficientTerm_depth (n : Nat) (d : Fin (n+1)) :
    (coefficientTerm n d).depth ≤ factorDepth n+n.size*((n+1).size+1) :=
  productEntry_depth _ (factorTerm_depth n 0) _ _ _ _ _

end Mathproof.MinimumGeneration.RankBerkowitz.Formula
