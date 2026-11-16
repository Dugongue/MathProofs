import Mathproof.MinimumGenerationRankBerkowitzMoments
import Mathlib.Algebra.BigOperators.Fin

namespace Mathproof.MinimumGeneration.RankBerkowitz.Formula

/-- Arithmetic formulas for characteristic coefficients. Leaves are exact
matrix-entry coordinates. The formula is a correctness specification for
local address navigation. -/
inductive Expr
  | zero
  | one
  | input (row column : Nat)
  | add (left right : Expr)
  | mul (left right : Expr)
  | sub (left right : Expr)

def Expr.eval {R : Type*} [CommRing R] (read : Nat → Nat → R) : Expr → R
  | .zero => 0
  | .one => 1
  | .input i j => read i j
  | .add l r => l.eval read + r.eval read
  | .mul l r => l.eval read * r.eval read
  | .sub l r => l.eval read - r.eval read

def Expr.depth : Expr → Nat
  | .zero | .one | .input _ _ => 0
  | .add l r | .mul l r | .sub l r => max l.depth r.depth + 1

/-- Sum a power-of-two interval, splitting it in half at each level. -/
def intervalSum (term : Nat → Expr) : Nat → Nat → Expr
  | 0, start => term start
  | h+1, start =>
      .add (intervalSum term h start) (intervalSum term h (start + 2^h))

theorem intervalSum_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    (term : Nat → Expr) (h start : Nat) :
    (intervalSum term h start).eval read =
      ∑ i ∈ Finset.range (2^h), (term (start+i)).eval read := by
  induction h generalizing start with
  | zero => simp [intervalSum]
  | succ h ih =>
      simp only [intervalSum, Expr.eval, ih, pow_succ, Nat.mul_two]
      rw [Finset.sum_range_add]
      simp only [Nat.add_left_comm, Nat.add_comm]

theorem intervalSum_depth (term : Nat → Expr) (h start K : Nat)
    (hDepth : ∀ i, (term i).depth ≤ K) : (intervalSum term h start).depth ≤ K+h := by
  induction h generalizing start with
  | zero => simpa [intervalSum] using hDepth start
  | succ h ih =>
    exact Nat.succ_le_succ (max_le (ih start) (ih (start+2^h)))

/-- Use a zero-padded balanced binary sum for the shared dot products. -/
def finiteSum {n : Nat} (term : Fin n → Expr) : Expr :=
  intervalSum (fun i => if hi : i < n then term ⟨i,hi⟩ else .zero) n.size 0

theorem finiteSum_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    {n : Nat} (term : Fin n → Expr) :
    (finiteSum term).eval read = ∑ i, (term i).eval read := by
  unfold finiteSum
  rw [intervalSum_eval]
  simp only [Nat.zero_add]
  let f : Nat → R := fun k => (if hk : k < n then term ⟨k,hk⟩ else .zero).eval read
  change ∑ i ∈ Finset.range (2^n.size), f i = _
  have hs : (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.range (2^n.size), f i) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.lt_size_self n).le)
    intro i _ hi
    have hn : ¬ i < n := by simpa only [Finset.mem_range] using hi
    simp [f, hn, Expr.eval]
  rw [← hs, ← Fin.sum_univ_eq_sum_range f n]
  exact Finset.sum_congr rfl fun i _ => by simp [f,i.isLt]

theorem finiteSum_depth {n K : Nat} (term : Fin n → Expr)
    (hDepth : ∀ i, (term i).depth ≤ K) : (finiteSum term).depth ≤ K+n.size := by
  apply intervalSum_depth
  intro i
  by_cases hi : i < n
  · simpa only [dif_pos hi] using hDepth ⟨i,hi⟩
  · simp [hi, Expr.depth]

def delta {n : Nat} (i j : Fin n) : Expr :=
  if i = j then .one else .zero

/-- Balanced expression for an entry of an ordered product. Factor entries
are supplied by their stage and two matrix coordinates. -/
def productEntry {n : Nat} (factor : Nat → Fin n → Fin n → Expr) :
    Nat → Nat → Nat → Fin n → Fin n → Expr
  | 0, s, e, i, j => if e = 0 then delta i j else if e = 1 then factor s i j else .zero
  | h+1, s, e, i, j =>
    if e = 0 then delta i j else if e = 1 then factor s i j
    else finiteSum fun k =>
      .mul (productEntry factor h s (e/2) i k)
        (productEntry factor h (s+e/2) (e-e/2) k j)

theorem productEntry_eval {R : Type*} [CommRing R] (read : Nat → Nat → R)
    {n : Nat} (factor : Nat → Fin n → Fin n → Expr) (h s e : Nat) (i j : Fin n) :
    (productEntry factor h s e i j).eval read =
      MatrixProduct.entry (fun t r c => (factor t r c).eval read) h s e i j := by
  induction h generalizing s e i j with
  | zero =>
      by_cases hz : e = 0
      · by_cases he : i = j <;> simp [productEntry, MatrixProduct.entry, delta, hz,he,Expr.eval]
      · by_cases ho : e = 1 <;> simp [productEntry, MatrixProduct.entry, hz,ho,Expr.eval]
  | succ h ih =>
      by_cases hz : e = 0
      · by_cases he : i = j <;> simp [productEntry, MatrixProduct.entry, delta, hz,he,Expr.eval]
      by_cases ho : e = 1
      · simp [productEntry, MatrixProduct.entry, hz,ho]
      simp only [productEntry, MatrixProduct.entry, hz,ho,if_false,finiteSum_eval,Expr.eval,ih]

theorem productEntry_depth {n K : Nat} (factor : Nat → Fin n → Fin n → Expr)
    (hDepth : ∀ s i j, (factor s i j).depth ≤ K) (h s e : Nat) (i j : Fin n) :
    (productEntry factor h s e i j).depth ≤ K+h*(n.size+1) := by
  induction h generalizing s e i j with
  | zero =>
      simp only [productEntry, Nat.zero_mul, Nat.add_zero]
      split_ifs with he₀ he₁
      · by_cases he : i = j <;> simp [delta,he,Expr.depth]
      · exact hDepth s i j
      · simp [Expr.depth]
  | succ h ih =>
      simp only [productEntry]
      split_ifs with he₀ he₁
      · by_cases he : i = j <;> simp [delta,he,Expr.depth]
      · exact (hDepth s i j).trans (Nat.le_add_right _ _)
      · have hs := finiteSum_depth (K := K+h*(n.size+1)+1)
          (fun k => .mul (productEntry factor h s (e/2) i k)
              (productEntry factor h (s+e/2) (e-e/2) k j))
          (by exact fun k => Nat.succ_le_succ (max_le (ih _ _ _ _) (ih _ _ _ _)))
        rw [Nat.succ_mul]
        omega

end Mathproof.MinimumGeneration.RankBerkowitz.Formula
