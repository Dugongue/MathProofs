import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.Nat.Choose.Basic

namespace ClassTwoPowerRecords

private theorem move_past_pow {G : Type*} [Monoid G] (x y c : G)
    (hyx : y * x = x * y * c) (hyc : Commute y c) (n : ℕ) :
    y ^ n * x = x * y ^ n * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcy : c ^ n * y = y * c ^ n := (hyc.pow_right n).eq.symm
      calc
        y ^ (n + 1) * x = y ^ n * (y * x) := by simp [pow_succ, mul_assoc]
        _ = (y ^ n * x) * y * c := by rw [hyx]; simp [mul_assoc]
        _ = (x * y ^ n) * (c ^ n * y) * c := by rw [ih]; simp [mul_assoc]
        _ = x * y ^ (n + 1) * c ^ (n + 1) := by rw [hcy]; simp [pow_succ, mul_assoc]

/-- The central commutation defect accumulates once for each crossed pair. -/
theorem central_commutator_power {G : Type*} [Monoid G] (x y c : G)
    (hyx : y * x = x * y * c) (hxc : Commute x c) (hyc : Commute y c) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * c ^ (n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpower : c ^ (n.choose 2) * (x * y) = (x * y) * c ^ (n.choose 2) :=
        ((hxc.mul_left hyc).pow_right (n.choose 2)).eq.symm
      have hcy : c ^ n * y = y * c ^ n := (hyc.pow_right n).eq.symm
      have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
        rw [show 2 = 1 + 1 by rfl, Nat.choose_succ_succ', Nat.choose_one_right]
      calc
        (x * y) ^ (n + 1) = (x ^ n * y ^ n * c ^ (n.choose 2)) * (x * y) := by
          rw [pow_succ, ih]
        _ = (x ^ n * y ^ n) * (c ^ (n.choose 2) * (x * y)) := mul_assoc _ _ _
        _ = x ^ n * (y ^ n * x) * y * c ^ (n.choose 2) := by
          rw [hpower]; simp [mul_assoc]
        _ = (x ^ n * x * y ^ n) * (c ^ n * y) * c ^ (n.choose 2) := by
          rw [move_past_pow x y c hyx hyc n]; simp [mul_assoc]
        _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by
          rw [hcy, hchoose, pow_add c n (n.choose 2)]; simp [pow_succ, mul_assoc]

/-- Coordinates in the ordered tensor output of the integral quadratic marking map. -/
def markedSquare {ι R : Type*} [LinearOrder ι] [Add R]
    (a d : ι → R) (b : ι → ι → R) (i j : ι) : R :=
  if i < j then b i j else if j < i then b j i else a i + d i + d i

/-- Equality of the two marked outputs forces every coordinate except the diagonal copy,
whose doubled value is fixed. Over characteristic two the off-diagonal terms still survive. -/
theorem marked_square_recovery {ι R : Type*} [LinearOrder ι] [AddLeftCancelSemigroup R]
    (a d d' : ι → R) (b b' : ι → ι → R)
    (h : markedSquare a d b = markedSquare a d' b') :
    (∀ i j, i < j → b i j = b' i j) ∧ (∀ i, d i + d i = d' i + d' i) := by
  constructor
  · intro i j hij
    simpa [markedSquare, hij] using congrFun (congrFun h i) j
  · intro i
    have hdiag : a i + (d i + d i) = a i + (d' i + d' i) := by
      simpa [markedSquare, add_assoc] using congrFun (congrFun h i) i
    exact add_left_cancel hdiag

end ClassTwoPowerRecords
