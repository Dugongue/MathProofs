import Mathlib

open Matrix

namespace OrbitQ

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A matrix supported in one column, with that column equal to v. -/
def column (r : n) (v : n → K) : Matrix n n K :=
  fun i j => if j = r then v i else 0

/-- The simultaneous transporter for the anchored two-matrix tuples, with a
prescribed determinant. Nonzero determinant is equivalent to invertibility. -/
def rel (a : n → K) (r : n) (v : n → K) (z : K) : Prop :=
  ∃ X : Matrix n n K, X.det = z ∧
    X * diagonal a = diagonal a * X ∧
    X * column r (fun _ => 1) = column r (fun i => v i / v r) * X

/-- The whole attainable determinant range is one scalar power family.
This follows by recovering each diagonal entry from the anchored column
equations. Infinite fields and all finite characteristics are admitted. -/
theorem profile (a : n → K) (ha : Function.Injective a) (r : n)
    (v : n → K) (hv : v r ≠ 0) (z : K) :
    rel a r v z ↔ ∃ c : K, c ^ Fintype.card n * (∏ i, v i) = z := by
  constructor
  · rintro ⟨X, hz, hA, hC⟩
    have hoff (i j : n) (hij : i ≠ j) : X i j = 0 := by
      by_contra hne
      have he := congrArg (fun M : Matrix n n K => M i j) hA
      simp only [mul_diagonal, diagonal_mul] at he
      apply hij
      apply ha
      apply mul_left_cancel₀ hne
      exact (he.trans (mul_comm _ _)).symm
    have hdiag : X = diagonal (fun i => X i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [diagonal_apply_ne _ hij, hoff i j hij]
    have hcol (i : n) : X i i = v i / v r * X r r := by
      have he := congrArg (fun M : Matrix n n K => M i r) hC
      rw [hdiag] at he
      simpa [mul_diagonal, diagonal_mul, column] using he
    let c := X r r / v r
    have hs : (fun i => X i i) = fun i => c * v i := by
      funext i
      rw [hcol]
      simp only [c, div_eq_mul_inv]
      ring
    refine ⟨c, ?_⟩
    rw [hdiag, hs, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ] at hz
    exact hz
  · rintro ⟨c, hz⟩
    refine ⟨diagonal (fun i => c * v i), ?_, ?_, ?_⟩
    · simpa only [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ] using hz
    · exact (Matrix.commute_diagonal _ _).eq
    · ext i j
      simp only [diagonal_mul, mul_diagonal]
      by_cases hj : j = r
      · subst j
        simp [column]
        field_simp [hv] <;> ring
      · simp [column, hj]

/-- Concrete anchored tuples use a translated consecutive spectrum and one
coordinate twist. The width is m + 1. -/
def twisted (p m shift : ℕ) (t z : ZMod p) [Fact (Nat.Prime p)] : Prop :=
  rel (fun i : Fin (m + 1) => (i.val : ZMod p) + shift) (0 : Fin (m + 1))
    (fun i => if i = 0 then t else 1) z

private theorem twisted_iff (p m shift : ℕ) (t : ZMod p) {z : ZMod p}
    [Fact (Nat.Prime p)] (hn : m + 1 ≤ p) (ht : t ≠ 0) :
    twisted p m shift t z ↔ ∃ c : ZMod p, c ^ (m + 1) * t = z := by
  unfold twisted
  rw [profile]
  · simp
  · intro i j h
    have he : (i.val : ZMod p) = (j.val : ZMod p) := add_right_cancel h
    apply Fin.ext
    have hi := ZMod.val_natCast_of_lt (i.isLt.trans_le hn)
    have hj := ZMod.val_natCast_of_lt (j.isLt.trans_le hn)
    exact hi.symm.trans ((congrArg ZMod.val he).trans hj)
  · simpa using ht

section Q5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem b040 : twisted 5 1 0 2 2 ∧ ¬ twisted 5 1 0 2 1 := by
  simp only [twisted_iff 5 1 0 2 (by decide) (by decide)]
  decide

theorem b000 : twisted 5 1 1 4 1 := by
  simp only [twisted_iff 5 1 1 4 (by decide) (by decide)]
  decide

theorem b020 : ∀ z : ZMod 5, twisted 5 1 2 4 z ↔ z ∈ ([0, 1, 4] : List (ZMod 5)) := by
  simp only [twisted_iff 5 1 2 4 (by decide) (by decide)]
  decide

theorem b030 : twisted 5 1 3 4 1 := by
  simp only [twisted_iff 5 1 3 4 (by decide) (by decide)]
  decide

theorem b010 : twisted 5 1 4 3 3 ∧ ¬ twisted 5 1 4 3 1 := by
  simp only [twisted_iff 5 1 4 3 (by decide) (by decide)]
  decide

end Q5

section Q7
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem b113 : ∀ z : ZMod 7, twisted 7 1 0 2 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 1 0 2 (by decide) (by decide)]
  decide

theorem b001 : twisted 7 1 1 5 5 ∧ ¬ twisted 7 1 1 5 1 := by
  simp only [twisted_iff 7 1 1 5 (by decide) (by decide)]
  decide

theorem b050 : ∀ z : ZMod 7, twisted 7 1 2 3 z ↔ z ∈ ([0, 3, 5, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 1 2 3 (by decide) (by decide)]
  decide

theorem b131 : ∀ z : ZMod 7, twisted 7 1 3 4 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 1 3 4 (by decide) (by decide)]
  decide

theorem b011 : ∀ z : ZMod 7, twisted 7 1 4 5 z ↔ z ∈ ([0, 3, 5, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 1 4 5 (by decide) (by decide)]
  decide

theorem b149 : ∀ z : ZMod 7, twisted 7 1 5 3 z ↔ z ∈ ([0, 3, 5, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 1 5 3 (by decide) (by decide)]
  decide

theorem b021 : twisted 7 1 6 4 1 := by
  simp only [twisted_iff 7 1 6 4 (by decide) (by decide)]
  decide

theorem b077 : ∀ z : ZMod 7, twisted 7 2 0 5 z ↔ z ∈ ([0, 2, 5] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 0 5 (by decide) (by decide)]
  decide

theorem b104 : ∀ z : ZMod 7, twisted 7 2 1 5 z ↔ z ∈ ([0, 2, 5] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 1 5 (by decide) (by decide)]
  decide

theorem b095 : ∀ z : ZMod 7, twisted 7 2 2 4 z ↔ z ∈ ([0, 3, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 2 4 (by decide) (by decide)]
  decide

theorem b167 : ∀ z : ZMod 7, twisted 7 2 3 6 z ↔ z ∈ ([0, 1, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 3 6 (by decide) (by decide)]
  decide

theorem b185 : ∀ z : ZMod 7, twisted 7 2 4 3 z ↔ z ∈ ([0, 3, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 4 3 (by decide) (by decide)]
  decide

theorem b059 : ∀ z : ZMod 7, twisted 7 2 5 5 z ↔ z ∈ ([0, 2, 5] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 5 5 (by decide) (by decide)]
  decide

theorem b122 : ∀ z : ZMod 7, twisted 7 2 6 6 z ↔ z ∈ ([0, 1, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 2 6 6 (by decide) (by decide)]
  decide

theorem b158 : ∀ z : ZMod 7, twisted 7 3 0 4 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 0 4 (by decide) (by decide)]
  decide

theorem b176 : ∀ z : ZMod 7, twisted 7 3 1 2 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 1 2 (by decide) (by decide)]
  decide

theorem b086 : ∀ z : ZMod 7, twisted 7 3 2 6 z ↔ z ∈ ([0, 3, 5, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 2 6 (by decide) (by decide)]
  decide

theorem b041 : ∀ z : ZMod 7, twisted 7 3 3 3 z ↔ z ∈ ([0, 3, 5, 6] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 3 3 (by decide) (by decide)]
  decide

theorem b068 : ∀ z : ZMod 7, twisted 7 3 4 2 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 4 2 (by decide) (by decide)]
  decide

theorem b031 : twisted 7 3 5 6 6 ∧ ¬ twisted 7 3 5 6 1 := by
  simp only [twisted_iff 7 3 5 6 (by decide) (by decide)]
  decide

theorem b140 : ∀ z : ZMod 7, twisted 7 3 6 1 z ↔ z ∈ ([0, 1, 2, 4] : List (ZMod 7)) := by
  simp only [twisted_iff 7 3 6 1 (by decide) (by decide)]
  decide

end Q7

section Q11
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem b087 : twisted 11 1 3 5 1 := by
  simp only [twisted_iff 11 1 3 5 (by decide) (by decide)]
  decide

theorem b123 : twisted 11 1 6 5 1 := by
  simp only [twisted_iff 11 1 6 5 (by decide) (by decide)]
  decide

theorem b096 : twisted 11 1 8 5 1 := by
  simp only [twisted_iff 11 1 8 5 (by decide) (by decide)]
  decide

theorem b042 : twisted 11 1 10 4 1 := by
  simp only [twisted_iff 11 1 10 4 (by decide) (by decide)]
  decide

theorem b114 : twisted 11 3 0 5 1 := by
  simp only [twisted_iff 11 3 0 5 (by decide) (by decide)]
  decide

theorem b234 : twisted 11 3 1 5 1 := by
  simp only [twisted_iff 11 3 1 5 (by decide) (by decide)]
  decide

theorem b242 : ∀ z : ZMod 11, twisted 11 3 3 10 z ↔ z ∈ ([0, 2, 6, 7, 8, 10] : List (ZMod 11)) := by
  simp only [twisted_iff 11 3 3 10 (by decide) (by decide)]
  decide

theorem b210 : twisted 11 3 4 3 1 := by
  simp only [twisted_iff 11 3 4 3 (by decide) (by decide)]
  decide

theorem b078 : twisted 11 3 6 4 1 := by
  simp only [twisted_iff 11 3 6 4 (by decide) (by decide)]
  decide

theorem b168 : twisted 11 3 8 5 1 := by
  simp only [twisted_iff 11 3 8 5 (by decide) (by decide)]
  decide

theorem b141 : twisted 11 3 9 3 1 := by
  simp only [twisted_iff 11 3 9 3 (by decide) (by decide)]
  decide

theorem b194 : ∀ z : ZMod 11, twisted 11 3 10 1 z ↔ z ∈ ([0, 1, 3, 4, 5, 9] : List (ZMod 11)) := by
  simp only [twisted_iff 11 3 10 1 (by decide) (by decide)]
  decide

theorem b060 : twisted 11 4 0 10 1 := by
  simp only [twisted_iff 11 4 0 10 (by decide) (by decide)]
  decide

theorem b002 : ∀ z : ZMod 11, twisted 11 4 5 7 z ↔ z ∈ ([0, 4, 7] : List (ZMod 11)) := by
  simp only [twisted_iff 11 4 5 7 (by decide) (by decide)]
  decide

theorem b202 : twisted 11 4 6 5 5 ∧ ¬ twisted 11 4 6 5 1 := by
  simp only [twisted_iff 11 4 6 5 (by decide) (by decide)]
  decide

theorem b012 : twisted 11 4 8 10 1 := by
  simp only [twisted_iff 11 4 8 10 (by decide) (by decide)]
  decide

theorem b132 : twisted 11 4 9 10 1 := by
  simp only [twisted_iff 11 4 9 10 (by decide) (by decide)]
  decide

theorem b069 : twisted 11 5 1 3 1 := by
  simp only [twisted_iff 11 5 1 3 (by decide) (by decide)]
  decide

theorem b022 : twisted 11 5 2 6 6 ∧ ¬ twisted 11 5 2 6 1 := by
  simp only [twisted_iff 11 5 2 6 (by decide) (by decide)]
  decide

theorem b159 : twisted 11 5 4 9 1 := by
  simp only [twisted_iff 11 5 4 9 (by decide) (by decide)]
  decide

theorem b226 : twisted 11 5 5 10 10 ∧ ¬ twisted 11 5 5 10 1 := by
  simp only [twisted_iff 11 5 5 10 (by decide) (by decide)]
  decide

theorem b218 : ∀ z : ZMod 11, twisted 11 5 6 8 z ↔ z ∈ ([0, 2, 6, 7, 8, 10] : List (ZMod 11)) := by
  simp only [twisted_iff 11 5 6 8 (by decide) (by decide)]
  decide

theorem b150 : twisted 11 7 0 3 1 := by
  simp only [twisted_iff 11 7 0 3 (by decide) (by decide)]
  decide

theorem b177 : twisted 11 7 1 4 1 := by
  simp only [twisted_iff 11 7 1 4 (by decide) (by decide)]
  decide

theorem b105 : twisted 11 7 2 5 1 := by
  simp only [twisted_iff 11 7 2 5 (by decide) (by decide)]
  decide

theorem b032 : ∀ z : ZMod 11, twisted 11 7 3 9 z ↔ z ∈ ([0, 1, 3, 4, 5, 9] : List (ZMod 11)) := by
  simp only [twisted_iff 11 7 3 9 (by decide) (by decide)]
  decide

theorem b051 : twisted 11 7 4 4 1 := by
  simp only [twisted_iff 11 7 4 4 (by decide) (by decide)]
  decide

theorem b186 : twisted 11 7 10 4 1 := by
  simp only [twisted_iff 11 7 10 4 (by decide) (by decide)]
  decide

end Q11

section Q13
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem b235 : twisted 13 1 1 6 6 ∧ ¬ twisted 13 1 1 6 1 := by
  simp only [twisted_iff 13 1 1 6 (by decide) (by decide)]
  decide

theorem b052 : twisted 13 1 2 5 5 ∧ ¬ twisted 13 1 2 5 1 := by
  simp only [twisted_iff 13 1 2 5 (by decide) (by decide)]
  decide

theorem b160 : twisted 13 1 4 11 11 ∧ ¬ twisted 13 1 4 11 1 := by
  simp only [twisted_iff 13 1 4 11 (by decide) (by decide)]
  decide

theorem b195 : twisted 13 1 5 9 1 := by
  simp only [twisted_iff 13 1 5 9 (by decide) (by decide)]
  decide

theorem b243 : twisted 13 1 6 4 1 := by
  simp only [twisted_iff 13 1 6 4 (by decide) (by decide)]
  decide

theorem b124 : twisted 13 1 7 7 7 ∧ ¬ twisted 13 1 7 7 1 := by
  simp only [twisted_iff 13 1 7 7 (by decide) (by decide)]
  decide

theorem b003 : twisted 13 1 8 9 1 := by
  simp only [twisted_iff 13 1 8 9 (by decide) (by decide)]
  decide

theorem b115 : twisted 13 1 9 8 8 ∧ ¬ twisted 13 1 9 8 1 := by
  simp only [twisted_iff 13 1 9 8 (by decide) (by decide)]
  decide

theorem b219 : twisted 13 1 10 10 1 := by
  simp only [twisted_iff 13 1 10 10 (by decide) (by decide)]
  decide

theorem b211 : twisted 13 1 11 5 5 ∧ ¬ twisted 13 1 11 5 1 := by
  simp only [twisted_iff 13 1 11 5 (by decide) (by decide)]
  decide

theorem b142 : twisted 13 2 4 6 6 ∧ ¬ twisted 13 2 4 6 1 := by
  simp only [twisted_iff 13 2 4 6 (by decide) (by decide)]
  decide

theorem b023 : ∀ z : ZMod 13, twisted 13 2 5 4 z ↔ z ∈ ([0, 4, 6, 7, 9] : List (ZMod 13)) := by
  simp only [twisted_iff 13 2 5 4 (by decide) (by decide)]
  decide

theorem b169 : twisted 13 2 6 7 7 ∧ ¬ twisted 13 2 6 7 1 := by
  simp only [twisted_iff 13 2 6 7 (by decide) (by decide)]
  decide

theorem b106 : twisted 13 2 9 9 9 ∧ ¬ twisted 13 2 9 9 1 := by
  simp only [twisted_iff 13 2 9 9 (by decide) (by decide)]
  decide

theorem b178 : twisted 13 3 3 10 10 ∧ ¬ twisted 13 3 3 10 1 := by
  simp only [twisted_iff 13 3 3 10 (by decide) (by decide)]
  decide

theorem b061 : twisted 13 3 5 7 7 ∧ ¬ twisted 13 3 5 7 1 := by
  simp only [twisted_iff 13 3 5 7 (by decide) (by decide)]
  decide

theorem b088 : twisted 13 3 8 6 6 ∧ ¬ twisted 13 3 8 6 1 := by
  simp only [twisted_iff 13 3 8 6 (by decide) (by decide)]
  decide

theorem b043 : twisted 13 3 9 4 4 ∧ ¬ twisted 13 3 9 4 1 := by
  simp only [twisted_iff 13 3 9 4 (by decide) (by decide)]
  decide

theorem b013 : twisted 13 3 11 5 5 ∧ ¬ twisted 13 3 11 5 1 := by
  simp only [twisted_iff 13 3 11 5 (by decide) (by decide)]
  decide

theorem b187 : twisted 13 5 0 5 5 ∧ ¬ twisted 13 5 0 5 1 := by
  simp only [twisted_iff 13 5 0 5 (by decide) (by decide)]
  decide

theorem b151 : twisted 13 5 1 4 4 ∧ ¬ twisted 13 5 1 4 1 := by
  simp only [twisted_iff 13 5 1 4 (by decide) (by decide)]
  decide

theorem b033 : twisted 13 5 2 12 1 := by
  simp only [twisted_iff 13 5 2 12 (by decide) (by decide)]
  decide

theorem b070 : twisted 13 5 5 3 3 ∧ ¬ twisted 13 5 5 3 1 := by
  simp only [twisted_iff 13 5 5 3 (by decide) (by decide)]
  decide

theorem b097 : twisted 13 5 6 10 10 ∧ ¬ twisted 13 5 6 10 1 := by
  simp only [twisted_iff 13 5 6 10 (by decide) (by decide)]
  decide

theorem b227 : ∀ z : ZMod 13, twisted 13 5 9 6 z ↔ z ∈ ([0, 6, 7] : List (ZMod 13)) := by
  simp only [twisted_iff 13 5 9 6 (by decide) (by decide)]
  decide

theorem b203 : ∀ z : ZMod 13, twisted 13 7 2 10 z ↔ z ∈ ([0, 4, 10, 12] : List (ZMod 13)) := by
  simp only [twisted_iff 13 7 2 10 (by decide) (by decide)]
  decide

theorem b079 : twisted 13 7 6 8 8 ∧ ¬ twisted 13 7 6 8 1 := by
  simp only [twisted_iff 13 7 6 8 (by decide) (by decide)]
  decide

theorem b133 : twisted 13 7 8 10 10 ∧ ¬ twisted 13 7 8 10 1 := by
  simp only [twisted_iff 13 7 8 10 (by decide) (by decide)]
  decide

end Q13

section Q17
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem b228 : twisted 17 1 1 9 1 := by
  simp only [twisted_iff 17 1 1 9 (by decide) (by decide)]
  decide

theorem b044 : ∀ z : ZMod 17, twisted 17 1 11 11 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 1 11 11 (by decide) (by decide)]
  decide

theorem b143 : ∀ z : ZMod 17, twisted 17 1 12 16 z ↔ z ∈ ([0, 1, 2, 4, 8, 9, 13, 15, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 1 12 16 (by decide) (by decide)]
  decide

theorem b053 : ∀ z : ZMod 17, twisted 17 1 14 7 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 1 14 7 (by decide) (by decide)]
  decide

theorem b098 : ∀ z : ZMod 17, twisted 17 3 2 12 z ↔ z ∈ ([0, 3, 5, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 3 2 12 (by decide) (by decide)]
  decide

theorem b244 : twisted 17 3 4 9 9 ∧ ¬ twisted 17 3 4 9 1 := by
  simp only [twisted_iff 17 3 4 9 (by decide) (by decide)]
  decide

theorem b161 : ∀ z : ZMod 17, twisted 17 3 5 3 z ↔ z ∈ ([0, 3, 5, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 3 5 3 (by decide) (by decide)]
  decide

theorem b204 : twisted 17 3 8 4 1 := by
  simp only [twisted_iff 17 3 8 4 (by decide) (by decide)]
  decide

theorem b080 : ∀ z : ZMod 17, twisted 17 3 9 5 z ↔ z ∈ ([0, 3, 5, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 3 9 5 (by decide) (by decide)]
  decide

theorem b220 : twisted 17 3 12 9 9 ∧ ¬ twisted 17 3 12 9 1 := by
  simp only [twisted_iff 17 3 12 9 (by decide) (by decide)]
  decide

theorem b071 : ∀ z : ZMod 17, twisted 17 3 13 13 z ↔ z ∈ ([0, 1, 4, 13, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 3 13 13 (by decide) (by decide)]
  decide

theorem b196 : twisted 17 3 16 8 8 ∧ ¬ twisted 17 3 16 8 1 := by
  simp only [twisted_iff 17 3 16 8 (by decide) (by decide)]
  decide

theorem b212 : ∀ z : ZMod 17, twisted 17 5 1 10 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 1 10 (by decide) (by decide)]
  decide

theorem b125 : ∀ z : ZMod 17, twisted 17 5 2 15 z ↔ z ∈ ([0, 1, 2, 4, 8, 9, 13, 15, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 2 15 (by decide) (by decide)]
  decide

theorem b034 : twisted 17 5 3 14 14 ∧ ¬ twisted 17 5 3 14 1 := by
  simp only [twisted_iff 17 5 3 14 (by decide) (by decide)]
  decide

theorem b134 : ∀ z : ZMod 17, twisted 17 5 4 8 z ↔ z ∈ ([0, 1, 2, 4, 8, 9, 13, 15, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 4 8 (by decide) (by decide)]
  decide

theorem b236 : ∀ z : ZMod 17, twisted 17 5 7 3 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 7 3 (by decide) (by decide)]
  decide

theorem b014 : ∀ z : ZMod 17, twisted 17 5 9 11 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 9 11 (by decide) (by decide)]
  decide

theorem b188 : ∀ z : ZMod 17, twisted 17 5 11 11 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 11 11 (by decide) (by decide)]
  decide

theorem b107 : ∀ z : ZMod 17, twisted 17 5 12 11 z ↔ z ∈ ([0, 3, 5, 6, 7, 10, 11, 12, 14] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 12 11 (by decide) (by decide)]
  decide

theorem b089 : ∀ z : ZMod 17, twisted 17 5 15 15 z ↔ z ∈ ([0, 1, 2, 4, 8, 9, 13, 15, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 5 15 15 (by decide) (by decide)]
  decide

theorem b024 : twisted 17 5 16 4 1 := by
  simp only [twisted_iff 17 5 16 4 (by decide) (by decide)]
  decide

theorem b179 : ∀ z : ZMod 17, twisted 17 7 2 6 z ↔ z ∈ ([0, 6, 11] : List (ZMod 17)) := by
  simp only [twisted_iff 17 7 2 6 (by decide) (by decide)]
  decide

theorem b004 : twisted 17 7 3 4 4 ∧ ¬ twisted 17 7 3 4 1 := by
  simp only [twisted_iff 17 7 3 4 (by decide) (by decide)]
  decide

theorem b116 : ∀ z : ZMod 17, twisted 17 7 9 13 z ↔ z ∈ ([0, 4, 13] : List (ZMod 17)) := by
  simp only [twisted_iff 17 7 9 13 (by decide) (by decide)]
  decide

theorem b170 : ∀ z : ZMod 17, twisted 17 7 10 7 z ↔ z ∈ ([0, 7, 10] : List (ZMod 17)) := by
  simp only [twisted_iff 17 7 10 7 (by decide) (by decide)]
  decide

theorem b062 : ∀ z : ZMod 17, twisted 17 7 13 1 z ↔ z ∈ ([0, 1, 16] : List (ZMod 17)) := by
  simp only [twisted_iff 17 7 13 1 (by decide) (by decide)]
  decide

theorem b152 : ∀ z : ZMod 17, twisted 17 7 15 6 z ↔ z ∈ ([0, 6, 11] : List (ZMod 17)) := by
  simp only [twisted_iff 17 7 15 6 (by decide) (by decide)]
  decide

end Q17

section Q19
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

theorem b090 : twisted 19 1 0 16 1 := by
  simp only [twisted_iff 19 1 0 16 (by decide) (by decide)]
  decide

theorem b189 : twisted 19 1 4 17 1 := by
  simp only [twisted_iff 19 1 4 17 (by decide) (by decide)]
  decide

theorem b205 : twisted 19 1 8 13 13 ∧ ¬ twisted 19 1 8 13 1 := by
  simp only [twisted_iff 19 1 8 13 (by decide) (by decide)]
  decide

theorem b063 : twisted 19 1 9 17 1 := by
  simp only [twisted_iff 19 1 9 17 (by decide) (by decide)]
  decide

theorem b197 : ∀ z : ZMod 19, twisted 19 1 11 11 z ↔ z ∈ ([0, 1, 4, 5, 6, 7, 9, 11, 16, 17] : List (ZMod 19)) := by
  simp only [twisted_iff 19 1 11 11 (by decide) (by decide)]
  decide

theorem b162 : twisted 19 1 12 9 1 := by
  simp only [twisted_iff 19 1 12 9 (by decide) (by decide)]
  decide

theorem b099 : twisted 19 1 13 11 1 := by
  simp only [twisted_iff 19 1 13 11 (by decide) (by decide)]
  decide

theorem b045 : twisted 19 1 15 16 1 := by
  simp only [twisted_iff 19 1 15 16 (by decide) (by decide)]
  decide

theorem b005 : ∀ z : ZMod 19, twisted 19 2 0 18 z ↔ z ∈ ([0, 1, 7, 8, 11, 12, 18] : List (ZMod 19)) := by
  simp only [twisted_iff 19 2 0 18 (by decide) (by decide)]
  decide

theorem b245 : ∀ z : ZMod 19, twisted 19 2 5 10 z ↔ z ∈ ([0, 4, 6, 9, 10, 13, 15] : List (ZMod 19)) := by
  simp only [twisted_iff 19 2 5 10 (by decide) (by decide)]
  decide

theorem b054 : twisted 19 2 7 7 1 := by
  simp only [twisted_iff 19 2 7 7 (by decide) (by decide)]
  decide

theorem b229 : twisted 19 2 11 3 3 ∧ ¬ twisted 19 2 11 3 1 := by
  simp only [twisted_iff 19 2 11 3 (by decide) (by decide)]
  decide

theorem b144 : twisted 19 2 14 11 1 := by
  simp only [twisted_iff 19 2 14 11 (by decide) (by decide)]
  decide

theorem b072 : twisted 19 3 1 4 1 := by
  simp only [twisted_iff 19 3 1 4 (by decide) (by decide)]
  decide

theorem b213 : twisted 19 3 3 16 1 := by
  simp only [twisted_iff 19 3 3 16 (by decide) (by decide)]
  decide

theorem b035 : ∀ z : ZMod 19, twisted 19 3 17 9 z ↔ z ∈ ([0, 1, 4, 5, 6, 7, 9, 11, 16, 17] : List (ZMod 19)) := by
  simp only [twisted_iff 19 3 17 9 (by decide) (by decide)]
  decide

theorem b135 : twisted 19 5 4 11 1 := by
  simp only [twisted_iff 19 5 4 11 (by decide) (by decide)]
  decide

theorem b180 : twisted 19 5 8 7 1 := by
  simp only [twisted_iff 19 5 8 7 (by decide) (by decide)]
  decide

theorem b237 : twisted 19 5 9 7 1 := by
  simp only [twisted_iff 19 5 9 7 (by decide) (by decide)]
  decide

theorem b153 : twisted 19 5 10 7 1 := by
  simp only [twisted_iff 19 5 10 7 (by decide) (by decide)]
  decide

theorem b126 : twisted 19 5 16 7 1 := by
  simp only [twisted_iff 19 5 16 7 (by decide) (by decide)]
  decide

theorem b081 : twisted 19 5 17 7 1 := by
  simp only [twisted_iff 19 5 17 7 (by decide) (by decide)]
  decide

theorem b015 : twisted 19 5 18 7 1 := by
  simp only [twisted_iff 19 5 18 7 (by decide) (by decide)]
  decide

theorem b025 : twisted 19 7 1 14 14 ∧ ¬ twisted 19 7 1 14 1 := by
  simp only [twisted_iff 19 7 1 14 (by decide) (by decide)]
  decide

theorem b108 : twisted 19 7 7 16 1 := by
  simp only [twisted_iff 19 7 7 16 (by decide) (by decide)]
  decide

theorem b221 : ∀ z : ZMod 19, twisted 19 7 9 14 z ↔ z ∈ ([0, 2, 3, 8, 10, 12, 13, 14, 15, 18] : List (ZMod 19)) := by
  simp only [twisted_iff 19 7 9 14 (by decide) (by decide)]
  decide

theorem b171 : twisted 19 7 11 17 1 := by
  simp only [twisted_iff 19 7 11 17 (by decide) (by decide)]
  decide

theorem b117 : twisted 19 7 15 11 1 := by
  simp only [twisted_iff 19 7 15 11 (by decide) (by decide)]
  decide

end Q19

section Q23
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem b136 : twisted 23 1 2 10 10 ∧ ¬ twisted 23 1 2 10 1 := by
  simp only [twisted_iff 23 1 2 10 (by decide) (by decide)]
  decide

theorem b016 : twisted 23 1 3 14 14 ∧ ¬ twisted 23 1 3 14 1 := by
  simp only [twisted_iff 23 1 3 14 (by decide) (by decide)]
  decide

theorem b118 : twisted 23 1 5 21 21 ∧ ¬ twisted 23 1 5 21 1 := by
  simp only [twisted_iff 23 1 5 21 (by decide) (by decide)]
  decide

theorem b230 : ∀ z : ZMod 23, twisted 23 1 10 11 z ↔ z ∈ ([0, 5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22] : List (ZMod 23)) := by
  simp only [twisted_iff 23 1 10 11 (by decide) (by decide)]
  decide

theorem b091 : twisted 23 1 15 20 20 ∧ ¬ twisted 23 1 15 20 1 := by
  simp only [twisted_iff 23 1 15 20 (by decide) (by decide)]
  decide

theorem b154 : twisted 23 1 16 17 17 ∧ ¬ twisted 23 1 16 17 1 := by
  simp only [twisted_iff 23 1 16 17 (by decide) (by decide)]
  decide

theorem b073 : twisted 23 1 18 14 14 ∧ ¬ twisted 23 1 18 14 1 := by
  simp only [twisted_iff 23 1 18 14 (by decide) (by decide)]
  decide

theorem b036 : twisted 23 1 19 12 1 := by
  simp only [twisted_iff 23 1 19 12 (by decide) (by decide)]
  decide

theorem b222 : twisted 23 1 22 13 1 := by
  simp only [twisted_iff 23 1 22 13 (by decide) (by decide)]
  decide

theorem b145 : twisted 23 3 0 17 17 ∧ ¬ twisted 23 3 0 17 1 := by
  simp only [twisted_iff 23 3 0 17 (by decide) (by decide)]
  decide

theorem b214 : twisted 23 3 1 20 20 ∧ ¬ twisted 23 3 1 20 1 := by
  simp only [twisted_iff 23 3 1 20 (by decide) (by decide)]
  decide

theorem b109 : twisted 23 3 2 10 10 ∧ ¬ twisted 23 3 2 10 1 := by
  simp only [twisted_iff 23 3 2 10 (by decide) (by decide)]
  decide

theorem b206 : ∀ z : ZMod 23, twisted 23 3 7 22 z ↔ z ∈ ([0, 5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22] : List (ZMod 23)) := by
  simp only [twisted_iff 23 3 7 22 (by decide) (by decide)]
  decide

theorem b064 : twisted 23 3 8 14 14 ∧ ¬ twisted 23 3 8 14 1 := by
  simp only [twisted_iff 23 3 8 14 (by decide) (by decide)]
  decide

theorem b100 : twisted 23 3 10 14 14 ∧ ¬ twisted 23 3 10 14 1 := by
  simp only [twisted_iff 23 3 10 14 (by decide) (by decide)]
  decide

theorem b082 : twisted 23 3 13 19 19 ∧ ¬ twisted 23 3 13 19 1 := by
  simp only [twisted_iff 23 3 13 19 (by decide) (by decide)]
  decide

theorem b026 : ∀ z : ZMod 23, twisted 23 3 16 9 z ↔ z ∈ ([0, 1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18] : List (ZMod 23)) := by
  simp only [twisted_iff 23 3 16 9 (by decide) (by decide)]
  decide

theorem b006 : twisted 23 3 17 2 1 := by
  simp only [twisted_iff 23 3 17 2 (by decide) (by decide)]
  decide

theorem b190 : twisted 23 3 22 22 22 ∧ ¬ twisted 23 3 22 22 1 := by
  simp only [twisted_iff 23 3 22 22 (by decide) (by decide)]
  decide

theorem b246 : twisted 23 5 5 8 1 := by
  simp only [twisted_iff 23 5 5 8 (by decide) (by decide)]
  decide

theorem b198 : twisted 23 5 12 12 1 := by
  simp only [twisted_iff 23 5 12 12 (by decide) (by decide)]
  decide

theorem b055 : twisted 23 7 0 14 14 ∧ ¬ twisted 23 7 0 14 1 := by
  simp only [twisted_iff 23 7 0 14 (by decide) (by decide)]
  decide

theorem b163 : twisted 23 7 4 5 5 ∧ ¬ twisted 23 7 4 5 1 := by
  simp only [twisted_iff 23 7 4 5 (by decide) (by decide)]
  decide

theorem b181 : twisted 23 7 5 22 22 ∧ ¬ twisted 23 7 5 22 1 := by
  simp only [twisted_iff 23 7 5 22 (by decide) (by decide)]
  decide

theorem b238 : twisted 23 7 8 7 7 ∧ ¬ twisted 23 7 8 7 1 := by
  simp only [twisted_iff 23 7 8 7 (by decide) (by decide)]
  decide

theorem b172 : twisted 23 7 14 21 21 ∧ ¬ twisted 23 7 14 21 1 := by
  simp only [twisted_iff 23 7 14 21 (by decide) (by decide)]
  decide

theorem b046 : twisted 23 7 17 7 7 ∧ ¬ twisted 23 7 17 7 1 := by
  simp only [twisted_iff 23 7 17 7 (by decide) (by decide)]
  decide

theorem b127 : twisted 23 7 19 14 14 ∧ ¬ twisted 23 7 19 14 1 := by
  simp only [twisted_iff 23 7 19 14 (by decide) (by decide)]
  decide

end Q23

section Q29
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

theorem b047 : ∀ z : ZMod 29, twisted 29 1 6 12 z ↔ z ∈ ([0, 2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 1 6 12 (by decide) (by decide)]
  decide

theorem b037 : twisted 29 1 17 21 21 ∧ ¬ twisted 29 1 17 21 1 := by
  simp only [twisted_iff 29 1 17 21 (by decide) (by decide)]
  decide

theorem b247 : twisted 29 1 19 19 19 ∧ ¬ twisted 29 1 19 19 1 := by
  simp only [twisted_iff 29 1 19 19 (by decide) (by decide)]
  decide

theorem b223 : twisted 29 1 28 27 27 ∧ ¬ twisted 29 1 28 27 1 := by
  simp only [twisted_iff 29 1 28 27 (by decide) (by decide)]
  decide

theorem b056 : ∀ z : ZMod 29, twisted 29 3 3 14 z ↔ z ∈ ([0, 2, 3, 11, 14, 17, 19, 21] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 3 14 (by decide) (by decide)]
  decide

theorem b155 : ∀ z : ZMod 29, twisted 29 3 6 8 z ↔ z ∈ ([0, 8, 10, 12, 15, 18, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 6 8 (by decide) (by decide)]
  decide

theorem b173 : ∀ z : ZMod 29, twisted 29 3 20 15 z ↔ z ∈ ([0, 8, 10, 12, 15, 18, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 20 15 (by decide) (by decide)]
  decide

theorem b017 : ∀ z : ZMod 29, twisted 29 3 21 1 z ↔ z ∈ ([0, 1, 7, 16, 20, 23, 24, 25] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 21 1 (by decide) (by decide)]
  decide

theorem b146 : ∀ z : ZMod 29, twisted 29 3 24 6 z ↔ z ∈ ([0, 4, 5, 6, 9, 13, 22, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 24 6 (by decide) (by decide)]
  decide

theorem b137 : ∀ z : ZMod 29, twisted 29 3 27 16 z ↔ z ∈ ([0, 1, 7, 16, 20, 23, 24, 25] : List (ZMod 29)) := by
  simp only [twisted_iff 29 3 27 16 (by decide) (by decide)]
  decide

theorem b182 : ∀ z : ZMod 29, twisted 29 5 2 1 z ↔ z ∈ ([0, 1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 5 2 1 (by decide) (by decide)]
  decide

theorem b110 : ∀ z : ZMod 29, twisted 29 5 3 9 z ↔ z ∈ ([0, 1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 5 3 9 (by decide) (by decide)]
  decide

theorem b027 : twisted 29 5 6 9 1 := by
  simp only [twisted_iff 29 5 6 9 (by decide) (by decide)]
  decide

theorem b207 : twisted 29 5 10 4 1 := by
  simp only [twisted_iff 29 5 10 4 (by decide) (by decide)]
  decide

theorem b007 : twisted 29 5 12 26 26 ∧ ¬ twisted 29 5 12 26 1 := by
  simp only [twisted_iff 29 5 12 26 (by decide) (by decide)]
  decide

theorem b215 : ∀ z : ZMod 29, twisted 29 5 13 17 z ↔ z ∈ ([0, 2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 5 13 17 (by decide) (by decide)]
  decide

theorem b101 : ∀ z : ZMod 29, twisted 29 5 23 14 z ↔ z ∈ ([0, 2, 3, 8, 10, 11, 12, 14, 15, 17, 18, 19, 21, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 5 23 14 (by decide) (by decide)]
  decide

theorem b119 : ∀ z : ZMod 29, twisted 29 5 25 6 z ↔ z ∈ ([0, 1, 4, 5, 6, 7, 9, 13, 16, 20, 22, 23, 24, 25, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 5 25 6 (by decide) (by decide)]
  decide

theorem b074 : ∀ z : ZMod 29, twisted 29 6 16 3 z ↔ z ∈ ([0, 3, 7, 22, 26] : List (ZMod 29)) := by
  simp only [twisted_iff 29 6 16 3 (by decide) (by decide)]
  decide

theorem b164 : ∀ z : ZMod 29, twisted 29 6 18 3 z ↔ z ∈ ([0, 3, 7, 22, 26] : List (ZMod 29)) := by
  simp only [twisted_iff 29 6 18 3 (by decide) (by decide)]
  decide

theorem b239 : ∀ z : ZMod 29, twisted 29 6 24 13 z ↔ z ∈ ([0, 11, 13, 16, 18] : List (ZMod 29)) := by
  simp only [twisted_iff 29 6 24 13 (by decide) (by decide)]
  decide

theorem b128 : ∀ z : ZMod 29, twisted 29 6 27 23 z ↔ z ∈ ([0, 6, 14, 15, 23] : List (ZMod 29)) := by
  simp only [twisted_iff 29 6 27 23 (by decide) (by decide)]
  decide

theorem b231 : twisted 29 7 8 24 1 := by
  simp only [twisted_iff 29 7 8 24 (by decide) (by decide)]
  decide

theorem b092 : ∀ z : ZMod 29, twisted 29 7 10 10 z ↔ z ∈ ([0, 8, 10, 12, 15, 18, 26, 27] : List (ZMod 29)) := by
  simp only [twisted_iff 29 7 10 10 (by decide) (by decide)]
  decide

theorem b191 : ∀ z : ZMod 29, twisted 29 7 19 4 z ↔ z ∈ ([0, 4, 5, 6, 9, 13, 22, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 7 19 4 (by decide) (by decide)]
  decide

theorem b083 : ∀ z : ZMod 29, twisted 29 7 21 14 z ↔ z ∈ ([0, 2, 3, 11, 14, 17, 19, 21] : List (ZMod 29)) := by
  simp only [twisted_iff 29 7 21 14 (by decide) (by decide)]
  decide

theorem b199 : twisted 29 7 22 13 13 ∧ ¬ twisted 29 7 22 13 1 := by
  simp only [twisted_iff 29 7 22 13 (by decide) (by decide)]
  decide

theorem b065 : ∀ z : ZMod 29, twisted 29 7 27 4 z ↔ z ∈ ([0, 4, 5, 6, 9, 13, 22, 28] : List (ZMod 29)) := by
  simp only [twisted_iff 29 7 27 4 (by decide) (by decide)]
  decide

end Q29

section Q31
local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

theorem b240 : twisted 31 1 15 10 1 := by
  simp only [twisted_iff 31 1 15 10 (by decide) (by decide)]
  decide

theorem b129 : twisted 31 1 16 7 1 := by
  simp only [twisted_iff 31 1 16 7 (by decide) (by decide)]
  decide

theorem b057 : twisted 31 1 20 7 1 := by
  simp only [twisted_iff 31 1 20 7 (by decide) (by decide)]
  decide

theorem b093 : twisted 31 1 29 5 1 := by
  simp only [twisted_iff 31 1 29 5 (by decide) (by decide)]
  decide

theorem b156 : twisted 31 2 7 2 1 := by
  simp only [twisted_iff 31 2 7 2 (by decide) (by decide)]
  decide

theorem b248 : ∀ z : ZMod 31, twisted 31 2 19 17 z ↔ z ∈ ([0, 3, 6, 7, 12, 14, 17, 19, 24, 25, 28] : List (ZMod 31)) := by
  simp only [twisted_iff 31 2 19 17 (by decide) (by decide)]
  decide

theorem b102 : twisted 31 3 0 9 1 := by
  simp only [twisted_iff 31 3 0 9 (by decide) (by decide)]
  decide

theorem b084 : twisted 31 3 5 4 1 := by
  simp only [twisted_iff 31 3 5 4 (by decide) (by decide)]
  decide

theorem b200 : ∀ z : ZMod 31, twisted 31 4 0 28 z ↔ z ∈ ([0, 3, 13, 15, 16, 18, 28] : List (ZMod 31)) := by
  simp only [twisted_iff 31 4 0 28 (by decide) (by decide)]
  decide

theorem b018 : twisted 31 4 6 26 1 := by
  simp only [twisted_iff 31 4 6 26 (by decide) (by decide)]
  decide

theorem b038 : ∀ z : ZMod 31, twisted 31 4 12 12 z ↔ z ∈ ([0, 2, 10, 12, 19, 21, 29] : List (ZMod 31)) := by
  simp only [twisted_iff 31 4 12 12 (by decide) (by decide)]
  decide

theorem b111 : twisted 31 4 14 26 1 := by
  simp only [twisted_iff 31 4 14 26 (by decide) (by decide)]
  decide

theorem b183 : twisted 31 4 23 6 1 := by
  simp only [twisted_iff 31 4 23 6 (by decide) (by decide)]
  decide

theorem b208 : twisted 31 4 30 22 22 ∧ ¬ twisted 31 4 30 22 1 := by
  simp only [twisted_iff 31 4 30 22 (by decide) (by decide)]
  decide

theorem b008 : ∀ z : ZMod 31, twisted 31 5 6 17 z ↔ z ∈ ([0, 3, 6, 12, 17, 24] : List (ZMod 31)) := by
  simp only [twisted_iff 31 5 6 17 (by decide) (by decide)]
  decide

theorem b120 : twisted 31 5 12 16 1 := by
  simp only [twisted_iff 31 5 12 16 (by decide) (by decide)]
  decide

theorem b066 : twisted 31 5 17 2 1 := by
  simp only [twisted_iff 31 5 17 2 (by decide) (by decide)]
  decide

theorem b147 : twisted 31 5 25 16 1 := by
  simp only [twisted_iff 31 5 25 16 (by decide) (by decide)]
  decide

theorem b192 : twisted 31 5 26 4 1 := by
  simp only [twisted_iff 31 5 26 4 (by decide) (by decide)]
  decide

theorem b165 : twisted 31 5 30 2 1 := by
  simp only [twisted_iff 31 5 30 2 (by decide) (by decide)]
  decide

theorem b174 : twisted 31 7 4 18 1 := by
  simp only [twisted_iff 31 7 4 18 (by decide) (by decide)]
  decide

theorem b075 : twisted 31 7 10 14 1 := by
  simp only [twisted_iff 31 7 10 14 (by decide) (by decide)]
  decide

theorem b232 : twisted 31 7 11 11 11 ∧ ¬ twisted 31 7 11 11 1 := by
  simp only [twisted_iff 31 7 11 11 (by decide) (by decide)]
  decide

theorem b138 : twisted 31 7 12 14 1 := by
  simp only [twisted_iff 31 7 12 14 (by decide) (by decide)]
  decide

theorem b216 : twisted 31 7 15 18 1 := by
  simp only [twisted_iff 31 7 15 18 (by decide) (by decide)]
  decide

theorem b048 : twisted 31 7 17 9 1 := by
  simp only [twisted_iff 31 7 17 9 (by decide) (by decide)]
  decide

theorem b028 : twisted 31 7 18 23 23 ∧ ¬ twisted 31 7 18 23 1 := by
  simp only [twisted_iff 31 7 18 23 (by decide) (by decide)]
  decide

theorem b224 : ∀ z : ZMod 31, twisted 31 7 30 14 z ↔ z ∈ ([0, 1, 2, 4, 5, 7, 8, 9, 10, 14, 16, 18, 19, 20, 25, 28] : List (ZMod 31)) := by
  simp only [twisted_iff 31 7 30 14 (by decide) (by decide)]
  decide

end Q31

section Q37
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

theorem b094 : twisted 37 1 0 17 17 ∧ ¬ twisted 37 1 0 17 1 := by
  simp only [twisted_iff 37 1 0 17 (by decide) (by decide)]
  decide

theorem b166 : twisted 37 1 2 23 23 ∧ ¬ twisted 37 1 2 23 1 := by
  simp only [twisted_iff 37 1 2 23 (by decide) (by decide)]
  decide

theorem b039 : twisted 37 1 7 36 1 := by
  simp only [twisted_iff 37 1 7 36 (by decide) (by decide)]
  decide

theorem b209 : ∀ z : ZMod 37, twisted 37 1 8 7 z ↔ z ∈ ([0, 1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List (ZMod 37)) := by
  simp only [twisted_iff 37 1 8 7 (by decide) (by decide)]
  decide

theorem b085 : twisted 37 1 18 15 15 ∧ ¬ twisted 37 1 18 15 1 := by
  simp only [twisted_iff 37 1 18 15 (by decide) (by decide)]
  decide

theorem b233 : ∀ z : ZMod 37, twisted 37 1 28 10 z ↔ z ∈ ([0, 1, 3, 4, 7, 9, 10, 11, 12, 16, 21, 25, 26, 27, 28, 30, 33, 34, 36] : List (ZMod 37)) := by
  simp only [twisted_iff 37 1 28 10 (by decide) (by decide)]
  decide

theorem b201 : twisted 37 1 30 10 1 := by
  simp only [twisted_iff 37 1 30 10 (by decide) (by decide)]
  decide

theorem b184 : twisted 37 2 5 24 24 ∧ ¬ twisted 37 2 5 24 1 := by
  simp only [twisted_iff 37 2 5 24 (by decide) (by decide)]
  decide

theorem b241 : twisted 37 2 9 3 3 ∧ ¬ twisted 37 2 9 3 1 := by
  simp only [twisted_iff 37 2 9 3 (by decide) (by decide)]
  decide

theorem b058 : twisted 37 2 28 9 9 ∧ ¬ twisted 37 2 28 9 1 := by
  simp only [twisted_iff 37 2 28 9 (by decide) (by decide)]
  decide

theorem b067 : twisted 37 2 34 19 19 ∧ ¬ twisted 37 2 34 19 1 := by
  simp only [twisted_iff 37 2 34 19 (by decide) (by decide)]
  decide

theorem b103 : twisted 37 3 1 35 35 ∧ ¬ twisted 37 3 1 35 1 := by
  simp only [twisted_iff 37 3 1 35 (by decide) (by decide)]
  decide

theorem b175 : twisted 37 3 29 27 27 ∧ ¬ twisted 37 3 29 27 1 := by
  simp only [twisted_iff 37 3 29 27 (by decide) (by decide)]
  decide

theorem b148 : twisted 37 3 31 31 31 ∧ ¬ twisted 37 3 31 31 1 := by
  simp only [twisted_iff 37 3 31 31 (by decide) (by decide)]
  decide

theorem b076 : twisted 37 5 1 25 25 ∧ ¬ twisted 37 5 1 25 1 := by
  simp only [twisted_iff 37 5 1 25 (by decide) (by decide)]
  decide

theorem b139 : twisted 37 5 9 31 31 ∧ ¬ twisted 37 5 9 31 1 := by
  simp only [twisted_iff 37 5 9 31 (by decide) (by decide)]
  decide

theorem b009 : twisted 37 5 15 26 1 := by
  simp only [twisted_iff 37 5 15 26 (by decide) (by decide)]
  decide

theorem b112 : twisted 37 5 20 20 20 ∧ ¬ twisted 37 5 20 20 1 := by
  simp only [twisted_iff 37 5 20 20 (by decide) (by decide)]
  decide

theorem b130 : twisted 37 5 29 13 13 ∧ ¬ twisted 37 5 29 13 1 := by
  simp only [twisted_iff 37 5 29 13 (by decide) (by decide)]
  decide

theorem b157 : twisted 37 5 30 17 17 ∧ ¬ twisted 37 5 30 17 1 := by
  simp only [twisted_iff 37 5 30 17 (by decide) (by decide)]
  decide

theorem b049 : twisted 37 5 35 25 25 ∧ ¬ twisted 37 5 35 25 1 := by
  simp only [twisted_iff 37 5 35 25 (by decide) (by decide)]
  decide

theorem b019 : twisted 37 7 9 5 5 ∧ ¬ twisted 37 7 9 5 1 := by
  simp only [twisted_iff 37 7 9 5 (by decide) (by decide)]
  decide

theorem b029 : ∀ z : ZMod 37, twisted 37 7 13 30 z ↔ z ∈ ([0, 3, 4, 11, 21, 25, 27, 28, 30, 36] : List (ZMod 37)) := by
  simp only [twisted_iff 37 7 13 30 (by decide) (by decide)]
  decide

theorem b217 : twisted 37 7 16 15 15 ∧ ¬ twisted 37 7 16 15 1 := by
  simp only [twisted_iff 37 7 16 15 (by decide) (by decide)]
  decide

theorem b121 : twisted 37 7 18 22 22 ∧ ¬ twisted 37 7 18 22 1 := by
  simp only [twisted_iff 37 7 18 22 (by decide) (by decide)]
  decide

theorem b193 : twisted 37 7 19 23 23 ∧ ¬ twisted 37 7 19 23 1 := by
  simp only [twisted_iff 37 7 19 23 (by decide) (by decide)]
  decide

theorem b225 : twisted 37 7 31 7 1 := by
  simp only [twisted_iff 37 7 31 7 (by decide) (by decide)]
  decide

end Q37

end OrbitQ
