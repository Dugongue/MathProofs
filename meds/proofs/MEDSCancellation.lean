import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

theorem MEDSCancellation.inverse_from_slice {K m n : Type*} [CommRing K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (C P : Matrix m n K) (R B : Matrix n n K)
    (E : Matrix n m K) (hsolve : A * C = P * R)
    (hB : R * B = 1) (hP : P * E = 1) :
    A * (C * B * E) = 1 ∧ (C * B * E) * A = 1 := by
    have h : A * (C * B * E) = 1 := by
      calc
        A * (C * B * E) = ((A * C) * B) * E := by simp only [Matrix.mul_assoc]
        _ = ((P * R) * B) * E := by rw [hsolve]
        _ = 1 := by rw [Matrix.mul_assoc P R B, hB, Matrix.mul_one, hP]
    exact ⟨h, mul_eq_one_comm.mp h⟩
