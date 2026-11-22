import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem scalarUnitCorner {R : Type*} [CommRing R] (a b : R) :
    Matrix.det !![(1 : R), a, 0; b, 1, a; 0, -b, 1] = 1 := by
  rw [Matrix.det_fin_three]
  simp

theorem inflatedSchurCorner {R : Type*} [CommRing R] :
    Matrix.det
      ((1 : Matrix (Fin 2) (Fin 2) R)
        - !![0, 0; (1 : R), 0] * !![0, (1 : R); 0, 0]
        + !![0, (1 : R); 0, 0] * !![0, 0; (1 : R), 0]) = 0 := by
  rw [Matrix.det_fin_two]
  simp
