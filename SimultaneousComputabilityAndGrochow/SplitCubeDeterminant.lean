import Mathlib

def explicitIntegralCubePencil {R : Type*} [CommRing R] (w x y : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![x * (w - 1) + y * (w - 1), x * (-2) + y * (-3);
     x * (-3) + y * (-2), x * (-w) + y * (-w)]

theorem explicit_integral_cube_pencil_det {R : Type*} [CommRing R] (w x y : R)
    (hw : w ^ 2 - w + 6 = 0) :
    (explicitIntegralCubePencil w x y).det = -(x * y) := by
  rw [Matrix.det_fin_two]
  simp [explicitIntegralCubePencil]
  linear_combination -(x + y) ^ 2 * hw
