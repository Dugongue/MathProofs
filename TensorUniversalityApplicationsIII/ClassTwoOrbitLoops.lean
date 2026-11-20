import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Tactic.Group

namespace ClassTwoOrbitLoops

/-- An orbit edge, transported back along its chosen representative, gives a stabilizer element. -/
theorem schreier_loop {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (π : G →* H) (x : X) (a b s : G) (edge : b • x = s • (a • x)) :
    ∃ loop : G, loop • x = x ∧ π loop = (π b)⁻¹ * π s * π a := by
  refine ⟨b⁻¹ * s * a, ?_, ?_⟩
  · simp only [mul_smul, ← edge, inv_smul_smul]
  · simp only [map_mul, map_inv]

/-- Labels of successive edges telescope to the label of the whole path. -/
theorem telescope_edge_labels {G : Type*} [Group G] (a b c u v : G) :
    (a * u * b⁻¹) * (b * v * c⁻¹) = a * (u * v) * c⁻¹ := by group

/-- A quotient homomorphism into the center defines a central shift. -/
theorem central_shift_mul {G A : Type*} [Group G] [Group A]
    (q : G →* A) (χ : A →* G) (central : ∀ a g, Commute (χ a) g) (x y : G) :
    x * y * χ (q (x * y)) = (x * χ (q x)) * (y * χ (q y)) := by
  simp only [map_mul]
  calc
    x * y * (χ (q x) * χ (q y)) = x * (y * χ (q x)) * χ (q y) := by
      simp only [mul_assoc]
    _ = x * (χ (q x) * y) * χ (q y) := by rw [(central (q x) y).eq]
    _ = (x * χ (q x)) * (y * χ (q y)) := by simp only [mul_assoc]

/-- Inverting the central values gives the inverse shift when they vanish in the quotient. -/
theorem central_shift_cancel {G A : Type*} [Group G] [Group A]
    (q : G →* A) (χ : A →* G) (trivial : ∀ a, q (χ a) = 1) (x : G) :
    (x * χ (q x)) * (χ (q (x * χ (q x))))⁻¹ = x := by
  simp [map_mul, trivial, mul_assoc]

end ClassTwoOrbitLoops
