import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

namespace CatalogueGraphRecovery

theorem cross_reindex {G : Type*} [Group G] (g h g0 h0 : G) :
    (g⁻¹ * g0) * (g0⁻¹ * h * h0⁻¹ * g0) * (g0⁻¹ * h0) = g⁻¹ * h := by
  group

theorem left_from_right_coset {G : Type*} [Group G] (a b k : G) :
    a * (b * k) = (a * b) * k := by
  rw [mul_assoc]

theorem right_from_left_coset {G : Type*} [Group G] (a b k : G) :
    (k * b) * a = k * (b * a) := by
  rw [mul_assoc]

theorem row_order_below_half_gap
    (a b a' b' ε : ℝ) (ha : |a' - a| ≤ ε) (hb : |b' - b| ≤ ε)
    (gap : 2 * ε < b - a) : a' < b' := by
  have hu : a' - a ≤ ε := (abs_le.mp ha).2
  have hl : -ε ≤ b' - b := (abs_le.mp hb).1
  linarith

theorem common_quotient_commutes_of_reversed_pairs
    {B D Q : Type*} [Group B] [Group D] [Group Q]
    (p : B →* Q) (q : D →* Q) (sp : Function.Surjective p) (sq : Function.Surjective q)
    (hrev : ∀ b b' d d', p b = q d → p b' = q d' → p (b' * b) = q (d * d')) :
    ∀ u v : Q, u * v = v * u := by
  intro u v
  obtain ⟨b, rfl⟩ := sp u
  obtain ⟨b', rfl⟩ := sp v
  obtain ⟨d, hd⟩ := sq (p b)
  obtain ⟨d', hd'⟩ := sq (p b')
  calc
    p b * p b' = q d * q d' := by rw [hd, hd']
    _ = q (d * d') := (map_mul q _ _).symm
    _ = p (b' * b) := (hrev b b' d d' hd.symm hd'.symm).symm
    _ = p b' * p b := map_mul p _ _

end CatalogueGraphRecovery

#print axioms CatalogueGraphRecovery.cross_reindex
#print axioms CatalogueGraphRecovery.left_from_right_coset
#print axioms CatalogueGraphRecovery.right_from_left_coset
#print axioms CatalogueGraphRecovery.row_order_below_half_gap
#print axioms CatalogueGraphRecovery.common_quotient_commutes_of_reversed_pairs
