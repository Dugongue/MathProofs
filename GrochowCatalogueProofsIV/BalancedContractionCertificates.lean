import Lean.Elab.Tactic.Omega

namespace GrochowCatalogueFourth

/-- A balanced four-cycle has an opposite pair costing at most five sixths
    of the full contraction exponent when that pair is summed out. -/
theorem balanced_opposite_pair (a b c e d : Nat)
    (hab : d ≤ 3 * (a + b)) (hbc : d ≤ 3 * (b + c))
    (hce : d ≤ 3 * (c + e)) (hea : d ≤ 3 * (e + a)) :
    (d ≤ 6 * a ∧ d ≤ 6 * c) ∨ (d ≤ 6 * b ∧ d ≤ 6 * e) := by
  omega

/-- Near the naive exponent boundary, no dimension of the four matrices
    is small. This is what makes square blocking improve the exponent. -/
theorem near_boundary_all_large (a b c e d : Nat)
    (hab : d ≤ 3 * (a + b)) (hbc : d ≤ 3 * (b + c))
    (hce : d ≤ 3 * (c + e)) (hea : d ≤ 3 * (e + a))
    (hac : 120 * a ≤ 23 * d ∨ 120 * c ≤ 23 * d)
    (hbe : 120 * b ≤ 23 * d ∨ 120 * e ≤ 23 * d) :
    17 * d ≤ 120 * a ∧ 17 * d ≤ 120 * b ∧
    17 * d ≤ 120 * c ∧ 17 * d ≤ 120 * e := by
  omega

end GrochowCatalogueFourth

#print axioms GrochowCatalogueFourth.balanced_opposite_pair
#print axioms GrochowCatalogueFourth.near_boundary_all_large
