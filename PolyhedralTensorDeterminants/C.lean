
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PolyhedralIntervals

open scoped BigOperators

theorem potential_product_by_endpoints {α G : Type*}
    [Fintype α] [DecidableEq α] [CommGroup G]
    (E : Finset (α × α)) (u : α → G) :
    (∏ e ∈ E, u e.2 / u e.1) =
      (∏ x : α, u x ^ (E.filter fun e => e.2 = x).card) /
        ∏ x : α, u x ^ (E.filter fun e => e.1 = x).card := by
  rw [Finset.prod_div_distrib, ← Finset.prod_fiberwise' E Prod.snd u,
    ← Finset.prod_fiberwise' E Prod.fst u]
  simp only [Finset.prod_const]

end PolyhedralIntervals
