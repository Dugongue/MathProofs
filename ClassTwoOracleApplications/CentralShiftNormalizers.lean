import Mathlib.Algebra.Group.Equiv.Basic

namespace CentralShiftNormalizers

theorem shifts_intertwine_iff {A A' C C' G H : Type*} [Group G] [Group H]
    (f : G ≃* H) (p : G → A) (q : H → A') (inC : C → G) (inC' : C' → H)
    (alpha : A → A') (gamma : C → C') (d : A → C) (d' : A' → C')
    (hp : Function.Surjective p) (hinj : Function.Injective inC')
    (hpq : ∀ g, q (f g) = alpha (p g))
    (hkernel : ∀ c, f (inC c) = inC' (gamma c)) :
    (∀ g, f (g * inC (d (p g))) = f g * inC' (d' (q (f g)))) ↔
      ∀ a, gamma (d a) = d' (alpha a) := by
  constructor
  · intro h a
    obtain ⟨g, rfl⟩ := hp a
    apply hinj
    apply mul_left_cancel (a := f g)
    simpa only [map_mul, hkernel, hpq] using h g
  · intro h g
    rw [map_mul, hkernel, hpq, h (p g)]

theorem evaluation_action_unique {A A' C C' D D' : Type*}
    (eval : D → A → C) (eval' : D' → A' → C')
    (alpha : A → A') (gamma : C → C') (s t : D → D')
    (hAlpha : Function.Surjective alpha) (hEval' : Function.Injective eval')
    (hs : ∀ d a, eval' (s d) (alpha a) = gamma (eval d a))
    (ht : ∀ d a, eval' (t d) (alpha a) = gamma (eval d a)) :
    s = t := by
  funext d
  apply hEval'
  funext target
  obtain ⟨a, rfl⟩ := hAlpha target
  exact (hs d a).trans (ht d a).symm

end CentralShiftNormalizers

#print axioms CentralShiftNormalizers.shifts_intertwine_iff
#print axioms CentralShiftNormalizers.evaluation_action_unique
