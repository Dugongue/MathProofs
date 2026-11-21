import Mathlib.Algebra.Algebra.Subalgebra.Lattice

namespace HolonomyCharts

theorem one_chart_map_matches_all_queries {R A B I : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    (s : Set A) (reference : A →ₐ[R] B)
    (alternate : I → (A →ₐ[R] B)) (query : I → A)
    (agrees : ∀ i, Set.EqOn reference (alternate i) s)
    (generated : ∀ i, query i ∈ Algebra.adjoin R s) :
    ∀ i, reference (query i) = alternate i (query i) := by
  intro i
  exact AlgHom.adjoin_le_equalizer reference (alternate i) (agrees i) (generated i)

end HolonomyCharts
