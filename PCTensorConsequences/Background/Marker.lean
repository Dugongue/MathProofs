import Mathlib.LinearAlgebra.Span.Basic

namespace PCThreeRoutes

theorem shared_column_scalar {K V W ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] V) (Q : W →ₗ[K] W) (column : W →ₗ[K] K)
    (a : W) (ha : column a = 1) (v : ι → V)
    (arrows : ∀ i w, L (column w • v i) = column (Q w) • v i) :
    ∀ x ∈ Submodule.span K (Set.range v), L x = column (Q a) • x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    simpa [ha] using arrows i a
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul c x _ hx => simpa [map_smul, hx] using smul_comm c (column (Q a)) x

end PCThreeRoutes
