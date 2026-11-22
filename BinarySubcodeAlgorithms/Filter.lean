import Mathlib.LinearAlgebra.Span.Basic

namespace BinarySubcode

theorem filter_preserves_transport {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (T : V →ₗ[K] W) (C : Submodule K V) (D : Submodule K W)
    (p : V → Prop) (q : W → Prop)
    (preserves : ∀ v, p v → q (T v))
    (generates : C = Submodule.span K {v : V | v ∈ C ∧ p v}) :
    C ≤ D.comap T ↔
      C ≤ (Submodule.span K {w : W | w ∈ D ∧ q w}).comap T := by
  constructor
  · intro h
    conv_lhs => rw [generates]
    apply Submodule.span_le.mpr
    intro v hv
    exact Submodule.subset_span ⟨h hv.1, preserves v hv.2⟩
  · intro h v hv
    have inc : Submodule.span K {w : W | w ∈ D ∧ q w} ≤ D :=
      Submodule.span_le.mpr (fun _ hw => hw.1)
    exact inc (h hv)

end BinarySubcode
