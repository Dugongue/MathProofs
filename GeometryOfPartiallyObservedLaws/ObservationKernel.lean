import Mathlib.Algebra.Module.Submodule.Ker

theorem observed_linear_map_iff_kernel
    {K V Y W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup Y] [Module K Y] [AddCommGroup W] [Module K W]
    (P : V →ₗ[K] Y) (F : V →ₗ[K] W) :
    (∀ v w, P v = P w → F v = F w) ↔ LinearMap.ker P ≤ LinearMap.ker F := by
  constructor
  · intro h v hv
    have same : P v = P 0 := by
      simpa only [map_zero] using (LinearMap.mem_ker.mp hv)
    apply LinearMap.mem_ker.mpr
    simpa only [map_zero] using h v 0 same
  · intro h v w same
    have diff : v - w ∈ LinearMap.ker P := LinearMap.mem_ker.mpr (by
      rw [map_sub, same, sub_self])
    have zero : F v - F w = 0 := by
      simpa only [map_sub] using (LinearMap.mem_ker.mp (h diff))
    exact sub_eq_zero.mp zero
