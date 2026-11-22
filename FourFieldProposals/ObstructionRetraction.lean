import Mathlib.RingTheory.Ideal.Basic

theorem certificate_obstruction_of_retraction
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (U W : Submodule R V) (J : Ideal R) (v : V) (ell : V →ₗ[R] R)
    (ell_v : ell v = 1)
    (ell_U : ∀ w ∈ U, ell w = 0)
    (ell_W : ∀ w ∈ W, ell w ∈ J)
    (J_v : ∀ a ∈ J, a • v ∈ W)
    (a : R) :
    a • v ∈ U ⊔ W ↔ a ∈ J := by
  constructor
  · intro h
    obtain ⟨u, hu, w, hw, eq⟩ := Submodule.mem_sup.mp h
    have hw' : ell w ∈ J := ell_W w hw
    have hEq : ell w = a := by
      have hEval := congrArg ell eq
      simpa [ell_U u hu, ell_v] using hEval
    rwa [hEq] at hw'
  · intro h
    exact Submodule.mem_sup_right (J_v a h)
