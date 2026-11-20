import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

namespace StablePresentationLift

variable {R P Q M : Type*} [Ring R]
variable [AddCommGroup P] [AddCommGroup Q] [AddCommGroup M]
variable [Module R P] [Module R Q] [Module R M]

/-- Swap two projective covers after lifting in both directions by linear maps. -/
def swapCovers (a : P →ₗ[R] Q) (b : Q →ₗ[R] P) : (P × Q) ≃ₗ[R] (Q × P) where
  toFun p := (a p.1 + (p.2 - a (b p.2)), p.1 - b p.2)
  invFun p := (p.2 + b (p.1 - a p.2), p.1 - a p.2)
  left_inv p := by
    apply Prod.ext <;> simp
  right_inv p := by
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Prod.ext <;> simp <;> abel
  map_smul' r x := by
    apply Prod.ext
    · change a (r • x.1) + (r • x.2 - a (b (r • x.2))) =
        r • (a x.1 + (x.2 - a (b x.2)))
      simp [smul_add, smul_sub]
    · change r • x.1 - b (r • x.2) = r • (x.1 - b x.2)
      simp [smul_sub]

/-- Two surjections from projectives onto a common module become equivalent
after adjoining the other projective as a zero summand. -/
theorem surjections_equivalent_after_padding [Module.Projective R P] [Module.Projective R Q]
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M) (hp : Function.Surjective p) (hq : Function.Surjective q) :
    ∃ e : (P × Q) ≃ₗ[R] (Q × P), ∀ x, q (e x).1 = p x.1 := by
  obtain ⟨a, ha⟩ := Module.projective_lifting_property q p hq
  obtain ⟨b, hb⟩ := Module.projective_lifting_property p q hp
  refine ⟨swapCovers a b, ?_⟩
  intro x
  have ha' (y : P) : q (a y) = p y := DFunLike.congr_fun ha y
  have hb' (y : Q) : p (b y) = q y := DFunLike.congr_fun hb y
  change q (a x.1 + (x.2 - a (b x.2))) = p x.1
  simp only [map_add, map_sub, ha', hb', sub_self, add_zero]

/-- With a submodule mark, the top-right block of an invertible triangular
change of coordinates is arbitrary inside the marked submodule. -/
theorem triangular_transport_iff {P' : Type*} [AddCommGroup P'] [Module R P'] (A : P ≃ₗ[R] P')
    (K : Submodule R P) (K' : Submodule R P') (S : Q →ₗ[R] P') :
    (∀ x y, x ∈ K ↔ A x + S y ∈ K') ↔
      ((∀ x, x ∈ K ↔ A x ∈ K') ∧ ∀ y, S y ∈ K') := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun y => ?_⟩
    · simpa using h x 0
    · simpa using (h 0 y).mp K.zero_mem
  · rintro ⟨hA, hS⟩ x y
    constructor
    · exact fun hx => K'.add_mem ((hA x).mp hx) (hS y)
    · intro h
      apply (hA x).mpr
      simpa using K'.sub_mem h (hS y)

end StablePresentationLift
