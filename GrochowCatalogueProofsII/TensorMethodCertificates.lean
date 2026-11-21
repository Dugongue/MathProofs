import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Abel

namespace CatalogueTensorMethods

inductive GenerationTerm where
  | seed
  | product : GenerationTerm → GenerationTerm → GenerationTerm

def evalTerm {V : Type*} (op : V → V → V) (v : V) : GenerationTerm → V
  | .seed => v
  | .product a b => op (evalTerm op v a) (evalTerm op v b)

/-- Equivariant products send every word in a seed to the corresponding word. -/
theorem evalTerm_transport {V W : Type*} (g : V → W) (op : V → V → V)
    (op' : W → W → W) (v : V) (h : ∀ x y, g (op x y) = op' (g x) (g y))
    (t : GenerationTerm) :
    g (evalTerm op v t) = evalTerm op' (g v) t := by
  induction t with
  | seed => rfl
  | product a b ha hb =>
    change g (op (evalTerm op v a) (evalTerm op v b)) =
      op' (evalTerm op' (g v) a) (evalTerm op' (g v) b)
    rw [h, ha, hb]

/-- A transporter of a seed and its product is unique if its words span. -/
theorem spanning_seed_transport_unique {R V W : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (g h : V →ₗ[R] W) (op : V → V → V) (op' : W → W → W) (v : V)
    (hg : ∀ x y, g (op x y) = op' (g x) (g y))
    (hh : ∀ x y, h (op x y) = op' (h x) (h y)) (hs : g v = h v)
    (hspan : Submodule.span R (Set.range (evalTerm op v)) = ⊤) :
    g = h := by
  ext x
  have hx : x ∈ Submodule.span R (Set.range (evalTerm op v)) := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨t, rfl⟩
    rw [evalTerm_transport g op op' v hg t, evalTerm_transport h op op' v hh t, hs]
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro a y _ hy
    simp [hy]

/-- The action defect is additive modulo the next invariant layer. -/
theorem orbit_lift_additive_mod {R V : Type*} [Semiring R]
    [AddCommGroup V] [Module R V]
    (g h : V →ₗ[R] V) (F K : Submodule R V) (v : V)
    (hh : h v - v ∈ F) (hg : ∀ x ∈ F, g x - x ∈ K) :
    (g (h v) - v) - ((g v - v) + (h v - v)) ∈ K := by
  have hv := hg (h v - v) hh
  rw [map_sub] at hv
  have eq : (g (h v) - v) - ((g v - v) + (h v - v)) =
      g (h v) - g v - (h v - v) := by abel
  exact eq.symm ▸ hv

end CatalogueTensorMethods
