import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Abel

namespace ShearSTPP

variable {I X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

def DisjointTranslates {G : Type*} [AddCommGroup G]
    (t : I → G) (S : I → Set G) : Prop :=
  ∀ i j u v, u ∈ S i → v ∈ S j → t i + u = t j + v → i = j

def leftPoint (x : I → X) (y : I → Y) (i : I) (u : X) : X × Y × Z :=
  (x i + u, y i, 0)

def middlePoint (y : I → Y) (i : I) (v : Y) : X × Y × Z :=
  (0, y i + v, 0)

def rightPoint (z : Z) : X × Y × Z :=
  (0, 0, z)

def cycle (x : I → X) (y : I → Y) (i j k : I)
    (u w : X) (s t : Y) (p q : Z) : X × Y × Z :=
  (leftPoint x y i u - middlePoint y i s) +
  (middlePoint y j t - rightPoint p) +
  (rightPoint q - leftPoint x y k w)

private theorem cycle_components (x : I → X) (y : I → Y) (i j k : I)
    (u w : X) (s t : Y) (p q : Z) :
    cycle x y i j k u w s t p q =
      ((x i + u) - (x k + w), (y j + t) - (y k + s), q - p) := by
  ext <;> simp [cycle, leftPoint, middlePoint, rightPoint] <;> abel

def Realizes (x : I → X) (y : I → Y) (S : I → Set X) (T : I → Set Y) : Prop :=
  ∀ i j k u w s t (p q : Z),
    u ∈ S i → w ∈ S k → s ∈ T i → t ∈ T j →
    cycle x y i j k u w s t p q = 0 →
    i = k ∧ j = k ∧ u = w ∧ s = t ∧ p = q

/-- The two shear coordinates admit precisely two independent packings. -/
theorem realizes_iff (x : I → X) (y : I → Y) (S : I → Set X) (T : I → Set Y)
    (hS : ∀ i, (S i).Nonempty) (hT : ∀ i, (0 : Y) ∈ T i) :
    Realizes (Z := Z) x y S T ↔ DisjointTranslates x S ∧ DisjointTranslates y T := by
  constructor
  · intro h
    constructor
    · intro i j u v hu hv huv
      have hc : cycle x y i j j u v 0 0 (0 : Z) 0 = 0 := by
        rw [cycle_components, huv]
        simp
      exact (h i j j u v 0 0 0 0 hu hv (hT i) (hT j) hc).1
    · intro i j u v hu hv huv
      obtain ⟨z, hz⟩ := hS j
      have hc : cycle x y j i j z z v u (0 : Z) 0 = 0 := by
        rw [cycle_components, huv]
        simp
      exact (h j i j z z v u 0 0 hz hz hv hu hc).2.1
  · rintro ⟨hx, hy⟩ i j k u w s t p q hu hw hs ht hc
    rw [cycle_components] at hc
    have hX : (x i + u) - (x k + w) = 0 := congrArg Prod.fst hc
    have hY : (y j + t) - (y k + s) = 0 := congrArg (fun r => r.2.1) hc
    have hZ : q - p = 0 := congrArg (fun r => r.2.2) hc
    have hik := hx i k u w hu hw (sub_eq_zero.mp hX)
    subst i
    have hjk := hy j k t s ht hs (sub_eq_zero.mp hY)
    subst j
    exact ⟨rfl, rfl, add_left_cancel (sub_eq_zero.mp hX),
      (add_left_cancel (sub_eq_zero.mp hY)).symm, (sub_eq_zero.mp hZ).symm⟩

end ShearSTPP
