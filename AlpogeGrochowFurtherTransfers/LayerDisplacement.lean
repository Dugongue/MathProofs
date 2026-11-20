import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

namespace TensorLayerDisplacement

variable {G V W : Type*} [Group G] [AddCommGroup V] [AddCommGroup W]

/--
If the represented action is trivial on the projected displacement of the source,
the projected displacement is a homomorphism into the additive target layer.
-/
def displacementHom (act : G → V →+ V)
    (hmul : ∀ g h v, act (g * h) v = act g (act h v))
    (s : V) (hone : act 1 s = s)
    (project : V →+ W)
    (htriv : ∀ g h, project (act g (act h s - s)) = project (act h s - s)) :
    G →* Multiplicative W where
  toFun g := Multiplicative.ofAdd (project (act g s - s))
  map_one' := by
    change project (act 1 s - s) = 0
    rw [hone, sub_self, map_zero]
  map_mul' g h := by
    change project (act (g * h) s - s) =
      project (act g s - s) + project (act h s - s)
    calc
      _ = project ((act g (act h s) - act g s) + (act g s - s)) := by
        rw [hmul, sub_add_sub_cancel]
      _ = project (act g (act h s - s)) + project (act g s - s) := by
        rw [map_add, map_sub (act g)]
      _ = _ := by rw [htriv, add_comm]

theorem displacement_mul (act : G → V →+ V)
    (hmul : ∀ g h v, act (g * h) v = act g (act h v))
    (s : V) (hone : act 1 s = s)
    (project : V →+ W)
    (htriv : ∀ g h, project (act g (act h s - s)) = project (act h s - s))
    (g h : G) :
    project (act (g * h) s - s) = project (act g s - s) + project (act h s - s) :=
  (displacementHom act hmul s hone project htriv).map_mul g h

end TensorLayerDisplacement
