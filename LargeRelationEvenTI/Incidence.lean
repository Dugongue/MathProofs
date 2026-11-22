import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Logic.Relation

open scoped BigOperators

namespace RelationParity

variable {V A : Type*} [Fintype V] [DecidableEq V] [AddCommGroup A]

def point (v : V) (a : A) : V → A := fun u => if v = u then a else 0

def boundary {E : Type*} [Fintype E] (src dst : E → V) :
    (E → A) →+ (V → A) where
  toFun w := ∑ e, (point (dst e) (w e) - point (src e) (w e))
  map_zero' := by ext v; simp [point]
  map_add' w z := by
    ext v
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.add_apply, point, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hd : dst e = v <;> by_cases hs : src e = v <;> simp [hd, hs, add_comm]

theorem incidence_iff_zero_sum {E : Type*} [Fintype E] (src dst : E → V)
    (root : V) (connected : ∀ v, Relation.ReflTransGen
      (fun u w => ∃ e, (src e = u ∧ dst e = w) ∨ (src e = w ∧ dst e = u)) root v) (f : V → A) :
    (∃ weights : E → A, boundary src dst weights = f) ↔ ∑ v, f v = 0 := by
  classical
  let B := boundary (A := A) src dst
  constructor
  · rintro ⟨w, rfl⟩
    simp only [boundary, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.sub_apply]
    rw [Finset.sum_comm]
    simp [Finset.sum_sub_distrib, point]
  · intro htotal
    have edge (e : E) (a : A) : point (dst e) a - point (src e) a ∈ B.range := by
      refine ⟨fun q => if q = e then a else 0, ?_⟩
      change (∑ q, (point (dst q) (if q = e then a else 0) -
        point (src q) (if q = e then a else 0))) = _
      rw [Finset.sum_eq_single e]
      · simp
      · intro j _ hje
        ext v
        simp [hje, point]
      · simp
    have transfer (v : V) (a : A) : point v a - point root a ∈ B.range := by
      induction connected v with
      | refl => simp
      | @tail u w hu huw ih =>
        obtain ⟨e, h | h⟩ := huw
        · obtain ⟨hs, hd⟩ := h
          have he := edge e a
          rw [hs, hd] at he
          simpa using B.range.add_mem he ih
        · obtain ⟨hs, hd⟩ := h
          have he := B.range.neg_mem (edge e a)
          rw [hs, hd, neg_sub] at he
          simpa using B.range.add_mem he ih
    have hmem : (∑ v, (point v (f v) - point root (f v))) ∈ B.range :=
      B.range.sum_mem fun v _ => transfer v (f v)
    have heq : (∑ v, (point v (f v) - point root (f v))) = f := by
      ext u
      simp only [Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, point]
      by_cases h : root = u <;> simp [h, htotal]
    rw [heq] at hmem
    exact hmem

end RelationParity
