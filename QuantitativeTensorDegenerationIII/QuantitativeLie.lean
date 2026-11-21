import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Abel

namespace QuantitativeLie

def vertexWeight {ι R : Type*} [DecidableEq ι] [Zero R] [One R] (i : ι) (x : ι) : R :=
  if x = i then 1 else 0

def cornerWeight {ι R : Type*} [DecidableEq ι] [Ring R] (i j : ι) (x : ι) : R :=
  vertexWeight i x - vertexWeight j x

theorem edge_has_endpoints {ι R : Type*} [DecidableEq ι] [Ring R] [Nontrivial R]
    {i j p q : ι} (hij : i ≠ j)
    (h : cornerWeight (R := R) i j = cornerWeight p q) :
    (i = p ∧ j = q) ∨ (i = q ∧ j = p) := by
  have hi : i = p ∨ i = q := by
    by_contra hn
    have hp : i ≠ p := fun hp => hn (Or.inl hp)
    have hq : i ≠ q := fun hq => hn (Or.inr hq)
    have he := congrFun h i
    simp [cornerWeight, vertexWeight, hij, hp, hq] at he
  have hj : j = p ∨ j = q := by
    by_contra hn
    have hp : j ≠ p := fun hp => hn (Or.inl hp)
    have hq : j ≠ q := fun hq => hn (Or.inr hq)
    have he := congrFun h j
    simp [cornerWeight, vertexWeight, hij.symm, hp, hq] at he
  rcases hi with hp | hq
  · rcases hj with hp' | hq'
    · exact (hij (hp.trans hp'.symm)).elim
    · exact Or.inl ⟨hp, hq'⟩
  · rcases hj with hp' | hq'
    · exact Or.inr ⟨hq, hp'⟩
    · exact (hij (hq.trans hq'.symm)).elim

theorem root_weight_difference {ι R : Type*} [DecidableEq ι] [Ring R]
    (o i j x : ι) :
    cornerWeight (R := R) o j x - cornerWeight o i x = cornerWeight i j x := by
  unfold cornerWeight
  abel

private theorem unit_product {R α : Type*} [CommRing R] (s : Finset α) (f : α → R)
    (hf : ∀ x ∈ s, IsUnit (f x)) : IsUnit (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

theorem tagged_vandermonde_unit {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → R) (h : ∀ i j : Fin n, i < j → IsUnit (v j - v i)) :
    IsUnit (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact unit_product Finset.univ _ (fun i _ =>
    unit_product (Finset.Ioi i) _ (fun j hj => h i j (Finset.mem_Ioi.mp hj)))

end QuantitativeLie
