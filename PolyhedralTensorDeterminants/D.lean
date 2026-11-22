import Mathlib

namespace PolyhedraFour.Surface

open scoped BigOperators

private theorem sum_two_flags {F A M : Type*} [Fintype F] [Fintype A]
    [AddCommGroup M] (e : F ≃ A × Bool) (q : A → M) :
    (∑ x, q (e x).1) = (2 : ℕ) • (∑ a, q a) := by
  calc
    (∑ x, q (e x).1) = ∑ y : A × Bool, q y.1 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = (2 : ℕ) • (∑ a, q a) := by
      rw [Fintype.sum_prod_type, Finset.smul_sum]
      simp

/-- Every comparable pair of the three rank types occurs in exactly two flags. -/
theorem flag_boundary_twice {F A B C M : Type*} [Fintype F] [Fintype A]
    [Fintype B] [Fintype C] [AddCommGroup M]
    (incA : F ≃ A × Bool) (incB : F ≃ B × Bool) (incC : F ≃ C × Bool)
    (a : A → M) (b : B → M) (c : C → M) :
    (∑ x : F, (a (incA x).1 + b (incB x).1 - c (incC x).1)) =
      (2 : ℕ) • ((∑ i : A, a i) + (∑ i : B, b i) - (∑ i : C, c i)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_two_flags incA, sum_two_flags incB, sum_two_flags incC, nsmul_sub, nsmul_add]

/-- The comparability sum is twice the vertex-face chain plus the half-boundary. -/
theorem comparison_chain_decomposition {M : Type*} [AddCommGroup M]
    (vertexEdge edgeFace vertexFace : M) :
    vertexEdge + edgeFace + vertexFace =
      (2 : ℕ) • vertexFace + (vertexEdge + edgeFace - vertexFace) := by
  abel

end PolyhedraFour.Surface
