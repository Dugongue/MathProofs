import Mathlib

namespace TruncatedTensor

open scoped BigOperators

/-- Scaling one truncated coordinate on the full monomial basis. -/
theorem det_coordinate_scale {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (c : K) :
    (Matrix.diagonal fun i : Fin d × ι => c ^ (i.1 : ℕ)).det =
      c ^ (Fintype.card ι * (d * (d - 1) / 2)) := by
  have sum_exponents : (∑ i : Fin d × ι, (i.1 : ℕ)) =
      Fintype.card ι * (d * (d - 1) / 2) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]
    first | rfl | simp
  rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, sum_exponents]

/-- Simultaneously exchanging the two equal digit positions in every fiber. -/
theorem sign_coordinate_exchange {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) :
    Equiv.Perm.sign
      (Equiv.prodCongr (Equiv.prodComm (Fin d) (Fin d)) (Equiv.refl ι)) =
      (-1 : ℤˣ) ^ ((d * d * Fintype.card ι - d * Fintype.card ι) / 2) := by
  let σ : Equiv.Perm ((Fin d × Fin d) × ι) :=
    Equiv.prodCongr (Equiv.prodComm (Fin d) (Fin d)) (Equiv.refl ι)
  change Equiv.Perm.sign σ = _
  have hσ : σ ^ 2 = 1 := by
    rw [pow_two]
    ext x <;> rfl
  let fixed : Function.fixedPoints σ ≃ Fin d × ι :=
    { toFun := fun x => (x.1.1.1, x.1.2)
      invFun := fun x => ⟨((x.1, x.1), x.2), rfl⟩
      left_inv := by
        rintro ⟨⟨⟨a, b⟩, v⟩, h⟩
        have he : b = a := congrArg (fun y : (Fin d × Fin d) × ι => y.1.1) h
        subst b
        rfl
      right_inv := fun _ => rfl }
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ, Fintype.card_congr fixed]
  simp only [Fintype.card_prod, Fintype.card_fin]

end TruncatedTensor
