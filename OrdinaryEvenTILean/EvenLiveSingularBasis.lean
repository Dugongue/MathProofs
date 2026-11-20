import EvenSingularPrefix

/-! Extension of prescribed retained input coordinates to a full basis. -/
namespace Mathproof.EvenOrdinaryTISingular
open Module

noncomputable section

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem suffix_comp {b : ℕ} (t : ℕ) (f : V → W) (x : Fin (b+t) → V) :
    suffix t (f ∘ x) = f ∘ suffix t x := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih (Fin.tail x)

theorem suffix_extension_exists [Module.Finite K V] {b : ℕ}
    (y : Independent K V b) (t : ℕ) (ht : b+t ≤ finrank K V) :
    ∃ x : Independent K V (b+t), suffix t x.val = y.val := by
  induction t with
  | zero => exact ⟨y, rfl⟩
  | succ t ih =>
    obtain ⟨x, hx⟩ := ih (by omega)
    let U := Submodule.span K (Set.range x.val)
    have hd : finrank K U = b+t := by
      simpa only [U, Fintype.card_fin] using finrank_span_eq_card x.property
    have hp : U ≠ ⊤ := by
      intro h
      rw [h, finrank_top] at hd
      omega
    obtain ⟨u, hu⟩ : ∃ u : V, u ∉ U := by
      by_contra! h
      exact hp (Submodule.eq_top_iff'.mpr h)
    refine ⟨⟨Fin.cons (α:=fun _ => V) u x.val, linearIndependent_finCons.mpr ⟨x.property, hu⟩⟩, ?_⟩
    change suffix t (Fin.tail (Fin.cons (α:=fun _ => V) u x.val)) = y.val
    rw [Fin.tail_cons]
    exact hx

/-- Every independent retained family occurs as the suffix of a full basis. -/
theorem suffix_basis_exists [Module.Finite K V] {b t : ℕ}
    (y : Independent K V b) (ht : b+t = finrank K V) :
    ∃ x : Basis (Fin (b+t)) K V, suffix t x = y.val := by
  obtain ⟨x, hx⟩ := suffix_extension_exists y t ht.le
  let e := basisOfLinearIndependentOfCardEqFinrank' x.val x.property
    (by rw [Fintype.card_fin, ht])
  exact ⟨e, by simpa [e] using hx⟩

/-- An isomorphism between spaces of the same dimension is specified uniquely
by a full independent family of image columns on a fixed source basis. -/
def linearEquivColumns [Module.Finite K W] {k : ℕ}
    (B : Basis (Fin k) K V) (hk : k = finrank K W) :
    (V ≃ₗ[K] W) ≃ Independent K W k where
  toFun f := ⟨f ∘ B, B.linearIndependent.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr f.injective)⟩
  invFun x := B.equiv (basisOfLinearIndependentOfCardEqFinrank' x.val x.property
    (by rw [Fintype.card_fin, hk])) (Equiv.refl _)
  left_inv f := by
    apply LinearEquiv.toLinearMap_injective
    apply B.ext
    intro i
    simp only [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
      coe_basisOfLinearIndependentOfCardEqFinrank', Function.comp_apply]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp only [Function.comp_apply, Basis.equiv_apply, Equiv.refl_apply,
      coe_basisOfLinearIndependentOfCardEqFinrank']

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.suffix_basis_exists
#print axioms Mathproof.EvenOrdinaryTISingular.linearEquivColumns
