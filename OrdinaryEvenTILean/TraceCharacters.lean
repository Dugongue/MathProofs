import Mathproof.Meta.Problem18FourierCore20260930
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace Mathproof.Problem17TraceCharacters
open Module LinearMap
open Mathproof.Problem18FourierCore20260930

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]

theorem every_character_is_linear [Fintype V] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (χ : AddChar V ℂ) : ∃ l : Module.Dual K V, ∀ v, χ v = ψ (l v) := by
  classical
  have : Finite (Module.Dual K V) :=
    Finite.of_injective (fun f : Module.Dual K V => (f : V → K)) DFunLike.coe_injective
  have : Fintype (Module.Dual K V) := Fintype.ofFinite _
  let g (l : Module.Dual K V) : AddChar V ℂ := ψ.compAddMonoidHom l.toAddMonoidHom
  have hi : Function.Injective g := by
    intro l m h
    apply sub_eq_zero.mp
    apply (character_detects_linear_map ψ hψ (l - m)).mp
    intro v
    have h' : ψ (l v) = ψ (m v) := congrArg (fun f : AddChar V ℂ => f v) h
    change ψ (l v - m v) = 1
    rw [AddChar.map_sub_eq_div, h', div_self (ψ.val_isUnit (m v)).ne_zero]
  have hc : Fintype.card (Module.Dual K V) = Fintype.card (AddChar V ℂ) := by
    rw [AddChar.card_eq, Module.card_eq_pow_finrank (K := K) (V := Module.Dual K V),
      Subspace.dual_finrank_eq, ← Module.card_eq_pow_finrank (K := K) (V := V)]
  obtain ⟨l, hl⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hi, hc⟩).surjective χ
  exact ⟨l, fun v => congrArg (fun f : AddChar V ℂ => f v) hl.symm⟩

variable {W : Type*} [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [FiniteDimensional K W]

theorem character_on_pair_subspace (S : Submodule K (V × W)) [Fintype S]
    (B : LinearMap.BilinForm K V) (D : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (hD : D.Nondegenerate)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (χ : AddChar S ℂ) :
    ∃ p : V, ∃ q : W, ∀ x : S, χ x = ψ (B p x.val.1 + D q x.val.2) := by
  obtain ⟨l, hl⟩ := every_character_is_linear ψ hψ χ
  obtain ⟨f, hf⟩ := LinearMap.exists_extend l
  obtain ⟨p, hp⟩ := (B.toDual hB).surjective (f.comp (LinearMap.inl K V W))
  obtain ⟨q, hq⟩ := (D.toDual hD).surjective (f.comp (LinearMap.inr K V W))
  refine ⟨p, q, fun x => ?_⟩
  have he₁ := LinearMap.congr_fun hp x.val.1
  have he₂ := LinearMap.congr_fun hq x.val.2
  change B p x.val.1 = f (x.val.1, 0) at he₁
  change D q x.val.2 = f (0, x.val.2) at he₂
  have he₃ : f x.val = l x := LinearMap.congr_fun hf x
  rw [hl, he₁, he₂, ← map_add, ← he₃]
  have ht : (x.val.1, (0 : W)) + ((0 : V), x.val.2) = x.val := by
    apply Prod.ext <;> simp
  rw [ht]

end Mathproof.Problem17TraceCharacters

#print axioms Mathproof.Problem17TraceCharacters.character_on_pair_subspace
