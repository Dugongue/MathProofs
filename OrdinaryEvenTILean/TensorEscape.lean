import Anticommutator
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Mathproof.Problem17TensorEscape
open scoped TensorProduct
open Module LinearMap

variable {K V W A : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable [AddCommGroup A] [Module K A] [FiniteDimensional K A]

def tensorSum (L : End K V) (M : End K W) : End K (V ⊗[K] W) :=
  TensorProduct.map L LinearMap.id + TensorProduct.map LinearMap.id M

omit [FiniteDimensional K A] in
theorem tensorSum_rank_ge (L : End K V) (M : End K W) (i : A →ₗ[K] V) (p : V →ₗ[K] A)
    (kill : p.comp i = 0) (recover : p.comp (L.comp i) = LinearMap.id) :
    finrank K A * finrank K W ≤ finrank K (tensorSum L M).range := by
  let source : (A ⊗[K] W) →ₗ[K] (V ⊗[K] W) := TensorProduct.map i LinearMap.id
  let target : (V ⊗[K] W) →ₗ[K] (A ⊗[K] W) := TensorProduct.map p LinearMap.id
  have he : target.comp ((tensorSum L M).comp source) = LinearMap.id := by
    apply TensorProduct.ext'
    intro a w
    have hk := LinearMap.congr_fun kill a
    have hr := LinearMap.congr_fun recover a
    change p (i a) = 0 at hk
    change p (L (i a)) = a at hr
    simp [target, source, tensorSum, TensorProduct.map_tmul, hr, hk]
  let e := (tensorSum L M).rangeRestrict.comp source
  have hinj : Function.Injective e := by
    intro x y h
    have h' := congrArg (fun z : (tensorSum L M).range => target z.val) h
    exact (LinearMap.congr_fun he x).symm.trans (h'.trans (LinearMap.congr_fun he y))
  have : Module.Finite K (V ⊗[K] W) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis K V).tensorProduct (Module.Free.chooseBasis K W))
  simpa only [Module.finrank_tensorProduct] using LinearMap.finrank_le_finrank_of_injective hinj

theorem restrict_escape (L : End K V) (i : A →ₗ[K] V) (p : V →ₗ[K] A)
    (kill : p.comp i = 0) (recover : p.comp (L.comp i) = LinearMap.id)
    (S : Submodule K V) (π : V →ₗ[K] S) (hπ : π.comp S.subtype = LinearMap.id) :
    ∃ D : Submodule K A, finrank K A ≤ finrank K D + 2 * finrank K (V ⧸ S) ∧
      ∃ (i' : D →ₗ[K] S) (p' : S →ₗ[K] D),
        p'.comp i' = 0 ∧ p'.comp ((π.comp (L.comp S.subtype)).comp i') = LinearMap.id := by
  let f := (S.mkQ.comp i).prod (S.mkQ.comp (L.comp i))
  let D := f.ker
  have h : finrank K f.range + finrank K D = finrank K A := f.finrank_range_add_finrank_ker
  have hr : finrank K f.range ≤ 2 * finrank K (V ⧸ S) := by
    simpa [Module.finrank_prod, two_mul] using
      (Submodule.finrank_le f.range)
  have hD (x : D) : i x.val ∈ S ∧ L (i x.val) ∈ S := by
    have hx : f x.val = 0 := x.property
    exact ⟨(Submodule.Quotient.mk_eq_zero S).mp (congrArg Prod.fst hx),
      (Submodule.Quotient.mk_eq_zero S).mp (congrArg Prod.snd hx)⟩
  obtain ⟨q, hq⟩ := D.subtype.exists_leftInverse_of_injective D.ker_subtype
  let i' : D →ₗ[K] S := (i.comp D.subtype).codRestrict S fun x => (hD x).1
  let p' : S →ₗ[K] D := q.comp (p.comp S.subtype)
  refine ⟨D, by omega, i', p', ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change q (p (i x.val)) = 0
    have hk := LinearMap.congr_fun kill x.val
    change p (i x.val) = 0 at hk
    rw [hk, map_zero]
  · apply LinearMap.ext
    intro x
    have hπx : π (L (i x.val)) = ⟨L (i x.val), (hD x).2⟩ :=
      LinearMap.congr_fun hπ ⟨L (i x.val), (hD x).2⟩
    have hrx := LinearMap.congr_fun recover x.val
    change p (L (i x.val)) = x.val at hrx
    change q (p (π (L (i x.val))).val) = x
    rw [hπx]
    change q (p (L (i x.val))) = x
    rw [hrx]
    exact LinearMap.congr_fun hq x

theorem compressed_tensorSum_rank_ge (L : End K V) (M : End K W)
    (i : A →ₗ[K] V) (p : V →ₗ[K] A)
    (kill : p.comp i = 0) (recover : p.comp (L.comp i) = LinearMap.id)
    (S : Submodule K V) (π : V →ₗ[K] S) (hπ : π.comp S.subtype = LinearMap.id) :
    (finrank K A - 2 * finrank K (V ⧸ S)) * finrank K W ≤
      finrank K (tensorSum (π.comp (L.comp S.subtype)) M).range := by
  obtain ⟨D, hD, i', p', hk, hr⟩ := restrict_escape L i p kill recover S π hπ
  exact (Nat.mul_le_mul_right _ (show _ ≤ finrank K D by omega)).trans
    (tensorSum_rank_ge _ M i' p' hk hr)

open Mathproof.Problem17Anticommutator in
theorem compressed_anticommutator_tensor_rank_ge
    (P : End K V) (hP : ∀ c : K, P ≠ c • LinearMap.id)
    (M : End K W) (S : Submodule K (End K V)) (π : End K V →ₗ[K] S)
    (hπ : π.comp S.subtype = LinearMap.id) :
    (finrank K V - 2 * finrank K (End K V ⧸ S)) * finrank K W ≤
      finrank K (tensorSum (π.comp ((shifted P 0).comp S.subtype)) M).range := by
  obtain ⟨v, hv⟩ := exists_outside_line P hP
  obtain ⟨i, p, hk, hr⟩ := shifted_escape P 0 v hv
  simpa only [Subspace.dual_finrank_eq] using
    compressed_tensorSum_rank_ge (shifted P 0) M i p hk hr S π hπ

end Mathproof.Problem17TensorEscape

#print axioms Mathproof.Problem17TensorEscape.compressed_tensorSum_rank_ge
#print axioms Mathproof.Problem17TensorEscape.compressed_anticommutator_tensor_rank_ge

