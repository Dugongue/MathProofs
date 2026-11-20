import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Mathproof.Problem17Anticommutator
open Module LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def shifted (P : End K V) (t : K) : End K V →ₗ[K] End K V where
  toFun X := P.comp X + X.comp P - t • X
  map_add' X Y := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, smul_apply, map_add, smul_add]
    abel
  map_smul' c X := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, smul_apply, map_smul, RingHom.id_apply,
      smul_sub, smul_add, smul_smul]
    rw [mul_comm t c]

theorem shifted_escape (P : End K V) (t : K) (v : V) (hv : P v ∉ K ∙ v) :
    ∃ (i : Module.Dual K V →ₗ[K] End K V) (p : End K V →ₗ[K] Module.Dual K V),
      p.comp i = 0 ∧ p.comp ((shifted P t).comp i) = LinearMap.id := by
  let W := K ∙ v
  obtain ⟨f, hf, hfv⟩ := LinearMap.exists_extend_of_notMem (0 : W →ₗ[K] K) hv 1
  have hf0 : f v = 0 :=
    LinearMap.congr_fun hf ⟨v, Submodule.mem_span_singleton_self v⟩
  let make : Module.Dual K V →ₗ[K] End K V :=
    (LinearMap.smulRightₗ : (V →ₗ[K] K) →ₗ[K] V →ₗ[K] End K V).flip v
  refine ⟨make, f.compRight K, ?_, ?_⟩
  · ext g x
    change f (g x • v) = 0
    simp [hf0]
  · ext g x
    change f (P (g x • v) + g (P x) • v - t • (g x • v)) = g x
    simp [map_smul, hf0, hfv]

theorem shifted_rank_ge [FiniteDimensional K V]
    (P : End K V) (t : K) (v : V) (hv : P v ∉ K ∙ v) :
    finrank K V ≤ finrank K (shifted P t).range := by
  obtain ⟨i, p, -, hp⟩ := shifted_escape P t v hv
  let into := (shifted P t).rangeRestrict.comp i
  have hi : Function.Injective into := by
    intro g g' h
    have he := congrArg (fun z : (shifted P t).range => p z.val) h
    exact (LinearMap.congr_fun hp g).symm.trans (he.trans (LinearMap.congr_fun hp g'))
  rw [← Subspace.dual_finrank_eq (K := K) (V := V)]
  exact LinearMap.finrank_le_finrank_of_injective hi

theorem exists_outside_line (P : End K V) (hP : ∀ c : K, P ≠ c • LinearMap.id) :
    ∃ v : V, P v ∉ K ∙ v := by
  classical
  by_contra! h
  have hex : ∃ v : V, v ≠ 0 := by
    by_contra! hz
    apply hP 0
    ext v
    simp [hz v]
  obtain ⟨v, hv⟩ := hex
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h v)
  apply hP a
  ext w
  change P w = a • w
  by_cases hw : w ∈ K ∙ v
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, ← ha, smul_comm c a]
  · obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (h w)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (h (v + w))
    obtain ⟨f, hf, hfw⟩ := LinearMap.exists_extend_of_notMem
      (0 : (K ∙ v) →ₗ[K] K) hw 1
    have hf0 : f v = 0 := by
      exact LinearMap.congr_fun hf ⟨v, Submodule.mem_span_singleton_self v⟩
    rw [map_add, ← ha, ← hb, smul_add] at hd
    have hd' : d = b := by
      simpa [map_add, map_smul, hf0, hfw] using congrArg f hd
    have hba : b = a := smul_left_injective K hv (add_right_cancel (hd' ▸ hd))
    rw [← hb, hba]

theorem shifted_rank_ge_of_nonscalar [FiniteDimensional K V]
    (P : End K V) (t : K) (hP : ∀ c : K, P ≠ c • LinearMap.id) :
    finrank K V ≤ finrank K (shifted P t).range := by
  obtain ⟨v, hv⟩ := exists_outside_line P hP
  exact shifted_rank_ge P t v hv

end Mathproof.Problem17Anticommutator

#print axioms Mathproof.Problem17Anticommutator.shifted_rank_ge
#print axioms Mathproof.Problem17Anticommutator.shifted_rank_ge_of_nonscalar

