import Anticommutator
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open Module LinearMap Submodule
open Mathproof.Problem17Anticommutator (exists_outside_line)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- If no new pair escapes in a quotient of dimension at least two, the
operator preserves the subspace and induces a scalar on the quotient. -/
theorem scalar_shift_range_le_of_no_escape (P : End K V) (S : Submodule K V)
    (hq : 1 < finrank K (V ⧸ S))
    (h : ∀ x, S.mkQ x ≠ 0 → S.mkQ (P x) ∈ K ∙ S.mkQ x) :
    ∃ a : K, (P - a • LinearMap.id).range ≤ S := by
  have hmem (x : V) : S.mkQ x = 0 ↔ x ∈ S := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hstable : S ≤ S.comap P := by
    intro w hw
    change P w ∈ S
    apply (hmem _).mp
    by_contra hz
    let z := S.mkQ (P w)
    have hline : (K ∙ z) ≠ ⊤ := by
      intro ht
      have hd := finrank_span_singleton (K := K) hz
      rw [ht, finrank_top] at hd
      omega
    have hex : ∃ u : V ⧸ S, u ∉ K ∙ z := by
      by_contra! hu
      apply hline
      exact eq_top_iff.mpr (fun u _ => hu u)
    obtain ⟨u, hu⟩ := hex
    have hu0 : u ≠ 0 := by
      intro he
      apply hu
      rw [he]
      exact (K ∙ z).zero_mem
    obtain ⟨x, hx⟩ := S.mkQ_surjective u
    have hxw : S.mkQ (x + w) = u := by
      rw [map_add, hx, (hmem _).mpr hw, add_zero]
    have h1 := h x (hx.symm ▸ hu0)
    have h2 := h (x+w) (hxw.symm ▸ hu0)
    rw [hx] at h1
    rw [hxw, map_add, map_add] at h2
    have h3 : z ∈ K ∙ u := by
      simpa only [add_sub_cancel_left] using (K ∙ u).sub_mem h2 h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h3
    have ha0 : a ≠ 0 := by
      intro ha0
      exact hz (by simpa [ha0, z] using ha.symm)
    apply hu
    apply Submodule.mem_span_singleton.mpr
    exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  let Q : End K (V ⧸ S) := S.mapQ S P hstable
  have hQ (y : V ⧸ S) : Q y ∈ K ∙ y := by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    change S.mkQ (P x) ∈ K ∙ S.mkQ x
    by_cases h0 : S.mkQ x = 0
    · rw [(hmem _).mpr (hstable ((hmem _).mp h0))]
      exact (K ∙ S.mkQ x).zero_mem
    · exact h x h0
  obtain ⟨a, ha⟩ : ∃ a : K, Q = a • LinearMap.id := by
    by_contra! hn
    obtain ⟨y, hy⟩ := exists_outside_line Q hn
    exact hy (hQ y)
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply (hmem _).mp
  have hax : S.mkQ (P x) = a • S.mkQ x := LinearMap.congr_fun ha (S.mkQ x)
  change S.mkQ (P x - a • x) = 0
  rw [map_sub, map_smul, hax, sub_self]

#print axioms scalar_shift_range_le_of_no_escape

end Mathproof.EvenTI.Reciprocal.SquareLow
