import Mathproof.Meta.P15RecogLinAlg20261007

/-! P15 (LEAD): the full kernel basis of a reduced row echelon basis.
For a pivoted basis `bs` of a subspace `U ⊆ K^ι`, the vectors `kerVec bs f` over the free
(non-pivot) columns `f` span `U^⊥ = {x | ∀ u ∈ U, Σ u_i x_i = 0}`. -/

namespace Mathproof.P15LinAlgKer20261007

open Mathproof.P15RecogOps20261007 Mathproof.P15RecogLinAlg20261007

variable {α : Type} (A : Ops α) {ι : Type} [DecidableEq ι]

/-- Free (non-pivot) columns. -/
def freeCols (idx : List ι) (bs : List (ι × (ι → α))) : List ι :=
  idx.filter (fun i => !(bs.any (fun pb => decide (pb.1 = i))))

/-- Kernel basis: one vector per free column. -/
def kerBasis (idx : List ι) (bs : List (ι × (ι → α))) : List (ι → α) :=
  (freeCols idx bs).map (kerVec A bs)

variable {K : Type} [Field K] [DecidableEq K]

local notation "O" => Ops.ofField K

/-- The orthogonal complement for the standard dot product. -/
def perp [Fintype ι] (U : Submodule K (ι → K)) : Submodule K (ι → K) where
  carrier := {x | ∀ u ∈ U, ∑ i, u i * x i = 0}
  add_mem' := by
    intro x y hx hy u hu
    simp [mul_add, Finset.sum_add_distrib, hx u hu, hy u hu]
  zero_mem' := by intro u _; simp
  smul_mem' := by
    intro c x hx u hu
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ i, u i * (c * x i)) = c * ∑ i, u i * x i by
      rw [Finset.mul_sum]; congr 1; funext i; ring, hx u hu, mul_zero]

theorem kerVec_free_other {bs : List (ι × (ι → K))} {f g : ι}
    (hf : ∀ pb ∈ bs, pb.1 ≠ f) (hfg : f ≠ g) : kerVec O bs g f = 0 := by
  have hnone : bs.find? (fun x => decide (x.1 = f)) = none := by
    apply List.find?_eq_none.2
    intro x hx; simp only [decide_eq_true_eq]; exact hf x hx
  simp [kerVec, hfg, hnone]

theorem mem_freeCols {idx : List ι} {bs : List (ι × (ι → K))} {f : ι} :
    f ∈ freeCols idx bs ↔ f ∈ idx ∧ ∀ pb ∈ bs, pb.1 ≠ f := by
  simp [freeCols, List.mem_filter]

theorem kerBasis_le [Fintype ι] {idx : List ι} {bs : List (ι × (ι → K))} (hP : Pivoted bs) :
    spanL (kerBasis O idx bs) ≤ perp (spanB bs) := by
  unfold spanL
  rw [Submodule.span_le]
  intro v hv u hu
  simp only [Set.mem_setOf_eq, kerBasis, List.mem_map] at hv
  obtain ⟨f, hf, rfl⟩ := hv
  exact kerVec_orth hP ((mem_freeCols.1 hf).2) hu

theorem kerBasis_spec [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx)
    {bs : List (ι × (ι → K))} (hP : Pivoted bs) :
    spanL (kerBasis O idx bs) = perp (spanB bs) := by
  classical
  apply le_antisymm (kerBasis_le hP)
  intro x hx
  set FC := (freeCols idx bs).toFinset with hFC
  set s : ι → K := ∑ f ∈ FC, x f • kerVec O bs f with hs
  have hs_mem : s ∈ spanL (kerBasis O idx bs) := by
    rw [hs]
    apply Submodule.sum_mem
    intro f hf
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Set.mem_setOf_eq, kerBasis, List.mem_map]
    exact ⟨f, List.mem_toFinset.1 hf, rfl⟩
  have hy_perp : x - s ∈ perp (spanB bs) := Submodule.sub_mem _ hx (kerBasis_le hP hs_mem)
  -- `x - s` vanishes on free columns
  have hfree0 : ∀ f ∈ FC, (x - s) f = 0 := by
    intro f hf
    have hfree := (mem_freeCols.1 (List.mem_toFinset.1 hf)).2
    have : s f = x f := by
      rw [hs, Finset.sum_apply, Finset.sum_eq_single f]
      · simp [kerVec_self]
      · intro g _ hgf
        simp [kerVec_free_other hfree (Ne.symm hgf)]
      · intro h; exact absurd hf h
    simp [this]
  -- `x - s` vanishes on pivot columns
  have hpiv0 : ∀ pb ∈ bs, (x - s) pb.1 = 0 := by
    intro pb hpb
    have h0 := hy_perp pb.2 (mem_spanB hpb)
    rw [Finset.sum_eq_single pb.1] at h0
    · rwa [hP.2.1 pb hpb, one_mul] at h0
    · intro i _ hi
      by_cases hif : i ∈ FC
      · simp [hfree0 i hif]
      · have : ∃ pb' ∈ bs, pb'.1 = i := by
          by_contra hno
          push_neg at hno
          exact hif (List.mem_toFinset.2 (mem_freeCols.2 ⟨hidx i, hno⟩))
        obtain ⟨pb', hpb', rfl⟩ := this
        rw [hP.2.2 pb' hpb' pb hpb hi, zero_mul]
    · simp
  have hy0 : x - s = 0 := by
    funext i
    by_cases hif : i ∈ FC
    · exact hfree0 i hif
    · have : ∃ pb' ∈ bs, pb'.1 = i := by
        by_contra hno
        push_neg at hno
        exact hif (List.mem_toFinset.2 (mem_freeCols.2 ⟨hidx i, hno⟩))
      obtain ⟨pb', hpb', rfl⟩ := this
      exact hpiv0 pb' hpb'
  have : x = s := sub_eq_zero.1 hy0
  rw [this]; exact hs_mem


/-- Double orthogonal: a vector orthogonal to the kernel basis lies in the row span. -/
theorem mem_spanB_of_perp_kerBasis [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx)
    {bs : List (ι × (ι → K))} (hP : Pivoted bs) {z : ι → K}
    (hz : ∀ v ∈ kerBasis O idx bs, ∑ i, z i * v i = 0) : z ∈ spanB bs := by
  classical
  set s : ι → K := ∑ t : Fin bs.length, z (bs.get t).1 • (bs.get t).2 with hs
  have hs_mem : s ∈ spanB bs := by
    rw [hs]
    exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (mem_spanB (List.get_mem _ _)))
  have hs_piv : ∀ u : Fin bs.length, s (bs.get u).1 = z (bs.get u).1 := by
    intro u
    rw [hs, Finset.sum_apply, Finset.sum_eq_single u]
    · have h1 := hP.2.1 _ (List.get_mem bs u)
      simp only [List.get_eq_getElem] at h1 ⊢
      simp [h1]
    · intro t _ htu
      have hne : (bs.get u).1 ≠ (bs.get t).1 := by
        intro h
        apply htu
        have := hP.1
        rw [List.nodup_iff_injective_get] at this
        have h' : (bs.map Prod.fst).get ⟨t, by simp⟩ = (bs.map Prod.fst).get ⟨u, by simp⟩ := by
          simpa using h.symm
        exact Fin.ext (by simpa using congrArg Fin.val (this h'))
      have h0 := hP.2.2 _ (List.get_mem bs u) _ (List.get_mem bs t) hne
      simp only [List.get_eq_getElem] at h0 ⊢
      simp [h0]
    · simp
  set w := z - s with hw
  have hw_piv : ∀ pb ∈ bs, w pb.1 = 0 := by
    intro pb hpb
    obtain ⟨u, rfl⟩ := List.get_of_mem hpb
    have h1 := hs_piv u
    simp only [hw, Pi.sub_apply, h1, sub_self]
  have hw_free : ∀ f, (∀ pb ∈ bs, pb.1 ≠ f) → w f = 0 := by
    intro f hf
    have hfc : f ∈ freeCols idx bs := mem_freeCols.2 ⟨hidx f, hf⟩
    have h1 := hz (kerVec O bs f) (by simp [kerBasis]; exact ⟨f, hfc, rfl⟩)
    have h2 := kerVec_orth hP hf hs_mem
    have h3 : ∑ i, w i * kerVec O bs f i = 0 := by
      simp only [hw, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, h1, h2, sub_self]
    rw [Finset.sum_eq_single f] at h3
    · simpa [kerVec_self] using h3
    · intro i _ hif
      by_cases hip : ∃ pb ∈ bs, pb.1 = i
      · obtain ⟨pb, hpb, rfl⟩ := hip
        simp [hw_piv pb hpb]
      · push_neg at hip
        simp [kerVec_free_other hip hif]
    · simp
  have hw0 : w = 0 := by
    funext i
    by_cases hip : ∃ pb ∈ bs, pb.1 = i
    · obtain ⟨pb, hpb, rfl⟩ := hip; exact hw_piv pb hpb
    · push_neg at hip; exact hw_free i hip
  have : z = s := sub_eq_zero.1 hw0
  rw [this]; exact hs_mem

end Mathproof.P15LinAlgKer20261007
