import EvenLiveSingularBlock
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Mathproof.EvenTI.Reciprocal.Part1

open Module
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open scoped BigOperators

variable {K V L : Type*} [Field K] [Fintype K]
variable [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype V] [Fintype L]

private theorem exists_spanning_subset (U : L → V) (r : Nat)
    (hr : r ≤ Fintype.card L)
    (hU : finrank K (Submodule.span K (Set.range U)) ≤ r) :
    ∃ s : Finset L, s.card = r ∧ Set.range U ⊆ Submodule.span K (U '' (s : Set L)) := by
  classical
  have he : LinearIndepOn K U (∅ : Set L) := linearIndepOn_empty K U
  have hu : (∅ : Set L) ⊆ Set.univ := Set.empty_subset _
  let t := (he.extend hu).toFinset
  have ht : (t : Set L) = he.extend hu := Set.coe_toFinset _
  have hs : Submodule.span K (U '' (t : Set L)) = Submodule.span K (Set.range U) := by
    rw [ht, he.span_image_extend_eq_span_image, Set.image_univ]
  have hi : LinearIndependent K (fun i : t => U i) := by
    change LinearIndepOn K U (t : Set L)
    rw [ht]
    exact he.linearIndepOn_extend hu
  have hh := finrank_span_eq_card hi
  have hR :
      Set.range (fun i : t => U i) = U '' (t : Set L) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hh' : finrank K (Submodule.span K (U '' (t : Set L))) = t.card := by
    rw [← hR, ← Fintype.card_coe]
    exact hh
  have htR : t.card ≤ r := by rwa [← hh', hs]
  obtain ⟨s, hts, -, hscard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ t) htR (by simpa using hr)
  refine ⟨s, hscard, ?_⟩
  calc
    Set.range U ⊆ (Submodule.span K (Set.range U) : Set V) := Submodule.subset_span
    _ = (Submodule.span K (U '' (t : Set L)) : Set V) := congrArg SetLike.coe hs.symm
    _ ⊆ _ := Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hts))

private abbrev SpanCode (s : Finset L) :=
  Σ u : s → V, ({i : L // i ∉ s} → Submodule.span K (Set.range u))

private theorem spanCode_count (s : Finset L) :
    Nat.card (SpanCode (K := K) (V := V) s) ≤
      Fintype.card K ^ (finrank K V * s.card + s.card * (Fintype.card L - s.card)) := by
  classical
  have hc : Fintype.card {i : L // i ∉ s} = Fintype.card L - s.card := by
    simpa using Fintype.card_compl_set (s : Set L)
  have hs (u : s → V) : finrank K (Submodule.span K (Set.range u)) ≤ s.card := by
    simpa [Set.finrank] using finrank_range_le_card (R := K) u
  rw [Nat.card_sigma, pow_add]
  calc
    _ ≤ ∑ _ : s → V, Fintype.card K ^ (s.card * (Fintype.card L - s.card)) := by
      apply Finset.sum_le_sum
      intro u _
      rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := K),
        Nat.card_eq_fintype_card (α := K),
        Nat.card_eq_fintype_card (α := {i : L // i ∉ s}), hc, ← pow_mul]
      exact Nat.pow_le_pow_right Fintype.card_pos (Nat.mul_le_mul_right _ (hs u))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Fintype.card_fun, Module.card_eq_pow_finrank (K := K) (V := V),
        Fintype.card_coe, ← pow_mul]
      rfl

private theorem rank_count_le (r : Nat) (hr : r ≤ Fintype.card L) :
    Nat.card {U : L → V // finrank K (Submodule.span K (Set.range U)) ≤ r} ≤
      2 ^ Fintype.card L *
        Fintype.card K ^ (finrank K V * r + r * (Fintype.card L - r)) := by
  classical
  let A := {U : L → V // finrank K (Submodule.span K (Set.range U)) ≤ r}
  let S := {s : Finset L // s.card = r}
  let chosen (U : A) : S :=
    ⟨(exists_spanning_subset (K := K) U.val r hr U.property).choose,
      (exists_spanning_subset (K := K) U.val r hr U.property).choose_spec.1⟩
  let pack (U : A) : Σ s : S, SpanCode (K := K) (V := V) s.val := by
    refine ⟨chosen U, (fun i => U.val i), fun i => ⟨U.val i, ?_⟩⟩
    have h := (exists_spanning_subset (K := K) U.val r hr U.property).choose_spec.2
      (show U.val i ∈ Set.range U.val from ⟨i, rfl⟩)
    have he : U.val '' ((chosen U).val : Set L) = Set.range (fun j : (chosen U).val => U.val j) := by
      ext z
      constructor
      · rintro ⟨j, hj, hU⟩
        exact ⟨⟨j, hj⟩, hU⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, j.property, rfl⟩
    change U.val i ∈ Submodule.span K (U.val '' ((chosen U).val : Set L)) at h
    exact he ▸ h
  let unpack (x : Σ s : S, SpanCode (K := K) (V := V) s.val) (i : L) : V :=
    if hi : i ∈ x.1.val then x.2.1 ⟨i, hi⟩ else (x.2.2 ⟨i, hi⟩).val
  have hinj : Function.Injective pack := by
    intro U V h
    apply Subtype.ext
    funext i
    have hh := congrArg (fun x => unpack x i) h
    simpa [unpack, pack] using hh
  apply (Nat.card_le_card_of_injective pack hinj).trans
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _ : S, Fintype.card K ^ (finrank K V * r + r * (Fintype.card L - r)) :=
      Finset.sum_le_sum fun s _ => by simpa only [s.property] using spanCode_count (K := K) (V := V) s.val
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply Nat.mul_le_mul_right
      rw [← Fintype.card_finset]
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- A deficient family has a small subset spanning every row. Counting all such
subsets suffices for an exponential tail without an exact Gaussian binomial. -/
theorem uniformFraction_rank_le (r : Nat) (hr : r ≤ Fintype.card L)
    (hd : r ≤ finrank K V) :
    uniformFraction (L → V) (fun U => finrank K (Submodule.span K (Set.range U)) ≤ r) ≤
      (2 : ℝ)^Fintype.card L /
        (Fintype.card K : ℝ)^((Fintype.card L - r) * (finrank K V - r)) := by
  have h := rank_count_le (K := K) (V := V) r hr
  have hcard : Nat.card (L → V) = Fintype.card K ^ (finrank K V * Fintype.card L) := by
    rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := K),
      Nat.card_eq_fintype_card (α := K), Nat.card_eq_fintype_card (α := L), pow_mul]
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Fintype.card_pos (α := K))
  have he : finrank K V * Fintype.card L =
      (finrank K V * r + r * (Fintype.card L-r)) +
        (Fintype.card L-r) * (finrank K V-r) := by
    have ha := Nat.sub_add_cancel hr
    have hb := Nat.sub_add_cancel hd
    have hc : finrank K V * (Fintype.card L-r) =
        r * (Fintype.card L-r) + (Fintype.card L-r) * (finrank K V-r) := by
      nth_rw 1 [← hb]
      ring
    calc
      finrank K V * Fintype.card L = finrank K V * (Fintype.card L-r+r) :=
        congrArg (fun b => finrank K V * b) ha.symm
      _ = finrank K V * r + finrank K V * (Fintype.card L-r) := by ring
      _ = _ := by rw [hc, add_assoc]
  unfold uniformFraction
  rw [hcard, Nat.cast_pow, he, pow_add]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hq _) (pow_pos hq _)) (pow_pos hq _)).mpr
  have h' :
    (Nat.card {U : L → V // finrank K (Submodule.span K (Set.range U)) ≤ r} : ℝ) ≤
      (2 : ℝ)^Fintype.card L * q^(finrank K V * r + r * (Fintype.card L - r)) := by
    dsimp [q]
    exact_mod_cast h
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h' (pow_nonneg hq.le _)

#print axioms uniformFraction_rank_le

end Mathproof.EvenTI.Reciprocal.Part1
