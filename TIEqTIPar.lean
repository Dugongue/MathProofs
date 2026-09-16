import Mathlib

/-!
# Tensor isomorphism under maximal parabolic groups

Over every field, three-tensor isomorphism under the maximal parabolic
P_(n,n), the stabilizer of the first n coordinates in dimension 2n,
generates the same reduction class as ordinary three-tensor isomorphism.

The lower reduction embeds ordinary transporters as diag(P,I).
The upper reduction encodes flag constraints by marker slices and then
removes the tensor partitions. Both orbit equivalences and polynomial
output-size bounds are proved using the coordinate-projection system below.
Uniform machine running times and bit complexity are not formalized here.

This addresses the parabolic research direction explicitly proposed in
Chen, Grochow, Qiao, Tang, and Zhang, ITCS 2024, Section 1.5 of the full
version, arXiv:2306.03135. It is not a numbered open question.
Partition removal follows Futorny, Grochow, and Sergeichuk,
Linear Algebra and its Applications 566 (2019), 212-244.
-/

namespace ParabolicTI

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section

section

universe u v

variable {K : Type u} [Field K]

section

variable {M N : Type v} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def submoduleProductEquiv (p : Submodule K M) (q : Submodule K N) :
    (p.prod q) ≃ₗ[K] (p × q) where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := by ext <;> rfl
  right_inv _ := by ext <;> rfl

theorem finrank_prod_submodule [FiniteDimensional K M] [FiniteDimensional K N]
    (p : Submodule K M) (q : Submodule K N) :
    Module.finrank K (p.prod q) = Module.finrank K p + Module.finrank K q := by
  rw [(submoduleProductEquiv p q).finrank_eq, Module.finrank_prod]

end

section

variable {R₁ R₂ C₁ C₂ : Type v}
variable [Fintype R₁] [Fintype R₂] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₁] [DecidableEq R₂] [DecidableEq C₁] [DecidableEq C₂]

def sumPiEquiv (ι κ : Type v) : ((ι ⊕ κ) → K) ≃ₗ[K] ((ι → K) × (κ → K)) where
  toFun f := (fun i => f (Sum.inl i), fun j => f (Sum.inr j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Sum.elim p.1 p.2
  left_inv f := by funext x; cases x <;> rfl
  right_inv p := by ext <;> rfl

theorem mulVecLin_fromBlocks (M : Matrix R₁ C₁ K) (N : Matrix R₂ C₂ K) :
    (Matrix.fromBlocks M 0 0 N).mulVecLin
      = (sumPiEquiv (K := K) R₁ R₂).symm.toLinearMap ∘ₗ
          LinearMap.prodMap M.mulVecLin N.mulVecLin ∘ₗ
            (sumPiEquiv (K := K) C₁ C₂).toLinearMap := by

  apply LinearMap.ext
  intro v
  funext i
  cases i with
  | inl i =>
      simp [sumPiEquiv, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]
  | inr i =>
      simp [sumPiEquiv, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]

theorem rank_fromBlocks_zero_offdiag (M : Matrix R₁ C₁ K) (N : Matrix R₂ C₂ K) :
    (Matrix.fromBlocks M 0 0 N).rank = M.rank + N.rank := by
  classical
  have hmap := mulVecLin_fromBlocks (K := K) M N
  unfold Matrix.rank
  rw [hmap, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearMap.range_prodMap]
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_prod_submodule _ _

end

end

end

section

section

open Finset

universe u

variable {K : Type u} [Field K]

def ltEquiv (W c : ℕ) (h : c ≤ W) : {a : Fin W // (a : ℕ) < c} ≃ Fin c where
  toFun x := ⟨(x.1 : ℕ), x.2⟩
  invFun k := ⟨⟨(k : ℕ), lt_of_lt_of_le k.isLt h⟩, k.isLt⟩
  left_inv := by rintro ⟨⟨a, ha⟩, h2⟩; rfl
  right_inv := by rintro ⟨k, hk⟩; rfl

theorem card_lt_subtype (W c : ℕ) (h : c ≤ W) :
    Fintype.card {a : Fin W // (a : ℕ) < c} = c := by
  rw [Fintype.card_congr (ltEquiv W c h), Fintype.card_fin]

theorem card_filter_lt (W c : ℕ) (h : c ≤ W) :
    (Finset.univ.filter (fun a : Fin W => (a : ℕ) < c)).card = c := by
  classical
  rw [← Fintype.card_subtype (fun a : Fin W => (a : ℕ) < c)]
  exact card_lt_subtype W c h

variable {s : ℕ}

def chunkF (W r : ℕ) (γ : Fin s) : Finset (Fin s × Fin W) :=
  ({γ} : Finset (Fin s)) ×ˢ (Finset.univ.filter (fun a : Fin W => (a : ℕ) < 2 ^ (γ : ℕ) * r))

theorem card_chunkF (W r : ℕ) (γ : Fin s) (h : 2 ^ (γ : ℕ) * r ≤ W) :
    (chunkF W r γ).card = 2 ^ (γ : ℕ) * r := by
  classical
  rw [chunkF, Finset.card_product, Finset.card_singleton, one_mul,
    card_filter_lt W (2 ^ (γ : ℕ) * r) h]

theorem chunkF_disjoint (W r : ℕ) {γ δ : Fin s} (hne : γ ≠ δ) :
    Disjoint (chunkF W r γ) (chunkF W r δ) := by
  classical
  rw [Finset.disjoint_left]
  rintro p hp hq
  rw [chunkF, Finset.mem_product, Finset.mem_singleton] at hp hq

  exact hne (hp.1.symm.trans hq.1)

theorem card_biUnion_chunkF (W r : ℕ) (T : Finset (Fin s))
    (h : ∀ γ ∈ T, 2 ^ (γ : ℕ) * r ≤ W) :
    (T.biUnion (fun γ => chunkF W r γ)).card = ∑ γ ∈ T, 2 ^ (γ : ℕ) * r := by
  classical
  rw [Finset.card_biUnion (fun γ _ δ _ hne => chunkF_disjoint W r hne)]
  exact Finset.sum_congr rfl fun γ hγ => card_chunkF W r γ (h γ hγ)

theorem chunk_le_width (r : ℕ) (γ : Fin s) : 2 ^ (γ : ℕ) * r ≤ 2 ^ s * r :=
  Nat.mul_le_mul_right r (Nat.pow_le_pow_right (by norm_num) (le_of_lt γ.isLt))

end

end

section

section

open Finset

variable {m : ℕ}

def SuperIncr (ρ : Fin m → ℕ) (σ : ℕ) : Prop :=
  ∀ i : Fin m, (∑ j ∈ univ.filter (fun j => j < i), ρ j) + σ < ρ i

theorem exists_max_symmDiff {T T' : Finset (Fin m)} (h : T ≠ T') :
    ∃ i : Fin m, ((i ∈ T ∧ i ∉ T') ∨ (i ∈ T' ∧ i ∉ T)) ∧
      ∀ j, i < j → (j ∈ T ↔ j ∈ T') := by
  classical
  set D : Finset (Fin m) := (T \ T') ∪ (T' \ T) with hD
  have hmemD : ∀ j : Fin m, j ∈ D ↔ ¬ (j ∈ T ↔ j ∈ T') := by
    intro j
    simp only [hD, Finset.mem_union, Finset.mem_sdiff]
    by_cases h1 : j ∈ T <;> by_cases h2 : j ∈ T' <;> simp [h1, h2]
  have hne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact h (Finset.ext fun j => by
      by_contra hcon
      have hjD : j ∈ D := (hmemD j).mpr hcon
      rw [hempty] at hjD
      simp at hjD)
  refine ⟨D.max' hne, ?_, ?_⟩
  ·
    have hmem := (hmemD (D.max' hne)).mp (D.max'_mem hne)
    tauto
  · intro j hj
    by_contra hcon
    have hjD : j ∈ D := (hmemD j).mpr hcon
    exact absurd (D.le_max' j hjD) (not_le.mpr hj)

theorem sum_lt_of_mem_of_max {ρ : Fin m → ℕ} {σ : ℕ} (hρ : SuperIncr ρ σ)
    {T T' : Finset (Fin m)} {i : Fin m} (hi : i ∈ T) (hi' : i ∉ T')
    (hmax : ∀ j, i < j → (j ∈ T ↔ j ∈ T')) :
    (∑ j ∈ T', ρ j) + σ < ∑ j ∈ T, ρ j := by
  classical
  set U : Finset (Fin m) := T.filter (fun j => i < j) with hU
  set L : Finset (Fin m) := univ.filter (fun j : Fin m => j < i) with hL

  have hiU : i ∉ U := by simp [hU]
  have hsubT : insert i U ⊆ T := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact hi
    · exact (Finset.mem_filter.mp hj').1
  have hlowT : (∑ j ∈ U, ρ j) + ρ i ≤ ∑ j ∈ T, ρ j := by
    have := Finset.sum_le_sum_of_subset (f := ρ) hsubT
    rwa [Finset.sum_insert hiU, add_comm (ρ i)] at this

  have hsubT' : T' ⊆ U ∪ L := by
    intro j hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(hmax j hlt).mpr hj, hlt⟩)
    · exact absurd hj hi'
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem_univ j, hgt⟩)
  have hdisj : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro a haU haL
    have h1 : i < a := (Finset.mem_filter.mp haU).2
    have h2 : a < i := (Finset.mem_filter.mp haL).2
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  have hhighT' : ∑ j ∈ T', ρ j ≤ (∑ j ∈ U, ρ j) + ∑ j ∈ L, ρ j := by
    calc ∑ j ∈ T', ρ j ≤ ∑ j ∈ U ∪ L, ρ j := Finset.sum_le_sum_of_subset hsubT'
      _ = (∑ j ∈ U, ρ j) + ∑ j ∈ L, ρ j := Finset.sum_union hdisj
  have hgap : (∑ j ∈ L, ρ j) + σ < ρ i := hρ i
  omega

theorem sum_add_ne_of_ne {ρ : Fin m → ℕ} {σ : ℕ} (hρ : SuperIncr ρ σ)
    {T T' : Finset (Fin m)} (hne : T ≠ T') {s s' : ℕ} (hs : s ≤ σ) (hs' : s' ≤ σ) :
    (∑ j ∈ T, ρ j) + s ≠ (∑ j ∈ T', ρ j) + s' := by
  obtain ⟨i, hi, hmax⟩ := exists_max_symmDiff hne
  rcases hi with ⟨hiT, hiT'⟩ | ⟨hiT', hiT⟩
  · have := sum_lt_of_mem_of_max hρ hiT hiT' hmax
    omega
  · have hmax' : ∀ j, i < j → (j ∈ T' ↔ j ∈ T) := fun j hj => (hmax j hj).symm
    have := sum_lt_of_mem_of_max hρ hiT' hiT hmax'
    omega

theorem subset_eq_of_sum_eq {ρ : Fin m → ℕ} {σ : ℕ} (hρ : SuperIncr ρ σ)
    {T T' : Finset (Fin m)} {s s' : ℕ} (hs : s ≤ σ) (hs' : s' ≤ σ)
    (h : (∑ j ∈ T, ρ j) + s = (∑ j ∈ T', ρ j) + s') : T = T' := by
  by_contra hne
  exact sum_add_ne_of_ne hρ hne hs hs' h

theorem sum_range_two_pow (n : ℕ) : (∑ j ∈ Finset.range n, 2 ^ j) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

theorem superIncr_geometric (r : ℕ) (hr : 0 < r) :
    SuperIncr (fun γ : Fin m => 2 ^ (γ : ℕ) * r) (r - 1) := by
  classical
  intro i

  show (∑ j ∈ univ.filter (fun j : Fin m => j < i), 2 ^ (j : ℕ) * r) + (r - 1)
      < 2 ^ (i : ℕ) * r

  have hmap : ∑ j ∈ univ.filter (fun j : Fin m => j < i), 2 ^ (j : ℕ) * r
      = ∑ x ∈ (univ.filter (fun j : Fin m => j < i)).map Fin.valEmbedding, 2 ^ x * r :=
    (Finset.sum_map _ Fin.valEmbedding (fun x => 2 ^ x * r)).symm
  have hsub : (univ.filter (fun j : Fin m => j < i)).map Fin.valEmbedding
      ⊆ Finset.range (i : ℕ) := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simpa using hj
  have hle : ∑ j ∈ univ.filter (fun j : Fin m => j < i), 2 ^ (j : ℕ) * r
      ≤ ∑ j ∈ Finset.range (i : ℕ), 2 ^ j * r := by
    rw [hmap]
    exact Finset.sum_le_sum_of_subset hsub
  have hgeom : (∑ j ∈ Finset.range (i : ℕ), 2 ^ j * r) + r = 2 ^ (i : ℕ) * r := by
    rw [← Finset.sum_mul, ← sum_range_two_pow (i : ℕ)]
    ring
  omega

end

end

section

section

open Finset

universe u

variable {K : Type u} [Field K] {t s : ℕ}

theorem S_blockDiagonal_of_ranks
    (str : Fin t → Fin s) (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin t) (Fin t) K)
    (T : Fin t → Finset (Fin s))
    (hT : ∀ k γ, γ ∈ T k ↔ ∃ j, str j = γ ∧ S j k ≠ 0)
    (arank crank : Fin t → ℕ)
    (ha : ∀ k, arank k < r) (hc : ∀ k, crank k < r)
    (hrank : ∀ k, (∑ γ ∈ T k, 2 ^ (γ : ℕ) * r) + crank k
              = 2 ^ ((str k : Fin s) : ℕ) * r + arank k) :
    ∀ j k, str j ≠ str k → S j k = 0 := by
  intro j k hjk
  by_contra hS

  have hsingle : (∑ γ ∈ ({str k} : Finset (Fin s)), 2 ^ (γ : ℕ) * r) + arank k
      = 2 ^ ((str k : Fin s) : ℕ) * r + arank k := by
    rw [Finset.sum_singleton]
  have hsum : (∑ γ ∈ T k, 2 ^ (γ : ℕ) * r) + crank k
      = (∑ γ ∈ ({str k} : Finset (Fin s)), 2 ^ (γ : ℕ) * r) + arank k := by
    rw [hsingle]; exact hrank k

  have hak : arank k < r := ha k
  have hck : crank k < r := hc k
  have hTk : T k = ({str k} : Finset (Fin s)) :=
    subset_eq_of_sum_eq (superIncr_geometric r hr)
      (by omega : crank k ≤ r - 1) (by omega : arank k ≤ r - 1) hsum

  have hmem : str j ∈ T k := (hT k (str j)).mpr ⟨j, rfl, hS⟩
  rw [hTk, Finset.mem_singleton] at hmem
  exact hjk hmem

end

end

section

section

open Matrix
open Finset

universe u

variable {K : Type u} [Field K]

section

variable {s : ℕ}

def Ediag (r : ℕ) (γ : Fin s) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin s × Fin (2 ^ s * r)) K :=
  Matrix.diagonal (fun p => if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0)

end

section

variable {s t : ℕ}

def gadget (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin t × (Fin s × Fin (2 ^ s * r))) K :=
  Matrix.of fun p jq => c jq.1 * Ediag r (str jq.1) p jq.2

def uni (r : ℕ) (T : Finset (Fin s)) : Finset (Fin s × Fin (2 ^ s * r)) :=
  T.biUnion (fun γ => chunkF (2 ^ s * r) r γ)

def EdiagT (r : ℕ) (T : Finset (Fin s)) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin s × Fin (2 ^ s * r)) K :=
  Matrix.diagonal (fun p => if p ∈ uni r T then (1 : K) else 0)

theorem rank_EdiagT (r : ℕ) (T : Finset (Fin s)) :
    (EdiagT (K := K) r T).rank = ∑ γ ∈ T, 2 ^ (γ : ℕ) * r := by
  classical
  have hfilter : (Finset.univ.filter
      (fun p : Fin s × Fin (2 ^ s * r) => (if p ∈ uni r T then (1 : K) else 0) ≠ 0))
      = uni r T := by
    ext p
    by_cases h : p ∈ uni r T <;> simp [h]
  rw [EdiagT, Matrix.rank_diagonal, Fintype.card_subtype, hfilter, uni]
  exact card_biUnion_chunkF (2 ^ s * r) r T (fun γ _ => chunk_le_width r γ)

theorem indUni_eq_sum (r : ℕ) (T : Finset (Fin s)) (p : Fin s × Fin (2 ^ s * r)) :
    (if p ∈ uni r T then (1 : K) else 0)
      = ∑ γ ∈ T, (if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0) := by
  classical
  by_cases h : p ∈ uni r T
  · obtain ⟨γ, hγT, hγ⟩ := Finset.mem_biUnion.mp h
    rw [if_pos h]
    rw [Finset.sum_eq_single γ]
    · rw [if_pos hγ]
    · intro δ hδT hne
      rw [if_neg]
      intro hcon
      exact (Finset.disjoint_left.mp (chunkF_disjoint (2 ^ s * r) r hne) hcon) hγ
    · intro hnot
      exact absurd hγT hnot
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun γ hγT => ?_).symm
    rw [if_neg]
    intro hcon
    exact h (Finset.mem_biUnion.mpr ⟨γ, hγT, hcon⟩)

theorem gadget_mulVec (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (v : (Fin t × (Fin s × Fin (2 ^ s * r))) → K) (p : Fin s × Fin (2 ^ s * r)) :
    (gadget (K := K) r str c *ᵥ v) p
      = ∑ j : Fin t, c j * ((if p ∈ chunkF (2 ^ s * r) r (str j) then (1 : K) else 0) * v (j, p)) := by
  classical

  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gadget, Matrix.of_apply, Ediag, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single p]
  · simp [mul_assoc]
  · intro q _ hq
    simp [Ne.symm hq]
  · intro hnot
    exact absurd (Finset.mem_univ p) hnot

theorem EdiagT_mulVec (r : ℕ) (T : Finset (Fin s))
    (u : (Fin s × Fin (2 ^ s * r)) → K) (p : Fin s × Fin (2 ^ s * r)) :
    (EdiagT (K := K) r T *ᵥ u) p = (if p ∈ uni r T then (1 : K) else 0) * u p := by
  simp [EdiagT, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_ite_eq]

theorem Ediag_mulVec (r : ℕ) (γ : Fin s)
    (u : (Fin s × Fin (2 ^ s * r)) → K) (p : Fin s × Fin (2 ^ s * r)) :
    (Ediag (K := K) r γ *ᵥ u) p
      = (if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0) * u p := by
  simp [Ediag, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_ite_eq]

theorem range_gadget (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (T : Finset (Fin s)) (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0) :
    LinearMap.range (gadget (K := K) r str c).mulVecLin
      = LinearMap.range (EdiagT (K := K) r T).mulVecLin := by
  classical
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    refine ⟨(gadget r str c).mulVecLin v, ?_⟩
    funext p
    rw [Matrix.mulVecLin_apply, EdiagT_mulVec]
    by_cases hp : p ∈ uni r T
    · rw [if_pos hp, one_mul]
    · rw [if_neg hp, zero_mul, Matrix.mulVecLin_apply, gadget_mulVec]

      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases hcj : c j = 0
      · rw [hcj, zero_mul]
      · have hstr : str j ∈ T := (hT (str j)).mpr ⟨j, rfl, hcj⟩
        have : p ∉ chunkF (2 ^ s * r) r (str j) := fun hcon =>
          hp (Finset.mem_biUnion.mpr ⟨str j, hstr, hcon⟩)
        rw [if_neg this, zero_mul, mul_zero]
  · rintro w ⟨u, rfl⟩
    have hpt : ∀ p, ((EdiagT (K := K) r T).mulVecLin u) p
        = ∑ γ ∈ T, ((Ediag (K := K) r γ).mulVecLin u) p := by
      intro p
      rw [Matrix.mulVecLin_apply, EdiagT_mulVec, indUni_eq_sum r T p, Finset.sum_mul]
      exact Finset.sum_congr rfl fun γ _ => by rw [Matrix.mulVecLin_apply, Ediag_mulVec]
    have hsplit : (EdiagT (K := K) r T).mulVecLin u
        = ∑ γ ∈ T, (Ediag (K := K) r γ).mulVecLin u := by
      funext p
      rw [hpt p]
      exact (Finset.sum_apply p T (fun γ => (Ediag (K := K) r γ).mulVecLin u)).symm
    rw [hsplit]
    refine Submodule.sum_mem _ fun γ hγT => ?_
    obtain ⟨j, hstrj, hcj⟩ := (hT γ).mp hγT
    refine ⟨fun jq => if jq.1 = j then (c j)⁻¹ * u jq.2 else 0, ?_⟩
    funext p
    rw [Matrix.mulVecLin_apply, gadget_mulVec, Matrix.mulVecLin_apply, Ediag_mulVec]
    rw [Finset.sum_eq_single j]
    · subst hstrj
      by_cases hp : p ∈ chunkF (2 ^ s * r) r (str j)
      ·
        simp [hp, mul_inv_cancel_left₀ hcj]
      · simp [hp]
    · intro j' _ hj'
      simp [hj']
    · intro hnot
      exact absurd (Finset.mem_univ j) hnot

theorem rank_gadget (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (T : Finset (Fin s)) (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0) :
    (gadget (K := K) r str c).rank = ∑ γ ∈ T, 2 ^ (γ : ℕ) * r := by
  unfold Matrix.rank
  rw [range_gadget r str c T hT]
  exact rank_EdiagT r T

theorem rank_padded {Rows Cols : Type} [Fintype Rows] [Fintype Cols]
    [DecidableEq Rows] [DecidableEq Cols]
    (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (T : Finset (Fin s)) (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0)
    (M : Matrix Rows Cols K) :
    (Matrix.fromBlocks (gadget (K := K) r str c) 0 0 M).rank
      = (∑ γ ∈ T, 2 ^ (γ : ℕ) * r) + M.rank := by
  rw [rank_fromBlocks_zero_offdiag,
    rank_gadget r str c T hT]

end

section

theorem rank_lt_of_card_rows_lt {R C : Type} [Fintype R] [Fintype C] {r : ℕ}
    (h : Fintype.card R < r) (M : Matrix R C K) : M.rank < r := by
  have h0 : Module.finrank K (R → K) = Fintype.card R := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank K (LinearMap.range M.mulVecLin) ≤ Module.finrank K (R → K) :=
    Submodule.finrank_le _
  unfold Matrix.rank
  omega

end

end

end

section

section

open Matrix

universe u

abbrev GR (n r : ℕ) : Type := Fin n × Fin (2 ^ n * r)

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

abbrev PArr (K : Type u) [Field K] (β γ : Type) (RowIdx : β → Type) (ColIdx : γ → Type) (t : ℕ) :=
  Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K

def IsBlockDiag {I ρ : Type} [DecidableEq ρ] (blk : I → ρ) (M : Matrix I I K) : Prop :=
  ∀ i j, blk i ≠ blk j → M i j = 0

theorem isBlockDiag_const {I : Type} (M : Matrix I I K) :
    IsBlockDiag (fun _ : I => (0 : Fin 1)) M :=
  fun _ _ h => absurd rfl h

def BlockEquiv (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) : Prop :=
  ∃ (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (R : Matrix (Fin t) (Fin t) K),
    (∀ b, IsUnit (P b).det) ∧ (∀ s, IsUnit (Q s).det) ∧ IsUnit R.det ∧ IsBlockDiag str R ∧
    ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)

section

variable (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

abbrev GRb (b : β) : Type := {p : GR n r // b = b₀}

abbrev GCs (s : γ) : Type := {jq : Fin t × GR n r // s = c₀}

abbrev PadRow (b : β) : Type := GRb b₀ (n := n) r b ⊕ RowIdx b

abbrev PadCol (s : γ) : Type := GCs c₀ (n := n) (t := t) r s ⊕ ColIdx s

def ind (k : Fin t) : Fin t → K := fun j => if j = k then 1 else 0

def gadgetBlock (c : Fin t → K) (b : β) (s : γ) :
    Matrix (GRb b₀ (n := n) r b) (GCs c₀ (n := n) (t := t) r s) K :=
  Matrix.of fun p jq => gadget r str c p.1 jq.1

def padPartitioned (X : PArr K β γ RowIdx ColIdx t) :
    PArr K β γ (PadRow b₀ r (RowIdx := RowIdx) (n := n)) (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t)) t :=
  fun k b s => Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind k) b s) 0 0 (X k b s)

theorem sum_smul_gadgetBlock (b : β) (s : γ) (R : Matrix (Fin t) (Fin t) K) (k : Fin t) :
    ∑ k', R k k' • gadgetBlock b₀ c₀ r str (ind k') b s =
      gadgetBlock b₀ c₀ r str (fun j => R k j) b s := by
  ext p jq
  simp only [Matrix.sum_apply, Matrix.smul_apply, gadgetBlock, Matrix.of_apply, gadget, ind,
    smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_smul_fromBlocks {R₁ R₂ C₁ C₂ : Type} [Fintype R₁] [Fintype R₂] [Fintype C₁] [Fintype C₂]
    {ι : Type} [Fintype ι] (c : ι → K) (f : ι → Matrix R₁ C₁ K) (g : ι → Matrix R₂ C₂ K) :
    ∑ i, c i • Matrix.fromBlocks (f i) 0 0 (g i) =
      Matrix.fromBlocks (∑ i, c i • f i) 0 0 (∑ i, c i • g i) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

def kron (X : Matrix (Fin t) (Fin t) K) : Matrix (Fin t × GR n r) (Fin t × GR n r) K :=
  Matrix.kroneckerMap (· * ·) X (1 : Matrix (GR n r) (GR n r) K)

theorem kron_mul (X Y : Matrix (Fin t) (Fin t) K) :
    kron r X * kron r Y = kron (n := n) r (X * Y) := by
  unfold kron
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem kron_one : kron (n := n) (t := t) r (1 : Matrix (Fin t) (Fin t) K) = 1 := by
  unfold kron
  exact Matrix.one_kronecker_one

theorem kron_apply (X : Matrix (Fin t) (Fin t) K) (a b : Fin t × GR n r) :
    kron r X a b = X a.1 b.1 * (if a.2 = b.2 then 1 else 0) := by
  unfold kron
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply]

def kronS (X : Matrix (Fin t) (Fin t) K) (s : γ) :
    Matrix (GCs c₀ (n := n) (t := t) r s) (GCs c₀ (n := n) (t := t) r s) K :=
  Matrix.of fun a b => kron r X a.1 b.1

theorem kronS_mul (X Y : Matrix (Fin t) (Fin t) K) (s : γ) :
    kronS (n := n) c₀ r X s * kronS (n := n) c₀ r Y s = kronS (n := n) c₀ r (X * Y) s := by
  ext a b
  by_cases hs : s = c₀
  · have hsub : ∀ F : GCs c₀ (n := n) (t := t) r s → K,
        ∑ x, F x = ∑ y : Fin t × GR n r, F ⟨y, hs⟩ := fun F =>
      (Equiv.sum_comp (Equiv.subtypeUnivEquiv fun _ : Fin t × GR n r => hs).symm F).symm
    rw [Matrix.mul_apply, hsub]
    simp only [kronS, Matrix.of_apply]
    rw [← kron_mul, Matrix.mul_apply]
  · exact absurd a.2 hs

theorem kronS_one (s : γ) : kronS (n := n) c₀ r (1 : Matrix (Fin t) (Fin t) K) s = 1 := by
  ext a b
  simp only [kronS, Matrix.of_apply, kron_one, Matrix.one_apply, Subtype.ext_iff]

theorem isUnit_kronS (X : Matrix (Fin t) (Fin t) K) (hX : IsUnit X.det) (s : γ) :
    IsUnit (kronS (n := n) c₀ r X s) := by
  refine ⟨⟨kronS (n := n) c₀ r X s, kronS (n := n) c₀ r X⁻¹ s, ?_, ?_⟩, rfl⟩
  · rw [kronS_mul, Matrix.mul_nonsing_inv X hX, kronS_one]
  · rw [kronS_mul, Matrix.nonsing_inv_mul X hX, kronS_one]

theorem gadgetBlock_mul_kronS (R : Matrix (Fin t) (Fin t) K) (hR : IsUnit R.det)
    (hbd : IsBlockDiag str R) (k : Fin t) (b : β) (s : γ) :
    gadgetBlock b₀ c₀ r str (fun j => R k j) b s * (kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ =
      gadgetBlock b₀ c₀ r str (ind k) b s := by
  ext p jq
  by_cases hs : s = c₀
  · have hsub : ∀ F : GCs c₀ (n := n) (t := t) r s → K,
        ∑ x, F x = ∑ y : Fin t × GR n r, F ⟨y, hs⟩ := fun F =>
      (Equiv.sum_comp (Equiv.subtypeUnivEquiv fun _ : Fin t × GR n r => hs).symm F).symm
    simp only [Matrix.mul_apply]
    rw [hsub]
    simp only [Matrix.transpose_apply, kronS, Matrix.of_apply, gadgetBlock, gadget, kron_apply]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

    have hstr : ∀ j, R k j * Ediag r (str j) p.1 jq.1.2 * R⁻¹ j jq.1.1 =
        R k j * R⁻¹ j jq.1.1 * Ediag r (str k) p.1 jq.1.2 := by
      intro j
      by_cases hj : R k j = 0
      · rw [hj, zero_mul, zero_mul, zero_mul]
      · have : str j = str k := by
          by_contra hne
          exact hj (hbd k j (Ne.symm hne))
        rw [this]; ring
    simp only [hstr]
    rw [← Finset.sum_mul, ← Matrix.mul_apply, Matrix.mul_nonsing_inv R hR, Matrix.one_apply, ind]
    by_cases hk : jq.1.1 = k
    · simp [hk]
    · simp [hk, Ne.symm hk]
  · exact absurd jq.2 hs

theorem pad_transport (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K)
    (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K) (Wq : ∀ s, Matrix (GCs c₀ (n := n) (t := t) r s) (GCs c₀ (n := n) (t := t) r s) K)
    (G : Matrix (GRb b₀ (n := n) r b) (GCs c₀ (n := n) (t := t) r s) K) (M : Matrix (RowIdx b) (ColIdx s) K) :
    Matrix.fromBlocks (1 : Matrix (GRb b₀ (n := n) r b) (GRb b₀ (n := n) r b) K) 0 0 (P b) *
        Matrix.fromBlocks G 0 0 M * (Matrix.fromBlocks (Wq s) 0 0 (Q s))ᵀ =
      Matrix.fromBlocks (G * (Wq s)ᵀ) 0 0 (P b * M * (Q s)ᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

theorem blockEquiv_pad (X Y : PArr K β γ RowIdx ColIdx t) (h : BlockEquiv str X Y) :
    BlockEquiv (fun _ : Fin t => (0 : Fin 1)) (padPartitioned b₀ c₀ r str X) (padPartitioned b₀ c₀ r str Y) := by
  obtain ⟨P, Q, R, hP, hQ, hR, hbd, hXY⟩ := h
  have hRinvT : IsUnit ((R⁻¹)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det R hR
  refine ⟨fun b => Matrix.fromBlocks (1 : Matrix (GRb b₀ (n := n) r b) (GRb b₀ (n := n) r b) K) 0 0 (P b),
    fun s => Matrix.fromBlocks (kronS (n := n) c₀ r (R⁻¹)ᵀ s) 0 0 (Q s), R, ?_, ?_, hR, isBlockDiag_const R, ?_⟩
  · intro b
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hP b
  · intro s
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_kronS (n := n) c₀ r _ hRinvT s)).mul (hQ s)
  · intro k b s
    have hterm : ∀ a,
        Matrix.fromBlocks (1 : Matrix (GRb b₀ (n := n) r b) (GRb b₀ (n := n) r b) K) 0 0 (P b) *
            padPartitioned b₀ c₀ r str X a b s * (Matrix.fromBlocks (kronS (n := n) c₀ r (R⁻¹)ᵀ s) 0 0 (Q s))ᵀ =
          Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind a) b s * (kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ) 0 0
            (P b * X a b s * (Q s)ᵀ) := fun a => pad_transport b₀ c₀ r P Q _ _ _
    refine Eq.trans ?_ (Finset.sum_congr rfl fun x _ =>
      (congrArg (fun M => R k x • M) (hterm x)).symm)
    rw [sum_smul_fromBlocks, padPartitioned, Matrix.fromBlocks_inj]
    refine ⟨?_, rfl, rfl, hXY k b s⟩
    rw [← gadgetBlock_mul_kronS b₀ c₀ r str R hR hbd k b s,
      ← sum_smul_gadgetBlock b₀ c₀ r str b s R k, Matrix.sum_mul]
    simp only [Matrix.smul_mul]
    exact Finset.sum_congr rfl fun x _ => rfl

end

end

end

section

section

open LinearMap Submodule

universe u v

variable {R : Type u} [Ring R]

def Indecomposable (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ p q : Submodule R M, IsCompl p q → p = ⊥ ∨ q = ⊥

section

variable {M : Type v} [AddCommGroup M] [Module R M] [IsArtinian R M] [IsNoetherian R M]

theorem exists_isCompl_ker_pow_range_pow (f : Module.End R M) :
    ∃ n : ℕ, 1 ≤ n ∧ IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  exact ⟨n + 1, by omega, hn (n + 1) (by omega)⟩

theorem isUnit_of_injective (f : Module.End R M) (hf : Function.Injective f) : IsUnit f := by
  have hs : Function.Surjective f := IsArtinian.surjective_of_injective_endomorphism f hf
  let e : M ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hf, hs⟩
  refine ⟨⟨f, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
  · ext x; exact e.apply_symm_apply x
  · ext x; exact e.symm_apply_apply x

theorem injective_of_isUnit (f : Module.End R M) (hf : IsUnit f) : Function.Injective f := by
  obtain ⟨u, rfl⟩ := hf
  intro x y hxy
  have h := congrArg (↑u⁻¹ : Module.End R M) hxy
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply,
    Module.End.one_apply] at h

theorem isUnit_or_isNilpotent (hM : Indecomposable (R := R) M) (f : Module.End R M) :
    IsUnit f ∨ IsNilpotent f := by
  obtain ⟨n, hn1, hn⟩ := exists_isCompl_ker_pow_range_pow f
  rcases hM.2 _ _ hn with hk | hr
  ·
    left
    apply isUnit_of_injective
    rw [← LinearMap.ker_eq_bot]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : LinearMap.ker f ≤ LinearMap.ker (f ^ (m + 1)) := by
      rw [pow_succ]
      exact LinearMap.ker_le_ker_comp f (f ^ m)
    exact le_bot_iff.mp (hk ▸ hle)
  ·
    right
    exact ⟨n, LinearMap.range_eq_bot.mp hr⟩

end

section

variable {E A C : Type v} [AddCommGroup E] [Module R E] [AddCommGroup A] [Module R A]
  [AddCommGroup C] [Module R C]

def block11 (φ : (E × A) ≃ₗ[R] (E × C)) : Module.End R E :=
  (LinearMap.fst R E C) ∘ₗ (φ : E × A →ₗ[R] E × C) ∘ₗ (LinearMap.inl R E A)

def block21 (φ : (E × A) ≃ₗ[R] (E × C)) : E →ₗ[R] C :=
  (LinearMap.snd R E C) ∘ₗ (φ : E × A →ₗ[R] E × C) ∘ₗ (LinearMap.inl R E A)

def imageInl (φ : (E × A) ≃ₗ[R] (E × C)) : Submodule R (E × C) :=
  (LinearMap.range (LinearMap.inl R E A)).map (φ : E × A →ₗ[R] E × C)

theorem mem_imageInl (φ : (E × A) ≃ₗ[R] (E × C)) (x : E × C) :
    x ∈ imageInl φ ↔ ∃ e : E, φ (e, 0) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hy
    exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨(e, 0), LinearMap.mem_range.mpr ⟨e, rfl⟩, rfl⟩

theorem isCompl_imageInl_snd (φ : (E × A) ≃ₗ[R] (E × C)) (hα : Function.Bijective (block11 φ)) :
    IsCompl (imageInl φ) (LinearMap.range (LinearMap.inr R E C)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨e, rfl⟩ := (mem_imageInl φ x).mp hx
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hx'

    have h1 : block11 φ e = 0 := by
      have := congrArg Prod.fst hc
      simpa [block11] using this.symm
    have he : e = 0 := hα.1 (by simpa using h1)
    subst he; simp
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro ⟨e', c⟩
    obtain ⟨e, he⟩ := hα.2 e'

    refine Submodule.mem_sup.mpr ⟨φ (e, 0), (mem_imageInl φ _).mpr ⟨e, rfl⟩,
      (0, c - (φ (e, 0)).2), LinearMap.mem_range.mpr ⟨c - (φ (e, 0)).2, rfl⟩, ?_⟩
    have h1 : (φ (e, 0)).1 = e' := by simpa [block11] using he
    ext <;> simp [h1]

theorem isCompl_range_inl_inr :
    IsCompl (LinearMap.range (LinearMap.inl R E A)) (LinearMap.range (LinearMap.inr R E A)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hx
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hx'
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    simp only [LinearMap.inr_apply, LinearMap.inl_apply] at h1 h2
    ext <;> simp [← h1, h2]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro ⟨e, a⟩
    exact Submodule.mem_sup.mpr ⟨(e, 0), LinearMap.mem_range.mpr ⟨e, rfl⟩,
      (0, a), LinearMap.mem_range.mpr ⟨a, rfl⟩, by ext <;> simp⟩

noncomputable def cancelOfBlockUnit (φ : (E × A) ≃ₗ[R] (E × C))
    (hα : Function.Bijective (block11 φ)) : A ≃ₗ[R] C :=

  let e₁ : A ≃ₗ[R] LinearMap.range (LinearMap.inr R E A) :=
    (LinearEquiv.ofInjective (LinearMap.inr R E A) LinearMap.inr_injective)
  let e₂ : LinearMap.range (LinearMap.inr R E A) ≃ₗ[R]
      ((E × A) ⧸ LinearMap.range (LinearMap.inl R E A)) :=
    Submodule.quotientEquivOfIsCompl _ _ isCompl_range_inl_inr |>.symm

  let e₃ : ((E × A) ⧸ LinearMap.range (LinearMap.inl R E A)) ≃ₗ[R] ((E × C) ⧸ imageInl φ) :=
    Submodule.Quotient.equiv _ _ φ rfl

  let e₄ : ((E × C) ⧸ imageInl φ) ≃ₗ[R] LinearMap.range (LinearMap.inr R E C) :=
    Submodule.quotientEquivOfIsCompl _ _ (isCompl_imageInl_snd φ hα)
  let e₅ : LinearMap.range (LinearMap.inr R E C) ≃ₗ[R] C :=
    (LinearEquiv.ofInjective (LinearMap.inr R E C) LinearMap.inr_injective).symm
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄ ≪≫ₗ e₅

end

section

variable {E A C : Type v} [AddCommGroup E] [Module R E] [AddCommGroup A] [Module R A]
  [AddCommGroup C] [Module R C] [IsArtinian R E] [IsNoetherian R E]

def shear (l : C →ₗ[R] E) : (E × C) ≃ₗ[R] (E × C) where
  toFun := fun x => (x.1 + l x.2, x.2)
  invFun := fun x => (x.1 - l x.2, x.2)
  map_add' := by intro x y; ext <;> simp [add_add_add_comm]
  map_smul' := by intro c x; ext <;> simp
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp

theorem shear_apply (l : C →ₗ[R] E) (x : E × C) : shear l x = (x.1 + l x.2, x.2) := rfl

theorem block11_shear_trans (φ : (E × A) ≃ₗ[R] (E × C)) (l : C →ₗ[R] E) :
    block11 (φ ≪≫ₗ shear l) = block11 φ + l ∘ₗ block21 φ := by
  ext e
  simp [block11, block21, shear_apply]

theorem block_identity (φ : (E × A) ≃ₗ[R] (E × C)) :
    block11 φ.symm ∘ₗ block11 φ +
      ((LinearMap.fst R E A) ∘ₗ (φ.symm : E × C →ₗ[R] E × A) ∘ₗ (LinearMap.inr R E C)) ∘ₗ block21 φ
      = (1 : Module.End R E) := by
  ext e

  have h : φ.symm (φ (e, 0)) = (e, 0) := φ.symm_apply_apply _
  have hsplit : φ (e, 0) = ((φ (e, 0)).1, 0) + (0, (φ (e, 0)).2) := by ext <;> simp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, block11, block21, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
    Module.End.one_apply]
  have := congrArg Prod.fst h
  rw [hsplit, map_add] at this
  simpa using this

theorem isUnit_block11_of_isUnit_comp (φ : (E × A) ≃ₗ[R] (E × C))
    (h : IsUnit (block11 φ.symm ∘ₗ block11 φ)) : IsUnit (block11 φ) := by
  apply isUnit_of_injective
  intro x y hxy
  have hinj := injective_of_isUnit _ h
  exact hinj (by simp [LinearMap.comp_apply, hxy])

theorem cancel_of_indecomposable (hE : Indecomposable (R := R) E)
    (φ : (E × A) ≃ₗ[R] (E × C)) : Nonempty (A ≃ₗ[R] C) := by
  rcases isUnit_or_isNilpotent hE (block11 φ) with hα | hα
  ·
    exact ⟨cancelOfBlockUnit φ ⟨injective_of_isUnit _ hα,
      IsArtinian.surjective_of_injective_endomorphism _ (injective_of_isUnit _ hα)⟩⟩
  ·
    haveI : Nontrivial E := hE.1
    set β' : C →ₗ[R] E :=
      (LinearMap.fst R E A) ∘ₗ (φ.symm : E × C →ₗ[R] E × A) ∘ₗ (LinearMap.inr R E C) with hβ'
    have hna : ¬ IsUnit (block11 φ.symm ∘ₗ block11 φ) := fun h =>
      (IsNilpotent.not_isUnit hα) (isUnit_block11_of_isUnit_comp φ h)

    have hnil : IsNilpotent (block11 φ.symm ∘ₗ block11 φ) :=
      (isUnit_or_isNilpotent hE _).resolve_left hna
    have hunit : IsUnit (β' ∘ₗ block21 φ) := by
      have hid := block_identity φ

      have : β' ∘ₗ block21 φ = 1 - (block11 φ.symm ∘ₗ block11 φ) :=
        eq_sub_of_add_eq (by rw [add_comm]; exact hid)
      rw [this]
      have h' : IsNilpotent (-(block11 φ.symm ∘ₗ block11 φ)) := hnil.neg
      simpa [sub_eq_add_neg, add_comm] using h'.isUnit_add_one

    let u := hunit.unit
    let l : C →ₗ[R] E := (↑u⁻¹ : Module.End R E) ∘ₗ β'
    have hlγ : l ∘ₗ block21 φ = (1 : Module.End R E) := by
      show ((↑u⁻¹ : Module.End R E) ∘ₗ β') ∘ₗ block21 φ = 1
      rw [LinearMap.comp_assoc]
      change (↑u⁻¹ : Module.End R E) * (β' ∘ₗ block21 φ) = 1
      rw [← hunit.unit_spec]
      exact u.inv_mul
    have hblock : block11 (φ ≪≫ₗ shear l) = block11 φ + 1 := by
      rw [block11_shear_trans, hlγ]
    have hunit' : IsUnit (block11 (φ ≪≫ₗ shear l)) := by
      rw [hblock]; exact hα.isUnit_add_one
    exact ⟨cancelOfBlockUnit (φ ≪≫ₗ shear l) ⟨injective_of_isUnit _ hunit',
      IsArtinian.surjective_of_injective_endomorphism _ (injective_of_isUnit _ hunit')⟩⟩

end

section

variable {K : Type u} [Field K] [Algebra K R]
variable {A C : Type v} [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]

theorem exists_split {E : Type v} [AddCommGroup E] [Module R E] (hnt : Nontrivial E)
    (hnd : ¬ Indecomposable (R := R) E) :
    ∃ p q : Submodule R E, IsCompl p q ∧ p ≠ ⊥ ∧ q ≠ ⊥ := by
  unfold Indecomposable at hnd
  push Not at hnd
  obtain ⟨p, q, hpq, hp, hq⟩ := hnd hnt
  exact ⟨p, q, hpq, hp, hq⟩

noncomputable def prodSubsingletonEquiv (E : Type v) [AddCommGroup E] [Module R E] [Subsingleton E]
    (X : Type v) [AddCommGroup X] [Module R X] : (E × X) ≃ₗ[R] X where
  toFun := Prod.snd
  invFun := fun x => (0, x)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl
  right_inv := fun _ => rfl

theorem cancel_of_finiteDimensional :
    ∀ (n : ℕ) (E : Type v) [AddCommGroup E] [Module R E] [Module K E] [IsScalarTower K R E]
      [FiniteDimensional K E] [IsArtinian R E] [IsNoetherian R E],
      Module.finrank K E = n →
      ∀ (X Y : Type v) [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
        (φ : (E × X) ≃ₗ[R] (E × Y)), Nonempty (X ≃ₗ[R] Y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ _ _ _ _ hn A C _ _ _ _ φ
    by_cases hsub : Subsingleton E
    · exact ⟨(prodSubsingletonEquiv E A).symm ≪≫ₗ φ ≪≫ₗ prodSubsingletonEquiv E C⟩
    · have hnt : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
      by_cases hind : Indecomposable (R := R) E
      · exact cancel_of_indecomposable hind φ
      · obtain ⟨p, q, hpq, hp, hq⟩ := exists_split hnt hind

        let e : (↥p × ↥q) ≃ₗ[R] E := Submodule.prodEquivOfIsCompl p q hpq
        haveI hfp : FiniteDimensional K ↥p :=
          Module.Finite.of_injective (p.subtype.restrictScalars K) Subtype.val_injective
        haveI hfq : FiniteDimensional K ↥q :=
          Module.Finite.of_injective (q.subtype.restrictScalars K) Subtype.val_injective

        have hp_lt : Module.finrank K ↥p < n := by
          rw [← hn]
          have hiso : Module.finrank K ↥p =
              Module.finrank K (LinearMap.range (p.subtype.restrictScalars K)) :=
            (LinearEquiv.ofInjective (p.subtype.restrictScalars K)
              (Subtype.val_injective : Function.Injective (p.subtype.restrictScalars K))).finrank_eq
          rw [hiso]
          apply Submodule.finrank_lt
          intro htop
          apply hq
          have hpt : p = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro x
            have hx : x ∈ LinearMap.range (p.subtype.restrictScalars K) := by
              rw [htop]; exact Submodule.mem_top
            obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
            rw [← hy]; exact y.2
          rw [hpt] at hpq
          exact disjoint_top.mp hpq.disjoint.symm
        have hq_lt : Module.finrank K ↥q < n := by
          rw [← hn]
          have hiso : Module.finrank K ↥q =
              Module.finrank K (LinearMap.range (q.subtype.restrictScalars K)) :=
            (LinearEquiv.ofInjective (q.subtype.restrictScalars K)
              (Subtype.val_injective : Function.Injective (q.subtype.restrictScalars K))).finrank_eq
          rw [hiso]
          apply Submodule.finrank_lt
          intro htop
          apply hp
          have hqt : q = ⊤ := by
            rw [Submodule.eq_top_iff']
            intro x
            have hx : x ∈ LinearMap.range (q.subtype.restrictScalars K) := by
              rw [htop]; exact Submodule.mem_top
            obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
            rw [← hy]; exact y.2
          rw [hqt] at hpq
          exact disjoint_top.mp hpq.symm.disjoint.symm

        let φ' : (↥p × (↥q × A)) ≃ₗ[R] (↥p × (↥q × C)) :=
          (LinearEquiv.prodAssoc R ↥p ↥q A).symm ≪≫ₗ e.prodCongr (LinearEquiv.refl R A) ≪≫ₗ φ ≪≫ₗ
            e.symm.prodCongr (LinearEquiv.refl R C) ≪≫ₗ LinearEquiv.prodAssoc R ↥p ↥q C
        obtain ⟨ψ⟩ := ih _ hp_lt ↥p rfl (↥q × A) (↥q × C) φ'
        exact ih _ hq_lt ↥q rfl A C ψ

end

end

end

section

section

universe u v

variable {K : Type u} [Field K]
variable {Src Snk Arr : Type} [Fintype Src] [Fintype Snk] [Fintype Arr]
variable [DecidableEq Src] [DecidableEq Snk]

structure BRep (K : Type u) [Field K] (Src Snk Arr : Type) (V : Src → Type v) (W : Snk → Type v)
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] where
  f : Arr → ∀ s t, V s →ₗ[K] W t

section

variable {V V' DV : Src → Type v} {W W' DW : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ t, AddCommGroup (W' t)]
  [∀ t, Module K (W' t)]
variable [∀ s, AddCommGroup (DV s)] [∀ s, Module K (DV s)] [∀ t, AddCommGroup (DW t)]
  [∀ t, Module K (DW t)]

def RepresentationSimilarity (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W') : Prop :=
  ∃ (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t),
    ∀ a s t, (Q t : W t →ₗ[K] W' t) ∘ₗ A.f a s t = B.f a s t ∘ₗ (P s : V s →ₗ[K] V' s)

def directSumRepresentation (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W) :
    BRep K Src Snk Arr (fun s => DV s × V s) (fun t => DW t × W t) :=
  ⟨fun a s t => (D.f a s t).prodMap (A.f a s t)⟩

abbrev R (K : Type u) [Field K] (Src Snk Arr : Type) : Type u :=
  FreeAlgebra K (Src ⊕ Snk ⊕ Arr × Src × Snk)

abbrev Car (V : Src → Type v) (W : Snk → Type v) [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
    [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] : Type v :=
  (∀ s, V s) × (∀ t, W t)

def representationGenerator (A : BRep K Src Snk Arr V W) : Src ⊕ Snk ⊕ Arr × Src × Snk →
    Module.End K (Car (K := K) V W)
  | Sum.inl s => LinearMap.inl K _ _ ∘ₗ LinearMap.single K V s ∘ₗ LinearMap.proj s ∘ₗ LinearMap.fst K _ _
  | Sum.inr (Sum.inl t) =>
      LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t ∘ₗ LinearMap.proj t ∘ₗ LinearMap.snd K _ _
  | Sum.inr (Sum.inr (a, s, t)) =>
      LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t ∘ₗ A.f a s t ∘ₗ LinearMap.proj s ∘ₗ
        LinearMap.fst K _ _

noncomputable def representationHom (A : BRep K Src Snk Arr V W) :
    R K Src Snk Arr →ₐ[K] Module.End K (Car (K := K) V W) :=
  FreeAlgebra.lift K (representationGenerator A)

theorem representationHom_generator (A : BRep K Src Snk Arr V W) (g : Src ⊕ Snk ⊕ Arr × Src × Snk) :
    (representationHom A) (FreeAlgebra.ι K g) = (representationGenerator A) g :=
  FreeAlgebra.lift_ι_apply (representationGenerator A) g

def representationModule (_A : BRep K Src Snk Arr V W) : Type v := Car (K := K) V W

instance instAddCommGroupM (A : BRep K Src Snk Arr V W) : AddCommGroup (representationModule A) :=
  inferInstanceAs (AddCommGroup (Car (K := K) V W))
instance instModuleM (A : BRep K Src Snk Arr V W) : Module K (representationModule A) :=
  inferInstanceAs (Module K (Car (K := K) V W))
noncomputable instance instModuleRM (A : BRep K Src Snk Arr V W) : Module (R K Src Snk Arr) (representationModule A) :=
  Module.compHom (Car (K := K) V W) (representationHom A).toRingHom

theorem representation_smul_def (A : BRep K Src Snk Arr V W) (r : R K Src Snk Arr) (m : (representationModule A)) :
    r • m = (representationHom A) r m := rfl

instance instIsScalarTowerRM (A : BRep K Src Snk Arr V W) : IsScalarTower K (R K Src Snk Arr) (representationModule A) :=
  ⟨fun c r m => by
    change (representationHom A) (c • r) m = c • (representationHom A) r m
    rw [map_smul]
    rfl⟩

def toRepresentationModule (A : BRep K Src Snk Arr V W) : Car (K := K) V W ≃ₗ[K] (representationModule A) := LinearEquiv.refl K _

theorem representation_smul_generator (A : BRep K Src Snk Arr V W) (g : Src ⊕ Snk ⊕ Arr × Src × Snk) (m : (representationModule A)) :
    FreeAlgebra.ι K g • m = (representationGenerator A) g m := by
  rw [representation_smul_def, representationHom_generator]

instance instFiniteDimensionalM (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : FiniteDimensional K (representationModule A) :=
  inferInstanceAs (FiniteDimensional K (Car (K := K) V W))

instance instIsArtinianRMOfFiniteDimensional (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : IsArtinian (R K Src Snk Arr) (representationModule A) :=
  isArtinian_of_tower K (inferInstanceAs (IsArtinian K (Car (K := K) V W)))

instance instIsNoetherianRMOfFiniteDimensional (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : IsNoetherian (R K Src Snk Arr) (representationModule A) :=
  isNoetherian_of_tower K (inferInstanceAs (IsNoetherian K (Car (K := K) V W)))

end

section

variable {M N : Type v} [AddCommGroup M] [Module K M] [Module (R K Src Snk Arr) M]
  [IsScalarTower K (R K Src Snk Arr) M]
variable [AddCommGroup N] [Module K N] [Module (R K Src Snk Arr) N]
  [IsScalarTower K (R K Src Snk Arr) N]

theorem linear_of_gen (φ : M →ₗ[K] N)
    (h : ∀ (g : Src ⊕ Snk ⊕ Arr × Src × Snk) (m : M),
      φ (FreeAlgebra.ι K g • m) = FreeAlgebra.ι K g • φ m)
    (r : R K Src Snk Arr) (m : M) : φ (r • m) = r • φ m := by
  induction r using FreeAlgebra.induction generalizing m with
  | grade0 c => rw [algebraMap_smul, algebraMap_smul, map_smul]
  | grade1 g => exact h g m
  | mul a b ha hb => rw [mul_smul, mul_smul, ha, hb]
  | add a b ha hb => rw [add_smul, add_smul, map_add, ha, hb]

def linearEquivOfGenerators (φ : M ≃ₗ[K] N)
    (h : ∀ (g : Src ⊕ Snk ⊕ Arr × Src × Snk) (m : M),
      φ (FreeAlgebra.ι K g • m) = FreeAlgebra.ι K g • φ m) :
    M ≃ₗ[R K Src Snk Arr] N where
  toFun := φ
  invFun := φ.symm
  map_add' := φ.map_add
  map_smul' := fun r m => linear_of_gen (φ : M →ₗ[K] N) h r m
  left_inv := φ.left_inv
  right_inv := φ.right_inv

end

section

variable {V V' : Src → Type v} {W W' : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ t, AddCommGroup (W' t)]
  [∀ t, Module K (W' t)]

def pqEquiv (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t) :
    Car (K := K) V W ≃ₗ[K] Car (K := K) V' W' :=
  (LinearEquiv.piCongrRight P).prodCongr (LinearEquiv.piCongrRight Q)

theorem pqEquiv_apply (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t) (m : Car (K := K) V W) :
    pqEquiv P Q m = (fun s => P s (m.1 s), fun t => Q t (m.2 t)) := rfl

theorem single_map {ι : Type} [DecidableEq ι] {X Y : ι → Type v} [∀ i, AddCommGroup (X i)]
    [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (F : ∀ i, X i →ₗ[K] Y i) (i : ι) (x : X i) :
    (fun j => F j ((Pi.single i x : ∀ j, X j) j)) = Pi.single i (F i x) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

noncomputable def equivOfSimilarity (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t)
    (h : ∀ a s t, (Q t : W t →ₗ[K] W' t) ∘ₗ A.f a s t = B.f a s t ∘ₗ (P s : V s →ₗ[K] V' s)) :
    (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B) :=
  linearEquivOfGenerators ((toRepresentationModule A).symm ≪≫ₗ pqEquiv P Q ≪≫ₗ (toRepresentationModule B)) (by
    intro g m
    rw [representation_smul_generator, representation_smul_generator]
    rcases g with s | t | ⟨a, s, t⟩
    · change pqEquiv P Q (Pi.single s (m.1 s), 0) =
        (Pi.single s ((pqEquiv P Q ((toRepresentationModule A).symm m)).1 s), 0)
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · exact single_map (fun s => (P s : V s →ₗ[K] V' s)) s (m.1 s)
      · funext t; simp
    · change pqEquiv P Q (0, Pi.single t (m.2 t)) =
        (0, Pi.single t ((pqEquiv P Q ((toRepresentationModule A).symm m)).2 t))
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · funext s; simp
      · exact single_map (fun t => (Q t : W t →ₗ[K] W' t)) t (m.2 t)
    · change pqEquiv P Q (0, Pi.single t (A.f a s t (m.1 s))) =
        (0, Pi.single t (B.f a s t ((pqEquiv P Q ((toRepresentationModule A).symm m)).1 s)))
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · funext s'; simp
      · refine (single_map (fun t => (Q t : W t →ₗ[K] W' t)) t (A.f a s t (m.1 s))).trans ?_
        have := LinearMap.congr_fun (h a s t) (m.1 s)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
        exact congrArg (Pi.single t) this)

noncomputable def sourceMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (s : Src) : V s →ₗ[K] V' s :=
  LinearMap.proj s ∘ₗ LinearMap.fst K _ _ ∘ₗ ((toRepresentationModule B).symm : (representationModule B) →ₗ[K] Car (K := K) V' W') ∘ₗ
    ((ψ.restrictScalars K : (representationModule A) ≃ₗ[K] (representationModule B)) : (representationModule A) →ₗ[K] (representationModule B)) ∘ₗ
    ((toRepresentationModule A) : Car (K := K) V W →ₗ[K] (representationModule A)) ∘ₗ LinearMap.inl K _ _ ∘ₗ LinearMap.single K V s

noncomputable def sinkMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (t : Snk) : W t →ₗ[K] W' t :=
  LinearMap.proj t ∘ₗ LinearMap.snd K _ _ ∘ₗ ((toRepresentationModule B).symm : (representationModule B) →ₗ[K] Car (K := K) V' W') ∘ₗ
    ((ψ.restrictScalars K : (representationModule A) ≃ₗ[K] (representationModule B)) : (representationModule A) →ₗ[K] (representationModule B)) ∘ₗ
    ((toRepresentationModule A) : Car (K := K) V W →ₗ[K] (representationModule A)) ∘ₗ LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t

theorem sourceMap_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (s : Src) (v : V s) :
    (sourceMap A) B ψ s v = (ψ ((toRepresentationModule A) (Pi.single s v, 0)) : Car (K := K) V' W').1 s := rfl

theorem sinkMap_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (t : Snk) (w : W t) :
    (sinkMap A) B ψ t w = (ψ ((toRepresentationModule A) (0, Pi.single t w)) : Car (K := K) V' W').2 t := rfl

theorem representationEquiv_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (m : Car (K := K) V W) :
    (ψ ((toRepresentationModule A) m) : Car (K := K) V' W') =
      (fun s => (sourceMap A) B ψ s (m.1 s), fun t => (sinkMap A) B ψ t (m.2 t)) := by
  refine Prod.ext ?_ ?_
  · funext s
    have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inl s)) ((toRepresentationModule A) m)
    rw [representation_smul_generator, representation_smul_generator] at h
    change ψ ((toRepresentationModule A) (Pi.single s (m.1 s), 0)) =
      (Pi.single s ((ψ ((toRepresentationModule A) m) : Car (K := K) V' W').1 s), 0) at h
    show (ψ ((toRepresentationModule A) m) : Car (K := K) V' W').1 s = (sourceMap A) B ψ s (m.1 s)
    rw [sourceMap_apply, h]
    simp
  · funext t
    have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inr (Sum.inl t))) ((toRepresentationModule A) m)
    rw [representation_smul_generator, representation_smul_generator] at h
    change ψ ((toRepresentationModule A) (0, Pi.single t (m.2 t))) =
      (0, Pi.single t ((ψ ((toRepresentationModule A) m) : Car (K := K) V' W').2 t)) at h
    show (ψ ((toRepresentationModule A) m) : Car (K := K) V' W').2 t = (sinkMap A) B ψ t (m.2 t)
    rw [sinkMap_apply, h]
    simp

theorem representationEquiv_single_source (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (s : Src) (v : V s) :
    (ψ ((toRepresentationModule A) (Pi.single s v, 0)) : Car (K := K) V' W') = (Pi.single s ((sourceMap A) B ψ s v), 0) := by
  rw [representationEquiv_apply]
  refine Prod.ext ?_ ?_
  · exact single_map (fun s => (sourceMap A) B ψ s) s v
  · funext t; simp

theorem representationEquiv_single_sink (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (t : Snk) (w : W t) :
    (ψ ((toRepresentationModule A) (0, Pi.single t w)) : Car (K := K) V' W') = (0, Pi.single t ((sinkMap A) B ψ t w)) := by
  rw [representationEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext s; simp
  · exact single_map (fun t => (sinkMap A) B ψ t) t w

theorem sourceMap_symm_sourceMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (s : Src) (v : V s) :
    (sourceMap B) A ψ.symm s ((sourceMap A) B ψ s v) = v := by
  rw [sourceMap_apply]
  have h : ψ.symm ((toRepresentationModule B) (Pi.single s ((sourceMap A) B ψ s v), 0)) = (toRepresentationModule A) (Pi.single s v, 0) := by
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (toRepresentationModule B) ((representationEquiv_single_source A) B ψ s v)).symm
  rw [h]
  exact Pi.single_eq_same s v

theorem sinkMap_symm_sinkMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) (t : Snk) (w : W t) :
    (sinkMap B) A ψ.symm t ((sinkMap A) B ψ t w) = w := by
  rw [sinkMap_apply]
  have h : ψ.symm ((toRepresentationModule B) (0, Pi.single t ((sinkMap A) B ψ t w))) = (toRepresentationModule A) (0, Pi.single t w) := by
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (toRepresentationModule B) ((representationEquiv_single_sink A) B ψ t w)).symm
  rw [h]
  exact Pi.single_eq_same t w

theorem similarityOfEquiv (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : (representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) : RepresentationSimilarity A B := by
  refine ⟨fun s => LinearEquiv.ofLinear ((sourceMap A) B ψ s) ((sourceMap B) A ψ.symm s)
      (LinearMap.ext fun v => by
        have := (sourceMap_symm_sourceMap B) A ψ.symm s v
        rwa [LinearEquiv.symm_symm] at this)
      (LinearMap.ext fun v => (sourceMap_symm_sourceMap A) B ψ s v),
    fun t => LinearEquiv.ofLinear ((sinkMap A) B ψ t) ((sinkMap B) A ψ.symm t)
      (LinearMap.ext fun w => by
        have := (sinkMap_symm_sinkMap B) A ψ.symm t w
        rwa [LinearEquiv.symm_symm] at this)
      (LinearMap.ext fun w => (sinkMap_symm_sinkMap A) B ψ t w),
    fun a s t => ?_⟩
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply]
  have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inr (Sum.inr (a, s, t)))) ((toRepresentationModule A) (Pi.single s v, 0))
  rw [representation_smul_generator, representation_smul_generator] at h
  change ψ ((toRepresentationModule A) (0, Pi.single t (A.f a s t ((Pi.single s v : ∀ s, V s) s)))) =
    (0, Pi.single t (B.f a s t ((ψ ((toRepresentationModule A) (Pi.single s v, 0)) : Car (K := K) V' W').1 s))) at h
  rw [Pi.single_eq_same, (representationEquiv_single_sink A) B ψ, (representationEquiv_single_source A) B ψ] at h
  have h2 := congrArg (fun x : Car (K := K) V' W' => x.2 t) h
  simp only [Pi.single_eq_same] at h2
  exact h2

theorem similarity_iff_equiv (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W') :
    RepresentationSimilarity A B ↔ Nonempty ((representationModule A) ≃ₗ[R K Src Snk Arr] (representationModule B)) :=
  ⟨fun ⟨P, Q, h⟩ => ⟨(equivOfSimilarity A) B P Q h⟩, fun ⟨ψ⟩ => (similarityOfEquiv A) B ψ⟩

end

section

variable {V DV : Src → Type v} {W DW : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (DV s)] [∀ s, Module K (DV s)] [∀ t, AddCommGroup (DW t)]
  [∀ t, Module K (DW t)]

def carSplit : Car (K := K) (fun s => DV s × V s) (fun t => DW t × W t) ≃ₗ[K]
    (Car (K := K) DV DW × Car (K := K) V W) where
  toFun m := ((fun s => (m.1 s).1, fun t => (m.2 t).1), (fun s => (m.1 s).2, fun t => (m.2 t).2))
  invFun p := (fun s => (p.1.1 s, p.2.1 s), fun t => (p.1.2 t, p.2.2 t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem carSplit_apply (m : Car (K := K) (fun s => DV s × V s) (fun t => DW t × W t)) :
    carSplit m = ((fun s => (m.1 s).1, fun t => (m.2 t).1), (fun s => (m.1 s).2, fun t => (m.2 t).2)) :=
  rfl

theorem single_fst {ι : Type} [DecidableEq ι] {X Y : ι → Type v} [∀ i, AddCommGroup (X i)]
    [∀ i, AddCommGroup (Y i)] (i : ι) (x : X i × Y i) :
    (fun j => ((Pi.single i x : ∀ j, X j × Y j) j).1) = Pi.single i x.1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

theorem single_snd {ι : Type} [DecidableEq ι] {X Y : ι → Type v} [∀ i, AddCommGroup (X i)]
    [∀ i, AddCommGroup (Y i)] (i : ι) (x : X i × Y i) :
    (fun j => ((Pi.single i x : ∀ j, X j × Y j) j).2) = Pi.single i x.2 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

noncomputable def directSumRepresentationEquiv (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W) :
    (representationModule ((directSumRepresentation D) A)) ≃ₗ[R K Src Snk Arr] ((representationModule D) × (representationModule A)) :=
  linearEquivOfGenerators ((toRepresentationModule ((directSumRepresentation D) A)).symm ≪≫ₗ carSplit ≪≫ₗ (toRepresentationModule D).prodCongr (toRepresentationModule A)) (by
    intro g m
    rw [representation_smul_generator]
    change carSplit ((representationGenerator ((directSumRepresentation D) A)) g m) =
      (FreeAlgebra.ι K g • (toRepresentationModule D) (carSplit m).1, FreeAlgebra.ι K g • (toRepresentationModule A) (carSplit m).2)
    rw [representation_smul_generator, representation_smul_generator]
    rcases g with s | t | ⟨a, s, t⟩
    · change carSplit (Pi.single s (m.1 s), 0) =
        ((Pi.single s ((m.1 s).1), 0), (Pi.single s ((m.1 s).2), 0))
      rw [carSplit_apply]
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · exact single_fst s _
      · funext t; simp
      · exact single_snd s _
      · funext t; simp
    · change carSplit (0, Pi.single t (m.2 t)) =
        ((0, Pi.single t ((m.2 t).1)), (0, Pi.single t ((m.2 t).2)))
      rw [carSplit_apply]
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · funext s; simp
      · exact single_fst t _
      · funext s; simp
      · exact single_snd t _
    · change carSplit (0, Pi.single t (D.f a s t (m.1 s).1, A.f a s t (m.1 s).2)) =
        ((0, Pi.single t (D.f a s t (m.1 s).1)), (0, Pi.single t (A.f a s t (m.1 s).2)))
      rw [carSplit_apply]
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · funext s'; simp
      · exact single_fst t _
      · funext s'; simp
      · exact single_snd t _)

end

section

variable {V V' DV : Src → Type v} {W W' DW : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ t, AddCommGroup (W' t)]
  [∀ t, Module K (W' t)]
variable [∀ s, AddCommGroup (DV s)] [∀ s, Module K (DV s)] [∀ t, AddCommGroup (DW t)]
  [∀ t, Module K (DW t)]
variable [∀ s, FiniteDimensional K (DV s)] [∀ t, FiniteDimensional K (DW t)]

theorem bipartite_cancel (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W)
    (C : BRep K Src Snk Arr V' W') (h : RepresentationSimilarity ((directSumRepresentation D) A) ((directSumRepresentation D) C)) : RepresentationSimilarity A C := by
  obtain ⟨ψ⟩ := (similarity_iff_equiv _ _).mp h
  let e : ((representationModule D) × (representationModule A)) ≃ₗ[R K Src Snk Arr] ((representationModule D) × (representationModule C)) :=
    ((directSumRepresentationEquiv D) A).symm ≪≫ₗ ψ ≪≫ₗ (directSumRepresentationEquiv D) C
  obtain ⟨θ⟩ := cancel_of_finiteDimensional (R := R K Src Snk Arr) (K := K) _ (representationModule D) rfl (representationModule A) (representationModule C) e
  exact (similarityOfEquiv A) C θ

end

end

end

section

section

open TensorProduct

section

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

abbrev Hyp (K : Type*) [Field K] (U : Type*) [AddCommGroup U] [Module K U] :=
  U × Module.Dual K U

noncomputable def omegaH : Hyp K U →ₗ[K] Hyp K U →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => y.2 x.1 - x.2 y.1)
    (fun x₁ x₂ y => by simp; ring)
    (fun c x y => by simp [mul_sub])
    (fun x y₁ y₂ => by simp; ring)
    (fun x c y => by simp [mul_sub])

@[simp] theorem omegaH_apply (x y : Hyp K U) : omegaH x y = y.2 x.1 - x.2 y.1 := rfl

@[simp] theorem omegaH_self (x : Hyp K U) : omegaH x x = 0 := sub_self _

def IsSymplectic (g : Hyp K U ≃ₗ[K] Hyp K U) : Prop :=
  ∀ x y, omegaH (g x) (g y) = omegaH x y

def iota : U →ₗ[K] Hyp K U := LinearMap.inl K U (Module.Dual K U)

@[simp] theorem iota_apply (u : U) : (iota u : Hyp K U) = (u, 0) := rfl

theorem iota_injective : Function.Injective (iota : U →ₗ[K] Hyp K U) :=
  LinearMap.inl_injective

@[simp] theorem iota_isotropic (u v : U) : omegaH (iota u : Hyp K U) (iota v) = 0 := by simp

def levi (P : U ≃ₗ[K] U) : Hyp K U ≃ₗ[K] Hyp K U :=
  LinearEquiv.prodCongr P P.symm.dualMap

@[simp] theorem levi_apply (P : U ≃ₗ[K] U) (x : Hyp K U) :
    levi P x = (P x.1, P.symm.dualMap x.2) := rfl

theorem levi_isSymplectic (P : U ≃ₗ[K] U) : IsSymplectic (levi P) := by
  intro x y
  simp [LinearEquiv.dualMap_apply]

@[simp] theorem levi_iota (P : U ≃ₗ[K] U) (u : U) :
    levi P (iota u : Hyp K U) = iota (P u) := by
  simp [iota]

theorem levi_comp_iota (P : U ≃ₗ[K] U) :
    (levi P : Hyp K U →ₗ[K] Hyp K U) ∘ₗ (iota : U →ₗ[K] Hyp K U)
      = (iota : U →ₗ[K] Hyp K U) ∘ₗ (P : U →ₗ[K] U) :=
  LinearMap.ext fun u => levi_iota P u

end

section

variable {K : Type*} [Field K]
variable {V W X Y : Type*}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def evalSmul (x : X) (v : V) : Module.Dual K X →ₗ[K] V where
  toFun φ := φ x • v
  map_add' φ ψ := by simp [add_smul]
  map_smul' c φ := by simp [smul_smul]

@[simp] theorem evalSmul_apply (x : X) (v : V) (φ : Module.Dual K X) :
    evalSmul x v φ = φ x • v := rfl

noncomputable def contractBil : V →ₗ[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  LinearMap.mk₂ K (fun v x => evalSmul x v)
    (fun v w x => by ext φ; simp [smul_add])
    (fun c v x => by ext φ; exact smul_comm _ _ _)
    (fun v x y => by ext φ; simp [add_smul])
    (fun v c x => by ext φ; simp [smul_smul])

noncomputable def contract : V ⊗[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  TensorProduct.lift contractBil

@[simp] theorem contract_tmul (v : V) (x : X) (φ : Module.Dual K X) :
    contract (v ⊗ₜ[K] x) φ = φ x • v := rfl

theorem contract_map (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) (φ : Module.Dual K Y) :
    contract (TensorProduct.map f g T) φ = f (contract T (g.dualMap φ)) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [LinearMap.dualMap_apply]
  | add a b ha hb => simp [ha, hb]

noncomputable def msupp (T : V ⊗[K] X) : Submodule K V := LinearMap.range (contract T)

theorem mem_msupp (T : V ⊗[K] X) (φ : Module.Dual K X) : contract T φ ∈ msupp T :=
  LinearMap.mem_range_self _ _

theorem msupp_map_le (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) ≤ (msupp T).map f := by
  rintro w ⟨φ, rfl⟩
  exact ⟨contract T (g.dualMap φ), mem_msupp _ _, (contract_map f g T φ).symm⟩

theorem msupp_map (f : V →ₗ[K] W) {g : X →ₗ[K] Y} (hg : Function.Injective g) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) = (msupp T).map f := by
  refine le_antisymm (msupp_map_le f g T) ?_
  rintro w ⟨v, ⟨ψ, rfl⟩, rfl⟩
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hg ψ
  exact ⟨φ, by rw [contract_map f g T φ, hφ]⟩

theorem dualTensorHom_injective [FiniteDimensional K X] :
    Function.Injective (dualTensorHom K (Module.Dual K X) V) := by
  classical
  exact (dualTensorHomEquivOfBasis (N := V)
    (Module.finBasis K (Module.Dual K X))).injective

theorem contract_eq_comp :
    (contract : V ⊗[K] X →ₗ[K] Module.Dual K X →ₗ[K] V) =
      (dualTensorHom K (Module.Dual K X) V) ∘ₗ
        (TensorProduct.map (Module.Dual.eval K X) (LinearMap.id : V →ₗ[K] V)) ∘ₗ
        (TensorProduct.comm K V X).toLinearMap := by
  refine TensorProduct.ext' fun v x => ?_
  ext φ
  simp [dualTensorHom_apply]

theorem contract_injective [FiniteDimensional K X] :
    Function.Injective (contract : V ⊗[K] X →ₗ[K] Module.Dual K X →ₗ[K] V) := by
  classical
  have hev : Function.Injective (Module.Dual.eval K X) := by
    have : (Module.evalEquiv K X).toLinearMap = Module.Dual.eval K X := rfl
    rw [← this]
    exact (Module.evalEquiv K X).injective
  have h2 : Function.Injective
      (TensorProduct.map (Module.Dual.eval K X) (LinearMap.id : V →ₗ[K] V)) :=
    TensorProduct.map_injective_of_flat_flat _ _ hev Function.injective_id
  rw [contract_eq_comp]
  intro a b hab
  exact (TensorProduct.comm K V X).injective
    (h2 (dualTensorHom_injective (V := V) (X := X) hab))

theorem eq_zero_of_msupp_eq_bot [FiniteDimensional K X] (T : V ⊗[K] X) (h : msupp T = ⊥) :
    T = 0 := by
  apply contract_injective (V := V) (X := X)
  ext φ
  have : contract T φ ∈ msupp T := mem_msupp T φ
  rw [h, Submodule.mem_bot] at this
  simpa using this

theorem map_eq_of_eqOn_msupp [FiniteDimensional K X] {Z : Type*} [AddCommGroup Z] [Module K Z]
    (T : V ⊗[K] X) (f f' : V →ₗ[K] W) (hff : ∀ v ∈ msupp T, f v = f' v) (h : X →ₗ[K] Z) :
    TensorProduct.map f h T = TensorProduct.map f' h T := by
  set e : V →ₗ[K] W := f - f' with he
  have hfe : f = f' + e := by rw [he]; abel
  have hzero : TensorProduct.map e (LinearMap.id : X →ₗ[K] X) T = 0 := by
    apply eq_zero_of_msupp_eq_bot (V := W) (X := X)
    refine le_antisymm ?_ bot_le
    rintro w ⟨φ, rfl⟩
    rw [contract_map e LinearMap.id T φ]
    have hmem : contract T (LinearMap.dualMap (LinearMap.id : X →ₗ[K] X) φ) ∈ msupp T :=
      mem_msupp _ _
    have := hff _ hmem
    simp only [he, LinearMap.sub_apply, Submodule.mem_bot]
    rw [this]
    abel
  have hsplit : TensorProduct.map e h T = 0 := by
    have : TensorProduct.map e h = (TensorProduct.map (LinearMap.id : W →ₗ[K] W) h) ∘ₗ
        TensorProduct.map e (LinearMap.id : X →ₗ[K] X) := by
      rw [← TensorProduct.map_comp]; simp
    rw [this]
    simp [LinearMap.comp_apply, hzero]
  rw [hfe, TensorProduct.map_add_left]
  simp [hsplit]

attribute [irreducible] contract msupp

end

section

variable {K : Type*} [Field K]
variable {U H X Y : Type*}
variable [AddCommGroup U] [Module K U] [AddCommGroup H] [Module K H]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem msupp_padded_rigidity
    (ι : U →ₗ[K] H) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    (g : H →ₗ[K] H) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B) :
    ((msupp A).map ι).map g = (msupp B).map ι := by
  have h1 := msupp_map g hk (TensorProduct.map ι j A)
  rw [msupp_map ι hj A] at h1
  rw [← h1, hAB, msupp_map ι hj B]

theorem pad_reflect [FiniteDimensional K U]
    {ι : U →ₗ[K] H} (hι : Function.Injective ι) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    {g : H →ₗ[K] H} (hg : Function.Injective g) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B) :
    ∃ P : U ≃ₗ[K] U, ∀ u ∈ msupp A, g (ι u) = ι (P u) := by
  have hrig := msupp_padded_rigidity ι hj g hk A B hAB
  set e : (msupp A) ≃ₗ[K] (msupp B) :=
    (Submodule.equivMapOfInjective ι hι (msupp A)) ≪≫ₗ
      (Submodule.equivMapOfInjective g hg ((msupp A).map ι)) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrig) ≪≫ₗ
      (Submodule.equivMapOfInjective ι hι (msupp B)).symm with he
  obtain ⟨P, hP⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P, fun u hu => ?_⟩
  have hcoe : ι ((e ⟨u, hu⟩ : msupp B) : U) = g (ι u) := by
    rw [he]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.map_equivMapOfInjective_symm_apply ι hι (msupp B)]
    simp [Submodule.coe_equivMapOfInjective_apply]
  rw [← hcoe, hP ⟨u, hu⟩]

theorem pad_substitute [FiniteDimensional K U] [FiniteDimensional K X]
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    {ι : U →ₗ[K] H} (hι : Function.Injective ι) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    {g : H →ₗ[K] H} (hg : Function.Injective g) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B)
    (m : X →ₗ[K] Z) :
    ∃ P : U ≃ₗ[K] U,
      TensorProduct.map (ι ∘ₗ (P : U →ₗ[K] U)) m A = TensorProduct.map (g ∘ₗ ι) m A := by
  obtain ⟨P, hP⟩ := pad_reflect hι hj hg hk A B hAB
  exact ⟨P, map_eq_of_eqOn_msupp A _ _ (fun u hu => (hP u hu).symm) m⟩

structure SupportLiftWitness
    (A : U ⊗[K] X) (ι : U →ₗ[K] H) (g : H →ₗ[K] H) where
  P : U ≃ₗ[K] U
  agree : ∀ u ∈ msupp A, g (ι u) = ι (P u)

theorem substitute_of_supportLiftWitness [FiniteDimensional K X]
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (A : U ⊗[K] X) (ι : U →ₗ[K] H) (g : H →ₗ[K] H)
    (w : SupportLiftWitness A ι g) (m : X →ₗ[K] Z) :
    TensorProduct.map (ι ∘ₗ (w.P : U →ₗ[K] U)) m A =
      TensorProduct.map (g ∘ₗ ι) m A :=
  map_eq_of_eqOn_msupp A _ _
    (fun u hu => by
      change ι (w.P u) = g (ι u)
      exact (w.agree u hu).symm) m

end

section

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ W₁ W₂ W₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]
  [AddCommGroup W₃] [Module K W₃]

noncomputable def glAct (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] U₁ ⊗[K] (U₂ ⊗[K] U₃) :=
  TensorProduct.map (P₁ : U₁ →ₗ[K] U₁)
    (TensorProduct.map (P₂ : U₂ →ₗ[K] U₂) (P₃ : U₃ →ₗ[K] U₃))

noncomputable def spAct (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃) :
    Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) →ₗ[K]
      Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) :=
  TensorProduct.map (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁)
    (TensorProduct.map (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃))

noncomputable def pad3 :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) :=
  TensorProduct.map iota (TensorProduct.map iota iota)

theorem pad3_injective :
    Function.Injective (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _) :=
  TensorProduct.map_injective_of_flat_flat _ _ iota_injective
    (TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective)

theorem spAct_levi_comp_pad3 (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃) :
    spAct (levi P₁) (levi P₂) (levi P₃) ∘ₗ (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _)
      = (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _) ∘ₗ glAct P₁ P₂ P₃ := by
  simp only [spAct, pad3, glAct, ← TensorProduct.map_comp, levi_comp_iota]

theorem padded_of_gl (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) (h : glAct P₁ P₂ P₃ A = B) :
    spAct (levi P₁) (levi P₂) (levi P₃) (pad3 A) = pad3 B := by
  have := DFunLike.congr_fun (spAct_levi_comp_pad3 P₁ P₂ P₃) A
  simpa [h] using this

noncomputable def braid2 (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) ≃ₗ[K] U₂ ⊗[K] (U₁ ⊗[K] U₃) :=
  (TensorProduct.assoc K U₁ U₂ U₃).symm ≪≫ₗ
    TensorProduct.congr (TensorProduct.comm K U₁ U₂) (LinearEquiv.refl K U₃) ≪≫ₗ
    TensorProduct.assoc K U₂ U₁ U₃

noncomputable def braid3 (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) ≃ₗ[K] U₃ ⊗[K] (U₁ ⊗[K] U₂) :=
  (TensorProduct.assoc K U₁ U₂ U₃).symm ≪≫ₗ TensorProduct.comm K (U₁ ⊗[K] U₂) U₃

theorem braid2_natural (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃) :
    (braid2 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) ∘ₗ (braid2 K U₁ U₂ U₃).toLinearMap :=
  TensorProduct.ext_threefold' fun x y z => by simp [braid2]

theorem braid2_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid2 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₂ (TensorProduct.map f₁ f₃) (braid2 K U₁ U₂ U₃ T) :=
  DFunLike.congr_fun (braid2_natural f₁ f₂ f₃) T

theorem braid3_natural (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃) :
    (braid3 K W₁ W₂ W₃).toLinearMap ∘ₗ TensorProduct.map f₁ (TensorProduct.map f₂ f₃)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) ∘ₗ (braid3 K U₁ U₂ U₃).toLinearMap :=
  TensorProduct.ext_threefold' fun x y z => by simp [braid3]

theorem braid3_map (f₁ : U₁ →ₗ[K] W₁) (f₂ : U₂ →ₗ[K] W₂) (f₃ : U₃ →ₗ[K] W₃)
    (T : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    braid3 K W₁ W₂ W₃ (TensorProduct.map f₁ (TensorProduct.map f₂ f₃) T)
      = TensorProduct.map f₃ (TensorProduct.map f₁ f₂) (braid3 K U₁ U₂ U₃ T) :=
  DFunLike.congr_fun (braid3_natural f₁ f₂ f₃) T

variable [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃]

omit [FiniteDimensional K U₁] [FiniteDimensional K U₃] in

theorem pad3_mode2_reflect
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₂ : U₂ ≃ₗ[K] U₂, ∀ u ∈ msupp (braid2 K U₁ U₂ U₃ A),
      g₂ (iota u) = iota (P₂ u) := by
  let j₁₃ : U₁ ⊗[K] U₃ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₃ :=
    TensorProduct.map iota iota
  let k₁₃ : Hyp K U₁ ⊗[K] Hyp K U₃ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₃ :=
    TensorProduct.map (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃)
  have hj₁₃ : Function.Injective j₁₃ := by
    dsimp [j₁₃]
    exact TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  have hk₁₃ : Function.Injective k₁₃ := by
    dsimp [k₁₃]
    exact TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₃.injective
  have hAB₂ :
      TensorProduct.map (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) k₁₃
          (TensorProduct.map (iota : U₂ →ₗ[K] Hyp K U₂) j₁₃
            (braid2 K U₁ U₂ U₃ A)) =
        TensorProduct.map (iota : U₂ →ₗ[K] Hyp K U₂) j₁₃
          (braid2 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid2 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃)) hAB
    simpa only [spAct, pad3, j₁₃, k₁₃, braid2_map] using hb
  let S : Submodule K U₂ :=
    msupp (K := K) (V := U₂) (X := U₁ ⊗[K] U₃) (braid2 K U₁ U₂ U₃ A)
  let T : Submodule K U₂ :=
    msupp (K := K) (V := U₂) (X := U₁ ⊗[K] U₃) (braid2 K U₁ U₂ U₃ B)
  have hrig :
      (S.map (iota : U₂ →ₗ[K] Hyp K U₂)).map
          (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) =
        T.map (iota : U₂ →ₗ[K] Hyp K U₂) := by
    have hmap := msupp_map (K := K) (V := Hyp K U₂) (W := Hyp K U₂)
      (X := Hyp K U₁ ⊗[K] Hyp K U₃) (Y := Hyp K U₁ ⊗[K] Hyp K U₃)
      (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) hk₁₃
      (TensorProduct.map (iota : U₂ →ₗ[K] Hyp K U₂) j₁₃
        (braid2 K U₁ U₂ U₃ A))
    rw [msupp_map (K := K) (V := U₂) (W := Hyp K U₂)
      (X := U₁ ⊗[K] U₃) (Y := Hyp K U₁ ⊗[K] Hyp K U₃)
      (iota : U₂ →ₗ[K] Hyp K U₂) hj₁₃
      (braid2 K U₁ U₂ U₃ A)] at hmap
    change (S.map (iota : U₂ →ₗ[K] Hyp K U₂)).map
      (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) = T.map iota
    rw [← hmap, hAB₂,
      msupp_map (K := K) (V := U₂) (W := Hyp K U₂)
        (X := U₁ ⊗[K] U₃) (Y := Hyp K U₁ ⊗[K] Hyp K U₃)
        (iota : U₂ →ₗ[K] Hyp K U₂) hj₁₃
        (braid2 K U₁ U₂ U₃ B)]
  set e : S ≃ₗ[K] T :=
    (Submodule.equivMapOfInjective iota iota_injective S) ≪≫ₗ
      (Submodule.equivMapOfInjective (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) g₂.injective
        (S.map iota)) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrig) ≪≫ₗ
      (Submodule.equivMapOfInjective iota iota_injective T).symm with he
  obtain ⟨P₂, hP₂⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P₂, fun u hu => ?_⟩
  have hcoe : iota ((e ⟨u, hu⟩ : T) : U₂) = g₂ (iota u) := by
    rw [he]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.map_equivMapOfInjective_symm_apply iota iota_injective T]
    simp [Submodule.coe_equivMapOfInjective_apply]
  rw [← hcoe, hP₂ ⟨u, hu⟩]

omit [FiniteDimensional K U₁] [FiniteDimensional K U₂] in

theorem pad3_mode3_reflect
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₃ : U₃ ≃ₗ[K] U₃, ∀ u ∈ msupp (braid3 K U₁ U₂ U₃ A),
      g₃ (iota u) = iota (P₃ u) := by
  let j₁₂ : U₁ ⊗[K] U₂ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₂ :=
    TensorProduct.map iota iota
  let k₁₂ : Hyp K U₁ ⊗[K] Hyp K U₂ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₂ :=
    TensorProduct.map (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂)
  have hj₁₂ : Function.Injective j₁₂ := by
    dsimp [j₁₂]
    exact TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  have hk₁₂ : Function.Injective k₁₂ := by
    dsimp [k₁₂]
    exact TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₂.injective
  have hAB₃ :
      TensorProduct.map (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) k₁₂
          (TensorProduct.map (iota : U₃ →ₗ[K] Hyp K U₃) j₁₂
            (braid3 K U₁ U₂ U₃ A)) =
        TensorProduct.map (iota : U₃ →ₗ[K] Hyp K U₃) j₁₂
          (braid3 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid3 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃)) hAB
    simpa only [spAct, pad3, j₁₂, k₁₂, braid3_map] using hb
  let S : Submodule K U₃ :=
    msupp (K := K) (V := U₃) (X := U₁ ⊗[K] U₂) (braid3 K U₁ U₂ U₃ A)
  let T : Submodule K U₃ :=
    msupp (K := K) (V := U₃) (X := U₁ ⊗[K] U₂) (braid3 K U₁ U₂ U₃ B)
  have hrig :
      (S.map (iota : U₃ →ₗ[K] Hyp K U₃)).map
          (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) =
        T.map (iota : U₃ →ₗ[K] Hyp K U₃) := by
    have hmap := msupp_map (K := K) (V := Hyp K U₃) (W := Hyp K U₃)
      (X := Hyp K U₁ ⊗[K] Hyp K U₂) (Y := Hyp K U₁ ⊗[K] Hyp K U₂)
      (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) hk₁₂
      (TensorProduct.map (iota : U₃ →ₗ[K] Hyp K U₃) j₁₂
        (braid3 K U₁ U₂ U₃ A))
    rw [msupp_map (K := K) (V := U₃) (W := Hyp K U₃)
      (X := U₁ ⊗[K] U₂) (Y := Hyp K U₁ ⊗[K] Hyp K U₂)
      (iota : U₃ →ₗ[K] Hyp K U₃) hj₁₂
      (braid3 K U₁ U₂ U₃ A)] at hmap
    change (S.map (iota : U₃ →ₗ[K] Hyp K U₃)).map
      (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) = T.map iota
    rw [← hmap, hAB₃,
      msupp_map (K := K) (V := U₃) (W := Hyp K U₃)
        (X := U₁ ⊗[K] U₂) (Y := Hyp K U₁ ⊗[K] Hyp K U₂)
        (iota : U₃ →ₗ[K] Hyp K U₃) hj₁₂
        (braid3 K U₁ U₂ U₃ B)]
  set e : S ≃ₗ[K] T :=
    (Submodule.equivMapOfInjective iota iota_injective S) ≪≫ₗ
      (Submodule.equivMapOfInjective (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) g₃.injective
        (S.map iota)) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrig) ≪≫ₗ
      (Submodule.equivMapOfInjective iota iota_injective T).symm with he
  obtain ⟨P₃, hP₃⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P₃, fun u hu => ?_⟩
  have hcoe : iota ((e ⟨u, hu⟩ : T) : U₃) = g₃ (iota u) := by
    rw [he]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.map_equivMapOfInjective_symm_apply iota iota_injective T]
    simp [Submodule.coe_equivMapOfInjective_apply]
  rw [← hcoe, hP₃ ⟨u, hu⟩]

omit [FiniteDimensional K U₂] [FiniteDimensional K U₃] in

theorem pad3_mode1_reflect
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₁ : U₁ ≃ₗ[K] U₁, ∀ u ∈ msupp A, g₁ (iota u) = iota (P₁ u) := by
  let j₂₃ : U₂ ⊗[K] U₃ →ₗ[K] Hyp K U₂ ⊗[K] Hyp K U₃ :=
    TensorProduct.map iota iota
  let k₂₃ : Hyp K U₂ ⊗[K] Hyp K U₃ →ₗ[K] Hyp K U₂ ⊗[K] Hyp K U₃ :=
    TensorProduct.map (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃)
  have hj₂₃ : Function.Injective j₂₃ := by
    dsimp [j₂₃]
    exact TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  have hk₂₃ : Function.Injective k₂₃ := by
    dsimp [k₂₃]
    exact TensorProduct.map_injective_of_flat_flat _ _ g₂.injective g₃.injective
  have hAB₁ :
      TensorProduct.map (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) k₂₃
          (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁) j₂₃ A) =
        TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁) j₂₃ B := by
    simpa only [spAct, pad3, j₂₃, k₂₃] using hAB
  let S : Submodule K U₁ :=
    msupp (K := K) (V := U₁) (X := U₂ ⊗[K] U₃) A
  let T : Submodule K U₁ :=
    msupp (K := K) (V := U₁) (X := U₂ ⊗[K] U₃) B
  have hrig :
      (S.map (iota : U₁ →ₗ[K] Hyp K U₁)).map
          (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) =
        T.map (iota : U₁ →ₗ[K] Hyp K U₁) := by
    have hmap := msupp_map (K := K) (V := Hyp K U₁) (W := Hyp K U₁)
      (X := Hyp K U₂ ⊗[K] Hyp K U₃) (Y := Hyp K U₂ ⊗[K] Hyp K U₃)
      (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) hk₂₃
      (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁) j₂₃ A)
    rw [msupp_map (K := K) (V := U₁) (W := Hyp K U₁)
      (X := U₂ ⊗[K] U₃) (Y := Hyp K U₂ ⊗[K] Hyp K U₃)
      (iota : U₁ →ₗ[K] Hyp K U₁) hj₂₃ A] at hmap
    change (S.map (iota : U₁ →ₗ[K] Hyp K U₁)).map
      (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) = T.map iota
    rw [← hmap, hAB₁,
      msupp_map (K := K) (V := U₁) (W := Hyp K U₁)
        (X := U₂ ⊗[K] U₃) (Y := Hyp K U₂ ⊗[K] Hyp K U₃)
        (iota : U₁ →ₗ[K] Hyp K U₁) hj₂₃ B]
  set e : S ≃ₗ[K] T :=
    (Submodule.equivMapOfInjective iota iota_injective S) ≪≫ₗ
      (Submodule.equivMapOfInjective (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) g₁.injective
        (S.map iota)) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrig) ≪≫ₗ
      (Submodule.equivMapOfInjective iota iota_injective T).symm with he
  obtain ⟨P₁, hP₁⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P₁, fun u hu => ?_⟩
  have hcoe : iota ((e ⟨u, hu⟩ : T) : U₁) = g₁ (iota u) := by
    rw [he]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.map_equivMapOfInjective_symm_apply iota iota_injective T]
    simp [Submodule.coe_equivMapOfInjective_apply]
  rw [← hcoe, hP₁ ⟨u, hu⟩]

theorem pad3_mode1_substitute
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₁ : U₁ ≃ₗ[K] U₁,
      TensorProduct.map (iota ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map ((g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) ∘ₗ iota)
            ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)) A =
        TensorProduct.map ((g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) ∘ₗ iota)
          (TensorProduct.map ((g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) ∘ₗ iota)
            ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)) A := by
  obtain ⟨P₁, hP₁⟩ := pad3_mode1_reflect A B g₁ g₂ g₃ hAB
  let w : SupportLiftWitness A (iota : U₁ →ₗ[K] Hyp K U₁)
      (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) := ⟨P₁, hP₁⟩
  let m₂₃ : U₂ ⊗[K] U₃ →ₗ[K] Hyp K U₂ ⊗[K] Hyp K U₃ :=
    TensorProduct.map ((g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) ∘ₗ iota)
      ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)
  refine ⟨w.P, ?_⟩
  have hsub := substitute_of_supportLiftWitness
    (K := K) (U := U₁) (H := Hyp K U₁) (X := U₂ ⊗[K] U₃)
    (Z := Hyp K U₂ ⊗[K] Hyp K U₃) A iota
    (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) w m₂₃
  simpa only [m₂₃] using hsub

theorem pad3_mode2_substitute
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₂ : U₂ ≃ₗ[K] U₂, ∀ m₁ : U₁ →ₗ[K] Hyp K U₁,
      TensorProduct.map m₁
          (TensorProduct.map (iota ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)) A =
        TensorProduct.map m₁
          (TensorProduct.map ((g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) ∘ₗ iota)
            ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)) A := by
  obtain ⟨P₂, hP₂⟩ := pad3_mode2_reflect A B g₁ g₂ g₃ hAB
  let w : SupportLiftWitness (braid2 K U₁ U₂ U₃ A)
      (iota : U₂ →ₗ[K] Hyp K U₂) (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) :=
    ⟨P₂, hP₂⟩
  refine ⟨w.P, fun m₁ => ?_⟩
  apply (braid2 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃)).injective
  rw [braid2_map, braid2_map]
  let m₁₃ : U₁ ⊗[K] U₃ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₃ :=
    TensorProduct.map m₁ ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)
  have hsub := substitute_of_supportLiftWitness
    (K := K) (U := U₂) (H := Hyp K U₂) (X := U₁ ⊗[K] U₃)
    (Z := Hyp K U₁ ⊗[K] Hyp K U₃) (braid2 K U₁ U₂ U₃ A) iota
    (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) w m₁₃
  simpa only [m₁₃] using hsub

theorem pad3_mode3_substitute
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ P₃ : U₃ ≃ₗ[K] U₃,
      ∀ (m₁ : U₁ →ₗ[K] Hyp K U₁) (m₂ : U₂ →ₗ[K] Hyp K U₂),
      TensorProduct.map m₁ (TensorProduct.map m₂ (iota ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A =
        TensorProduct.map m₁
          (TensorProduct.map m₂ ((g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota)) A := by
  obtain ⟨P₃, hP₃⟩ := pad3_mode3_reflect A B g₁ g₂ g₃ hAB
  let w : SupportLiftWitness (braid3 K U₁ U₂ U₃ A)
      (iota : U₃ →ₗ[K] Hyp K U₃) (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) :=
    ⟨P₃, hP₃⟩
  refine ⟨w.P, fun m₁ m₂ => ?_⟩
  apply (braid3 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃)).injective
  rw [braid3_map, braid3_map]
  let m₁₂ : U₁ ⊗[K] U₂ →ₗ[K] Hyp K U₁ ⊗[K] Hyp K U₂ :=
    TensorProduct.map m₁ m₂
  have hsub := substitute_of_supportLiftWitness
    (K := K) (U := U₃) (H := Hyp K U₃) (X := U₁ ⊗[K] U₂)
    (Z := Hyp K U₁ ⊗[K] Hyp K U₂) (braid3 K U₁ U₂ U₃ A) iota
    (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) w m₁₂
  simpa only [m₁₂] using hsub

omit [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃] in

theorem pad3_cancel_substituted
    (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (h : TensorProduct.map (iota ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (iota ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (iota ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A = pad3 B) :
    glAct P₁ P₂ P₃ A = B := by
  apply (pad3_injective (K := K) (U₁ := U₁) (U₂ := U₂) (U₃ := U₃))
  have hnorm :
      (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K]
        Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃)) ∘ₗ glAct P₁ P₂ P₃ =
        TensorProduct.map (iota ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (iota ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (iota ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) := by
    simp only [pad3, glAct, ← TensorProduct.map_comp]
  calc
    pad3 (glAct P₁ P₂ P₃ A) =
        TensorProduct.map (iota ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (iota ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (iota ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A := by
      simpa only [LinearMap.comp_apply] using DFunLike.congr_fun hnorm A
    _ = pad3 B := h

theorem gl_of_padded
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃)
    (hAB : spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :
    ∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃),
      glAct P₁ P₂ P₃ A = B := by
  obtain ⟨P₁, h₁⟩ := pad3_mode1_substitute A B g₁ g₂ g₃ hAB
  obtain ⟨P₂, h₂⟩ := pad3_mode2_substitute A B g₁ g₂ g₃ hAB
  obtain ⟨P₃, h₃⟩ := pad3_mode3_substitute A B g₁ g₂ g₃ hAB
  let p₁ : U₁ →ₗ[K] Hyp K U₁ := iota ∘ₗ (P₁ : U₁ →ₗ[K] U₁)
  let p₂ : U₂ →ₗ[K] Hyp K U₂ := iota ∘ₗ (P₂ : U₂ →ₗ[K] U₂)
  let p₃ : U₃ →ₗ[K] Hyp K U₃ := iota ∘ₗ (P₃ : U₃ →ₗ[K] U₃)
  let a₁ : U₁ →ₗ[K] Hyp K U₁ :=
    (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁) ∘ₗ iota
  let a₂ : U₂ →ₗ[K] Hyp K U₂ :=
    (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) ∘ₗ iota
  let a₃ : U₃ →ₗ[K] Hyp K U₃ :=
    (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃) ∘ₗ iota
  have h₂' : TensorProduct.map p₁ (TensorProduct.map p₂ a₃) A =
      TensorProduct.map p₁ (TensorProduct.map a₂ a₃) A := by
    simpa only [p₁, p₂, a₂, a₃] using h₂ p₁
  have h₃' : TensorProduct.map p₁ (TensorProduct.map p₂ p₃) A =
      TensorProduct.map p₁ (TensorProduct.map p₂ a₃) A := by
    simpa only [p₁, p₂, p₃, a₃] using h₃ p₁ p₂
  have h₁' : TensorProduct.map p₁ (TensorProduct.map a₂ a₃) A =
      TensorProduct.map a₁ (TensorProduct.map a₂ a₃) A := by
    simpa only [p₁, a₁, a₂, a₃] using h₁
  have h₀ : TensorProduct.map a₁ (TensorProduct.map a₂ a₃) A = pad3 B := by
    have hnorm :
        (spAct g₁ g₂ g₃ :
          Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) →ₗ[K]
            Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃)) ∘ₗ
            (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K]
              Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃)) =
          TensorProduct.map a₁ (TensorProduct.map a₂ a₃) := by
      simp only [spAct, pad3, a₁, a₂, a₃, ← TensorProduct.map_comp]
    have heval := DFunLike.congr_fun hnorm A
    exact heval.symm.trans hAB
  refine ⟨P₁, P₂, P₃, pad3_cancel_substituted P₁ P₂ P₃ A B ?_⟩
  simpa only [p₁, p₂, p₃] using h₃'.trans (h₂'.trans (h₁'.trans h₀))

def PaddingReflects (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃]
    [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃] : Prop :=
  ∀ (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃),
    spAct g₁ g₂ g₃ (pad3 A) = pad3 B →
      ∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B

theorem padding_reflects : PaddingReflects K U₁ U₂ U₃ := by
  intro A B g₁ g₂ g₃ hAB
  exact gl_of_padded A B g₁ g₂ g₃ hAB

theorem gl_iff_padded_of_reflection
    (hOpen : PaddingReflects K U₁ U₂ U₃) (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B) ↔
      (∃ (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
        (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃), IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
          spAct g₁ g₂ g₃ (pad3 A) = pad3 B) := by
  constructor
  · rintro ⟨P₁, P₂, P₃, hP⟩
    exact ⟨levi P₁, levi P₂, levi P₃, levi_isSymplectic P₁, levi_isSymplectic P₂,
      levi_isSymplectic P₃, padded_of_gl P₁ P₂ P₃ A B hP⟩
  · rintro ⟨g₁, g₂, g₃, -, -, -, hg⟩
    exact hOpen A B g₁ g₂ g₃ hg

theorem gl_iff_padded (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B) ↔
      (∃ (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
        (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃), IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
          spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :=
  gl_iff_padded_of_reflection (padding_reflects (K := K) (U₁ := U₁)
    (U₂ := U₂) (U₃ := U₃)) A B

end

section

open scoped BigOperators

abbrev CoordHyp (K : Type*) (n : ℕ) := (Fin n → K) × (Fin n → K)

def coordHyperForm {K : Type*} [Field K] {n : ℕ} (x y : CoordHyp K n) : K :=
  ∑ i : Fin n, (y.2 i * x.1 i - x.2 i * y.1 i)

def diagOneRev {K : Type*} {n : ℕ} (x : CoordHyp K n) : CoordHyp K n :=
  (x.1, fun i => x.2 i.rev)

def revLinearEquiv (K : Type*) [Field K] (n : ℕ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl

def diagOneRevLinearEquiv (K : Type*) [Field K] (n : ℕ) :
    CoordHyp K n ≃ₗ[K] CoordHyp K n :=
  (LinearEquiv.refl K (Fin n → K)).prodCongr (revLinearEquiv K n)

@[simp] theorem diagOneRev_fst {K : Type*} {n : ℕ} (x : CoordHyp K n) :
    (diagOneRev x).1 = x.1 := rfl

@[simp] theorem diagOneRev_snd_apply {K : Type*} {n : ℕ} (x : CoordHyp K n) (i : Fin n) :
    (diagOneRev x).2 i = x.2 i.rev := rfl

@[simp] theorem diagOneRevLinearEquiv_apply {K : Type*} [Field K] {n : ℕ}
    (x : CoordHyp K n) : diagOneRevLinearEquiv K n x = diagOneRev x := rfl

noncomputable def dualCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Module.Dual K (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (Pi.basisFun K (Fin n)).dualBasis.equivFun

@[simp] theorem dualCoordEquiv_apply (K : Type*) [Field K] (n : ℕ)
    (f : Module.Dual K (Fin n → K)) (i : Fin n) :
    dualCoordEquiv K n f i = f (Pi.single i 1) := by
  simp [dualCoordEquiv]

theorem dual_eval_sum (K : Type*) [Field K] (n : ℕ)
    (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    (∑ i : Fin n, f (Pi.single i 1) * x i) = f x := by
  let b := Pi.basisFun K (Fin n)
  have h := DFunLike.congr_fun (b.sum_dual_apply_smul_coord f) x
  simpa [b, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.equivFun_apply] using h

noncomputable def hypCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Hyp K (Fin n → K) ≃ₗ[K] CoordHyp K n :=
  (LinearEquiv.refl K (Fin n → K)).prodCongr (dualCoordEquiv K n)

@[simp] theorem hypCoordEquiv_apply (K : Type*) [Field K] (n : ℕ)
    (x : Hyp K (Fin n → K)) :
    hypCoordEquiv K n x = (x.1, dualCoordEquiv K n x.2) := rfl

theorem hypCoordEquiv_isometry (K : Type*) [Field K] (n : ℕ)
    (x y : Hyp K (Fin n → K)) :
    coordHyperForm (hypCoordEquiv K n x) (hypCoordEquiv K n y) = omegaH x y := by
  simp only [coordHyperForm, hypCoordEquiv_apply, dualCoordEquiv_apply,
    Finset.sum_sub_distrib]
  rw [dual_eval_sum, dual_eval_sum]
  rfl

noncomputable def standardCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Hyp K (Fin n → K) ≃ₗ[K] CoordHyp K n :=
  hypCoordEquiv K n ≪≫ₗ diagOneRevLinearEquiv K n

@[simp] theorem standardCoordEquiv_iota (K : Type*) [Field K] (n : ℕ)
    (u : Fin n → K) :
    standardCoordEquiv K n (iota u) = (u, 0) := by
  simp only [standardCoordEquiv, LinearEquiv.trans_apply, hypCoordEquiv_apply,
    iota_apply, map_zero]
  change diagOneRev (u, 0) = (u, 0)
  ext <;> simp [diagOneRev]

end

universe u

structure ReductionSystem (Problem : Type u) where
  reduces : Problem → Problem → Prop
  refl : ∀ X, reduces X X
  trans : ∀ {X Y Z}, reduces X Y → reduces Y Z → reduces X Z

section

variable {Problem : Type u} (R : ReductionSystem Problem)

def problemClass (B : Problem) : Set Problem := {X | R.reduces X B}

theorem problemClass_mono {A B : Problem} (hAB : R.reduces A B) :
    (problemClass R) A ⊆ (problemClass R) B := by
  intro X hXA
  exact R.trans hXA hAB

theorem problemClass_eq_of_reduces_both {A B : Problem}
    (hAB : R.reduces A B) (hBA : R.reduces B A) :
    (problemClass R) A = (problemClass R) B := by
  apply Set.Subset.antisymm
  · exact (problemClass_mono R) hAB
  · exact (problemClass_mono R) hBA

end

end

end

section

section

abbrev ModeIndex (n : ℕ) := Sum (Fin n) (Fin n)

def coordPad3 {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) :
    ModeIndex n₁ → ModeIndex n₂ → ModeIndex n₃ → K
  | Sum.inl i, Sum.inl j, Sum.inl k => A i j k
  | _, _, _ => 0

@[simp] theorem coordPad3_inl {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i j k) :
    coordPad3 A (Sum.inl i) (Sum.inl j) (Sum.inl k) = A i j k := rfl

@[simp] theorem coordPad3_inr₁ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i : Fin n₁) (j) (k) :
    coordPad3 A (Sum.inr i) j k = 0 := rfl

@[simp] theorem coordPad3_inr₂ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i) (j : Fin n₂) (k) :
    coordPad3 A i (Sum.inr j) k = 0 := by cases i <;> rfl

@[simp] theorem coordPad3_inr₃ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i) (j) (k : Fin n₃) :
    coordPad3 A i j (Sum.inr k) = 0 := by cases i <;> cases j <;> rfl

end

end

section

section
open Matrix

universe u

/-- An orbit decision problem with a finite coordinate type at each size. -/
structure CoordProblem (K : Type u) where
  Idx : ℕ → Type
  fin : ∀ n, Fintype (Idx n)
  Rel : ∀ n, (Idx n → K) → (Idx n → K) → Prop

attribute [instance] CoordProblem.fin

inductive Src (I : Type) | coord (i : I) | zero | one | negOne

def evalSource {K : Type u} [Zero K] [One K] [Neg K] {I : Type} (A : I → K) : Src I → K
  | Src.coord i => A i
  | Src.zero => 0
  | Src.one => 1
  | Src.negOne => -1

/-- A reduction whose output entries copy input entries or use constants 0, 1, and -1,
with a polynomial bound on the total number of output coordinates. -/
structure Projection {K : Type u} [Zero K] [One K] [Neg K] (P Q : CoordProblem K) where
  size : ℕ → ℕ
  src : ∀ n, Q.Idx (size n) → Src (P.Idx n)
  polyBound : ∃ c k : ℕ, ∀ n, Fintype.card (Q.Idx (size n)) ≤ c * (Fintype.card (P.Idx n) + 1) ^ k
  correct : ∀ n (A B : P.Idx n → K),
    P.Rel n A B ↔ Q.Rel (size n) (fun j => (evalSource A (src n j))) (fun j => (evalSource B (src n j)))

section

variable {K : Type u} [Zero K] [One K] [Neg K]

def identityProjection (P : CoordProblem K) : Projection P P where
  size := id
  src := fun _ i => Src.coord i
  polyBound := ⟨1, 1, fun n => by simp⟩
  correct := fun _ _ _ => Iff.rfl

def composeSources {I J : Type} (f : J → Src I) : Src J → Src I
  | Src.coord j => f j
  | Src.zero => Src.zero
  | Src.one => Src.one
  | Src.negOne => Src.negOne

theorem composeSources_eval {I J : Type} (f : J → Src I) (A : I → K) (s : Src J) :
    (evalSource A (composeSources f s)) = (evalSource (fun j => (evalSource A (f j))) s) := by
  cases s <;> rfl

theorem polynomialCompositionBound (c₁ k₁ c₂ k₂ N : ℕ) (hN : 1 ≤ N) (M : ℕ) (hM : M ≤ c₁ * N ^ k₁) :
    c₂ * (M + 1) ^ k₂ ≤ c₂ * (c₁ + 1) ^ k₂ * (N ^ k₁) ^ k₂ := by
  have h1 : M + 1 ≤ (c₁ + 1) * N ^ k₁ := by
    have : 1 ≤ N ^ k₁ := Nat.one_le_pow _ _ hN
    nlinarith
  calc c₂ * (M + 1) ^ k₂ ≤ c₂ * ((c₁ + 1) * N ^ k₁) ^ k₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = c₂ * (c₁ + 1) ^ k₂ * (N ^ k₁) ^ k₂ := by rw [mul_pow]; ring

def composeProjections {P Q R : CoordProblem K} (r₁ : Projection P Q) (r₂ : Projection Q R) : Projection P R where
  size := fun n => r₂.size (r₁.size n)
  src := fun n i => composeSources (r₁.src n) (r₂.src (r₁.size n) i)
  polyBound := by
    obtain ⟨c₁, k₁, h₁⟩ := r₁.polyBound
    obtain ⟨c₂, k₂, h₂⟩ := r₂.polyBound
    refine ⟨c₂ * (c₁ + 1) ^ k₂, k₁ * k₂, fun n => ?_⟩
    have hN : 1 ≤ Fintype.card (P.Idx n) + 1 := Nat.le_add_left 1 _
    have := polynomialCompositionBound c₁ k₁ c₂ k₂ (Fintype.card (P.Idx n) + 1) hN
      (Fintype.card (Q.Idx (r₁.size n))) (h₁ n)
    calc Fintype.card (R.Idx (r₂.size (r₁.size n)))
        ≤ c₂ * (Fintype.card (Q.Idx (r₁.size n)) + 1) ^ k₂ := h₂ _
      _ ≤ c₂ * (c₁ + 1) ^ k₂ * ((Fintype.card (P.Idx n) + 1) ^ k₁) ^ k₂ := this
      _ = c₂ * (c₁ + 1) ^ k₂ * (Fintype.card (P.Idx n) + 1) ^ (k₁ * k₂) := by rw [← pow_mul]
  correct := by
    intro n A B
    rw [r₁.correct n A B, r₂.correct (r₁.size n)]
    simp only [composeSources_eval]

end

def projectionSystem (K : Type u) [Zero K] [One K] [Neg K] :
    ReductionSystem (CoordProblem K) where
  reduces := fun P Q => Nonempty (Projection P Q)
  refl := fun P => ⟨identityProjection P⟩
  trans := fun ⟨r₁⟩ ⟨r₂⟩ => ⟨(composeProjections r₁) r₂⟩

section

variable (K : Type u) [Field K]

def act3 {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K) :
    Fin n × Fin n × Fin n → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

def GL3TI : CoordProblem K where
  Idx := fun n => Fin n × Fin n × Fin n
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ P Q R : Matrix (Fin n) (Fin n) K,
    IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act3 K P Q R A = B

def stdJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

def IsSymplecticMat {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Prop :=
  gᵀ * stdJ K n * g = stdJ K n

def act3D {n : ℕ} (P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (A : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

def Sp3TI : CoordProblem K where
  Idx := fun n => (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
    IsSymplecticMat K P ∧ IsSymplecticMat K Q ∧ IsSymplecticMat K R ∧ act3D K P Q R A = B

theorem stdJ_mul_neg_self (n : ℕ) : stdJ K n * (-(stdJ K n)) = 1 := by
  unfold stdJ
  rw [Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem isUnit_det_stdJ (n : ℕ) : IsUnit (stdJ K n).det := by
  have h := congrArg Matrix.det (stdJ_mul_neg_self K n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact ⟨Units.mkOfMulEqOne _ _ h, rfl⟩

theorem isUnit_of_isSymplecticMat {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hg : IsSymplecticMat K g) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hu : IsUnit (g.det * (stdJ K n).det * g.det) := by rw [h]; exact isUnit_det_stdJ K n
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)

end

end

end

section

section

open Matrix
open TensorProduct Module

universe u

variable {K : Type u} [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable abbrev e (ι : Type) [Fintype ι] [DecidableEq ι] : Module.Basis ι K (ι → K) :=
  Pi.basisFun K ι

noncomputable def tb (ι : Type) [Fintype ι] [DecidableEq ι] :
    Module.Basis (ι × ι × ι) K ((ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K))) :=
  (e ι).tensorProduct ((e ι).tensorProduct (e ι))

theorem tb_apply (i j k : ι) :
    tb ι (i, j, k) = (e ι i) ⊗ₜ[K] ((e ι j) ⊗ₜ[K] (e ι k)) := by
  simp [tb, Module.Basis.tensorProduct_apply]

noncomputable def toTensor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (ι × ι × ι → K) ≃ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  (Finsupp.linearEquivFunOnFinite K K (ι × ι × ι)).symm.trans (tb ι).repr.symm

theorem toTensor_apply (A : ι × ι × ι → K) :
    toTensor ι A = ∑ x, A x • tb ι x := by
  simp only [toTensor, LinearEquiv.trans_apply]
  rw [Module.Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply]
  simp [Finsupp.sum_fintype]

def actι (P Q R : Matrix ι ι K) (A : ι × ι × ι → K) : ι × ι × ι → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

theorem act3D_eq_actι {n : ℕ} (P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (A : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    act3D K P Q R A = actι P Q R A := rfl

noncomputable def glActMat (P Q R : Matrix ι ι K) :
    (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) →ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  TensorProduct.map (Matrix.toLin' P) (TensorProduct.map (Matrix.toLin' Q) (Matrix.toLin' R))

theorem repr_toTensor (A : ι × ι × ι → K) (x : ι × ι × ι) :
    (tb ι).repr (toTensor ι A) x = A x := by
  simp [toTensor]

theorem repr_toLin'_basis (P : Matrix ι ι K) (i a : ι) :
    (e ι).repr (Matrix.toLin' P (e ι i)) a = P a i := by
  simp [Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]

theorem repr_glActMat_tb (P Q R : Matrix ι ι K) (i j k a b c : ι) :
    (tb ι).repr (glActMat P Q R (tb ι (i, j, k))) (a, b, c) = P a i * Q b j * R c k := by
  rw [tb_apply]
  simp only [glActMat, TensorProduct.map_tmul, tb]
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [repr_toLin'_basis, smul_eq_mul]
  ring

theorem toTensor_actι (P Q R : Matrix ι ι K) (A : ι × ι × ι → K) :
    toTensor ι (actι P Q R A) = glActMat P Q R (toTensor ι A) := by
  apply (tb ι).repr.injective
  ext ⟨a, b, c⟩
  rw [repr_toTensor]
  conv_rhs => rw [toTensor_apply, map_sum, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [actι, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [repr_glActMat_tb]
  ring

noncomputable def linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) : (ι → K) ≃ₗ[K] (ι → K) :=
  Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P ((Matrix.isUnit_iff_isUnit_det P).mp hP))

theorem coe_linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) :
    (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' P :=
  Matrix.toLinearEquiv'_apply P _

theorem linEquivOfIsUnit_apply (P : Matrix ι ι K) (hP : IsUnit P) (x : ι → K) :
    linEquivOfIsUnit P hP x = P *ᵥ x := by
  change (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) x = _
  rw [coe_linEquivOfIsUnit, Matrix.toLin'_apply]

theorem isUnit_toMatrix' (f : (ι → K) ≃ₗ[K] (ι → K)) :
    IsUnit (LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K))) := by
  have h₁ : LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) *
      LinearMap.toMatrix' (f.symm : (ι → K) →ₗ[K] (ι → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have h₂ : LinearMap.toMatrix' (f.symm : (ι → K) →ₗ[K] (ι → K)) *
      LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

theorem toMatrix'_mulVec (f : (ι → K) ≃ₗ[K] (ι → K)) (x : ι → K) :
    LinearMap.toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) *ᵥ x = f x := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem glAct_toTensor_iff (A B : ι × ι × ι → K) :
    (∃ P Q R : Matrix ι ι K, IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ actι P Q R A = B) ↔
      ∃ (e₁ e₂ e₃ : (ι → K) ≃ₗ[K] (ι → K)), glAct e₁ e₂ e₃ (toTensor ι A) = toTensor ι B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    refine ⟨linEquivOfIsUnit P hP, linEquivOfIsUnit Q hQ, linEquivOfIsUnit R hR, ?_⟩
    rw [← h, toTensor_actι]
    simp only [glAct, glActMat, coe_linEquivOfIsUnit]
  · rintro ⟨e₁, e₂, e₃, h⟩
    refine ⟨LinearMap.toMatrix' (e₁ : (ι → K) →ₗ[K] (ι → K)),
      LinearMap.toMatrix' (e₂ : (ι → K) →ₗ[K] (ι → K)),
      LinearMap.toMatrix' (e₃ : (ι → K) →ₗ[K] (ι → K)),
      isUnit_toMatrix' e₁, isUnit_toMatrix' e₂, isUnit_toMatrix' e₃, ?_⟩
    apply (toTensor ι).injective
    rw [toTensor_actι, ← h]
    simp only [glAct, glActMat, Matrix.toLin'_toMatrix']

end

end

section

section

open Matrix

universe u v

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {t : ℕ}
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]

def rep (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    BRep K γ β (Fin t) (fun s => ColIdx s → K) (fun b => RowIdx b → K) :=
  ⟨fun k s b => Matrix.toLin' (X k b s)⟩

theorem rep_f (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) (k : Fin t) (s : γ)
    (b : β) : (rep (RowIdx := RowIdx) (ColIdx := ColIdx) X).f k s b = Matrix.toLin' (X k b s) := rfl

theorem isUnit_det_transpose_inv {I : Type} [Fintype I] [DecidableEq I] (Q : Matrix I I K)
    (hQ : IsUnit Q.det) : IsUnit ((Qᵀ)⁻¹).det :=
  Matrix.isUnit_nonsing_inv_det Qᵀ (by rwa [Matrix.det_transpose])

theorem simEquiv_of_matrices (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (hP : ∀ b, IsUnit (P b).det) (hQ : ∀ s, IsUnit (Q s).det)
    (h : ∀ k b s, Y k b s = P b * X k b s * (Q s)ᵀ) : RepresentationSimilarity
        (rep
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) X)
        (rep
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) Y) := by
  refine ⟨fun s => linEquivOfIsUnit ((Q s)ᵀ)⁻¹
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_transpose_inv (Q s) (hQ s))),
    fun b => linEquivOfIsUnit (P b) ((Matrix.isUnit_iff_isUnit_det _).mpr (hP b)),
    fun k s b => ?_⟩
  rw [rep_f, rep_f, coe_linEquivOfIsUnit, coe_linEquivOfIsUnit, ← Matrix.toLin'_mul,
    ← Matrix.toLin'_mul, h k b s, Matrix.mul_assoc (P b * X k b s),
    Matrix.mul_nonsing_inv (Q s)ᵀ (by rw [Matrix.det_transpose]; exact hQ s), Matrix.mul_one]

theorem matrices_of_simEquiv (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (h : RepresentationSimilarity
        (rep
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) X)
        (rep
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) Y)) :
    ∃ (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K),
      (∀ b, IsUnit (P b).det) ∧ (∀ s, IsUnit (Q s).det) ∧
      ∀ k b s, Y k b s = P b * X k b s * (Q s)ᵀ := by
  obtain ⟨Ps, Qb, hc⟩ := h
  refine ⟨fun b => LinearMap.toMatrix' (Qb b : (RowIdx b → K) →ₗ[K] (RowIdx b → K)),
    fun s => ((LinearMap.toMatrix' (Ps s : (ColIdx s → K) →ₗ[K] (ColIdx s → K)))⁻¹)ᵀ,
    fun b => (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_toMatrix' (Qb b)),
    fun s => ?_, fun k b s => ?_⟩
  · rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_toMatrix' (Ps s)))
  · have hM : IsUnit (LinearMap.toMatrix' (Ps s : (ColIdx s → K) →ₗ[K] (ColIdx s → K))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_toMatrix' (Ps s))
    have e := congrArg LinearMap.toMatrix' (hc k s b)
    rw [rep_f, rep_f, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at e

    rw [Matrix.transpose_transpose]
    show Y k b s = LinearMap.toMatrix' (Qb b : (RowIdx b → K) →ₗ[K] (RowIdx b → K)) * X k b s *
      (LinearMap.toMatrix' (Ps s : (ColIdx s → K) →ₗ[K] (ColIdx s → K)))⁻¹
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]

section

variable {DR : β → Type} {DC : γ → Type}
variable [∀ b, Fintype (DR b)] [∀ b, DecidableEq (DR b)] [∀ s, Fintype (DC s)] [∀ s, DecidableEq (DC s)]

def padded (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    Fin t → ∀ (b : β) (s : γ), Matrix (DR b ⊕ RowIdx b) (DC s ⊕ ColIdx s) K :=
  fun k b s => Matrix.fromBlocks (Δ k b s) 0 0 (X k b s)

theorem simEquiv_rep_padded_dsum (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    RepresentationSimilarity
        (rep
        (RowIdx := fun b => DR b ⊕ RowIdx b)
        (ColIdx := fun s => DC s ⊕ ColIdx s)
        (padded
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) Δ X)) ((directSumRepresentation
        (rep
        (RowIdx := DR)
        (ColIdx := DC) Δ))
        (rep
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) X)) := by
  refine ⟨fun s => LinearEquiv.sumArrowLequivProdArrow (DC s) (ColIdx s) K K,
    fun b => LinearEquiv.sumArrowLequivProdArrow (DR b) (RowIdx b) K K, fun k s b => ?_⟩
  refine LinearMap.ext fun v => ?_
  refine Prod.ext ?_ ?_
  · funext i
    simp [rep, padded, directSumRepresentation, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    rfl
  · funext i
    simp [rep, padded, directSumRepresentation, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    rfl

theorem simEquiv_symm {V V' : γ → Type v} {W W' : β → Type v}
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ b, AddCommGroup (W b)] [∀ b, Module K (W b)]
    [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ b, AddCommGroup (W' b)] [∀ b, Module K (W' b)]
    {A : BRep K γ β (Fin t) V W} {B : BRep K γ β (Fin t) V' W'} (h : RepresentationSimilarity A B) : RepresentationSimilarity B A := by
  rw [similarity_iff_equiv] at h ⊢
  exact ⟨h.some.symm⟩

theorem simEquiv_trans {V V' V'' : γ → Type v} {W W' W'' : β → Type v}
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ b, AddCommGroup (W b)] [∀ b, Module K (W b)]
    [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ b, AddCommGroup (W' b)] [∀ b, Module K (W' b)]
    [∀ s, AddCommGroup (V'' s)] [∀ s, Module K (V'' s)] [∀ b, AddCommGroup (W'' b)]
    [∀ b, Module K (W'' b)]
    {A : BRep K γ β (Fin t) V W} {B : BRep K γ β (Fin t) V' W'} {C : BRep K γ β (Fin t) V'' W''}
    (h₁ : RepresentationSimilarity A B) (h₂ : RepresentationSimilarity B C) : RepresentationSimilarity A C := by
  rw [similarity_iff_equiv] at h₁ h₂ ⊢
  exact ⟨h₁.some ≪≫ₗ h₂.some⟩

theorem matrix_block_cancel (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (P' : ∀ b, Matrix (DR b ⊕ RowIdx b) (DR b ⊕ RowIdx b) K)
    (Q' : ∀ s, Matrix (DC s ⊕ ColIdx s) (DC s ⊕ ColIdx s) K)
    (hP' : ∀ b, IsUnit (P' b).det) (hQ' : ∀ s, IsUnit (Q' s).det)
    (h : ∀ k b s, padded
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) Δ Y k b s = P' b * padded
        (RowIdx := RowIdx)
        (ColIdx := ColIdx) Δ X k b s * (Q' s)ᵀ) :
    ∃ (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K),
      (∀ b, IsUnit (P b).det) ∧ (∀ s, IsUnit (Q s).det) ∧
      ∀ k b s, Y k b s = P b * X k b s * (Q s)ᵀ := by
  have h₁ : RepresentationSimilarity
      (rep
      (RowIdx := fun b => DR b ⊕ RowIdx b)
      (ColIdx := fun s => DC s ⊕ ColIdx s)
      (padded
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) Δ X))
      (rep
      (RowIdx := fun b => DR b ⊕ RowIdx b)
      (ColIdx := fun s => DC s ⊕ ColIdx s)
      (padded
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) Δ Y)) :=
    simEquiv_of_matrices
        (RowIdx := fun b => DR b ⊕ RowIdx b)
        (ColIdx := fun s => DC s ⊕ ColIdx s) _ _ P' Q' hP' hQ' h
  have h₂ : RepresentationSimilarity ((directSumRepresentation
      (rep
      (RowIdx := DR)
      (ColIdx := DC) Δ))
      (rep
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) X)) ((directSumRepresentation
      (rep
      (RowIdx := DR)
      (ColIdx := DC) Δ))
      (rep
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) Y)) :=
    simEquiv_trans (simEquiv_symm (simEquiv_rep_padded_dsum Δ X))
      (simEquiv_trans h₁ (simEquiv_rep_padded_dsum Δ Y))
  have h₃ : RepresentationSimilarity
      (rep
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) X)
      (rep
      (RowIdx := RowIdx)
      (ColIdx := ColIdx) Y) :=
    bipartite_cancel (K := K) (Src := γ) (Snk := β) (Arr := Fin t)
      (DV := fun s => DC s → K) (DW := fun b => DR b → K)
      (V := fun s => ColIdx s → K) (W := fun b => RowIdx b → K)
      (V' := fun s => ColIdx s → K) (W' := fun b => RowIdx b → K)
          (rep
          (RowIdx := DR)
          (ColIdx := DC) Δ)
          (rep
          (RowIdx := RowIdx)
          (ColIdx := ColIdx) X)
          (rep
          (RowIdx := RowIdx)
          (ColIdx := ColIdx) Y) h₂
  exact matrices_of_simEquiv X Y h₃

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}
variable (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

def recon (X : PArr K β γ RowIdx ColIdx t) (R : Matrix (Fin t) (Fin t) K) :
    PArr K β γ RowIdx ColIdx t :=
  fun k b s => ∑ k', R k k' • X k' b s

theorem sum_smul_padArr (X : PArr K β γ RowIdx ColIdx t) (R : Matrix (Fin t) (Fin t) K)
    (k : Fin t) (b : β) (s : γ) :
    ∑ k', R k k' • padPartitioned b₀ c₀ r str X k' b s =
      Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (fun j => R k j) b s) 0 0 (recon X R k b s) := by
  simp only [padPartitioned, sum_smul_fromBlocks, sum_smul_gadgetBlock, recon]

theorem fromBlocks_reindex {R₁ R₁' C₁ C₁' R₂ C₂ : Type} (e₁ : R₁ ≃ R₁') (e₂ : C₁ ≃ C₁')
    (G : Matrix R₁ C₁ K) (M : Matrix R₂ C₂ K) :
    Matrix.fromBlocks (Matrix.reindex e₁ e₂ G) 0 0 M =
      Matrix.reindex (e₁.sumCongr (Equiv.refl R₂)) (e₂.sumCongr (Equiv.refl C₂))
        (Matrix.fromBlocks G 0 0 M) := by
  ext (i | i) (j | j) <;> simp

theorem gadgetBlock_eq_reindex (c : Fin t → K) :
    gadgetBlock b₀ c₀ r str c b₀ c₀ =
      Matrix.reindex (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm
        (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm (gadget (K := K) r str c) := by
  ext p jq
  rfl

theorem rank_padBlock (c : Fin t → K) (T : Finset (Fin n))
    (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0) (M : Matrix (RowIdx b₀) (ColIdx c₀) K) :
    (Matrix.fromBlocks (gadgetBlock b₀ c₀ r str c b₀ c₀) 0 0 M).rank =
      (∑ γ ∈ T, 2 ^ (γ : ℕ) * r) + M.rank := by
  rw [gadgetBlock_eq_reindex, fromBlocks_reindex, Matrix.rank_reindex]
  exact rank_padded r str c T hT M

theorem hT_ind (k : Fin t) :
    ∀ γ, γ ∈ ({str k} : Finset (Fin n)) ↔ ∃ j, str j = γ ∧ ind (K := K) k j ≠ 0 := by
  intro γ
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨k, rfl, by simp [ind]⟩
  · rintro ⟨j, hj, hne⟩
    by_cases hjk : j = k
    · rw [← hj, hjk]
    · exact absurd (by simp [ind, hjk]) hne

theorem gadgetBlock_recon (R : Matrix (Fin t) (Fin t) K) (hR : IsUnit R.det)
    (hbd : IsBlockDiag str R) (k : Fin t) (b : β) (s : γ) :
    gadgetBlock b₀ c₀ r str (fun j => R k j) b s =
      gadgetBlock b₀ c₀ r str (ind k) b s * (kronS (n := n) c₀ r Rᵀ s)ᵀ := by
  have h := gadgetBlock_mul_kronS b₀ c₀ r str R hR hbd k b s
  have hW : (kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ * (kronS (n := n) c₀ r Rᵀ s)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, kronS_mul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul R hR,
      Matrix.transpose_one, kronS_one, Matrix.transpose_one]
  calc gadgetBlock b₀ c₀ r str (fun j => R k j) b s
      = gadgetBlock b₀ c₀ r str (fun j => R k j) b s *
          ((kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ * (kronS (n := n) c₀ r Rᵀ s)ᵀ) := by
        rw [hW, Matrix.mul_one]
    _ = gadgetBlock b₀ c₀ r str (fun j => R k j) b s * (kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ *
          (kronS (n := n) c₀ r Rᵀ s)ᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = gadgetBlock b₀ c₀ r str (ind k) b s * (kronS (n := n) c₀ r Rᵀ s)ᵀ :=
        congrArg (fun M => M * (kronS (n := n) c₀ r Rᵀ s)ᵀ) h

theorem isUnit_det_kronS_transpose (R : Matrix (Fin t) (Fin t) K) (hR : IsUnit R.det) (s : γ) :
    IsUnit (kronS (n := n) c₀ r Rᵀ s).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_kronS (n := n) c₀ r Rᵀ (by rwa [Matrix.det_transpose]) s)

theorem partition_deletion (hr : ∀ b, Fintype.card (RowIdx b) < r)
    (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔
      BlockEquiv (fun _ : Fin t => (0 : Fin 1)) (padPartitioned b₀ c₀ r str X) (padPartitioned b₀ c₀ r str Y) := by
  refine ⟨blockEquiv_pad b₀ c₀ r str X Y, fun h => ?_⟩
  classical
  obtain ⟨P', Q', R, hP', hQ', hR, -, hXY⟩ := h
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) (hr b₀)

  have hslice : ∀ k b s, padPartitioned b₀ c₀ r str Y k b s =
      P' b * Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (fun j => R k j) b s) 0 0 (recon X R k b s) *
        (Q' s)ᵀ := by
    intro k b s
    rw [hXY k b s, ← sum_smul_padArr]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

  let T : Fin t → Finset (Fin n) := fun k => Finset.univ.filter fun γ => ∃ j, str j = γ ∧ R k j ≠ 0
  have hT : ∀ k γ, γ ∈ T k ↔ ∃ j, str j = γ ∧ Rᵀ j k ≠ 0 := by
    intro k γ
    simp [T, Matrix.transpose_apply]
  have hrank : ∀ k, (∑ γ ∈ T k, 2 ^ (γ : ℕ) * r) + (recon X R k b₀ c₀).rank =
      2 ^ (str k : ℕ) * r + (Y k b₀ c₀).rank := by
    intro k
    have e := congrArg Matrix.rank (hslice k b₀ c₀)
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact hQ' c₀),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP' b₀)] at e
    rw [padPartitioned, rank_padBlock b₀ c₀ r str (ind k) {str k} (hT_ind str k),
      rank_padBlock b₀ c₀ r str (fun j => R k j) (T k) (fun γ => by
        rw [hT k γ]; simp [Matrix.transpose_apply])] at e
    exact e.symm
  have hbd : IsBlockDiag str R := by
    intro i j hij
    have := S_blockDiagonal_of_ranks str r hr0 Rᵀ T hT
      (fun k => (Y k b₀ c₀).rank) (fun k => (recon X R k b₀ c₀).rank)
      (fun k => rank_lt_of_card_rows_lt (hr b₀) _)
      (fun k => rank_lt_of_card_rows_lt (hr b₀) _)
      hrank j i (Ne.symm hij)
    simpa [Matrix.transpose_apply] using this

  let Q'' : ∀ s, Matrix (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t) s)
      (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t) s) K :=
    fun s => Q' s * Matrix.fromBlocks (kronS (n := n) c₀ r Rᵀ s) 0 0 (1 : Matrix (ColIdx s) (ColIdx s) K)
  have hQ'' : ∀ s, IsUnit (Q'' s).det := by
    intro s
    simp only [Q'']
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    exact (hQ' s).mul (isUnit_det_kronS_transpose c₀ r R hR s)
  have hsim : ∀ k b s, padPartitioned b₀ c₀ r str Y k b s =
      P' b * padPartitioned b₀ c₀ r str (recon X R) k b s * (Q'' s)ᵀ := by
    intro k b s
    have hpad : padPartitioned b₀ c₀ r str (recon X R) k b s *
        Matrix.fromBlocks (kronS (n := n) c₀ r Rᵀ s)ᵀ 0 0 (1 : Matrix (ColIdx s) (ColIdx s) K) =
        Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind k) b s * (kronS (n := n) c₀ r Rᵀ s)ᵀ) 0 0
          (recon X R k b s) := by
      rw [padPartitioned, Matrix.fromBlocks_multiply]
      simp
      all_goals rfl
    rw [hslice k b s, gadgetBlock_recon b₀ c₀ r str R hR hbd, ← hpad]
    simp only [Q'', Matrix.transpose_mul, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.mul_assoc]
    all_goals rfl

  obtain ⟨P, Q, hP, hQ, hYC⟩ := matrix_block_cancel
    (DR := fun b => GRb b₀ (n := n) r b) (DC := fun s => GCs c₀ (n := n) (t := t) r s)
    (fun k b s => gadgetBlock b₀ c₀ r str (ind k) b s) (recon X R) Y P' Q'' hP' hQ'' hsim

  refine ⟨P, Q, R, hP, hQ, hR, hbd, fun k b s => ?_⟩
  rw [hYC k b s, recon]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

section

variable {I₁ I₂ I₃ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
  [Fintype I₃] [DecidableEq I₃]

theorem sum3_swap_outer {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (g : A → B → C → K) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ b, ∑ a, ∑ c, g a b c :=
  Finset.sum_comm

theorem sum3_swap_inner {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (g : A → B → C → K) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

def act (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K)
    (X : I₁ × I₂ × I₃ → K) : I₁ × I₂ × I₃ → K :=
  fun x => ∑ i', ∑ j', ∑ k', P₁ x.1 i' * P₂ x.2.1 j' * P₃ x.2.2 k' * X (i', j', k')

def FlatEquiv {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂] [DecidableEq ρ₃]
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) : Prop :=
  ∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
    IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧
    IsBlockDiag blk₁ P₁ ∧ IsBlockDiag blk₂ P₂ ∧ IsBlockDiag blk₃ P₃ ∧
    act P₁ P₂ P₃ X = Y

def rot (X : I₁ × I₂ × I₃ → K) : I₂ × I₃ × I₁ → K :=
  fun x => X (x.2.2, x.1, x.2.1)

theorem act_rot (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K)
    (X : I₁ × I₂ × I₃ → K) :
    act P₂ P₃ P₁ (rot X) = rot (act P₁ P₂ P₃ X) := by
  funext x
  simp only [act, rot]
  rw [sum3_swap_inner, sum3_swap_outer]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem flatEquiv_rot {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂] [DecidableEq ρ₃]
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv blk₁ blk₂ blk₃ X Y ↔ FlatEquiv blk₂ blk₃ blk₁ (rot X) (rot Y) := by
  constructor
  · rintro ⟨P₁, P₂, P₃, h₁, h₂, h₃, b₁, b₂, b₃, hXY⟩
    exact ⟨P₂, P₃, P₁, h₂, h₃, h₁, b₂, b₃, b₁, by rw [act_rot, hXY]⟩
  · rintro ⟨P₂, P₃, P₁, h₂, h₃, h₁, b₂, b₃, b₁, hXY⟩
    refine ⟨P₁, P₂, P₃, h₁, h₂, h₃, b₁, b₂, b₃, ?_⟩
    rw [act_rot] at hXY
    funext x
    have := congrFun hXY (x.2.1, x.2.2, x.1)
    simpa [rot] using this

end

section

variable {β : Type} [Fintype β] [DecidableEq β] {RowIdx : β → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]

def flatStratumBlock (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K) (b : β) : Matrix (RowIdx b) (RowIdx b) K :=
  Matrix.of fun i i' => M ⟨b, i⟩ ⟨b, i'⟩

theorem isBlockDiag_blockDiagonal' (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) :
    IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) (Matrix.blockDiagonal' P) := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  exact Matrix.blockDiagonal'_apply_ne P i i' h

theorem blockDiagonal'_blockOf (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K)
    (hM : IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) M) :
    Matrix.blockDiagonal' (flatStratumBlock M) = M := by
  ext ⟨b, i⟩ ⟨b', i'⟩
  by_cases h : b = b'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, flatStratumBlock]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, hM ⟨b, i⟩ ⟨b', i'⟩ h]

theorem isUnit_det_blockDiagonal' (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K)
    (hP : ∀ b, IsUnit (P b).det) : IsUnit (Matrix.blockDiagonal' P).det := by
  refine (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨Matrix.blockDiagonal' P,
    Matrix.blockDiagonal' (fun b => (P b)⁻¹), ?_, ?_⟩, rfl⟩
  · rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext b
    exact Matrix.mul_nonsing_inv _ (hP b)
  · rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext b
    exact Matrix.nonsing_inv_mul _ (hP b)

theorem isUnit_det_flatStratumBlock (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K)
    (hM : IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) M) (hu : IsUnit M.det) (b : β) :
    IsUnit (flatStratumBlock M b).det := by
  have hleft : flatStratumBlock M b * flatStratumBlock M⁻¹ b = 1 := by
    ext i i'
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) ⟨b, i⟩) ⟨b, i'⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma] at h
    rw [Finset.sum_eq_single b] at h
    · simpa [flatStratumBlock, Matrix.mul_apply, Matrix.one_apply] using h
    · intro b' _ hb'
      exact Finset.sum_eq_zero fun i'' _ => by rw [hM ⟨b, i⟩ ⟨b', i''⟩ (Ne.symm hb'), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : flatStratumBlock M⁻¹ b * flatStratumBlock M b = 1 := by
    ext i i'
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul M hu) ⟨b, i⟩) ⟨b, i'⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma] at h
    rw [Finset.sum_eq_single b] at h
    · simpa [flatStratumBlock, Matrix.mul_apply, Matrix.one_apply] using h
    · intro b' _ hb'
      exact Finset.sum_eq_zero fun i'' _ => by rw [hM ⟨b', i''⟩ ⟨b, i'⟩ hb', mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hleft, hright⟩, rfl⟩

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

def flatten (X : PArr K β γ RowIdx ColIdx t) : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K :=
  fun x => X x.2.2 x.1.1 x.2.1.1 x.1.2 x.2.1.2

theorem sliceEq_apply (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K)
    (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K) (R : Matrix (Fin t) (Fin t) K)
    (X : PArr K β γ RowIdx ColIdx t) (k : Fin t) (b : β) (s : γ) (i : RowIdx b) (j : ColIdx s) :
    (∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) i j =
      ∑ i', ∑ j', ∑ k', P b i i' * Q s j j' * R k k' * X k' b s i' j' := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum3_swap_inner, sum3_swap_outer, sum3_swap_inner]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem act_blockDiagonal'_apply (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K)
    (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K) (R : Matrix (Fin t) (Fin t) K)
    (X : PArr K β γ RowIdx ColIdx t) (b : β) (i : RowIdx b) (s : γ) (j : ColIdx s) (k : Fin t) :
    act (Matrix.blockDiagonal' P) (Matrix.blockDiagonal' Q) R (flatten X) (⟨b, i⟩, ⟨s, j⟩, k) =
      ∑ i', ∑ j', ∑ k', P b i i' * Q s j j' * R k k' * X k' b s i' j' := by
  simp only [act, flatten]
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Fintype.sum_sigma, Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun k' _ => ?_
      simp [Matrix.blockDiagonal'_apply_eq]
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun k' _ => ?_
      rw [Matrix.blockDiagonal'_apply_ne Q j j' (Ne.symm hs')]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ =>
      Finset.sum_eq_zero fun k' _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne P i i' (Ne.symm hb')]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem blockEquiv_iff_flat (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔
      FlatEquiv (Sigma.fst : (Σ b, RowIdx b) → β) (Sigma.fst : (Σ s, ColIdx s) → γ) str
        (flatten X) (flatten Y) := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, hbd, hXY⟩
    refine ⟨Matrix.blockDiagonal' P, Matrix.blockDiagonal' Q, R, isUnit_det_blockDiagonal' P hP,
      isUnit_det_blockDiagonal' Q hQ, hR, isBlockDiag_blockDiagonal' P,
      isBlockDiag_blockDiagonal' Q, hbd, ?_⟩
    funext ⟨⟨b, i⟩, ⟨s, j⟩, k⟩
    rw [act_blockDiagonal'_apply]
    simp only [flatten]
    rw [hXY k b s, sliceEq_apply]
  · rintro ⟨P₁, P₂, R, h₁, h₂, hR, b₁, b₂, hbd, hXY⟩
    refine ⟨flatStratumBlock P₁, flatStratumBlock P₂, R, isUnit_det_flatStratumBlock P₁ b₁ h₁, isUnit_det_flatStratumBlock P₂ b₂ h₂,
      hR, hbd, fun k b s => ?_⟩
    ext i j
    rw [sliceEq_apply]
    have h := congrFun hXY (⟨b, i⟩, ⟨s, j⟩, k)
    rw [← blockDiagonal'_blockOf P₁ b₁, ← blockDiagonal'_blockOf P₂ b₂,
      act_blockDiagonal'_apply] at h
    simp only [flatten] at h
    exact h.symm

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

section

variable {I₁ I₂ I₃ J₁ J₂ J₃ : Type}
variable [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype I₃] [DecidableEq I₃]
variable [Fintype J₁] [DecidableEq J₁] [Fintype J₂] [DecidableEq J₂] [Fintype J₃] [DecidableEq J₃]

def reindex3 (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃) (X : I₁ × I₂ × I₃ → K) :
    J₁ × J₂ × J₃ → K :=
  fun y => X (e₁.symm y.1, e₂.symm y.2.1, e₃.symm y.2.2)

theorem reindex3_symm_reindex3 (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃)
    (X : I₁ × I₂ × I₃ → K) :
    reindex3 e₁.symm e₂.symm e₃.symm (reindex3 e₁ e₂ e₃ X) = X := by
  funext x
  simp [reindex3]

theorem sum3_reindex (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃) (g : I₁ → I₂ → I₃ → K) :
    ∑ a : J₁, ∑ b : J₂, ∑ c : J₃, g (e₁.symm a) (e₂.symm b) (e₃.symm c) =
      ∑ a : I₁, ∑ b : I₂, ∑ c : I₃, g a b c := by
  calc ∑ a : J₁, ∑ b : J₂, ∑ c : J₃, g (e₁.symm a) (e₂.symm b) (e₃.symm c)
      = ∑ a : J₁, ∑ b : J₂, ∑ c : I₃, g (e₁.symm a) (e₂.symm b) c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Equiv.sum_comp e₃.symm (fun c => g (e₁.symm a) (e₂.symm b) c)
    _ = ∑ a : J₁, ∑ b : I₂, ∑ c : I₃, g (e₁.symm a) b c :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp e₂.symm (fun b => ∑ c, g (e₁.symm a) b c)
    _ = ∑ a : I₁, ∑ b : I₂, ∑ c : I₃, g a b c :=
        Equiv.sum_comp e₁.symm (fun a => ∑ b, ∑ c, g a b c)

theorem act_reindex3 (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃)
    (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K) (X : I₁ × I₂ × I₃ → K) :
    act (Matrix.reindex e₁ e₁ P₁) (Matrix.reindex e₂ e₂ P₂) (Matrix.reindex e₃ e₃ P₃)
        (reindex3 e₁ e₂ e₃ X) =
      reindex3 e₁ e₂ e₃ (act P₁ P₂ P₃ X) := by
  funext y
  simp only [act, reindex3, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact sum3_reindex e₁ e₂ e₃ fun a b c =>
    P₁ (e₁.symm y.1) a * P₂ (e₂.symm y.2.1) b * P₃ (e₃.symm y.2.2) c * X (a, b, c)

theorem isBlockDiag_reindex {ρ : Type} [DecidableEq ρ] (e : I₁ ≃ J₁) (blk : I₁ → ρ)
    (P : Matrix I₁ I₁ K) (h : IsBlockDiag blk P) :
    IsBlockDiag (blk ∘ e.symm) (Matrix.reindex e e P) := by
  intro i j hij
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact h _ _ hij

theorem flatEquiv_reindex3_mp {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂] [DecidableEq ρ₃]
    (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃)
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K)
    (h : FlatEquiv blk₁ blk₂ blk₃ X Y) :
    FlatEquiv (blk₁ ∘ e₁.symm) (blk₂ ∘ e₂.symm) (blk₃ ∘ e₃.symm)
      (reindex3 e₁ e₂ e₃ X) (reindex3 e₁ e₂ e₃ Y) := by
  obtain ⟨P₁, P₂, P₃, h₁, h₂, h₃, b₁, b₂, b₃, hXY⟩ := h
  refine ⟨Matrix.reindex e₁ e₁ P₁, Matrix.reindex e₂ e₂ P₂, Matrix.reindex e₃ e₃ P₃,
    by rwa [Matrix.det_reindex_self], by rwa [Matrix.det_reindex_self],
    by rwa [Matrix.det_reindex_self], isBlockDiag_reindex e₁ blk₁ P₁ b₁,
    isBlockDiag_reindex e₂ blk₂ P₂ b₂, isBlockDiag_reindex e₃ blk₃ P₃ b₃, ?_⟩
  rw [act_reindex3, hXY]

theorem flatEquiv_reindex3 {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂] [DecidableEq ρ₃]
    (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃)
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv blk₁ blk₂ blk₃ X Y ↔
      FlatEquiv (blk₁ ∘ e₁.symm) (blk₂ ∘ e₂.symm) (blk₃ ∘ e₃.symm)
        (reindex3 e₁ e₂ e₃ X) (reindex3 e₁ e₂ e₃ Y) := by
  refine ⟨flatEquiv_reindex3_mp e₁ e₂ e₃ blk₁ blk₂ blk₃ X Y, fun h => ?_⟩
  have h' := flatEquiv_reindex3_mp e₁.symm e₂.symm e₃.symm _ _ _ _ _ h
  rw [reindex3_symm_reindex3, reindex3_symm_reindex3] at h'
  have hb₁ : (blk₁ ∘ e₁.symm) ∘ e₁.symm.symm = blk₁ := by funext i; simp
  have hb₂ : (blk₂ ∘ e₂.symm) ∘ e₂.symm.symm = blk₂ := by funext i; simp
  have hb₃ : (blk₃ ∘ e₃.symm) ∘ e₃.symm.symm = blk₃ := by funext i; simp
  rwa [hb₁, hb₂, hb₃] at h'

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

def unflatten (X : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) : PArr K β γ RowIdx ColIdx t :=
  fun k b s i j => X (⟨b, i⟩, ⟨s, j⟩, k)

theorem flatten_unflatten (X : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) :
    flatten (unflatten X) = X := by
  funext ⟨⟨b, i⟩, ⟨s, j⟩, k⟩
  rfl

theorem flatEquiv_iff_blockEquiv (str : Fin t → Fin n)
    (X Y : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) :
    FlatEquiv (Sigma.fst : (Σ b, RowIdx b) → β) (Sigma.fst : (Σ s, ColIdx s) → γ) str X Y ↔
      BlockEquiv str (unflatten X) (unflatten Y) := by
  rw [blockEquiv_iff_flat, flatten_unflatten, flatten_unflatten]

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

section

variable {I₁ I₂ I₃ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
  [Fintype I₃] [DecidableEq I₃]

theorem isBlockDiag_comp_equiv {I ρ ρ' : Type} [DecidableEq ρ] [DecidableEq ρ'] (e : ρ ≃ ρ')
    (blk : I → ρ) (M : Matrix I I K) : IsBlockDiag (e ∘ blk) M ↔ IsBlockDiag blk M := by
  constructor
  · intro h i j hij
    exact h i j fun heq => hij (e.injective heq)
  · intro h i j hij
    exact h i j fun heq => hij (congrArg e heq)

theorem flatEquiv_comp_equiv₃ {ρ₁ ρ₂ ρ₃ ρ₃' : Type} [DecidableEq ρ₁] [DecidableEq ρ₂]
    [DecidableEq ρ₃] [DecidableEq ρ₃'] (e : ρ₃ ≃ ρ₃')
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv blk₁ blk₂ blk₃ X Y ↔ FlatEquiv blk₁ blk₂ (e ∘ blk₃) X Y := by
  simp only [FlatEquiv, isBlockDiag_comp_equiv]

theorem flatEquiv_of_subsingleton {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂]
    [DecidableEq ρ₃] [Subsingleton ρ₁] [Subsingleton ρ₂] [Subsingleton ρ₃]
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv blk₁ blk₂ blk₃ X Y ↔
      ∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
        IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ X = Y := by
  constructor
  · rintro ⟨P₁, P₂, P₃, h₁, h₂, h₃, -, -, -, hXY⟩
    exact ⟨P₁, P₂, P₃, h₁, h₂, h₃, hXY⟩
  · rintro ⟨P₁, P₂, P₃, h₁, h₂, h₃, hXY⟩
    exact ⟨P₁, P₂, P₃, h₁, h₂, h₃, fun _ _ h => absurd (Subsingleton.elim _ _) h,
      fun _ _ h => absurd (Subsingleton.elim _ _) h,
      fun _ _ h => absurd (Subsingleton.elim _ _) h, hXY⟩

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {R : β → Type} {C : γ → Type}
variable [∀ b, Fintype (R b)] [∀ b, DecidableEq (R b)] [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]
variable {t : ℕ}

def eFront (t : ℕ) : Fin t ≃ Σ _ : Fin 1, Fin t where
  toFun k := ⟨0, k⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := Sigma.ext (Subsingleton.elim _ _) HEq.rfl

noncomputable def eRows (R : β → Type) [∀ b, Fintype (R b)] :
    (Σ b, R b) ≃ Fin (Fintype.card (Σ b, R b)) :=
  Fintype.equivFin _

noncomputable def rotStr (R : β → Type) [∀ b, Fintype (R b)] :
    Fin (Fintype.card (Σ b, R b)) → Fin (Fintype.card β) :=
  fun k => Fintype.equivFin β ((eRows R).symm k).1

noncomputable def rotStep (F : (Σ b, R b) × (Σ s, C s) × Fin t → K) :
    PArr K γ (Fin 1) C (fun _ => Fin t) (Fintype.card (Σ b, R b)) :=
  unflatten (reindex3 (Equiv.refl (Σ s, C s)) (eFront t) (eRows R) (rot F))

theorem rot_step (F G : (Σ b, R b) × (Σ s, C s) × Fin t → K) :
    FlatEquiv (Sigma.fst : (Σ b, R b) → β) (Sigma.fst : (Σ s, C s) → γ)
        (fun _ : Fin t => (0 : Fin 1)) F G ↔
      BlockEquiv (rotStr R) (rotStep F) (rotStep G) := by
  rw [flatEquiv_rot, flatEquiv_reindex3 (Equiv.refl (Σ s, C s)) (eFront t) (eRows R)]
  have h₁ : (Sigma.fst : (Σ s, C s) → γ) ∘ (Equiv.refl (Σ s, C s)).symm = Sigma.fst := by
    funext x; rfl
  have h₂ : (fun _ : Fin t => (0 : Fin 1)) ∘ (eFront t).symm =
      (Sigma.fst : (Σ _ : Fin 1, Fin t) → Fin 1) := funext fun _ => Subsingleton.elim _ _
  have h₃ : (Fintype.equivFin β) ∘ ((Sigma.fst : (Σ b, R b) → β) ∘ (eRows R).symm) =
      rotStr R := by
    funext k; rfl
  rw [h₁, h₂, flatEquiv_comp_equiv₃ (Fintype.equivFin β), h₃, flatEquiv_iff_blockEquiv]
  rfl

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

theorem card_lt_succ_card_sigma {β : Type} [Fintype β] (R : β → Type) [∀ b, Fintype (R b)] (b : β) :
    Fintype.card (R b) < Fintype.card (Σ b, R b) + 1 :=
  Nat.lt_succ_of_le (Fintype.card_le_of_injective (Sigma.mk b) sigma_mk_injective)

abbrev rad {β : Type} [Fintype β] (R : β → Type) [∀ b, Fintype (R b)] : ℕ :=
  Fintype.card (Σ b, R b) + 1

noncomputable def b₀ (β : Type) [Nonempty β] : β := Classical.arbitrary β

theorem delete_then_rotate {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {R : β → Type} {C : γ → Type}
    [∀ b, Fintype (R b)] [∀ b, DecidableEq (R b)] [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]
    {t m : ℕ} (b₀ : β) (c₀ : γ) (str : Fin t → Fin m) (X Y : PArr K β γ R C t) :
    BlockEquiv str X Y ↔
      BlockEquiv (rotStr (PadRow b₀ (rad R) (RowIdx := R) (n := m)))
        (rotStep (flatten (padPartitioned b₀ c₀ (rad R) str X)))
        (rotStep (flatten (padPartitioned b₀ c₀ (rad R) str Y))) := by
  rw [partition_deletion b₀ c₀ (rad R) str (fun b => card_lt_succ_card_sigma R b) X Y,
    blockEquiv_iff_flat, rot_step]

abbrev R₁ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type) (n t : ℕ)
    (c₀ : γ) : γ → Type :=
  PadCol c₀ (rad RowIdx) (ColIdx := ColIdx) (n := n) (t := t)

abbrev C₁ (t : ℕ) : Fin 1 → Type := fun _ => Fin t

abbrev t₁ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (n : ℕ) (b₀ : β) : ℕ :=
  Fintype.card (Σ b, PadRow b₀ (rad RowIdx) (RowIdx := RowIdx) (n := n) b)

noncomputable def stage1 (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    PArr K γ (Fin 1) (R₁ RowIdx ColIdx n t (b₀ γ)) (C₁ t) (t₁ RowIdx n (b₀ β)) :=
  rotStep (flatten (padPartitioned (b₀ β) (b₀ γ) (rad RowIdx) str X))

abbrev R₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type)
    [∀ s, Fintype (ColIdx s)] (n t : ℕ) (b₀ : β) (c₀ : γ) : Fin 1 → Type :=
  PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t c₀)) (ColIdx := C₁ t) (n := Fintype.card β)
    (t := t₁ RowIdx n b₀)

abbrev C₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (n : ℕ) (b₀ : β) : Fin 1 → Type :=
  fun _ => Fin (t₁ RowIdx n b₀)

abbrev t₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type)
    [∀ s, Fintype (ColIdx s)] (n t : ℕ) (c₀ : γ) : ℕ :=
  Fintype.card (Σ s, PadRow c₀ (rad (R₁ RowIdx ColIdx n t c₀)) (RowIdx := R₁ RowIdx ColIdx n t c₀)
    (n := Fintype.card β) s)

noncomputable def stage2 (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    PArr K (Fin 1) (Fin 1) (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (C₂ RowIdx n (b₀ β))
      (t₂ RowIdx ColIdx n t (b₀ γ)) :=
  rotStep (flatten (padPartitioned (b₀ γ) (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
    (rotStr (PadRow (b₀ β) (rad RowIdx) (RowIdx := RowIdx) (n := n))) (stage1 str X)))

noncomputable def T (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    (Σ b : Fin 1, PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ) b) ×
    (Σ s : Fin 1, PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ))
        s) ×
    Fin (t₂ RowIdx ColIdx n t (b₀ γ)) → K :=
  flatten (padPartitioned (0 : Fin 1) (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (rotStr (PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
      (n := Fintype.card β)))
    (stage2 str X))

theorem three_deletions (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔
      ∃ (P₁ : Matrix _ _ K) (P₂ : Matrix _ _ K) (P₃ : Matrix _ _ K),
        IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ (T str X) = T str Y := by
  rw [delete_then_rotate (b₀ β) (b₀ γ) str X Y]
  change BlockEquiv _ (stage1 str X) (stage1 str Y) ↔ _
  rw [delete_then_rotate (b₀ γ) (0 : Fin 1) _ (stage1 str X) (stage1 str Y)]
  change BlockEquiv _ (stage2 str X) (stage2 str Y) ↔ _
  rw [partition_deletion (0 : Fin 1) (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ))) _
    (fun b => card_lt_succ_card_sigma _ b), blockEquiv_iff_flat]
  exact flatEquiv_of_subsingleton Sigma.fst Sigma.fst (fun _ => (0 : Fin 1)) _ _

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

def SrcExpr {ι κ : Type} (F : (ι → K) → (κ → K)) : Prop :=
  ∀ z, ∃ s : Src ι, ∀ X, F X z = evalSource X s

theorem composeSourceExpressions {ι κ μ : Type} {F : (ι → K) → (κ → K)} {G : (κ → K) → (μ → K)}
    (hF : SrcExpr F) (hG : SrcExpr G) : SrcExpr (fun X => G (F X)) := by
  intro z
  obtain ⟨s, hs⟩ := hG z
  choose f hf using hF
  refine ⟨composeSources f s, fun X => ?_⟩
  show G (F X) z = _
  rw [hs, composeSources_eval]
  congr 1
  funext y
  exact hf y X

theorem permuteSourceExpression {ι κ κ' : Type} {F : (ι → K) → (κ → K)} (hF : SrcExpr F) (p : κ' → κ) :
    SrcExpr (fun X z => F X (p z)) :=
  fun z => hF (p z)

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

abbrev ArrayPosition (β γ : Type) (RowIdx : β → Type) (ColIdx : γ → Type) (t : ℕ) : Type :=
  Fin t × (Σ b, RowIdx b) × (Σ s, ColIdx s)

def toFun (X : PArr K β γ RowIdx ColIdx t) : ArrayPosition β γ RowIdx ColIdx t → K :=
  fun p => X p.1 p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2

def ofFun (F : ArrayPosition β γ RowIdx ColIdx t → K) : PArr K β γ RowIdx ColIdx t :=
  fun k b s i j => F (k, ⟨b, i⟩, ⟨s, j⟩)

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ} (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

theorem Ediag_zero_or_one (γ' : Fin n) (p q : GR n r) :
    Ediag (K := K) r γ' p q = 0 ∨ Ediag (K := K) r γ' p q = 1 := by
  unfold Ediag
  rw [Matrix.diagonal_apply]
  split_ifs <;> simp

theorem gadget_ind_zero_or_one (k : Fin t) (p : GR n r) (jq : Fin t × GR n r) :
    gadget (K := K) r str (ind k) p jq = 0 ∨ gadget (K := K) r str (ind k) p jq = 1 := by
  unfold gadget ind
  simp only [Matrix.of_apply]
  rcases Ediag_zero_or_one (K := K) r (str jq.1) p jq.2 with h | h <;> rw [h] <;> split_ifs <;> simp

theorem padArr_srcExpr :
    SrcExpr (fun F : ArrayPosition β γ RowIdx ColIdx t → K =>
      toFun (padPartitioned b₀ c₀ r str (ofFun F) :
        PArr K β γ (PadRow b₀ r (RowIdx := RowIdx) (n := n))
          (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t)) t)) := by
  rintro ⟨k, ⟨b, i⟩, ⟨s, j⟩⟩
  rcases i with p | i <;> rcases j with jq | j
  ·
    classical
    rcases gadget_ind_zero_or_one (K := K) r str k p.1 jq.1 with h | h
    · exact ⟨Src.zero, fun F => by
        show gadget (K := K) r str (ind k) p.1 jq.1 = _
        rw [h]; rfl⟩
    · exact ⟨Src.one, fun F => by
        show gadget (K := K) r str (ind k) p.1 jq.1 = _
        rw [h]; rfl⟩
  · exact ⟨Src.zero, fun F => rfl⟩
  · exact ⟨Src.zero, fun F => rfl⟩
  · exact ⟨Src.coord (k, ⟨b, i⟩, ⟨s, j⟩), fun F => rfl⟩

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {R : β → Type} {C : γ → Type}
variable [∀ b, Fintype (R b)] [∀ s, Fintype (C s)]
variable {t : ℕ}

theorem flatten_srcExpr :
    SrcExpr (fun F : ArrayPosition β γ R C t → K => flatten (ofFun F)) :=
  fun z => ⟨Src.coord (z.2.2, z.1, z.2.1), fun F => rfl⟩

theorem rotStep_srcExpr :
    SrcExpr (fun F : (Σ b, R b) × (Σ s, C s) × Fin t → K => toFun (rotStep F)) := by
  rintro ⟨k, ⟨s, j⟩, ⟨u, l⟩⟩
  refine ⟨Src.coord ((eRows R).symm k, ⟨s, j⟩, ((eFront t).symm ⟨u, l⟩)), fun F => ?_⟩
  rfl

end

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

theorem stage1_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : ArrayPosition β γ RowIdx ColIdx t → K => toFun (stage1 str (ofFun F))) :=
  (composeSourceExpressions (padArr_srcExpr (RowIdx := RowIdx) (ColIdx := ColIdx) (b₀ β) (b₀ γ) (rad RowIdx) str))
    ((composeSourceExpressions flatten_srcExpr) rotStep_srcExpr)

theorem stage2_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : ArrayPosition β γ RowIdx ColIdx t → K => toFun (stage2 str (ofFun F))) :=
  (composeSourceExpressions (stage1_srcExpr str))
    ((composeSourceExpressions (padArr_srcExpr (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ)) (ColIdx := C₁ t) (b₀ γ) (0 : Fin 1)
        (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
        (rotStr (PadRow (b₀ β) (rad RowIdx) (RowIdx := RowIdx) (n := n)))))
      ((composeSourceExpressions (flatten_srcExpr
          (R := PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
            (n := Fintype.card β))
          (C := PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (ColIdx := C₁ t)
            (n := Fintype.card β) (t := t₁ RowIdx n (b₀ β)))
          (t := t₁ RowIdx n (b₀ β))))
        (rotStep_srcExpr
          (R := PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
            (n := Fintype.card β))
          (C := PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (ColIdx := C₁ t)
            (n := Fintype.card β) (t := t₁ RowIdx n (b₀ β)))
          (t := t₁ RowIdx n (b₀ β)))))

theorem T_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : ArrayPosition β γ RowIdx ColIdx t → K => T str (ofFun F)) :=
  (composeSourceExpressions (stage2_srcExpr str))
    ((composeSourceExpressions (padArr_srcExpr (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (ColIdx := C₂ RowIdx n (b₀ β))
        (0 : Fin 1) (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (rotStr (PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
          (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ)) (n := Fintype.card β)))))
      (flatten_srcExpr
        (R := PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
          (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ))
        (C := PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
          (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ)))
        (t := t₂ RowIdx ColIdx n t (b₀ γ))))

end

end

end

section

section

open TensorProduct

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ H₁ H₂ H₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup H₁] [Module K H₁] [AddCommGroup H₂] [Module K H₂]
  [AddCommGroup H₃] [Module K H₃]

noncomputable def padG (ι₁ : U₁ →ₗ[K] H₁) (ι₂ : U₂ →ₗ[K] H₂) (ι₃ : U₃ →ₗ[K] H₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] H₁ ⊗[K] (H₂ ⊗[K] H₃) :=
  TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)

theorem padG_injective {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃) :
    Function.Injective (padG ι₁ ι₂ ι₃) :=
  TensorProduct.map_injective_of_flat_flat _ _ hι₁
    (TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃)

theorem padG_mode1_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    ∃ P₁ : U₁ ≃ₗ[K] U₁,
      TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₂ ι₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃
  have hk : Function.Injective
      (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₂.injective g₃.injective
  exact pad_substitute (K := K) (U := U₁) (H := H₁) (X := U₂ ⊗[K] U₃) (Y := H₂ ⊗[K] H₃)
    (Z := H₂ ⊗[K] H₃) hι₁ hj g₁.injective hk A B hAB
    (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃))

theorem padG_mode2_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B)
    (m₁ : U₁ →ₗ[K] H₁) :
    ∃ P₂ : U₂ ≃ₗ[K] U₂,
      TensorProduct.map m₁
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂)) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map m₁
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₁ ι₃) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₁ hι₃
  have hk : Function.Injective
      (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₃ : H₃ →ₗ[K] H₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₃.injective
  have hAB₂ :
      TensorProduct.map (g₂ : H₂ →ₗ[K] H₂)
          (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₂ (TensorProduct.map ι₁ ι₃) (braid2 K U₁ U₂ U₃ A)) =
        TensorProduct.map ι₂ (TensorProduct.map ι₁ ι₃) (braid2 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid2 K H₁ H₂ H₃) hAB
    simpa only [braid2_map] using hb
  obtain ⟨P₂, hP₂⟩ :=
    pad_substitute (K := K) (U := U₂) (H := H₂) (X := U₁ ⊗[K] U₃) (Y := H₁ ⊗[K] H₃)
      (Z := H₁ ⊗[K] H₃) hι₂ hj g₂.injective hk
      (braid2 K U₁ U₂ U₃ A) (braid2 K U₁ U₂ U₃ B) hAB₂
      (TensorProduct.map m₁ ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃))
  refine ⟨P₂, ?_⟩
  apply (braid2 K H₁ H₂ H₃).injective
  rw [braid2_map, braid2_map]
  exact hP₂

theorem padG_mode3_substitute [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B)
    (m₁ : U₁ →ₗ[K] H₁) (m₂ : U₂ →ₗ[K] H₂) :
    ∃ P₃ : U₃ ≃ₗ[K] U₃,
      TensorProduct.map m₁ (TensorProduct.map m₂ (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A =
        TensorProduct.map m₁ (TensorProduct.map m₂ ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A := by
  have hj : Function.Injective (TensorProduct.map ι₁ ι₂) :=
    TensorProduct.map_injective_of_flat_flat _ _ hι₁ hι₂
  have hk : Function.Injective
      (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₂ : H₂ →ₗ[K] H₂)) :=
    TensorProduct.map_injective_of_flat_flat _ _ g₁.injective g₂.injective
  have hAB₃ :
      TensorProduct.map (g₃ : H₃ →ₗ[K] H₃)
          (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁) (g₂ : H₂ →ₗ[K] H₂))
          (TensorProduct.map ι₃ (TensorProduct.map ι₁ ι₂) (braid3 K U₁ U₂ U₃ A)) =
        TensorProduct.map ι₃ (TensorProduct.map ι₁ ι₂) (braid3 K U₁ U₂ U₃ B) := by
    have hb := congrArg (braid3 K H₁ H₂ H₃) hAB
    simpa only [braid3_map] using hb
  obtain ⟨P₃, hP₃⟩ :=
    pad_substitute (K := K) (U := U₃) (H := H₃) (X := U₁ ⊗[K] U₂) (Y := H₁ ⊗[K] H₂)
      (Z := H₁ ⊗[K] H₂) hι₃ hj g₃.injective hk
      (braid3 K U₁ U₂ U₃ A) (braid3 K U₁ U₂ U₃ B) hAB₃
      (TensorProduct.map m₁ m₂)
  refine ⟨P₃, ?_⟩
  apply (braid3 K H₁ H₂ H₃).injective
  rw [braid3_map, braid3_map]
  exact hP₃

theorem padG_cancel_substituted
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (h : TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    glAct P₁ P₂ P₃ A = B := by
  apply padG_injective hι₁ hι₂ hι₃
  have hnorm :
      (padG ι₁ ι₂ ι₃ : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] H₁ ⊗[K] (H₂ ⊗[K] H₃)) ∘ₗ
          glAct P₁ P₂ P₃ =
        TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) := by
    simp only [padG, glAct, ← TensorProduct.map_comp]
  calc
    padG ι₁ ι₂ ι₃ (glAct P₁ P₂ P₃ A) =
        TensorProduct.map (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
          (TensorProduct.map (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
            (ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))) A := by
      simpa only [LinearMap.comp_apply] using DFunLike.congr_fun hnorm A
    _ = padG ι₁ ι₂ ι₃ B := h

theorem gl_of_padded_general [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K U₃]
    {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃)
    (g₁ : H₁ ≃ₗ[K] H₁) (g₂ : H₂ ≃ₗ[K] H₂) (g₃ : H₃ ≃ₗ[K] H₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (hAB : TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B) :
    ∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃),
      glAct P₁ P₂ P₃ A = B := by
  obtain ⟨P₁, h₁⟩ := padG_mode1_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
  obtain ⟨P₂, h₂⟩ := padG_mode2_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
    (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
  obtain ⟨P₃, h₃⟩ := padG_mode3_substitute hι₁ hι₂ hι₃ g₁ g₂ g₃ A B hAB
    (ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁)) (ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
  have h₀ :
      TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
          (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂) ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) A =
        TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B := by
    have hnorm :
        (TensorProduct.map (g₁ : H₁ →ₗ[K] H₁)
            (TensorProduct.map (g₂ : H₂ →ₗ[K] H₂) (g₃ : H₃ →ₗ[K] H₃))) ∘ₗ
            (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)) =
          TensorProduct.map ((g₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁)
            (TensorProduct.map ((g₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂)
              ((g₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃)) := by
      simp only [← TensorProduct.map_comp]
    have heval := DFunLike.congr_fun hnorm A
    simp only [LinearMap.comp_apply] at heval
    exact heval.symm.trans hAB
  exact ⟨P₁, P₂, P₃, padG_cancel_substituted hι₁ hι₂ hι₃ P₁ P₂ P₃ A B
    (h₃.trans (h₂.trans (h₁.trans h₀)))⟩

theorem padded_of_gl_general
    {ι₁ : U₁ →ₗ[K] H₁} {ι₂ : U₂ →ₗ[K] H₂} {ι₃ : U₃ →ₗ[K] H₃}
    (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (f₁ : H₁ ≃ₗ[K] H₁) (f₂ : H₂ ≃ₗ[K] H₂) (f₃ : H₃ ≃ₗ[K] H₃)
    (hf₁ : (f₁ : H₁ →ₗ[K] H₁) ∘ₗ ι₁ = ι₁ ∘ₗ (P₁ : U₁ →ₗ[K] U₁))
    (hf₂ : (f₂ : H₂ →ₗ[K] H₂) ∘ₗ ι₂ = ι₂ ∘ₗ (P₂ : U₂ →ₗ[K] U₂))
    (hf₃ : (f₃ : H₃ →ₗ[K] H₃) ∘ₗ ι₃ = ι₃ ∘ₗ (P₃ : U₃ →ₗ[K] U₃))
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) (h : glAct P₁ P₂ P₃ A = B) :
    TensorProduct.map (f₁ : H₁ →ₗ[K] H₁)
        (TensorProduct.map (f₂ : H₂ →ₗ[K] H₂) (f₃ : H₃ →ₗ[K] H₃))
        (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A) =
      TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) B := by
  have hcomp :
      (TensorProduct.map (f₁ : H₁ →ₗ[K] H₁)
          (TensorProduct.map (f₂ : H₂ →ₗ[K] H₂) (f₃ : H₃ →ₗ[K] H₃))) ∘ₗ
          (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)) =
        (TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)) ∘ₗ glAct P₁ P₂ P₃ := by
    simp only [glAct, ← TensorProduct.map_comp, hf₁, hf₂, hf₃]
  have := DFunLike.congr_fun hcomp A
  simp only [LinearMap.comp_apply] at this
  rw [this, h]

end

end

section

section

open TensorProduct Module

universe u

variable {K : Type u} [Field K]

section

variable {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι₃] [DecidableEq ι₃]

noncomputable def tb₃ (K : Type u) [Field K] (ι₁ ι₂ ι₃ : Type)
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃] :
    Module.Basis (ι₁ × ι₂ × ι₃) K ((ι₁ → K) ⊗[K] ((ι₂ → K) ⊗[K] (ι₃ → K))) :=
  (Pi.basisFun K ι₁).tensorProduct ((Pi.basisFun K ι₂).tensorProduct (Pi.basisFun K ι₃))

theorem tb₃_apply (i : ι₁) (j : ι₂) (k : ι₃) :
    tb₃ K ι₁ ι₂ ι₃ (i, j, k) =
      (Pi.basisFun K ι₁ i) ⊗ₜ[K] ((Pi.basisFun K ι₂ j) ⊗ₜ[K] (Pi.basisFun K ι₃ k)) := by
  simp [tb₃, Module.Basis.tensorProduct_apply]

noncomputable def toTensor₃ (K : Type u) [Field K] (ι₁ ι₂ ι₃ : Type)
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃] :
    (ι₁ × ι₂ × ι₃ → K) ≃ₗ[K] ((ι₁ → K) ⊗[K] ((ι₂ → K) ⊗[K] (ι₃ → K))) :=
  (Finsupp.linearEquivFunOnFinite K K (ι₁ × ι₂ × ι₃)).symm.trans (tb₃ K ι₁ ι₂ ι₃).repr.symm

theorem toTensor₃_apply (A : ι₁ × ι₂ × ι₃ → K) :
    toTensor₃ K ι₁ ι₂ ι₃ A = ∑ x, A x • tb₃ K ι₁ ι₂ ι₃ x := by
  simp only [toTensor₃, LinearEquiv.trans_apply]
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  simp [Finsupp.sum_fintype]

theorem repr_toTensor₃ (A : ι₁ × ι₂ × ι₃ → K) (x : ι₁ × ι₂ × ι₃) :
    (tb₃ K ι₁ ι₂ ι₃).repr (toTensor₃ K ι₁ ι₂ ι₃ A) x = A x := by
  simp [toTensor₃]

noncomputable def glActMat₃ (P : Matrix ι₁ ι₁ K) (Q : Matrix ι₂ ι₂ K) (R : Matrix ι₃ ι₃ K) :
    ((ι₁ → K) ⊗[K] ((ι₂ → K) ⊗[K] (ι₃ → K))) →ₗ[K]
      ((ι₁ → K) ⊗[K] ((ι₂ → K) ⊗[K] (ι₃ → K))) :=
  TensorProduct.map (Matrix.toLin' P) (TensorProduct.map (Matrix.toLin' Q) (Matrix.toLin' R))

theorem repr_glActMat₃_tb₃ (P : Matrix ι₁ ι₁ K) (Q : Matrix ι₂ ι₂ K) (R : Matrix ι₃ ι₃ K)
    (i a : ι₁) (j b : ι₂) (k c : ι₃) :
    (tb₃ K ι₁ ι₂ ι₃).repr (glActMat₃ P Q R (tb₃ K ι₁ ι₂ ι₃ (i, j, k))) (a, b, c) =
      P a i * Q b j * R c k := by
  rw [tb₃_apply]
  simp only [glActMat₃, TensorProduct.map_tmul, tb₃]
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [repr_toLin'_basis, smul_eq_mul]
  ring

theorem toTensor₃_act (P : Matrix ι₁ ι₁ K) (Q : Matrix ι₂ ι₂ K) (R : Matrix ι₃ ι₃ K)
    (A : ι₁ × ι₂ × ι₃ → K) :
    toTensor₃ K ι₁ ι₂ ι₃ (act P Q R A) = glActMat₃ P Q R (toTensor₃ K ι₁ ι₂ ι₃ A) := by
  apply (tb₃ K ι₁ ι₂ ι₃).repr.injective
  ext ⟨a, b, c⟩
  rw [repr_toTensor₃]
  conv_rhs => rw [toTensor₃_apply, map_sum, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [act, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [repr_glActMat₃_tb₃]
  ring

theorem glAct₃_toTensor₃_iff (A B : ι₁ × ι₂ × ι₃ → K) :
    (∃ (P : Matrix ι₁ ι₁ K) (Q : Matrix ι₂ ι₂ K) (R : Matrix ι₃ ι₃ K),
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R A = B) ↔
      ∃ (e₁ : (ι₁ → K) ≃ₗ[K] (ι₁ → K)) (e₂ : (ι₂ → K) ≃ₗ[K] (ι₂ → K))
        (e₃ : (ι₃ → K) ≃ₗ[K] (ι₃ → K)),
        glAct e₁ e₂ e₃ (toTensor₃ K ι₁ ι₂ ι₃ A) = toTensor₃ K ι₁ ι₂ ι₃ B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    refine ⟨linEquivOfIsUnit P hP, linEquivOfIsUnit Q hQ, linEquivOfIsUnit R hR, ?_⟩
    rw [← h, toTensor₃_act]
    simp only [glAct, glActMat₃, coe_linEquivOfIsUnit]
  · rintro ⟨e₁, e₂, e₃, h⟩
    refine ⟨LinearMap.toMatrix' (e₁ : (ι₁ → K) →ₗ[K] (ι₁ → K)),
      LinearMap.toMatrix' (e₂ : (ι₂ → K) →ₗ[K] (ι₂ → K)),
      LinearMap.toMatrix' (e₃ : (ι₃ → K) →ₗ[K] (ι₃ → K)),
      isUnit_toMatrix' e₁, isUnit_toMatrix' e₂, isUnit_toMatrix' e₃, ?_⟩
    apply (toTensor₃ K ι₁ ι₂ ι₃).injective
    rw [toTensor₃_act, ← h]
    simp only [glAct, glActMat₃, Matrix.toLin'_toMatrix']

end

section

variable {a b c N : ℕ}

def inc (K : Type u) [Field K] (a N : ℕ) : (Fin a → K) →ₗ[K] (Fin N → K) where
  toFun v := fun I => if h : (I : ℕ) < a then v ⟨(I : ℕ), h⟩ else 0
  map_add' u v := by
    funext I
    simp only [Pi.add_apply]
    by_cases h : (I : ℕ) < a
    · simp [h]
    · simp [h]
  map_smul' t v := by
    funext I
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    by_cases h : (I : ℕ) < a
    · simp [h]
    · simp [h]

theorem inc_apply (v : Fin a → K) (I : Fin N) :
    inc K a N v I = if h : (I : ℕ) < a then v ⟨(I : ℕ), h⟩ else 0 := rfl

def prj (K : Type u) [Field K] {a N : ℕ} (h : a ≤ N) : (Fin N → K) →ₗ[K] (Fin a → K) where
  toFun w := fun i => w (Fin.castLE h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem prj_apply (h : a ≤ N) (w : Fin N → K) (i : Fin a) :
    prj K h w i = w (Fin.castLE h i) := rfl

def cmp (K : Type u) [Field K] (a N : ℕ) : (Fin N → K) →ₗ[K] (Fin N → K) where
  toFun w := fun I => if (I : ℕ) < a then 0 else w I
  map_add' u v := by
    funext I
    simp only [Pi.add_apply]
    by_cases h : (I : ℕ) < a
    · simp [h]
    · simp [h]
  map_smul' t v := by
    funext I
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    by_cases h : (I : ℕ) < a
    · simp [h]
    · simp [h]

theorem cmp_apply (w : Fin N → K) (I : Fin N) :
    cmp K a N w I = if (I : ℕ) < a then 0 else w I := rfl

theorem prj_inc (h : a ≤ N) (v : Fin a → K) : prj K h (inc K a N v) = v := by
  funext i
  rw [prj_apply, inc_apply, dif_pos (show ((Fin.castLE h i : Fin N) : ℕ) < a by simp)]
  simp

theorem cmp_inc (v : Fin a → K) : cmp K a N (inc K a N v) = 0 := by
  funext I
  rw [cmp_apply, inc_apply]
  by_cases h : (I : ℕ) < a
  · simp [h]
  · simp [h]

theorem prj_cmp (h : a ≤ N) (w : Fin N → K) : prj K h (cmp K a N w) = 0 := by
  funext i
  rw [prj_apply, cmp_apply, if_pos (show ((Fin.castLE h i : Fin N) : ℕ) < a by simp)]
  rfl

theorem cmp_cmp (w : Fin N → K) : cmp K a N (cmp K a N w) = cmp K a N w := by
  funext I
  rw [cmp_apply, cmp_apply]
  by_cases h : (I : ℕ) < a
  · simp [h]
  · simp [h]

theorem inc_prj_add_cmp (h : a ≤ N) (w : Fin N → K) :
    inc K a N (prj K h w) + cmp K a N w = w := by
  funext I
  simp only [Pi.add_apply]
  rw [inc_apply, cmp_apply]
  by_cases hI : (I : ℕ) < a
  · rw [dif_pos hI, if_pos hI, prj_apply, add_zero]
    congr 1
  · rw [dif_neg hI, if_neg hI, zero_add]

theorem inc_injective (h : a ≤ N) : Function.Injective (inc K a N) := by
  intro u v huv
  funext i
  have h1 : prj K h (inc K a N u) = prj K h (inc K a N v) := by rw [huv]
  rw [prj_inc, prj_inc] at h1
  exact congrFun h1 i

noncomputable def extL (K : Type u) [Field K] {a N : ℕ} (h : a ≤ N)
    (e : (Fin a → K) →ₗ[K] (Fin a → K)) : (Fin N → K) →ₗ[K] (Fin N → K) :=
  (inc K a N) ∘ₗ e ∘ₗ (prj K h) + cmp K a N

theorem extL_apply (h : a ≤ N) (e : (Fin a → K) →ₗ[K] (Fin a → K)) (w : Fin N → K) :
    extL K h e w = inc K a N (e (prj K h w)) + cmp K a N w := rfl

theorem extL_comp_inc (h : a ≤ N) (e : (Fin a → K) →ₗ[K] (Fin a → K)) :
    extL K h e ∘ₗ inc K a N = inc K a N ∘ₗ e := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, extL_apply, prj_inc, cmp_inc, add_zero]

theorem extL_id (h : a ≤ N) :
    extL K h (LinearMap.id : (Fin a → K) →ₗ[K] (Fin a → K)) = LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  rw [extL_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact inc_prj_add_cmp h w

theorem extL_comp (h : a ≤ N) (e f : (Fin a → K) →ₗ[K] (Fin a → K)) :
    extL K h e ∘ₗ extL K h f = extL K h (e ∘ₗ f) := by
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.comp_apply, extL_apply, map_add, map_zero, prj_inc, prj_cmp, cmp_inc,
    cmp_cmp, add_zero, zero_add]

noncomputable def extend (h : a ≤ N) (e : (Fin a → K) ≃ₗ[K] (Fin a → K)) :
    (Fin N → K) ≃ₗ[K] (Fin N → K) :=
  LinearEquiv.ofLinearMap (extL K h (e : (Fin a → K) →ₗ[K] (Fin a → K)))
    (extL K h (e.symm : (Fin a → K) →ₗ[K] (Fin a → K)))
    (by
      rw [extL_comp]
      rw [show (e : (Fin a → K) →ₗ[K] (Fin a → K)) ∘ₗ (e.symm : (Fin a → K) →ₗ[K] (Fin a → K)) =
          LinearMap.id by ext x; simp]
      exact extL_id h)
    (by
      rw [extL_comp]
      rw [show (e.symm : (Fin a → K) →ₗ[K] (Fin a → K)) ∘ₗ (e : (Fin a → K) →ₗ[K] (Fin a → K)) =
          LinearMap.id by ext x; simp]
      exact extL_id h)

theorem coe_extend (h : a ≤ N) (e : (Fin a → K) ≃ₗ[K] (Fin a → K)) :
    ((extend h e : (Fin N → K) ≃ₗ[K] (Fin N → K)) : (Fin N → K) →ₗ[K] (Fin N → K)) =
      extL K h (e : (Fin a → K) →ₗ[K] (Fin a → K)) := rfl

theorem extend_comp_inc (h : a ≤ N) (e : (Fin a → K) ≃ₗ[K] (Fin a → K)) :
    ((extend h e : (Fin N → K) ≃ₗ[K] (Fin N → K)) : (Fin N → K) →ₗ[K] (Fin N → K)) ∘ₗ
        inc K a N = inc K a N ∘ₗ (e : (Fin a → K) →ₗ[K] (Fin a → K)) := by
  rw [coe_extend]
  exact extL_comp_inc h _

theorem inc_single (h : a ≤ N) (i : Fin a) :
    inc K a N (Pi.single i (1 : K)) = Pi.single (Fin.castLE h i) (1 : K) := by
  funext I
  rw [inc_apply]
  by_cases hI : (I : ℕ) < a
  · rw [dif_pos hI]
    simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
  · rw [dif_neg hI]
    simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    rw [if_neg (by have := i.isLt; omega)]

end

section

variable {a b c N : ℕ}

def cubeExt (K : Type u) [Field K] {a b c : ℕ} (N : ℕ) (X : Fin a × Fin b × Fin c → K) :
    Fin N × Fin N × Fin N → K :=
  fun z =>
    if h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c then
      X (⟨(z.1 : ℕ), h.1⟩, ⟨(z.2.1 : ℕ), h.2.1⟩, ⟨(z.2.2 : ℕ), h.2.2⟩)
    else 0

theorem cubeExt_apply (X : Fin a × Fin b × Fin c → K) (z : Fin N × Fin N × Fin N) :
    cubeExt K N X z =
      if h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c then
        X (⟨(z.1 : ℕ), h.1⟩, ⟨(z.2.1 : ℕ), h.2.1⟩, ⟨(z.2.2 : ℕ), h.2.2⟩)
      else 0 := rfl

theorem cubeExt_src (z : Fin N × Fin N × Fin N) :
    ∃ s : Src (Fin a × Fin b × Fin c),
      ∀ X : Fin a × Fin b × Fin c → K, cubeExt K N X z = (evalSource X s) := by
  by_cases h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c
  · exact ⟨Src.coord (⟨(z.1 : ℕ), h.1⟩, ⟨(z.2.1 : ℕ), h.2.1⟩, ⟨(z.2.2 : ℕ), h.2.2⟩),
      fun X => by rw [cubeExt_apply, dif_pos h]; rfl⟩
  · exact ⟨Src.zero, fun X => by rw [cubeExt_apply, dif_neg h]; rfl⟩

theorem cubeExt_add (X Y : Fin a × Fin b × Fin c → K) :
    cubeExt K N (X + Y) = cubeExt K N X + cubeExt K N Y := by
  funext z
  simp only [Pi.add_apply, cubeExt_apply]
  by_cases h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c
  · rw [dif_pos h, dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem cubeExt_smul (t : K) (X : Fin a × Fin b × Fin c → K) :
    cubeExt K N (t • X) = t • cubeExt K N X := by
  funext z
  simp only [Pi.smul_apply, cubeExt_apply, smul_eq_mul]
  by_cases h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, mul_zero]

def cubeExtL (K : Type u) [Field K] {a b c : ℕ} (N : ℕ) :
    (Fin a × Fin b × Fin c → K) →ₗ[K] (Fin N × Fin N × Fin N → K) where
  toFun := cubeExt K N
  map_add' := cubeExt_add
  map_smul' := cubeExt_smul

theorem cubeExtL_apply (X : Fin a × Fin b × Fin c → K) :
    cubeExtL K N X = cubeExt K N X := rfl

theorem cubeExt_single (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    cubeExt K N (Pi.single (i, j, k) (1 : K)) =
      Pi.single (Fin.castLE ha i, Fin.castLE hb j, Fin.castLE hc k) (1 : K) := by
  funext z
  obtain ⟨I, J, L⟩ := z
  rw [cubeExt_apply]
  by_cases h : ((I : ℕ) < a ∧ (J : ℕ) < b ∧ (L : ℕ) < c)
  · rw [dif_pos h]
    simp only [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE]
  · rw [dif_neg h]
    simp only [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE]
    have h1 := i.isLt
    have h2 := j.isLt
    have h3 := k.isLt
    rw [if_neg (by omega)]

theorem toTensor₃_single {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃] (z : ι₁ × ι₂ × ι₃) :
    toTensor₃ K ι₁ ι₂ ι₃ (Pi.single z (1 : K)) = tb₃ K ι₁ ι₂ ι₃ z := by
  rw [toTensor₃_apply]
  rw [Finset.sum_eq_single z]
  · simp
  · intro y _ hy
    simp [hy]
  · intro hz
    exact absurd (Finset.mem_univ z) hz

theorem toTensor₃_cubeExt (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (X : Fin a × Fin b × Fin c → K) :
    toTensor₃ K (Fin N) (Fin N) (Fin N) (cubeExt K N X) =
      TensorProduct.map (inc K a N)
        (TensorProduct.map (inc K b N) (inc K c N))
        (toTensor₃ K (Fin a) (Fin b) (Fin c) X) := by
  have key :
      ((toTensor₃ K (Fin N) (Fin N) (Fin N)).toLinearMap ∘ₗ cubeExtL K N) =
        (TensorProduct.map (inc K a N)
            (TensorProduct.map (inc K b N) (inc K c N))) ∘ₗ
          (toTensor₃ K (Fin a) (Fin b) (Fin c)).toLinearMap := by
    apply Module.Basis.ext (Pi.basisFun K (Fin a × Fin b × Fin c))
    rintro ⟨i, j, k⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, cubeExtL_apply]
    rw [cubeExt_single ha hb hc, toTensor₃_single, toTensor₃_single, tb₃_apply, tb₃_apply]
    simp only [TensorProduct.map_tmul, Pi.basisFun_apply]
    rw [inc_single ha, inc_single hb, inc_single hc]
  have := DFunLike.congr_fun key X
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, cubeExtL_apply] using this

end

section

variable {a b c N : ℕ}

theorem cubeExt_equiv_iff (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (X Y : Fin a × Fin b × Fin c → K) :
    (∃ (P : Matrix (Fin a) (Fin a) K) (Q : Matrix (Fin b) (Fin b) K)
        (R : Matrix (Fin c) (Fin c) K),
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R X = Y) ↔
      (∃ P' Q' R' : Matrix (Fin N) (Fin N) K,
        IsUnit P' ∧ IsUnit Q' ∧ IsUnit R' ∧
          act P' Q' R' (cubeExt K N X) = cubeExt K N Y) := by
  have hincA : Function.Injective (inc K a N) := inc_injective ha
  have hincB : Function.Injective (inc K b N) := inc_injective hb
  have hincC : Function.Injective (inc K c N) := inc_injective hc
  constructor
  ·
    intro hsmall
    rw [glAct₃_toTensor₃_iff] at hsmall
    obtain ⟨e₁, e₂, e₃, he⟩ := hsmall
    have hbig :
        ∃ (f₁ f₂ f₃ : (Fin N → K) ≃ₗ[K] (Fin N → K)),
          glAct f₁ f₂ f₃ (toTensor₃ K (Fin N) (Fin N) (Fin N) (cubeExt K N X)) =
            toTensor₃ K (Fin N) (Fin N) (Fin N) (cubeExt K N Y) := by
      refine ⟨extend ha e₁, extend hb e₂, extend hc e₃, ?_⟩
      rw [toTensor₃_cubeExt ha hb hc, toTensor₃_cubeExt ha hb hc]
      simp only [glAct]
      exact padded_of_gl_general (K := K) e₁ e₂ e₃ (extend ha e₁) (extend hb e₂) (extend hc e₃)
        (extend_comp_inc ha e₁) (extend_comp_inc hb e₂) (extend_comp_inc hc e₃) _ _ he
    exact (glAct₃_toTensor₃_iff (K := K) (cubeExt K N X) (cubeExt K N Y)).mpr hbig
  ·
    intro hbig
    rw [glAct₃_toTensor₃_iff] at hbig
    obtain ⟨f₁, f₂, f₃, hf⟩ := hbig
    rw [toTensor₃_cubeExt ha hb hc, toTensor₃_cubeExt ha hb hc] at hf
    simp only [glAct] at hf
    obtain ⟨P₁, P₂, P₃, hP⟩ :=
      gl_of_padded_general (K := K) hincA hincB hincC f₁ f₂ f₃
        (toTensor₃ K (Fin a) (Fin b) (Fin c) X)
        (toTensor₃ K (Fin a) (Fin b) (Fin c) Y) hf
    exact (glAct₃_toTensor₃_iff X Y).mpr ⟨P₁, P₂, P₃, hP⟩

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

section

variable {I₁ I₂ I₃ J₁ J₂ J₃ : Type}
variable [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype I₃] [DecidableEq I₃]
variable [Fintype J₁] [DecidableEq J₁] [Fintype J₂] [DecidableEq J₂] [Fintype J₃] [DecidableEq J₃]

theorem exists_act_reindex3 (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃) (X Y : I₁ × I₂ × I₃ → K) :
    (∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
        IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ X = Y) ↔
      (∃ (Q₁ : Matrix J₁ J₁ K) (Q₂ : Matrix J₂ J₂ K) (Q₃ : Matrix J₃ J₃ K),
        IsUnit Q₁.det ∧ IsUnit Q₂.det ∧ IsUnit Q₃.det ∧
          act Q₁ Q₂ Q₃ (reindex3 e₁ e₂ e₃ X) = reindex3 e₁ e₂ e₃ Y) := by
  have h := flatEquiv_reindex3 e₁ e₂ e₃ (fun _ : I₁ => ()) (fun _ : I₂ => ()) (fun _ : I₃ => ()) X Y
  rw [flatEquiv_of_subsingleton, flatEquiv_of_subsingleton] at h
  exact h

theorem exists_det_iff_isUnit {φ : Matrix I₁ I₁ K → Matrix I₂ I₂ K → Matrix I₃ I₃ K → Prop} :
    (∃ P₁ P₂ P₃, IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ φ P₁ P₂ P₃) ↔
      (∃ P₁ P₂ P₃, IsUnit P₁ ∧ IsUnit P₂ ∧ IsUnit P₃ ∧ φ P₁ P₂ P₃) := by
  simp only [Matrix.isUnit_iff_isUnit_det]

end

theorem act3_eq_act {N : ℕ} (P Q R : Matrix (Fin N) (Fin N) K) (A : Fin N × Fin N × Fin N → K) :
    act3 K P Q R A = act P Q R A := by
  funext ⟨i, j, k⟩
  rfl

theorem gl3ti_rel_iff {N : ℕ} (A B : Fin N × Fin N × Fin N → K) :
    (GL3TI K).Rel N A B ↔
      ∃ P Q R : Matrix (Fin N) (Fin N) K,
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R A = B := by
  simp only [GL3TI, act3_eq_act]

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable (RowIdx : β → Type) (ColIdx : γ → Type)
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable (n t : ℕ)

abbrev OutR : Type :=
  Σ b : Fin 1, PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ) b

abbrev OutC : Type :=
  Σ s : Fin 1, PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ)) s

noncomputable abbrev sideA : ℕ := Fintype.card (OutR RowIdx ColIdx n t)
noncomputable abbrev sideB : ℕ := Fintype.card (OutC RowIdx ColIdx n t)
noncomputable abbrev sideC : ℕ := t₂ RowIdx ColIdx n t (b₀ γ)

noncomputable abbrev Nside : ℕ := max (sideA RowIdx ColIdx n t) (max (sideB RowIdx ColIdx n t) (sideC RowIdx ColIdx n t))

theorem sideA_le : sideA RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t := le_max_left _ _
theorem sideB_le : sideB RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t :=
  le_max_of_le_right (le_max_left _ _)
theorem sideC_le : sideC RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t :=
  le_max_of_le_right (le_max_right _ _)

variable {RowIdx ColIdx n t}

noncomputable def Tf (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    Fin (sideA RowIdx ColIdx n t) × Fin (sideB RowIdx ColIdx n t) × Fin (sideC RowIdx ColIdx n t) → K :=
  reindex3 (Fintype.equivFin (OutR RowIdx ColIdx n t)) (Fintype.equivFin (OutC RowIdx ColIdx n t))
    (Equiv.refl _) (T str X)

theorem T_equiv_iff (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔
      ∃ (P : Matrix (Fin (sideA RowIdx ColIdx n t)) (Fin (sideA RowIdx ColIdx n t)) K)
        (Q : Matrix (Fin (sideB RowIdx ColIdx n t)) (Fin (sideB RowIdx ColIdx n t)) K)
        (R : Matrix (Fin (sideC RowIdx ColIdx n t)) (Fin (sideC RowIdx ColIdx n t)) K),
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R (Tf str X) = Tf str Y := by
  rw [three_deletions, exists_act_reindex3 (Fintype.equivFin (OutR RowIdx ColIdx n t))
    (Fintype.equivFin (OutC RowIdx ColIdx n t)) (Equiv.refl _), exists_det_iff_isUnit]
  rfl

noncomputable def cube (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    Fin (Nside RowIdx ColIdx n t) × Fin (Nside RowIdx ColIdx n t) × Fin (Nside RowIdx ColIdx n t) → K :=
  cubeExt K (Nside RowIdx ColIdx n t) (Tf str X)

theorem cube_equiv_iff (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔ (GL3TI K).Rel (Nside RowIdx ColIdx n t) (cube str X) (cube str Y) := by
  rw [T_equiv_iff, gl3ti_rel_iff,
    cubeExt_equiv_iff (sideA_le RowIdx ColIdx n t) (sideB_le RowIdx ColIdx n t)
      (sideC_le RowIdx ColIdx n t)]
  rfl

theorem cube_srcExpr {ι : Type} (str : Fin t → Fin n) (E : (ι → K) → PArr K β γ RowIdx ColIdx t)
    (hE : SrcExpr (fun A => toFun (E A))) :
    SrcExpr (fun A : ι → K => cube str (E A)) := by
  have h1 : SrcExpr (fun A : ι → K => Tf str (E A)) :=
    (permuteSourceExpression ((composeSourceExpressions hE) (T_srcExpr str))) fun y : Fin (sideA RowIdx ColIdx n t) ×
        Fin (sideB RowIdx ColIdx n t) × Fin (sideC RowIdx ColIdx n t) =>
      ((Fintype.equivFin (OutR RowIdx ColIdx n t)).symm y.1,
        (Fintype.equivFin (OutC RowIdx ColIdx n t)).symm y.2.1, y.2.2)
  have h2 : SrcExpr (fun X : Fin (sideA RowIdx ColIdx n t) × Fin (sideB RowIdx ColIdx n t) ×
      Fin (sideC RowIdx ColIdx n t) → K => cubeExt K (Nside RowIdx ColIdx n t) X) :=
    fun z => cubeExt_src z
  exact (composeSourceExpressions h1) h2

end

section

variable (P : CoordProblem K)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable (RowIdx : ℕ → β → Type) (ColIdx : ℕ → γ → Type)
variable [∀ m b, Fintype (RowIdx m b)] [∀ m b, DecidableEq (RowIdx m b)]
variable [∀ m s, Fintype (ColIdx m s)] [∀ m s, DecidableEq (ColIdx m s)]
variable (t nstr : ℕ → ℕ) (str : ∀ m, Fin (t m) → Fin (nstr m))
variable (E : ∀ m, (P.Idx m → K) → PArr K β γ (RowIdx m) (ColIdx m) (t m))

noncomputable def projectionOfEncoding
    (hcorrect : ∀ m (A B : P.Idx m → K), P.Rel m A B ↔ BlockEquiv (str m) (E m A) (E m B))
    (hsrc : ∀ m, SrcExpr (fun A : P.Idx m → K => toFun (E m A)))
    (hsize : ∃ c k : ℕ, ∀ m,
      Nside (RowIdx m) (ColIdx m) (nstr m) (t m) ^ 3 ≤ c * (Fintype.card (P.Idx m) + 1) ^ k) :
    Projection P (GL3TI K) where
  size := fun m => Nside (RowIdx m) (ColIdx m) (nstr m) (t m)
  src := fun m z => Classical.choose (cube_srcExpr (str m) (E m) (hsrc m) z)
  polyBound := by
    obtain ⟨c, k, h⟩ := hsize
    refine ⟨c, k, fun m => ?_⟩
    show Fintype.card (Fin _ × Fin _ × Fin _) ≤ _
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    calc Nside (RowIdx m) (ColIdx m) (nstr m) (t m) *
          (Nside (RowIdx m) (ColIdx m) (nstr m) (t m) * Nside (RowIdx m) (ColIdx m) (nstr m) (t m))
        = Nside (RowIdx m) (ColIdx m) (nstr m) (t m) ^ 3 := by ring
      _ ≤ _ := h m
  correct := fun m A B => by
    have hA : (fun j => evalSource A (Classical.choose (cube_srcExpr (str m) (E m) (hsrc m) j))) =
        cube (str m) (E m A) :=
      funext fun j => (Classical.choose_spec (cube_srcExpr (str m) (E m) (hsrc m) j) A).symm
    have hB : (fun j => evalSource B (Classical.choose (cube_srcExpr (str m) (E m) (hsrc m) j))) =
        cube (str m) (E m B) :=
      funext fun j => (Classical.choose_spec (cube_srcExpr (str m) (E m) (hsrc m) j) B).symm
    show P.Rel m A B ↔ (GL3TI K).Rel _ _ _
    rw [hcorrect, cube_equiv_iff]
    exact Iff.of_eq (congrArg₂ _ hA.symm hB.symm)

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

def formJ (n : ℕ) (x y : Fin n ⊕ Fin n → K) : K := x ⬝ᵥ (stdJ K n *ᵥ y)

theorem dotProduct_transpose_mul_mul_mulVec {n : ℕ} (g M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (x y : Fin n ⊕ Fin n → K) :
    x ⬝ᵥ ((gᵀ * M * g) *ᵥ y) = (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem isSymplecticMat_iff_formJ {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    IsSymplecticMat K g ↔ ∀ x y, formJ n (g *ᵥ x) (g *ᵥ y) = formJ n x y := by
  unfold IsSymplecticMat formJ
  constructor
  · intro h x y
    rw [← dotProduct_transpose_mul_mul_mulVec, h]
  · intro h
    ext i j
    have hij := h (Pi.single i 1) (Pi.single j 1)
    rw [← dotProduct_transpose_mul_mul_mulVec] at hij
    simpa [dotProduct, Pi.single_apply, Matrix.mulVec_single_one] using hij

def dbl (n : ℕ) : (Fin n ⊕ Fin n → K) ≃ₗ[K] CoordHyp K n :=
  LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) K K

theorem stdJ_mulVec_inl {n : ℕ} (y : Fin n ⊕ Fin n → K) (i : Fin n) :
    (stdJ K n *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [stdJ, Matrix.fromBlocks_mulVec]

theorem stdJ_mulVec_inr {n : ℕ} (y : Fin n ⊕ Fin n → K) (i : Fin n) :
    (stdJ K n *ᵥ y) (Sum.inr i) = -y (Sum.inl i) := by
  simp [stdJ, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem coordHyperForm_dbl {n : ℕ} (x y : Fin n ⊕ Fin n → K) :
    coordHyperForm (dbl n x) (dbl n y) = formJ n x y := by
  simp only [coordHyperForm, dbl, formJ, dotProduct, Fintype.sum_sum_type, stdJ_mulVec_inl,
    stdJ_mulVec_inr, LinearEquiv.sumArrowLequivProdArrow_apply_fst,
    LinearEquiv.sumArrowLequivProdArrow_apply_snd]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

noncomputable def hypVec (n : ℕ) : Hyp K (Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  hypCoordEquiv K n ≪≫ₗ (dbl n).symm

theorem formJ_hypVec {n : ℕ} (x y : Hyp K (Fin n → K)) :
    formJ n (hypVec n x) (hypVec n y) = omegaH x y := by
  rw [← coordHyperForm_dbl]
  simp only [hypVec, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact hypCoordEquiv_isometry K n x y

theorem hypVec_iota {n : ℕ} (u : Fin n → K) :
    hypVec n (iota u : Hyp K (Fin n → K)) = Sum.elim u 0 := by
  simp only [hypVec, LinearEquiv.trans_apply, hypCoordEquiv_apply, iota_apply, map_zero]
  funext s
  rcases s with i | i
  · simp [dbl]
  · simp [dbl]

noncomputable def matOf {n : ℕ} (h : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  LinearMap.toMatrix' (((hypVec n).symm ≪≫ₗ h ≪≫ₗ hypVec n : (Fin n ⊕ Fin n → K) ≃ₗ[K] _) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))

theorem matOf_mulVec {n : ℕ} (h : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K))
    (x : Fin n ⊕ Fin n → K) :
    matOf h *ᵥ x = hypVec n (h ((hypVec n).symm x)) := by
  unfold matOf
  rw [toMatrix'_mulVec]
  rfl

theorem isSymplecticMat_matOf {n : ℕ} (h : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K))
    (hs : IsSymplectic h) : IsSymplecticMat K (matOf h) := by
  rw [isSymplecticMat_iff_formJ]
  intro x y
  rw [matOf_mulVec, matOf_mulVec, formJ_hypVec, hs, ← formJ_hypVec,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

noncomputable def equivOf {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hg : IsUnit g) :
    Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K) :=
  hypVec n ≪≫ₗ linEquivOfIsUnit g hg ≪≫ₗ (hypVec n).symm

theorem equivOf_apply {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hg : IsUnit g)
    (x : Hyp K (Fin n → K)) :
    equivOf g hg x = (hypVec n).symm (g *ᵥ hypVec n x) := by
  simp only [equivOf, LinearEquiv.trans_apply, linEquivOfIsUnit_apply]

theorem hypVec_equivOf {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hg : IsUnit g)
    (x : Hyp K (Fin n → K)) :
    hypVec n (equivOf g hg x) = g *ᵥ hypVec n x := by
  rw [equivOf_apply, LinearEquiv.apply_symm_apply]

theorem isSymplectic_equivOf {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hg : IsUnit g)
    (hs : IsSymplecticMat K g) : IsSymplectic (equivOf g hg) := by
  intro x y
  rw [← formJ_hypVec, hypVec_equivOf, hypVec_equivOf, (isSymplecticMat_iff_formJ g).mp hs,
    formJ_hypVec]

end

end

section

section

open Matrix
open TensorProduct

universe u

variable {K : Type u} [Field K]

abbrev DoubledIndex (n : ℕ) := Fin n ⊕ Fin n

abbrev CoordinateHyperbolic (K : Type u) [Field K] (n : ℕ) := Hyp K (Fin n → K)

def padSrc {n : ℕ} : DoubledIndex n × DoubledIndex n × DoubledIndex n → Src (Fin n × Fin n × Fin n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => Src.coord (i, j, k)
  | _ => Src.zero

def padCoordinates {n : ℕ} (A : Fin n × Fin n × Fin n → K) : DoubledIndex n × DoubledIndex n × DoubledIndex n → K :=
  fun j => (evalSource A (padSrc j))

@[simp] theorem padArr_inl {n : ℕ} (A : Fin n × Fin n × Fin n → K) (i j k : Fin n) :
    padCoordinates A (Sum.inl i, Sum.inl j, Sum.inl k) = A (i, j, k) := rfl

theorem padArr_eq_zero {n : ℕ} (A : Fin n × Fin n × Fin n → K) (y : DoubledIndex n × DoubledIndex n × DoubledIndex n)
    (hy : ∀ i j k : Fin n, y ≠ (Sum.inl i, Sum.inl j, Sum.inl k)) : padCoordinates A y = 0 := by
  rcases y with ⟨a | a, b | b, c | c⟩
  · exact absurd rfl (hy a b c)
  all_goals rfl

noncomputable def congrH (n : ℕ) :
    (DoubledIndex n → K) ⊗[K] ((DoubledIndex n → K) ⊗[K] (DoubledIndex n → K)) ≃ₗ[K] CoordinateHyperbolic K n ⊗[K] (CoordinateHyperbolic K n ⊗[K] CoordinateHyperbolic K n) :=
  TensorProduct.congr (hypVec n).symm (TensorProduct.congr (hypVec n).symm (hypVec n).symm)

noncomputable def toTensorH (n : ℕ) :
    (DoubledIndex n × DoubledIndex n × DoubledIndex n → K) ≃ₗ[K] CoordinateHyperbolic K n ⊗[K] (CoordinateHyperbolic K n ⊗[K] CoordinateHyperbolic K n) :=
  toTensor (DoubledIndex n) ≪≫ₗ congrH n

noncomputable def tbH (n : ℕ) : Module.Basis (DoubledIndex n × DoubledIndex n × DoubledIndex n) K (CoordinateHyperbolic K n ⊗[K] (CoordinateHyperbolic K n ⊗[K] CoordinateHyperbolic K n)) :=
  (tb (DoubledIndex n)).map (congrH n)

theorem repr_toTensorH {n : ℕ} (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (y : DoubledIndex n × DoubledIndex n × DoubledIndex n) :
    (tbH n).repr (toTensorH n A) y = A y := by
  simp only [tbH, Module.Basis.map_repr, toTensorH, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact repr_toTensor A y

theorem hypVec_symm_single {n : ℕ} (i : Fin n) :
    (hypVec (K := K) n).symm (Pi.basisFun K (DoubledIndex n) (Sum.inl i)) =
      (iota (Pi.basisFun K (Fin n) i) : CoordinateHyperbolic K n) := by
  apply (hypVec n).injective
  rw [LinearEquiv.apply_symm_apply, hypVec_iota]
  funext s
  rcases s with j | j
  · simp [Pi.basisFun_apply, Pi.single_apply]
  · simp [Pi.basisFun_apply, Pi.single_apply]

theorem tbH_inl {n : ℕ} (i j k : Fin n) :
    tbH (K := K) n (Sum.inl i, Sum.inl j, Sum.inl k) = pad3 (tb (K := K) (Fin n) (i, j, k)) := by
  simp only [tbH, Module.Basis.map_apply, congrH, tb_apply, TensorProduct.congr_tmul,
    pad3, TensorProduct.map_tmul]
  rw [show (e (DoubledIndex n) (Sum.inl i) : DoubledIndex n → K) = Pi.basisFun K (DoubledIndex n) (Sum.inl i) from rfl,
    show (e (DoubledIndex n) (Sum.inl j) : DoubledIndex n → K) = Pi.basisFun K (DoubledIndex n) (Sum.inl j) from rfl,
    show (e (DoubledIndex n) (Sum.inl k) : DoubledIndex n → K) = Pi.basisFun K (DoubledIndex n) (Sum.inl k) from rfl,
    hypVec_symm_single, hypVec_symm_single, hypVec_symm_single]

theorem toTensorH_padArr {n : ℕ} (A : Fin n × Fin n × Fin n → K) :
    toTensorH n (padCoordinates A) = pad3 (toTensor (Fin n) A) := by
  apply (tbH n).repr.injective
  ext y
  rw [repr_toTensorH]
  conv_rhs => rw [toTensor_apply, map_sum, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ x : Fin n × Fin n × Fin n,
      (tbH (K := K) n).repr (pad3 (tb (K := K) (Fin n) x)) y =
        if (Sum.inl x.1, Sum.inl x.2.1, Sum.inl x.2.2) = y then 1 else 0 := by
    rintro ⟨i, j, k⟩
    rw [← tbH_inl, Module.Basis.repr_self, Finsupp.single_apply]
    try rfl
  simp only [key]
  rcases y with ⟨a | a, b | b, c | c⟩
  · rw [Finset.sum_eq_single (a, b, c)]
    · simp
    · rintro ⟨i, j, k⟩ - hne
      rw [if_neg, mul_zero]
      intro h
      apply hne
      simp only [Prod.mk.injEq, Sum.inl.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
    · intro h; exact absurd (Finset.mem_univ _) h
  all_goals
    rw [padArr_eq_zero _ _ (by rintro i j k h; cases h)]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Prod.mk.injEq]

theorem matOf_equivOf {n : ℕ} (P : Matrix (DoubledIndex n) (DoubledIndex n) K) (hP : IsUnit P) :
    matOf (equivOf P hP) = P := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, matOf_mulVec, hypVec_equivOf,
    LinearEquiv.apply_symm_apply]

theorem spAct_congrH {n : ℕ} (g₁ g₂ g₃ : CoordinateHyperbolic K n ≃ₗ[K] CoordinateHyperbolic K n)
    (T : (DoubledIndex n → K) ⊗[K] ((DoubledIndex n → K) ⊗[K] (DoubledIndex n → K))) :
    spAct g₁ g₂ g₃ (congrH n T) = congrH n (glActMat (matOf g₁) (matOf g₂) (matOf g₃) T) := by
  have hpt : ∀ (g : CoordinateHyperbolic K n ≃ₗ[K] CoordinateHyperbolic K n) (x : DoubledIndex n → K),
      g ((hypVec n).symm x) = (hypVec n).symm (matOf g *ᵥ x) := by
    intro g x
    rw [matOf_mulVec, LinearEquiv.symm_apply_apply]
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul x yz =>
    induction yz using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
      simp only [congrH, TensorProduct.congr_tmul, spAct, glActMat, TensorProduct.map_tmul,
        LinearEquiv.coe_coe, Matrix.toLin'_apply, hpt]
    | add y z hy hz =>
      simp only [TensorProduct.tmul_add, map_add] at hy hz ⊢
      rw [hy, hz]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem sp3ti_iff {n : ℕ} (A' B' : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    (Sp3TI K).Rel n A' B' ↔
      ∃ g₁ g₂ g₃ : CoordinateHyperbolic K n ≃ₗ[K] CoordinateHyperbolic K n, IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
        spAct g₁ g₂ g₃ (toTensorH n A') = toTensorH n B' := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    have uP := isUnit_of_isSymplecticMat K P hP
    have uQ := isUnit_of_isSymplecticMat K Q hQ
    have uR := isUnit_of_isSymplecticMat K R hR
    refine ⟨equivOf P uP, equivOf Q uQ, equivOf R uR, isSymplectic_equivOf P uP hP,
      isSymplectic_equivOf Q uQ hQ, isSymplectic_equivOf R uR hR, ?_⟩
    simp only [toTensorH, LinearEquiv.trans_apply]
    rw [spAct_congrH, matOf_equivOf, matOf_equivOf, matOf_equivOf, ← toTensor_actι,
      ← act3D_eq_actι, h]
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
    refine ⟨matOf g₁, matOf g₂, matOf g₃, isSymplecticMat_matOf g₁ h₁, isSymplecticMat_matOf g₂ h₂,
      isSymplecticMat_matOf g₃ h₃, ?_⟩
    apply (toTensorH n).injective
    rw [← h]
    simp only [toTensorH, LinearEquiv.trans_apply]
    rw [spAct_congrH, act3D_eq_actι, toTensor_actι]

theorem gl3ti_iff {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔
      ∃ e₁ e₂ e₃ : (Fin n → K) ≃ₗ[K] (Fin n → K),
        glAct e₁ e₂ e₃ (toTensor (Fin n) A) = toTensor (Fin n) B :=
  glAct_toTensor_iff A B

theorem gl3ti_iff_sp3ti_pad {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (Sp3TI K).Rel n (padCoordinates A) (padCoordinates B) := by
  rw [gl3ti_iff, sp3ti_iff, toTensorH_padArr, toTensorH_padArr]
  exact gl_iff_padded (toTensor (Fin n) A) (toTensor (Fin n) B)

def generalToSymplectic : Projection (GL3TI K) (Sp3TI K) where
  size := id
  src := fun _ j => padSrc j
  polyBound := ⟨8, 1, fun n => by
    change Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) ≤
      8 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 1
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, pow_one]
    have : (n + n) * ((n + n) * (n + n)) = 8 * (n * (n * n)) := by ring
    omega⟩
  correct := fun _ A B => gl3ti_iff_sp3ti_pad A B

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K] {t n : ℕ}

abbrev Fib (str : Fin t → Fin n) (g : Fin n) : Type := {k : Fin t // str k = g}

section

variable (str : Fin t → Fin n)

def assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    Matrix (Fin t) (Fin t) K :=
  Matrix.of fun i j => if h : str i = str j then Rst (str i) ⟨i, rfl⟩ ⟨j, h.symm⟩ else 0

def stratumBlock (R : Matrix (Fin t) (Fin t) K) (g : Fin n) : Matrix (Fib str g) (Fib str g) K :=
  R.submatrix Subtype.val Subtype.val

theorem isBlockDiag_assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    IsBlockDiag str (assemble str Rst) := by
  intro i j hij
  simp [assemble, dif_neg hij]

theorem assemble_apply_of_eq (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K)
    {i j : Fin t} (h : str i = str j) (g : Fin n) (hg : str i = g) :
    assemble str Rst i j = Rst g ⟨i, hg⟩ ⟨j, h.symm.trans hg⟩ := by
  subst hg
  simp [assemble, dif_pos h]

theorem blockOf_assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) (g : Fin n) :
    stratumBlock str (assemble str Rst) g = Rst g := by
  ext a b
  obtain ⟨i, hi⟩ := a
  obtain ⟨j, hj⟩ := b
  subst hi
  simp [stratumBlock, assemble, dif_pos hj.symm]

theorem sum_fibre {M : Type*} [AddCommMonoid M] (g : Fin n) (f : Fin t → M)
    (hf : ∀ l, str l ≠ g → f l = 0) :
    ∑ l : Fin t, f l = ∑ c : Fib str g, f c.1 := by
  classical
  have h1 : ∑ l ∈ Finset.univ.filter (fun l => str l = g), f l = ∑ l : Fin t, f l :=
    Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => hf l (by simpa using hl))
  have h2 : ∑ l ∈ Finset.univ.filter (fun l => str l = g), f l
      = ∑ c : Fib str g, f c.1 :=
    Finset.sum_subtype _ (by intro x; simp) f
  rw [← h1, h2]

theorem assemble_one :
    assemble str (fun g => (1 : Matrix (Fib str g) (Fib str g) K)) = 1 := by
  ext i j
  by_cases h : str i = str j
  · simp only [assemble, Matrix.of_apply, dif_pos h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg, if_neg hij]
      intro hcon
      exact hij (congrArg Subtype.val hcon)
  · rw [Matrix.one_apply]
    simp only [assemble, Matrix.of_apply, dif_neg h]
    rw [if_neg]
    rintro rfl
    exact h rfl

theorem assemble_mul (Rst Rst' : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    assemble str Rst * assemble str Rst' = assemble str (fun g => Rst g * Rst' g) := by
  ext i j
  by_cases h : str i = str j
  · rw [Matrix.mul_apply]
    rw [sum_fibre str (str i) (fun l => assemble str Rst i l * assemble str Rst' l j) ?_]
    · rw [assemble_apply_of_eq str _ h (str i) rfl]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc : str i = str c.1 := c.2.symm
      have hc' : str c.1 = str j := c.2.trans h
      rw [assemble_apply_of_eq str Rst hc (str i) rfl,
        assemble_apply_of_eq str Rst' hc' (str i) c.2]
    · intro l hl
      have : str i ≠ str l := fun hcon => hl hcon.symm
      simp [assemble, dif_neg this]
  · rw [Matrix.mul_apply]
    simp only [assemble, Matrix.of_apply, dif_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : str i = str l
    · have h2 : str l ≠ str j := fun hcon => h (h1.trans hcon)
      rw [dif_neg h2, mul_zero]
    · rw [dif_neg h1, zero_mul]

theorem blockOf_mul {M N : Matrix (Fin t) (Fin t) K} (hM : IsBlockDiag str M) (g : Fin n) :
    stratumBlock str (M * N) g = stratumBlock str M g * stratumBlock str N g := by
  ext a b
  simp only [stratumBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fibre str g (fun l => M a.1 l * N l b.1) ?_
  intro l hl
  have : str a.1 ≠ str l := fun hcon => hl (hcon ▸ a.2)
  rw [hM a.1 l this, zero_mul]

theorem isUnit_det_assemble {Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K}
    (h : ∀ g, IsUnit (Rst g).det) : IsUnit (assemble str Rst).det := by
  have hmul : assemble str Rst * assemble str (fun g => (Rst g)⁻¹) = 1 := by
    rw [assemble_mul]
    have : (fun g => Rst g * (Rst g)⁻¹) = fun g => (1 : Matrix (Fib str g) (Fib str g) K) := by
      funext g
      exact Matrix.mul_nonsing_inv _ (h g)
    rw [this, assemble_one]
  have hd : (assemble str Rst).det * (assemble str (fun g => (Rst g)⁻¹)).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  exact ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩

theorem isUnit_det_stratumBlock {R : Matrix (Fin t) (Fin t) K} (hR : IsBlockDiag str R)
    (hU : IsUnit R.det) (g : Fin n) : IsUnit (stratumBlock str R g).det := by
  have hinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hblk : stratumBlock str R g * stratumBlock str R⁻¹ g = 1 := by
    rw [← blockOf_mul str hR, hinv]
    ext a b
    simp [stratumBlock, Matrix.one_apply, Subtype.ext_iff]
  have hd : (stratumBlock str R g).det * (stratumBlock str R⁻¹ g).det = 1 := by
    rw [← Matrix.det_mul, hblk, Matrix.det_one]
  exact ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩

theorem isUnit_det_assemble_iff (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    IsUnit (assemble str Rst).det ↔ ∀ g, IsUnit (Rst g).det := by
  constructor
  · intro h g
    have := isUnit_det_stratumBlock str (isBlockDiag_assemble str Rst) h g
    rwa [blockOf_assemble str Rst g] at this
  · exact isUnit_det_assemble str

end

end

end

section

section

open Matrix

universe u v

section

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

def Coupling (Ψ : Matrix ι ι R) (g h : Matrix ι ι R) : Prop :=
  g * Ψ * hᵀ = Ψ

omit [DecidableEq ι] in
theorem coupling_def (Ψ g h : Matrix ι ι R) : Coupling Ψ g h ↔ g * Ψ * hᵀ = Ψ := Iff.rfl

theorem mul_eq_one_comm_sq {A B : Matrix ι ι R} (h : A * B = 1) : B * A = 1 := by
  have hd : A.det * B.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have hu : IsUnit A.det := ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩
  have hAB : A⁻¹ = B := Matrix.inv_eq_right_inv h
  rw [← hAB]
  exact Matrix.nonsing_inv_mul _ hu

theorem coupling_solve {Ψ g h : Matrix ι ι R} (hΨ : IsUnit Ψ.det) (hg : IsUnit g.det)
    (H : Coupling Ψ g h) : hᵀ = Ψ⁻¹ * g⁻¹ * Ψ := by
  have h1 : Ψ * hᵀ = g⁻¹ * Ψ := by
    have h0 : g⁻¹ * (g * Ψ * hᵀ) = g⁻¹ * Ψ := congrArg (fun M => g⁻¹ * M) H
    calc Ψ * hᵀ = (g⁻¹ * g) * Ψ * hᵀ := by rw [Matrix.nonsing_inv_mul _ hg, one_mul]
      _ = g⁻¹ * (g * Ψ * hᵀ) := by simp only [mul_assoc]
      _ = g⁻¹ * Ψ := h0
  calc hᵀ = (Ψ⁻¹ * Ψ) * hᵀ := by rw [Matrix.nonsing_inv_mul _ hΨ, one_mul]
    _ = Ψ⁻¹ * (Ψ * hᵀ) := by rw [mul_assoc]
    _ = Ψ⁻¹ * (g⁻¹ * Ψ) := by rw [h1]
    _ = Ψ⁻¹ * g⁻¹ * Ψ := by rw [mul_assoc]

theorem coupling_one_iff (g h : Matrix ι ι R) :
    Coupling (1 : Matrix ι ι R) g h ↔ g * hᵀ = 1 := by
  simp [Coupling]

theorem coupling_one_chain {g h k : Matrix ι ι R}
    (H₁ : Coupling (1 : Matrix ι ι R) g h) (H₂ : Coupling (1 : Matrix ι ι R) h k) : k = g := by
  rw [coupling_one_iff] at H₁ H₂
  have hk : k * hᵀ = 1 := by
    have := congrArg Matrix.transpose H₂
    simpa [Matrix.transpose_mul] using this
  have hleft : hᵀ * g = 1 := mul_eq_one_comm_sq H₁
  calc k = k * (hᵀ * g) := by rw [hleft, mul_one]
    _ = (k * hᵀ) * g := by rw [mul_assoc]
    _ = g := by rw [hk, one_mul]

end

end

end

section

section

open Matrix
open TensorProduct

universe u v

section

variable {K : Type u} [Field K] {U : Type v} [AddCommGroup U] [Module K U]

def PreservesBil (ω : U →ₗ[K] U →ₗ[K] K) (g : U ≃ₗ[K] U) : Prop :=
  ∀ x y, ω (g x) (g y) = ω x y

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

abbrev SymplecticIndex (n : ℕ) : Type := Fin n ⊕ Fin n

inductive Blk where

  | dat : Blk

  | cop : Blk

  | mid : Blk

  | anch : Blk
  deriving DecidableEq

instance instNonemptyBlk : Nonempty Blk := ⟨Blk.dat⟩

instance instFintypeBlk : Fintype Blk where
  elems := {Blk.dat, Blk.cop, Blk.mid, Blk.anch}
  complete := by intro x; cases x <;> decide

abbrev BIdx (n : ℕ) : Blk → Type
  | Blk.dat => SymplecticIndex n
  | Blk.cop => SymplecticIndex n
  | Blk.mid => SymplecticIndex n
  | Blk.anch => Unit

instance instFintypeBIdx (n : ℕ) : ∀ b : Blk, Fintype (BIdx n b)
  | Blk.dat => inferInstanceAs (Fintype (SymplecticIndex n))
  | Blk.cop => inferInstanceAs (Fintype (SymplecticIndex n))
  | Blk.mid => inferInstanceAs (Fintype (SymplecticIndex n))
  | Blk.anch => inferInstanceAs (Fintype Unit)

instance instDecEqBIdx (n : ℕ) : ∀ b : Blk, DecidableEq (BIdx n b)
  | Blk.dat => inferInstanceAs (DecidableEq (SymplecticIndex n))
  | Blk.cop => inferInstanceAs (DecidableEq (SymplecticIndex n))
  | Blk.mid => inferInstanceAs (DecidableEq (SymplecticIndex n))
  | Blk.anch => inferInstanceAs (DecidableEq Unit)

theorem card_S (n : ℕ) : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
  rw [Fintype.card_sum, Fintype.card_fin, two_mul]

theorem Hgadget_card (n : ℕ) : ∑ b : Blk, Fintype.card (BIdx n b) = 6 * n + 1 := by
  have huniv : (Finset.univ : Finset Blk) = {Blk.dat, Blk.cop, Blk.mid, Blk.anch} := rfl
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hd : Fintype.card (BIdx n Blk.dat) = 2 * n := card_S n
  have hc : Fintype.card (BIdx n Blk.cop) = 2 * n := card_S n
  have hm : Fintype.card (BIdx n Blk.mid) = 2 * n := card_S n
  have ha : Fintype.card (BIdx n Blk.anch) = 1 := rfl
  simp only [hd, hc, hm, ha]
  ring

noncomputable def Hgadget (n : ℕ) {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)
    (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) :
    PArr K Blk Blk (BIdx n) (BIdx n) th :=
  fun k b s =>
    match b, s with
    | Blk.dat, Blk.dat => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if h : strH k = 0 then A (i, j, (e0.symm ⟨k, h⟩ : SymplecticIndex n)) else 0
    | Blk.dat, Blk.cop => 0
    | Blk.dat, Blk.mid => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.dat, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 1 then stdJ K n i (e1.symm ⟨k, h⟩) else 0
    | Blk.cop, Blk.dat => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then stdJ K n i j else 0
    | Blk.cop, Blk.cop => 0
    | Blk.cop, Blk.mid => 0
    | Blk.cop, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.mid, Blk.dat => 0
    | Blk.mid, Blk.cop => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.mid, Blk.mid => 0
    | Blk.mid, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.dat => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.cop => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 0 then stdJ K n j (e0.symm ⟨k, h⟩) else 0
    | Blk.anch, Blk.mid => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.anch => Matrix.of fun (_ : Unit) (_ : Unit) =>
        if strH k = 3 then (1 : K) else 0

theorem ite_one_src (n : ℕ) (P : Prop) [Decidable P] :
    ∃ σ : Src (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n),
      ∀ A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K, (if P then (1 : K) else 0) = (evalSource A σ) := by
  by_cases h : P
  · exact ⟨Src.one, fun _ => by rw [if_pos h]; rfl⟩
  · exact ⟨Src.zero, fun _ => by rw [if_neg h]; rfl⟩

end

end

section

section

universe u

variable {K : Type u} [Field K]

abbrev thn (n : ℕ) : ℕ := 6 * n + 1

abbrev Idx3 (n : ℕ) : Type := SymplecticIndex n ⊕ (SymplecticIndex n ⊕ (SymplecticIndex n ⊕ Unit))

def tag3 (n : ℕ) : Idx3 n → Fin 4
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

theorem card_Idx3 (n : ℕ) : Fintype.card (Idx3 n) = thn n := by
  simp only [Idx3, thn, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

noncomputable def packEquiv (n : ℕ) : Idx3 n ≃ Fin (thn n) :=
  Fintype.equivFinOfCardEq (card_Idx3 n)

noncomputable def strHn (n : ℕ) : Fin (thn n) → Fin 4 :=
  fun k => tag3 n ((packEquiv n).symm k)

noncomputable def fibEquiv (n : ℕ) (g : Fin 4) :
    Fib (strHn n) g ≃ {x : Idx3 n // tag3 n x = g} :=
  Equiv.subtypeEquiv (packEquiv n).symm (fun _ => Iff.rfl)

noncomputable def sub0 (n : ℕ) : SymplecticIndex n ≃ {x : Idx3 n // tag3 n x = 0} :=
  Equiv.ofBijective (fun v => ⟨Sum.inl v, rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · exact ⟨v, rfl⟩
      · rcases y with u | z
        · simp [tag3] at hx
        · rcases z with p | q <;> simp [tag3] at hx⟩

noncomputable def sub1 (n : ℕ) : SymplecticIndex n ≃ {x : Idx3 n // tag3 n x = 1} :=
  Equiv.ofBijective (fun v => ⟨Sum.inr (Sum.inl v), rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [tag3] at hx
      · rcases y with u | z
        · exact ⟨u, rfl⟩
        · rcases z with p | q <;> simp [tag3] at hx⟩

noncomputable def sub2 (n : ℕ) : SymplecticIndex n ≃ {x : Idx3 n // tag3 n x = 2} :=
  Equiv.ofBijective (fun v => ⟨Sum.inr (Sum.inr (Sum.inl v)), rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [tag3] at hx
      · rcases y with u | z
        · simp [tag3] at hx
        · rcases z with p | q
          · exact ⟨p, rfl⟩
          · simp [tag3] at hx⟩

noncomputable def sub3 (n : ℕ) : Unit ≃ {x : Idx3 n // tag3 n x = 3} :=
  Equiv.ofBijective (fun _ => ⟨Sum.inr (Sum.inr (Sum.inr ())), rfl⟩)
    ⟨fun v w _ => Subsingleton.elim v w,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [tag3] at hx
      · rcases y with u | z
        · simp [tag3] at hx
        · rcases z with p | q
          · simp [tag3] at hx
          · exact ⟨(), by cases q; rfl⟩⟩

noncomputable def e0n (n : ℕ) : SymplecticIndex n ≃ Fib (strHn n) 0 := (sub0 n).trans (fibEquiv n 0).symm
noncomputable def e1n (n : ℕ) : SymplecticIndex n ≃ Fib (strHn n) 1 := (sub1 n).trans (fibEquiv n 1).symm
noncomputable def e2n (n : ℕ) : SymplecticIndex n ≃ Fib (strHn n) 2 := (sub2 n).trans (fibEquiv n 2).symm

noncomputable def e3n (n : ℕ) : Unit ≃ Fib (strHn n) 3 := (sub3 n).trans (fibEquiv n 3).symm

theorem H_card (n : ℕ) : Fintype.card (Σ b : Blk, BIdx n b) = thn n := by
  rw [Fintype.card_sigma]
  exact Hgadget_card n

theorem H_card_row (n : ℕ) : Fintype.card (Σ b : Blk, BIdx n b) = 6 * n + 1 := H_card n

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

section

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)

noncomputable abbrev invT (g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) : Matrix (SymplecticIndex n) (SymplecticIndex n) K := g⁻¹ᵀ

theorem isUnit_det_invT {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) : IsUnit (invT g).det := by
  rw [invT, Matrix.det_transpose]
  exact Matrix.isUnit_nonsing_inv_det g h

theorem mul_invT_transpose {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) :
    g * (invT g)ᵀ = 1 := by
  rw [invT, Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv g h

theorem invT_mul_transpose {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) :
    invT g * gᵀ = 1 := by
  rw [invT, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv g h, Matrix.transpose_one]

noncomputable def Pfwd (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K
  | Blk.dat => g₁
  | Blk.cop => g₂
  | Blk.mid => invT g₃
  | Blk.anch => 1

noncomputable def Qfwd (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    ∀ s : Blk, Matrix (BIdx n s) (BIdx n s) K
  | Blk.dat => g₂
  | Blk.cop => g₃
  | Blk.mid => invT g₁
  | Blk.anch => 1

theorem Pfwd_isUnit (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ b, IsUnit (Pfwd g₁ g₂ g₃ b).det
  | Blk.dat => h₁
  | Blk.cop => h₂
  | Blk.mid => isUnit_det_invT h₃
  | Blk.anch => by simp [Pfwd]

theorem Qfwd_isUnit (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ s, IsUnit (Qfwd g₁ g₂ g₃ s).det
  | Blk.dat => h₂
  | Blk.cop => h₃
  | Blk.mid => isUnit_det_invT h₁
  | Blk.anch => by simp [Qfwd]

noncomputable def Rst (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K
  | 0 => Matrix.reindex e0 e0 g₃
  | 1 => Matrix.reindex e1 e1 g₁
  | 2 => Matrix.reindex e2 e2 (invT g₂)
  | 3 => 1

theorem Rst_zero (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 0 = Matrix.reindex e0 e0 g₃ := rfl
theorem Rst_one (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 1 = Matrix.reindex e1 e1 g₁ := rfl
theorem Rst_two (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 2 = Matrix.reindex e2 e2 (invT g₂) := rfl
theorem Rst_three (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 3 = 1 := rfl

noncomputable def Rfwd (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) : Matrix (Fin th) (Fin th) K :=
  assemble strH (Rst strH e0 e1 e2 g₁ g₂ g₃)

theorem Rfwd_isBlockDiag (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    IsBlockDiag strH (Rfwd strH e0 e1 e2 g₁ g₂ g₃) :=
  isBlockDiag_assemble strH _

theorem Rfwd_isUnit (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : IsUnit (Rfwd strH e0 e1 e2 g₁ g₂ g₃).det := by
  rw [Rfwd, isUnit_det_assemble_iff]
  intro g
  match g with
  | 0 => rw [Rst_zero, Matrix.det_reindex_self]; exact h₃
  | 1 => rw [Rst_one, Matrix.det_reindex_self]; exact h₁
  | 2 => rw [Rst_two, Matrix.det_reindex_self]; exact isUnit_det_invT h₂
  | 3 => rw [Rst_three]; simp

end

section

variable {n th : ℕ} (strH : Fin th → Fin 4)

theorem sum_assemble_smul {I J : Type} [Fintype I] [Fintype J]
    (Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (M : Fin th → Matrix I J K) (g₀ : Fin 4) (hM : ∀ k', strH k' ≠ g₀ → M k' = 0) (k : Fin th) :
    ∑ k', assemble strH Rst k k' • M k' =
      if h : strH k = g₀ then ∑ k' : Fib strH g₀, Rst g₀ ⟨k, h⟩ k' • M k'.1 else 0 := by
  classical
  split_ifs with h
  · rw [← Finset.sum_filter_of_ne (p := fun k' => strH k' = g₀) (s := Finset.univ)
      (f := fun k' => assemble strH Rst k k' • M k')]
    · rw [Finset.sum_subtype (Finset.univ.filter fun k' => strH k' = g₀)
        (p := fun k' => strH k' = g₀) (by simp)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [assemble_apply_of_eq strH Rst (h.trans a.2.symm) g₀ h]
    · intro k' _ hne
      by_contra hk'
      exact hne (by rw [hM k' hk', smul_zero])
  · refine Finset.sum_eq_zero fun k' _ => ?_
    by_cases hk' : strH k' = g₀
    · have : assemble strH Rst k k' = 0 :=
        isBlockDiag_assemble strH Rst k k' (by rw [hk']; exact h)
      rw [this, zero_smul]
    · rw [hM k' hk', smul_zero]

theorem sum_fib_reindex {I J : Type} [Fintype I] [Fintype J] {g₀ : Fin 4} (e : SymplecticIndex n ≃ Fib strH g₀)
    (F : Fib strH g₀ → Matrix I J K) : ∑ k' : Fib strH g₀, F k' = ∑ m : SymplecticIndex n, F (e m) :=
  (Equiv.sum_comp e F).symm

theorem reindex_apply_symm {g₀ : Fin 4} (e : SymplecticIndex n ≃ Fib strH g₀) (G : Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (a : Fib strH g₀) (m : SymplecticIndex n) : Matrix.reindex e e G a (e m) = G (e.symm a) m := by
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

end

section

variable {n : ℕ}

def slice (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (m : SymplecticIndex n) : Matrix (SymplecticIndex n) (SymplecticIndex n) K :=
  Matrix.of fun i j => A (i, j, m)

theorem slice_apply (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (m i j : SymplecticIndex n) : slice A m i j = A (i, j, m) := rfl

theorem sum3_rotate_forward (f : SymplecticIndex n → SymplecticIndex n → SymplecticIndex n → K) :
    ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ k', ∑ j', ∑ i', f i' j' k' :=
  calc ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ j', ∑ i', ∑ k', f i' j' k' := Finset.sum_comm
    _ = ∑ j', ∑ k', ∑ i', f i' j' k' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k', ∑ j', ∑ i', f i' j' k' := Finset.sum_comm

theorem act3D_slice (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (k : SymplecticIndex n) :
    slice (act3D K g₁ g₂ g₃ A) k = ∑ m, g₃ k m • (g₁ * slice A m * g₂ᵀ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [slice_apply, act3D, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine (sum3_rotate_forward (fun i' j' k' => g₁ i i' * g₂ j j' * g₃ k k' * A (i', j', k'))).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun i' _ => ?_
  ring

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

theorem sum_smul_entry {I J ι : Type} [Fintype ι] (c : ι → K) (M : ι → Matrix I J K) (i : I)
    (j : J) : (∑ m, c m • M m) i j = ∑ m, c m * M m i j := by
  simp [Matrix.sum_apply]

section

variable {n : ℕ}

variable (K)

def colE {J : Type} (m : SymplecticIndex n) : Matrix (SymplecticIndex n) J K := Matrix.of fun i _ => if i = m then 1 else 0

def rowE {I : Type} (m : SymplecticIndex n) : Matrix I (SymplecticIndex n) K := Matrix.of fun _ j => if j = m then 1 else 0

variable {K} {I J : Type}

theorem mul_colE (g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m : SymplecticIndex n) :
    g * colE K (J := J) m = Matrix.of fun i _ => g i m := by
  ext i u
  rw [Matrix.mul_apply]
  simp [colE]

theorem rowE_mul (g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m : SymplecticIndex n) :
    rowE K (I := I) m * g = Matrix.of fun _ j => g m j := by
  ext u j
  rw [Matrix.mul_apply]
  simp [rowE]

theorem mul_inv_entry {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) (x i : SymplecticIndex n) :
    ∑ m, g x m * g⁻¹ m i = if x = i then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mul_nonsing_inv g h) x) i
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem colE_transport {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) (x : SymplecticIndex n) :
    ∑ m, g x m • (invT g * colE K (J := J) m) = colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colE, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [mul_inv_entry h, colE, Matrix.of_apply]
  by_cases hx : i = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem colE_transport_inv {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) (x : SymplecticIndex n) :
    ∑ m, invT g x m • (g * colE K (J := J) m) = colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colE, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [colE, Matrix.of_apply, ← mul_inv_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem rowE_transport {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) (x : SymplecticIndex n) :
    ∑ m, g x m • (rowE K (I := I) m * (invT g)ᵀ) = rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [invT, Matrix.transpose_transpose, rowE_mul, Matrix.of_apply]
  rw [mul_inv_entry h, rowE, Matrix.of_apply]
  by_cases hx : j = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem rowE_transport_inv {g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : IsUnit g.det) (x : SymplecticIndex n) :
    ∑ m, invT g x m • (rowE K (I := I) m * gᵀ) = rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [rowE_mul, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [rowE, Matrix.of_apply, ← mul_inv_entry h j x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem sum_one_smul {I : Type} [Fintype I] [DecidableEq I] {I' J' : Type} (a : I)
    (C : Matrix I' J' K) : ∑ j, (1 : Matrix I I K) a j • C = C := by
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]

end

section

variable {n th : ℕ} (strH : Fin th → Fin 4)

theorem block_step {I I' J J' : Type} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (P : Matrix I I' K) (Q : Matrix J J' K) (N : Fin th → Matrix I' J' K) (g₀ : Fin 4)
    (hN : ∀ k', strH k' ≠ g₀ → N k' = 0) (e : SymplecticIndex n ≃ Fib strH g₀) (G : Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (hG : Rst g₀ = Matrix.reindex e e G) (Nx : SymplecticIndex n → Matrix I' J' K)
    (hNx : ∀ m, N (e m).1 = Nx m) (k : Fin th) :
    ∑ k', assemble strH Rst k k' • (P * N k' * Qᵀ) =
      if h : strH k = g₀ then ∑ m, G (e.symm ⟨k, h⟩) m • (P * Nx m * Qᵀ) else 0 := by
  refine (sum_assemble_smul strH Rst (fun k' => P * N k' * Qᵀ) g₀
    (fun k' hk' => by simp [hN k' hk']) k).trans ?_
  by_cases h : strH k = g₀
  · rw [dif_pos h, dif_pos h, sum_fib_reindex strH e]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hG, reindex_apply_symm, hNx]
  · rw [dif_neg h, dif_neg h]

theorem block_step3 {I I' J J' : Type} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (P : Matrix I I' K) (Q : Matrix J J' K) (N : Fin th → Matrix I' J' K) (N3 : Matrix I' J' K)
    (hN : ∀ k', N k' = if strH k' = 3 then N3 else 0) (h3 : Rst 3 = 1) (k : Fin th) :
    ∑ k', assemble strH Rst k k' • (P * N k' * Qᵀ) =
      if strH k = 3 then P * N3 * Qᵀ else 0 := by
  refine (sum_assemble_smul strH Rst (fun k' => P * N k' * Qᵀ) 3
    (fun k' hk' => by simp [hN k', hk']) k).trans ?_
  by_cases h : strH k = 3
  · rw [dif_pos h, if_pos h, h3]
    have hfix : ∀ k' : Fib strH 3, P * N k'.1 * Qᵀ = P * N3 * Qᵀ := fun k' => by
      rw [hN k'.1, if_pos k'.2]
    simp only [hfix]
    exact sum_one_smul _ _
  · rw [dif_neg h, if_neg h]

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

def TIG (Grp : ∀ n, Matrix (DoubledIndex n) (DoubledIndex n) K → Prop) : CoordProblem K where
  Idx := fun n => DoubledIndex n × DoubledIndex n × DoubledIndex n
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ g₁ g₂ g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K,
    Grp n g₁ ∧ Grp n g₂ ∧ Grp n g₃ ∧ act3D K g₁ g₂ g₃ A = B

noncomputable def hypLift {n : ℕ} (P : Matrix (Fin n) (Fin n) K) : Matrix (DoubledIndex n) (DoubledIndex n) K :=
  Matrix.fromBlocks P 0 0 P⁻¹ᵀ

theorem padArr_inr₁ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (a : Fin n) (x y : DoubledIndex n) :
    padCoordinates A (Sum.inr a, x, y) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

theorem padArr_inr₂ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (x : DoubledIndex n) (a : Fin n) (y : DoubledIndex n) :
    padCoordinates A (x, Sum.inr a, y) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

theorem padArr_inr₃ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (x y : DoubledIndex n) (a : Fin n) :
    padCoordinates A (x, y, Sum.inr a) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

theorem act3D_hypLift_padArr {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K)
    (A : Fin n × Fin n × Fin n → K) :
    act3D K (hypLift P) (hypLift Q) (hypLift R) (padCoordinates A) = padCoordinates (act3 K P Q R A) := by
  funext y
  obtain ⟨i, j, k⟩ := y
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp [act3D, act3, hypLift, Fintype.sum_sum_type, padArr_inr₁, padArr_inr₂, padArr_inr₃]

def hypForm (n : ℕ) (ε : K) : Matrix (DoubledIndex n) (DoubledIndex n) K := Matrix.fromBlocks 0 1 (ε • 1) 0

def IsIsometry (n : ℕ) (ε : K) (g : Matrix (DoubledIndex n) (DoubledIndex n) K) : Prop :=
  gᵀ * hypForm n ε * g = hypForm n ε

theorem hypForm_mul_inv (n : ℕ) (ε : K) (hε : ε ≠ 0) :
    hypForm n ε * Matrix.fromBlocks 0 (ε⁻¹ • 1) 1 0 = 1 := by
  simp only [hypForm, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_zero,
    mul_inv_cancel₀ hε, inv_mul_cancel₀ hε, one_smul, Matrix.fromBlocks_one]

theorem isUnit_det_hypForm (n : ℕ) (ε : K) (hε : ε ≠ 0) : IsUnit (hypForm n ε).det := by
  have h := congrArg Matrix.det (hypForm_mul_inv n ε hε)
  rw [Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem isUnit_det_of_isometry {n : ℕ} {Φ g : Matrix (DoubledIndex n) (DoubledIndex n) K} (hΦ : IsUnit Φ.det)
    (h : gᵀ * Φ * g = Φ) : IsUnit g.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have h2 : (g.det * g.det) * Φ.det = 1 * Φ.det := by
    rw [one_mul]
    calc (g.det * g.det) * Φ.det = g.det * Φ.det * g.det := by ring
      _ = Φ.det := hd
  have h3 : g.det * g.det = 1 := mul_right_cancel₀ hΦ.ne_zero h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h3
  exact zero_ne_one h3

theorem hypLift_isIsometry {n : ℕ} (ε : K) (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) :
    IsIsometry n ε (hypLift P) := by
  unfold IsIsometry hypForm hypLift
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_transpose]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul P hP, Matrix.transpose_one]

theorem reindex3_padArr {n : ℕ} (A : Fin n × Fin n × Fin n → K) :
    reindex3 (finSumFinEquiv (m := n) (n := n)) finSumFinEquiv finSumFinEquiv (padCoordinates A) =
      cubeExt K (n + n) A := by
  funext y
  obtain ⟨y₁, y₂, y₃⟩ := y
  simp only [reindex3, cubeExt]
  induction y₁ using Fin.addCases with
  | left i =>
    induction y₂ using Fin.addCases with
    | left j =>
      induction y₃ using Fin.addCases with
      | left k => simp
      | right k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₃]
    | right j =>
      induction y₃ using Fin.addCases with
      | left k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₂]
      | right k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₂]
  | right i =>
    induction y₂ using Fin.addCases with
    | left j =>
      induction y₃ using Fin.addCases with
      | left k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₁]
      | right k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₁]
    | right j =>
      induction y₃ using Fin.addCases with
      | left k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₁]
      | right k =>
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        simp [padArr_inr₁]

theorem act3D_eq_act {n : ℕ} (g₁ g₂ g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    act3D K g₁ g₂ g₃ A = act g₁ g₂ g₃ A := by
  funext ⟨i, j, k⟩
  rfl

theorem gl3ti_of_padded {n : ℕ} (g₁ g₂ g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (h₁ : IsUnit g₁.det)
    (h₂ : IsUnit g₂.det) (h₃ : IsUnit g₃.det) (A B : Fin n × Fin n × Fin n → K)
    (h : act3D K g₁ g₂ g₃ (padCoordinates A) = padCoordinates B) : (GL3TI K).Rel n A B := by
  have hflat : ∃ P₁ P₂ P₃ : Matrix (DoubledIndex n) (DoubledIndex n) K,
      IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ (padCoordinates A) = padCoordinates B :=
    ⟨g₁, g₂, g₃, h₁, h₂, h₃, by rw [← act3D_eq_act]; exact h⟩
  rw [exists_act_reindex3 (finSumFinEquiv (m := n) (n := n)) finSumFinEquiv finSumFinEquiv,
    reindex3_padArr, reindex3_padArr, exists_det_iff_isUnit] at hflat
  have hle : n ≤ n + n := Nat.le_add_right n n
  exact (gl3ti_rel_iff A B).mpr ((cubeExt_equiv_iff (K := K) hle hle hle A B).mpr hflat)

theorem gl3ti_iff_tig_pad (Grp : ∀ n, Matrix (DoubledIndex n) (DoubledIndex n) K → Prop)
    (hunit : ∀ n (g : Matrix (DoubledIndex n) (DoubledIndex n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det → Grp n (hypLift P))
    {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (TIG Grp).Rel n (padCoordinates A) (padCoordinates B) := by
  constructor
  · intro hAB
    obtain ⟨P, Q, R, hP, hQ, hR, hact⟩ := (gl3ti_rel_iff A B).mp hAB
    refine ⟨hypLift P, hypLift Q, hypLift R, hlift n P ((Matrix.isUnit_iff_isUnit_det P).mp hP),
      hlift n Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ), hlift n R ((Matrix.isUnit_iff_isUnit_det R).mp hR), ?_⟩
    rw [act3D_hypLift_padArr, act3_eq_act, hact]
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
    exact gl3ti_of_padded g₁ g₂ g₃ (hunit n g₁ h₁) (hunit n g₂ h₂) (hunit n g₃ h₃) A B h

def leviProjection (Grp : ∀ n, Matrix (DoubledIndex n) (DoubledIndex n) K → Prop)
    (hunit : ∀ n (g : Matrix (DoubledIndex n) (DoubledIndex n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det → Grp n (hypLift P)) :
    Projection (GL3TI K) (TIG Grp) where
  size := id
  src := fun _ j => padSrc j
  polyBound := ⟨8, 1, fun n => by
    change Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) ≤
      8 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 1
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, pow_one]
    have : (n + n) * ((n + n) * (n + n)) = 8 * (n * (n * n)) := by ring
    omega⟩
  correct := fun _ A B => gl3ti_iff_tig_pad Grp hunit hlift A B

def TIIso (ε : K) : CoordProblem K := TIG (fun n g => IsIsometry n ε g)

def leviProjectionIso (ε : K) (hε : ε ≠ 0) : Projection (GL3TI K) (TIIso ε) :=
  leviProjection (fun n g => IsIsometry n ε g)
    (fun n g h => isUnit_det_of_isometry (isUnit_det_hypForm n ε hε) h)
    (fun n P hP => hypLift_isIsometry ε P hP)

theorem ti_reduces_tiIso (ε : K) (hε : ε ≠ 0) :
    (projectionSystem K).reduces (GL3TI K) (TIIso ε) :=
  ⟨leviProjectionIso ε hε⟩

theorem ti_class_le_tiIso_class (ε : K) (hε : ε ≠ 0) :
    problemClass (projectionSystem K) (GL3TI K) ⊆ problemClass (projectionSystem K) (TIIso ε) :=
  (problemClass_mono (projectionSystem K)) (ti_reduces_tiIso ε hε)

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

def blockLift {n : ℕ} (P X : Matrix (Fin n) (Fin n) K) : Matrix (DoubledIndex n) (DoubledIndex n) K :=
  Matrix.fromBlocks P 0 0 X

theorem act3D_blockLift_padArr {n : ℕ} (P Q R X Y Z : Matrix (Fin n) (Fin n) K)
    (A : Fin n × Fin n × Fin n → K) :
    act3D K (blockLift P X) (blockLift Q Y) (blockLift R Z) (padCoordinates A) =
      padCoordinates (act3 K P Q R A) := by
  funext y
  obtain ⟨i, j, k⟩ := y
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp [act3D, act3, blockLift, Fintype.sum_sum_type, padArr_inr₁, padArr_inr₂, padArr_inr₃]

theorem gl3ti_iff_tig_pad_gen (Grp : ∀ n, Matrix (DoubledIndex n) (DoubledIndex n) K → Prop)
    (hunit : ∀ n (g : Matrix (DoubledIndex n) (DoubledIndex n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det →
      ∃ X : Matrix (Fin n) (Fin n) K, Grp n (blockLift P X))
    {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (TIG Grp).Rel n (padCoordinates A) (padCoordinates B) := by
  constructor
  · intro hAB
    obtain ⟨P, Q, R, hP, hQ, hR, hact⟩ := (gl3ti_rel_iff A B).mp hAB
    obtain ⟨X, hX⟩ := hlift n P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
    obtain ⟨Y, hY⟩ := hlift n Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
    obtain ⟨Z, hZ⟩ := hlift n R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
    refine ⟨blockLift P X, blockLift Q Y, blockLift R Z, hX, hY, hZ, ?_⟩
    rw [act3D_blockLift_padArr, act3_eq_act, hact]
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
    exact gl3ti_of_padded g₁ g₂ g₃ (hunit n g₁ h₁) (hunit n g₂ h₂) (hunit n g₃ h₃) A B h

def leviProjectionGen (Grp : ∀ n, Matrix (DoubledIndex n) (DoubledIndex n) K → Prop)
    (hunit : ∀ n (g : Matrix (DoubledIndex n) (DoubledIndex n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det →
      ∃ X : Matrix (Fin n) (Fin n) K, Grp n (blockLift P X)) :
    Projection (GL3TI K) (TIG Grp) where
  size := id
  src := fun _ j => padSrc j
  polyBound := ⟨8, 1, fun n => by
    change Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) ≤
      8 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 1
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, pow_one]
    have : (n + n) * ((n + n) * (n + n)) = 8 * (n * (n * n)) := by ring
    omega⟩
  correct := fun _ A B => gl3ti_iff_tig_pad_gen Grp hunit hlift A B

end

end

section

section

variable {K : Type} [Field K] {n : ℕ}

private theorem unit_matrix {P : Matrix (Fin n) (Fin n) K} (h : IsUnit P.det) :
    IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 h

end

end

section

section

noncomputable section

open MvPolynomial Finset

section

variable {G : Type*} [CommGroup G] (n : ℕ)

def powSub : Subgroup G := (powMonoidHom n : G →* G).range

def prodHom : (G × G × G) →* G where
  toFun d := d.1 * d.2.1 * d.2.2
  map_one' := by simp
  map_mul' := by
    intro a b
    simp only [Prod.fst_mul, Prod.snd_mul]
    simp [mul_comm, mul_assoc, mul_left_comm]

def obHom : (G × G × G) →* (G ⧸ powSub (G := G) n) × (G ⧸ powSub (G := G) n) × G :=
  (((QuotientGroup.mk' (powSub (G := G) n)).comp (MonoidHom.fst G (G × G))).prod
    ((((QuotientGroup.mk' (powSub (G := G) n)).comp
        ((MonoidHom.fst G G).comp (MonoidHom.snd G (G × G)))).prod (prodHom (G := G)))))

@[simp] theorem obHom_apply (d : G × G × G) :
    obHom (G := G) n d = (QuotientGroup.mk d.1, QuotientGroup.mk d.2.1, d.1 * d.2.1 * d.2.2) :=
  rfl

end

section

def gGL : MvPolynomial (Fin 2) ℚ := X 0 * X 1 - 1

def gSL : MvPolynomial (Fin 2) ℚ := X 0 - 1

def specU : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ :=
  (MvPolynomial.aeval (R := ℚ) (fun i : Fin 2 => if i = 0 then (X 0 : MvPolynomial (Fin 2) ℚ)
    else 1)).toRingHom

@[simp] theorem specU_gGL : specU gGL = gSL := by
  simp [specU, gGL, gSL]

end

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

section

local instance instFact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def leviCivita5 (t : Fin 3 × Fin 3 × Fin 3) : ZMod 5 :=
  if t = (0, 1, 2) ∨ t = (1, 2, 0) ∨ t = (2, 0, 1) then 1
  else if t = (0, 2, 1) ∨ t = (2, 1, 0) ∨ t = (1, 0, 2) then -1
  else 0

end

end

end

section

section

universe u

variable {K : Type u} [Field K]

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ} (b₀ : β) (c₀ : γ) (r : ℕ)

theorem card_GR : Fintype.card (GR n r) = n * (2 ^ n * r) := by
  simp [GR, Fintype.card_prod, Fintype.card_fin]

theorem card_GRb_le (b : β) : Fintype.card (GRb b₀ (n := n) r b) ≤ n * (2 ^ n * r) :=
  (Fintype.card_subtype_le _).trans_eq (card_GR r)

theorem card_GCs_le (s : γ) :
    Fintype.card (GCs c₀ (n := n) (t := t) r s) ≤ t * (n * (2 ^ n * r)) := by
  refine (Fintype.card_subtype_le _).trans_eq ?_
  rw [Fintype.card_prod, Fintype.card_fin, card_GR]

theorem card_sigma_padRow_le :
    Fintype.card (Σ b, PadRow b₀ r (RowIdx := RowIdx) (n := n) b) ≤
      Fintype.card β * (n * (2 ^ n * r)) + Fintype.card (Σ b, RowIdx b) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp only [PadRow, Fintype.card_sum]
  rw [Finset.sum_add_distrib]
  gcongr with b
  · calc ∑ b : β, Fintype.card (GRb b₀ (n := n) r b) ≤ ∑ _b : β, n * (2 ^ n * r) :=
          Finset.sum_le_sum fun b _ => card_GRb_le b₀ r b
      _ = Fintype.card β * (n * (2 ^ n * r)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem card_sigma_padCol_le :
    Fintype.card (Σ s, PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t) s) ≤
      Fintype.card γ * (t * (n * (2 ^ n * r))) + Fintype.card (Σ s, ColIdx s) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp only [PadCol, Fintype.card_sum]
  rw [Finset.sum_add_distrib]
  gcongr with s
  · calc ∑ s : γ, Fintype.card (GCs c₀ (n := n) (t := t) r s) ≤ ∑ _s : γ, t * (n * (2 ^ n * r)) :=
          Finset.sum_le_sum fun s _ => card_GCs_le c₀ r s
      _ = Fintype.card γ * (t * (n * (2 ^ n * r))) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end

section

def meas (rows cols sl : ℕ) : ℕ := rows + cols + sl + 1

theorem one_le_meas (rows cols sl : ℕ) : 1 ≤ meas rows cols sl := by
  unfold meas; omega

theorem gadget_card_le {n c r m : ℕ} (hn : n ≤ c) (hr : r ≤ m) :
    n * (2 ^ n * r) ≤ c ^ 2 * 2 ^ c * m := by
  have h1 : 2 ^ n ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : n * (2 ^ n * r) ≤ c * (2 ^ c * m) := by
    apply Nat.mul_le_mul hn
    exact Nat.mul_le_mul h1 hr
  calc n * (2 ^ n * r) ≤ c * (2 ^ c * m) := h2
    _ ≤ c ^ 2 * 2 ^ c * m := by
        have : c ≤ c ^ 2 := by nlinarith [Nat.zero_le c]
        nlinarith [Nat.zero_le (2 ^ c * m)]

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

theorem stage_sides_le (b₀ : β) (c₀ : γ) {c : ℕ}
    (hc : Fintype.card β + Fintype.card γ + n + 2 ≤ c) :
    let rows := Fintype.card (Σ b, RowIdx b)
    let cols := Fintype.card (Σ s, ColIdx s)
    let m := meas rows cols t

    Fintype.card (Σ s, PadCol c₀ (rad RowIdx) (ColIdx := ColIdx) (n := n) (t := t) s) ≤
        (c ^ 3 * 2 ^ c + 1) * m ^ 2 ∧

    t ≤ (c ^ 3 * 2 ^ c + 1) * m ^ 2 ∧

    Fintype.card (Σ b, PadRow b₀ (rad RowIdx) (RowIdx := RowIdx) (n := n) b) ≤
        (c ^ 3 * 2 ^ c + 1) * m ^ 2 := by
  intro rows cols m
  have hm1 : 1 ≤ m := one_le_meas _ _ _
  have hrows : rows ≤ m := by unfold m meas; omega
  have hcols : cols ≤ m := by unfold m meas; omega
  have ht : t ≤ m := by unfold m meas; omega
  have hr : rad RowIdx ≤ m := by
    show Fintype.card (Σ b, RowIdx b) + 1 ≤ m
    unfold m meas rows; omega
  have hcb : Fintype.card β ≤ c := by omega
  have hcc : Fintype.card γ ≤ c := by omega
  have hn : n ≤ c := by omega
  have hg : n * (2 ^ n * rad RowIdx) ≤ c ^ 2 * 2 ^ c * m := gadget_card_le hn hr
  refine ⟨?_, ?_, ?_⟩
  · calc Fintype.card (Σ s, PadCol c₀ (rad RowIdx) (ColIdx := ColIdx) (n := n) (t := t) s)
        ≤ Fintype.card γ * (t * (n * (2 ^ n * rad RowIdx))) + cols := card_sigma_padCol_le c₀ _
      _ ≤ c * (m * (c ^ 2 * 2 ^ c * m)) + m := by gcongr
      _ ≤ (c ^ 3 * 2 ^ c + 1) * m ^ 2 := by
          have : c * (m * (c ^ 2 * 2 ^ c * m)) = c ^ 3 * 2 ^ c * m ^ 2 := by ring
          rw [this]
          have hmm : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
          nlinarith [hmm]
  · calc t ≤ m := ht
      _ ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
      _ ≤ (c ^ 3 * 2 ^ c + 1) * m ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
  · calc Fintype.card (Σ b, PadRow b₀ (rad RowIdx) (RowIdx := RowIdx) (n := n) b)
        ≤ Fintype.card β * (n * (2 ^ n * rad RowIdx)) + rows := card_sigma_padRow_le b₀ _
      _ ≤ c * (c ^ 2 * 2 ^ c * m) + m := by gcongr
      _ ≤ (c ^ 3 * 2 ^ c + 1) * m ^ 2 := by
          have hmm : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
          have : c * (c ^ 2 * 2 ^ c * m) = c ^ 3 * 2 ^ c * m := by ring
          rw [this]
          have h2 : c ^ 3 * 2 ^ c * m ≤ c ^ 3 * 2 ^ c * m ^ 2 := Nat.mul_le_mul_left _ hmm
          nlinarith [h2, hmm]

end

end

end

section

section

abbrev Kq (c : ℕ) : ℕ := c ^ 3 * 2 ^ c + 1

theorem one_le_Kq (c : ℕ) : 1 ≤ Kq c := Nat.le_add_left 1 _

theorem meas_le_of_sides {rows cols sl X : ℕ} (hr : rows ≤ X) (hc : cols ≤ X) (hs : sl ≤ X)
    (hX : 1 ≤ X) : meas rows cols sl ≤ 4 * X := by
  unfold meas; omega

theorem card_sigma_fin1 (t : ℕ) : Fintype.card (Σ _ : Fin 1, Fin t) = t := by simp

theorem iter3 {Kk m₀ m₁ m₂ s : ℕ} (h1 : m₁ ≤ Kk * m₀ ^ 2) (h2 : m₂ ≤ Kk * m₁ ^ 2)
    (h3 : s ≤ Kk * m₂ ^ 2) : s ≤ Kk ^ 7 * m₀ ^ 8 := by
  have h2' : m₂ ≤ Kk ^ 3 * m₀ ^ 4 := by
    calc m₂ ≤ Kk * m₁ ^ 2 := h2
      _ ≤ Kk * (Kk * m₀ ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
      _ = Kk ^ 3 * m₀ ^ 4 := by ring
  calc s ≤ Kk * m₂ ^ 2 := h3
    _ ≤ Kk * (Kk ^ 3 * m₀ ^ 4) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2' 2)
    _ = Kk ^ 7 * m₀ ^ 8 := by ring

theorem one_le_Kq_mul_sq (c m : ℕ) (hm : 1 ≤ m) : 1 ≤ Kq c * m ^ 2 :=
  Nat.mul_pos (one_le_Kq c) (pow_pos hm 2)

theorem Kq_mul_le (c m : ℕ) : Kq c * m ^ 2 ≤ 4 * Kq c * m ^ 2 :=
  Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left (Kq c) (by norm_num))

section

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

abbrev meas₀ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type)
    [∀ s, Fintype (ColIdx s)] (t : ℕ) : ℕ :=
  meas (Fintype.card (Σ b, RowIdx b)) (Fintype.card (Σ s, ColIdx s)) t

abbrev Kcomp (β γ : Type) [Fintype β] [Fintype γ] (n : ℕ) : ℕ :=
  4 * Kq (Fintype.card β + Fintype.card γ + n + 4)

theorem T_sides_le :
    Fintype.card (Σ b : Fin 1, PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ) b) ≤
      Kcomp β γ n ^ 7 * meas₀ RowIdx ColIdx t ^ 8 ∧
    Fintype.card (Σ s : Fin 1, PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ)
        (t := t₂ RowIdx ColIdx n t (b₀ γ)) s) ≤
      Kcomp β γ n ^ 7 * meas₀ RowIdx ColIdx t ^ 8 ∧
    t₂ RowIdx ColIdx n t (b₀ γ) ≤ Kcomp β γ n ^ 7 * meas₀ RowIdx ColIdx t ^ 8 := by
  have hc1 : Fintype.card β + Fintype.card γ + n + 2 ≤
      Fintype.card β + Fintype.card γ + n + 4 := by omega
  have hc2 : Fintype.card γ + Fintype.card (Fin 1) + Fintype.card β + 2 ≤
      Fintype.card β + Fintype.card γ + n + 4 := by
    simp only [Fintype.card_fin]; omega
  have hc3 : Fintype.card (Fin 1) + Fintype.card (Fin 1) + Fintype.card γ + 2 ≤
      Fintype.card β + Fintype.card γ + n + 4 := by
    simp only [Fintype.card_fin]; omega

  obtain ⟨a1, a2, a3⟩ := stage_sides_le (RowIdx := RowIdx) (ColIdx := ColIdx) (n := n) (t := t)
    (b₀ β) (b₀ γ) hc1

  obtain ⟨b1, b2, b3⟩ := stage_sides_le (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ)) (ColIdx := C₁ t)
    (n := Fintype.card β) (t := t₁ RowIdx n (b₀ β)) (b₀ γ) (0 : Fin 1) hc2

  obtain ⟨c1, c2, c3⟩ := stage_sides_le (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ))
    (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ))
    (0 : Fin 1) (0 : Fin 1) hc3
  have hm0 : 1 ≤ meas₀ RowIdx ColIdx t := one_le_meas _ _ _
  have h1 : meas (Fintype.card (Σ s, R₁ RowIdx ColIdx n t (b₀ γ) s))
      (Fintype.card (Σ s : Fin 1, C₁ t s)) (t₁ RowIdx n (b₀ β)) ≤
      Kcomp β γ n * meas₀ RowIdx ColIdx t ^ 2 := by
    rw [mul_assoc]
    exact meas_le_of_sides a1 ((card_sigma_fin1 t).le.trans a2) a3 (one_le_Kq_mul_sq _ _ hm0)
  have hm1 : 1 ≤ meas (Fintype.card (Σ s, R₁ RowIdx ColIdx n t (b₀ γ) s))
      (Fintype.card (Σ s : Fin 1, C₁ t s)) (t₁ RowIdx n (b₀ β)) := one_le_meas _ _ _
  have h2 : meas (Fintype.card (Σ b : Fin 1, R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ) b))
      (Fintype.card (Σ s : Fin 1, C₂ RowIdx n (b₀ β) s)) (t₂ RowIdx ColIdx n t (b₀ γ)) ≤
      Kcomp β γ n * (meas (Fintype.card (Σ s, R₁ RowIdx ColIdx n t (b₀ γ) s))
        (Fintype.card (Σ s : Fin 1, C₁ t s)) (t₁ RowIdx n (b₀ β))) ^ 2 := by
    rw [mul_assoc]
    exact meas_le_of_sides b1 ((card_sigma_fin1 _).le.trans b2) b3 (one_le_Kq_mul_sq _ _ hm1)
  refine ⟨iter3 h1 h2 (c3.trans (Kq_mul_le _ _)), iter3 h1 h2 (c1.trans (Kq_mul_le _ _)),
    iter3 h1 h2 (c2.trans (Kq_mul_le _ _))⟩

end

end

end

section

section

theorem exponent_decompositions : 21 = 16 + 4 + 1 ∧ 20 = 16 + 4 := ⟨by norm_num, by norm_num⟩

end

end

section

section

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M]

def F1 (φ : K → M) (x y : K) : M := φ (x * y)

def F2 (φ : K → M) (x y : K) : M := φ (x * y) + φ (y ^ 21)

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

noncomputable def k3 (n : ℕ) : Fin (thn n) := ((e3n n) ()).1

theorem strHn_k3 (n : ℕ) : strHn n (k3 n) = 3 := ((e3n n) ()).2

theorem eq_k3 (n : ℕ) {k : Fin (thn n)} (h : strHn n k = 3) : k = k3 n := by
  have h1 : (e3n n) ((e3n n).symm ⟨k, h⟩) = ⟨k, h⟩ := (e3n n).apply_symm_apply _
  have h2 : ((e3n n).symm ⟨k, h⟩) = () := Subsingleton.elim _ _
  rw [h2] at h1
  exact (congrArg Subtype.val h1).symm

theorem unit_matrix_ext {M N : Matrix Unit Unit K} (h : M () () = N () ()) : M = N := by
  ext i j
  cases i; cases j
  exact h

theorem unit_entry_ne_zero {M : Matrix Unit Unit K} (h : IsUnit M.det) : M () () ≠ 0 := by
  intro hc
  have h0 : M = 0 := unit_matrix_ext (by rw [hc]; simp)
  rw [h0] at h
  simp at h

theorem scaled_block {r c : Type} [Fintype r] [Fintype c] (a b : K)
    (M : Matrix r r K) (X : Matrix r c K) (N : Matrix c c K) :
    (a • M) * X * ((b • N))ᵀ = (a * b) • (M * X * Nᵀ) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, mul_comm b a]

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

noncomputable def Rres {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : SymplecticIndex n ≃ Fib strH γ)
    (R : Matrix (Fin th) (Fin th) K) : Matrix (SymplecticIndex n) (SymplecticIndex n) K :=
  Matrix.of fun x y => R (e x).1 (e y).1

theorem Rres_apply {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : SymplecticIndex n ≃ Fib strH γ)
    (R : Matrix (Fin th) (Fin th) K) (x y : SymplecticIndex n) :
    Rres (K := K) e R x y = R (e x).1 (e y).1 := rfl

theorem symm_coe {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : SymplecticIndex n ≃ Fib strH γ) (x : SymplecticIndex n)
    (h : strH (e x).1 = γ) : e.symm ⟨(e x).1, h⟩ = x := by
  have hs : (⟨(e x).1, h⟩ : Fib strH γ) = e x := Subtype.ext rfl
  rw [hs, Equiv.symm_apply_apply]

theorem anchorSlice_coupling {n : ℕ} (b s : Blk) (M : Matrix (BIdx n b) (BIdx n s) K)
    (X Y : PArr K Blk Blk (BIdx n) (BIdx n) (thn n))
    (hXon : X (k3 n) b s = M)
    (hXoff : ∀ k, strHn n k ≠ 3 → X k b s = 0)
    (hYon : Y (k3 n) b s = M)
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (hR1 : R (k3 n) (k3 n) = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    P b * M * (Q s)ᵀ = M := by
  classical
  have hsum : (∑ k', R (k3 n) k' • (P b * X k' b s * (Q s)ᵀ))
      = R (k3 n) (k3 n) • (P b * M * (Q s)ᵀ) := by
    rw [Finset.sum_eq_single (k3 n)]
    · rw [hXon]
    · intro k' _ hk'
      have hs : strHn n k' ≠ 3 := fun hc => hk' (eq_k3 n hc)
      rw [hXoff k' hs]
      simp
    · intro hnot
      exact absurd (Finset.mem_univ (k3 n)) hnot
  have h := heq (k3 n) b s
  rw [hYon, hsum, hR1, one_smul] at h
  exact h.symm

theorem stratumRow_coupling {n : ℕ} (b : Blk) {γ : Fin 4} (e : SymplecticIndex n ≃ Fib (strHn n) γ)
    (M : Matrix (BIdx n b) (SymplecticIndex n) K)
    (X Y : PArr K Blk Blk (BIdx n) (BIdx n) (thn n))
    (hXon : ∀ (k : Fin (thn n)) (h : strHn n k = γ) (i : BIdx n b) (u : BIdx n Blk.anch),
      X k b Blk.anch i u = M i (e.symm ⟨k, h⟩))
    (hXoff : ∀ k, strHn n k ≠ γ → X k b Blk.anch = 0)
    (hYon : ∀ (k : Fin (thn n)) (h : strHn n k = γ) (i : BIdx n b) (u : BIdx n Blk.anch),
      Y k b Blk.anch i u = M i (e.symm ⟨k, h⟩))
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (hQa : Q Blk.anch = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    P b * M * (Rres e R)ᵀ = M := by
  classical
  ext i x
  have hk : strHn n (e x).1 = γ := (e x).2
  have hex : e.symm ⟨(e x).1, hk⟩ = x := symm_coe e x hk
  have hQt : ((Q Blk.anch)ᵀ : Matrix (BIdx n Blk.anch) (BIdx n Blk.anch) K) = 1 := by
    rw [hQa, Matrix.transpose_one]

  have h := congrFun (congrFun (heq (e x).1 b Blk.anch) i) (default : BIdx n Blk.anch)
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (thn n),
      (R (e x).1 k' • (P b * X k' b Blk.anch * (Q Blk.anch)ᵀ)) i (default : BIdx n Blk.anch)
        = R (e x).1 k' * ∑ i', P b i i' * X k' b Blk.anch i' (default : BIdx n Blk.anch) := by
    intro k'
    rw [hQt, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (thn n), strHn n k' ≠ γ →
      R (e x).1 k' * ∑ i', P b i i' * X k' b Blk.anch i' (default : BIdx n Blk.anch) = 0 := by
    intro k' hk'
    rw [hXoff k' hk']
    simp
  rw [sum_fibre (strHn n) γ _ hzero] at h
  have hre : (∑ c : Fib (strHn n) γ,
        R (e x).1 c.1 * ∑ i', P b i i' * X c.1 b Blk.anch i' (default : BIdx n Blk.anch))
      = ∑ y : SymplecticIndex n, R (e x).1 (e y).1 * ∑ i', P b i i' * M i' y := by
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro y
    have hin : ∀ i' : BIdx n b,
        P b i i' * M i' y
          = P b i i' * X (e y).1 b Blk.anch i' (default : BIdx n Blk.anch) := by
      intro i'
      rw [hXon (e y).1 (e y).2 i' default, symm_coe e y (e y).2]
    rw [Finset.sum_congr rfl fun i' _ => hin i']
  rw [hre, hYon (e x).1 hk i default, hex] at h
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.transpose_apply, Rres_apply, Matrix.mul_apply, mul_comm]

theorem stratumCol_coupling {n : ℕ} (s : Blk) {γ : Fin 4} (e : SymplecticIndex n ≃ Fib (strHn n) γ)
    (M : Matrix (BIdx n s) (SymplecticIndex n) K)
    (X Y : PArr K Blk Blk (BIdx n) (BIdx n) (thn n))
    (hXon : ∀ (k : Fin (thn n)) (h : strHn n k = γ) (u : BIdx n Blk.anch) (j : BIdx n s),
      X k Blk.anch s u j = M j (e.symm ⟨k, h⟩))
    (hXoff : ∀ k, strHn n k ≠ γ → X k Blk.anch s = 0)
    (hYon : ∀ (k : Fin (thn n)) (h : strHn n k = γ) (u : BIdx n Blk.anch) (j : BIdx n s),
      Y k Blk.anch s u j = M j (e.symm ⟨k, h⟩))
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (hPa : P Blk.anch = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    Q s * M * (Rres e R)ᵀ = M := by
  classical
  ext j x
  have hk : strHn n (e x).1 = γ := (e x).2
  have hex : e.symm ⟨(e x).1, hk⟩ = x := symm_coe e x hk
  have h := congrFun (congrFun (heq (e x).1 Blk.anch s) (default : BIdx n Blk.anch)) j
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (thn n),
      (R (e x).1 k' • (P Blk.anch * X k' Blk.anch s * (Q s)ᵀ))
          (default : BIdx n Blk.anch) j
        = R (e x).1 k' * ∑ j', Q s j j' * X k' Blk.anch s (default : BIdx n Blk.anch) j' := by
    intro k'
    rw [hPa, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Matrix.transpose_apply, mul_comm]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (thn n), strHn n k' ≠ γ →
      R (e x).1 k' * ∑ j', Q s j j' * X k' Blk.anch s (default : BIdx n Blk.anch) j' = 0 := by
    intro k' hk'
    rw [hXoff k' hk']
    simp
  rw [sum_fibre (strHn n) γ _ hzero] at h
  have hre : (∑ c : Fib (strHn n) γ,
        R (e x).1 c.1 * ∑ j', Q s j j' * X c.1 Blk.anch s (default : BIdx n Blk.anch) j')
      = ∑ y : SymplecticIndex n, R (e x).1 (e y).1 * ∑ j', Q s j j' * M j' y := by
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro y
    have hin : ∀ j' : BIdx n s,
        Q s j j' * M j' y
          = Q s j j' * X (e y).1 Blk.anch s (default : BIdx n Blk.anch) j' := by
      intro j'
      rw [hXon (e y).1 (e y).2 default j', symm_coe e y (e y).2]
    rw [Finset.sum_congr rfl fun j' _ => hin j']
  rw [hre, hYon (e x).1 hk default j, hex] at h
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.transpose_apply, Rres_apply, Matrix.mul_apply, mul_comm]

theorem coupling_transpose {ι : Type} [Fintype ι]
    {Ψ g h : Matrix ι ι K} (hc : Coupling Ψ g h) : Coupling Ψᵀ h g := by
  rw [coupling_def] at hc ⊢
  have h1 := congrArg Matrix.transpose hc
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
  rw [Matrix.mul_assoc]
  exact h1

theorem coupling_one_symm {ι : Type} [Fintype ι] [DecidableEq ι]
    {g h : Matrix ι ι K} (hc : Coupling (1 : Matrix ι ι K) g h) :
    Coupling (1 : Matrix ι ι K) h g := by
  have := coupling_transpose hc
  rwa [Matrix.transpose_one] at this

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

theorem sum3_rotate {α : Type} [Fintype α] (F : α → α → α → K) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset α)) =>
    (Finset.sum_comm : (∑ a, ∑ c, F a b c) = ∑ c, ∑ a, F a b c)]
  rw [Finset.sum_comm]

end

end

section

section

universe u

set_option maxHeartbeats 800000

variable {K : Type u} [Field K]

theorem meas₀_H_le (n : ℕ) : meas₀ (BIdx n) (BIdx n) (thn n) ≤ 22 * (n + 1) := by
  have h : Fintype.card (Σ b : Blk, BIdx n b) = 6 * n + 1 := H_card_row n
  unfold meas₀ meas
  rw [h]
  have ht : thn n = 6 * n + 1 := rfl
  rw [ht]
  omega

theorem card_S3 (n : ℕ) : Fintype.card (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n) = 8 * n ^ 3 := by
  simp only [SymplecticIndex, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

theorem cube_succ_le (n : ℕ) : (n + 1) ^ 3 ≤ 8 * n ^ 3 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    have h2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right h (by norm_num)
    nlinarith [h1, h2]

theorem Nside_H_bound (n : ℕ) :
    Nside (BIdx n) (BIdx n) 4 (thn n) ^ 3 ≤
      (Kcomp Blk Blk 4 ^ 21 * 22 ^ 24) * (Fintype.card (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n) + 1) ^ 8 := by
  have hm := meas₀_H_le n
  have hN : Nside (BIdx n) (BIdx n) 4 (thn n) ≤
      Kcomp Blk Blk 4 ^ 7 * meas₀ (BIdx n) (BIdx n) (thn n) ^ 8 := by
    obtain ⟨ha, hb, hc⟩ := T_sides_le (RowIdx := BIdx n) (ColIdx := BIdx n) (n := 4) (t := thn n)
    exact max_le ha (max_le hb hc)
  rw [card_S3]
  have h3 := cube_succ_le n
  generalize hK : Kcomp Blk Blk 4 = Kk at hN ⊢
  generalize hM : meas₀ (BIdx n) (BIdx n) (thn n) = m₀ at hN hm ⊢
  calc Nside (BIdx n) (BIdx n) 4 (thn n) ^ 3
      ≤ (Kk ^ 7 * m₀ ^ 8) ^ 3 := Nat.pow_le_pow_left hN 3
    _ = Kk ^ 21 * (m₀ ^ 3) ^ 8 := by ring
    _ ≤ Kk ^ 21 * ((22 * (n + 1)) ^ 3) ^ 8 := by gcongr
    _ = (Kk ^ 21 * 22 ^ 24) * ((n + 1) ^ 3) ^ 8 := by ring
    _ ≤ (Kk ^ 21 * 22 ^ 24) * (8 * n ^ 3 + 1) ^ 8 := by gcongr

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coupling_smul {Ψ g h : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (H : Coupling (c • Ψ) g h) : Coupling Ψ g h := by
  rw [coupling_def] at H ⊢
  have key : c • (g * Ψ * hᵀ) = c • Ψ := by
    have e : g * (c • Ψ) * hᵀ = c • (g * Ψ * hᵀ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [← e]; exact H
  have h2 := congrArg (fun M : Matrix ι ι K => c⁻¹ • M) key
  simpa [smul_smul, inv_mul_cancel₀ hc] using h2

theorem coupling_symm_of_epsSym {Ψ g h : Matrix ι ι K} {ε : K} (hε : ε ≠ 0)
    (hsym : Ψᵀ = ε • Ψ) (hc : Coupling Ψ g h) : Coupling Ψ h g := by
  have h1 := coupling_transpose hc
  rw [hsym] at h1
  exact coupling_smul hε h1

theorem isUnit_det_of_covariant {Ψ g : Matrix ι ι K} (hΨ : IsUnit Ψ.det)
    (H : g * Ψ * gᵀ = Ψ) : IsUnit g.det := by
  have hd := congrArg Matrix.det H
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have h2 : (g.det * g.det) * Ψ.det = 1 * Ψ.det := by
    rw [one_mul]
    calc (g.det * g.det) * Ψ.det = g.det * Ψ.det * g.det := by ring
      _ = Ψ.det := hd
  have h3 : g.det * g.det = 1 := mul_right_cancel₀ hΨ.ne_zero h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h3
  exact zero_ne_one h3

theorem isUnit_det_of_contravariant {Φ g : Matrix ι ι K} (hΦ : IsUnit Φ.det)
    (H : gᵀ * Φ * g = Φ) : IsUnit g.det := by
  have hd := congrArg Matrix.det H
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have h2 : (g.det * g.det) * Φ.det = 1 * Φ.det := by
    rw [one_mul]
    calc (g.det * g.det) * Φ.det = g.det * Φ.det * g.det := by ring
      _ = Φ.det := hd
  have h3 : g.det * g.det = 1 := mul_right_cancel₀ hΦ.ne_zero h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h3
  exact zero_ne_one h3

theorem contravariant_of_covariant {Φ Ψ : Matrix ι ι K} (hΦΨ : Φ * Ψ = 1) (g : Matrix ι ι K)
    (H : g * Ψ * gᵀ = Ψ) : gᵀ * Φ * g = Φ := by
  have hΨΦ : Ψ * Φ = 1 := mul_eq_one_comm_sq hΦΨ
  have hdΨ : IsUnit Ψ.det := by
    have h := congrArg Matrix.det hΨΦ
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨Units.mkOfMulEqOne _ _ h, rfl⟩
  have hg : IsUnit g.det := isUnit_det_of_covariant hdΨ H
  have hinvΨ : Ψ⁻¹ = Φ := Matrix.inv_eq_right_inv hΨΦ
  have hT : gᵀ = Φ * g⁻¹ * Ψ := by
    have h1 := coupling_solve (Ψ := Ψ) (g := g) (h := g) hdΨ hg H
    rwa [hinvΨ] at h1
  calc gᵀ * Φ * g = (Φ * g⁻¹ * Ψ) * Φ * g := by rw [hT]
    _ = Φ * g⁻¹ * (Ψ * Φ) * g := by simp only [mul_assoc]
    _ = Φ * g⁻¹ * 1 * g := by rw [hΨΦ]
    _ = Φ * (g⁻¹ * g) := by rw [mul_one, mul_assoc]
    _ = Φ := by rw [Matrix.nonsing_inv_mul _ hg, mul_one]

theorem covariant_iff_contravariant_of_inverse {Φ Ψ : Matrix ι ι K} (hΦΨ : Φ * Ψ = 1)
    (g : Matrix ι ι K) : g * Ψ * gᵀ = Ψ ↔ gᵀ * Φ * g = Φ := by
  refine ⟨contravariant_of_covariant hΦΨ g, fun H => ?_⟩
  have hΨΦ : Ψ * Φ = 1 := mul_eq_one_comm_sq hΦΨ
  have h1 := contravariant_of_covariant hΨΦ gᵀ (by rw [Matrix.transpose_transpose]; exact H)
  rwa [Matrix.transpose_transpose] at h1

theorem chain_certifies_covariant {Ψ g h k : Matrix ι ι K}
    (H₁ : Coupling (1 : Matrix ι ι K) g h) (H₂ : Coupling (1 : Matrix ι ι K) h k)
    (HΨ : Coupling Ψ g k) : g * Ψ * gᵀ = Ψ := by
  have hkg : k = g := coupling_one_chain H₁ H₂
  rw [hkg] at HΨ
  exact HΨ

theorem gadget_constraints_certify_form {Ψ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Matrix ι ι K}
    (h₁₁ : Coupling (1 : Matrix ι ι K) a₁ b₁) (h₁₂ : Coupling (1 : Matrix ι ι K) b₁ c₁)
    (h₁₃ : Coupling Ψ a₁ c₁)
    (h₂₁ : Coupling (1 : Matrix ι ι K) a₂ b₂) (h₂₂ : Coupling (1 : Matrix ι ι K) b₂ c₂)
    (h₂₃ : Coupling Ψ a₂ c₂)
    (h₃₁ : Coupling (1 : Matrix ι ι K) a₃ b₃) (h₃₂ : Coupling (1 : Matrix ι ι K) b₃ c₃)
    (h₃₃ : Coupling Ψ a₃ c₃) :
    a₁ * Ψ * a₁ᵀ = Ψ ∧ a₂ * Ψ * a₂ᵀ = Ψ ∧ a₃ * Ψ * a₃ᵀ = Ψ :=
  ⟨chain_certifies_covariant h₁₁ h₁₂ h₁₃,
   chain_certifies_covariant h₂₁ h₂₂ h₂₃,
   chain_certifies_covariant h₃₁ h₃₂ h₃₃⟩

end

noncomputable def HgadgetF (n : ℕ) (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)
    (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) :
    PArr K Blk Blk (BIdx n) (BIdx n) th :=
  fun k b s =>
    match b, s with
    | Blk.dat, Blk.dat => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if h : strH k = 0 then A (i, j, (e0.symm ⟨k, h⟩ : SymplecticIndex n)) else 0
    | Blk.dat, Blk.cop => 0
    | Blk.dat, Blk.mid => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.dat, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 1 then Ψ i (e1.symm ⟨k, h⟩) else 0
    | Blk.cop, Blk.dat => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then Ψ i j else 0
    | Blk.cop, Blk.cop => 0
    | Blk.cop, Blk.mid => 0
    | Blk.cop, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.mid, Blk.dat => 0
    | Blk.mid, Blk.cop => Matrix.of fun (i : SymplecticIndex n) (j : SymplecticIndex n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.mid, Blk.mid => 0
    | Blk.mid, Blk.anch => Matrix.of fun (i : SymplecticIndex n) (_ : Unit) =>
        if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.dat => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.cop => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 0 then Ψ j (e0.symm ⟨k, h⟩) else 0
    | Blk.anch, Blk.mid => Matrix.of fun (_ : Unit) (j : SymplecticIndex n) =>
        if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.anch => Matrix.of fun (_ : Unit) (_ : Unit) =>
        if strH k = 3 then (1 : K) else 0

section

variable (n : ℕ) (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) {th : ℕ} (strH : Fin th → Fin 4)
  (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)
  (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (k : Fin th)

theorem HgadgetF_dat_dat (i : BIdx n Blk.dat) (j : BIdx n Blk.dat) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.dat i j
      = if h : strH k = 0 then A (i, j, (e0.symm ⟨k, h⟩ : SymplecticIndex n)) else 0 := rfl

theorem HgadgetF_dat_cop (i : BIdx n Blk.dat) (j : BIdx n Blk.cop) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.cop i j = 0 := rfl

theorem HgadgetF_dat_mid (i : BIdx n Blk.dat) (j : BIdx n Blk.mid) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.mid i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_dat_anch (i : BIdx n Blk.dat) (j : BIdx n Blk.anch) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.anch i j
      = if h : strH k = 1 then Ψ i (e1.symm ⟨k, h⟩) else 0 := rfl

theorem HgadgetF_cop_dat (i : BIdx n Blk.cop) (j : BIdx n Blk.dat) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.dat i j
      = if strH k = 3 then Ψ i j else 0 := rfl

theorem HgadgetF_cop_cop (i : BIdx n Blk.cop) (j : BIdx n Blk.cop) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.cop i j = 0 := rfl

theorem HgadgetF_cop_mid (i : BIdx n Blk.cop) (j : BIdx n Blk.mid) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.mid i j = 0 := rfl

theorem HgadgetF_cop_anch (i : BIdx n Blk.cop) (j : BIdx n Blk.anch) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.anch i j
      = if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_mid_dat (i : BIdx n Blk.mid) (j : BIdx n Blk.dat) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.dat i j = 0 := rfl

theorem HgadgetF_mid_cop (i : BIdx n Blk.mid) (j : BIdx n Blk.cop) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.cop i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_mid_mid (i : BIdx n Blk.mid) (j : BIdx n Blk.mid) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.mid i j = 0 := rfl

theorem HgadgetF_mid_anch (i : BIdx n Blk.mid) (j : BIdx n Blk.anch) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.anch i j
      = if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_anch_dat (i : BIdx n Blk.anch) (j : BIdx n Blk.dat) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.dat i j
      = if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_anch_cop (i : BIdx n Blk.anch) (j : BIdx n Blk.cop) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.cop i j
      = if h : strH k = 0 then Ψ j (e0.symm ⟨k, h⟩) else 0 := rfl

theorem HgadgetF_anch_mid (i : BIdx n Blk.anch) (j : BIdx n Blk.mid) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.mid i j
      = if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem HgadgetF_anch_anch (i : BIdx n Blk.anch) (j : BIdx n Blk.anch) :
    HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.anch i j
      = if strH k = 3 then (1 : K) else 0 := rfl

end

theorem const_src (n : ℕ) {c : K} (h : c = 0 ∨ c = 1 ∨ c = -1) :
    ∃ σ : Src (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n), ∀ A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K, c = (evalSource A σ) := by
  rcases h with h | h | h
  · exact ⟨Src.zero, fun _ => by rw [h]; rfl⟩
  · exact ⟨Src.one, fun _ => by rw [h]; rfl⟩
  · exact ⟨Src.negOne, fun _ => by rw [h]; rfl⟩

theorem HgadgetF_src (n : ℕ) (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (hΨ : ∀ i j, Ψ i j = 0 ∨ Ψ i j = 1 ∨ Ψ i j = -1)
    {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)
    (k : Fin th) (b s : Blk) (i : BIdx n b) (j : BIdx n s) :
    ∃ σ : Src (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n),
      ∀ A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K,
        HgadgetF (K := K) n Ψ strH e0 e1 e2 A k b s i j = (evalSource A σ) := by
  classical
  cases b <;> cases s

  · by_cases h : strH k = 0
    · exact ⟨Src.coord (i, j, (e0.symm ⟨k, h⟩ : SymplecticIndex n)), fun A => by
        rw [HgadgetF_dat_dat, dif_pos h]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_dat_dat, dif_neg h]; rfl⟩

  · exact ⟨Src.zero, fun A => by rw [HgadgetF_dat_cop]; rfl⟩

  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = j)
      exact ⟨σ, fun A => by rw [HgadgetF_dat_mid, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_dat_mid, if_neg h]; rfl⟩

  · by_cases h : strH k = 1
    · obtain ⟨σ, hσ⟩ := const_src (K := K) n (hΨ i (e1.symm ⟨k, h⟩))
      exact ⟨σ, fun A => by rw [HgadgetF_dat_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_dat_anch, dif_neg h]; rfl⟩

  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := const_src (K := K) n (hΨ i j)
      exact ⟨σ, fun A => by rw [HgadgetF_cop_dat, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_cop_dat, if_neg h]; rfl⟩

  · exact ⟨Src.zero, fun A => by rw [HgadgetF_cop_cop]; rfl⟩

  · exact ⟨Src.zero, fun A => by rw [HgadgetF_cop_mid]; rfl⟩

  · by_cases h : strH k = 2
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = e2.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [HgadgetF_cop_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_cop_anch, dif_neg h]; rfl⟩

  · exact ⟨Src.zero, fun A => by rw [HgadgetF_mid_dat]; rfl⟩

  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = j)
      exact ⟨σ, fun A => by rw [HgadgetF_mid_cop, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_mid_cop, if_neg h]; rfl⟩

  · exact ⟨Src.zero, fun A => by rw [HgadgetF_mid_mid]; rfl⟩

  · by_cases h : strH k = 0
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = e0.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [HgadgetF_mid_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_mid_anch, dif_neg h]; rfl⟩

  · by_cases h : strH k = 2
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (j = e2.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [HgadgetF_anch_dat, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_anch_dat, dif_neg h]; rfl⟩

  · by_cases h : strH k = 0
    · obtain ⟨σ, hσ⟩ := const_src (K := K) n (hΨ j (e0.symm ⟨k, h⟩))
      exact ⟨σ, fun A => by rw [HgadgetF_anch_cop, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_anch_cop, dif_neg h]; rfl⟩

  · by_cases h : strH k = 1
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (j = e1.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [HgadgetF_anch_mid, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_anch_mid, dif_neg h]; rfl⟩

  · by_cases h : strH k = 3
    · exact ⟨Src.one, fun A => by rw [HgadgetF_anch_anch, if_pos h]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [HgadgetF_anch_anch, if_neg h]; rfl⟩

noncomputable def HF (n : ℕ) (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) :
    PArr K Blk Blk (BIdx n) (BIdx n) (thn n) :=
  HgadgetF n Ψ (strHn n) (e0n n) (e1n n) (e2n n) A

theorem HF_src (n : ℕ) (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (hΨ : ∀ i j, Ψ i j = 0 ∨ Ψ i j = 1 ∨ Ψ i j = -1)
    (z : Fin (thn n) × (Σ b : Blk, BIdx n b) × (Σ s : Blk, BIdx n s)) :
    ∃ σ : Src (SymplecticIndex n × SymplecticIndex n × SymplecticIndex n),
      ∀ A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K,
        HF (K := K) n Ψ A z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 = (evalSource A σ) :=
  HgadgetF_src n Ψ hΨ (strHn n) (e0n n) (e1n n) (e2n n) z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2

section

variable {n : ℕ}

theorem anchor_scalar_prod_gen (X Y : PArr K Blk Blk (BIdx n) (BIdx n) (thn n))
    (hXon : X (k3 n) Blk.anch Blk.anch = 1)
    (hXoff : ∀ k, strHn n k ≠ 3 → X k Blk.anch Blk.anch = 0)
    (hYon : Y (k3 n) Blk.anch Blk.anch () () = 1)
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    R (k3 n) (k3 n) * (P Blk.anch () ()) * (Q Blk.anch () ()) = 1 := by
  classical
  have hsum : (∑ k', R (k3 n) k' • (P Blk.anch * X k' Blk.anch Blk.anch * (Q Blk.anch)ᵀ))
      = R (k3 n) (k3 n) • (P Blk.anch * (Q Blk.anch)ᵀ) := by
    rw [Finset.sum_eq_single (k3 n)]
    · rw [hXon, Matrix.mul_one]
    · intro k' _ hk'
      have hs : strHn n k' ≠ 3 := fun hc => hk' (eq_k3 n hc)
      rw [hXoff k' hs]
      simp
    · intro hnot
      exact absurd (Finset.mem_univ (k3 n)) hnot
  have h := congrFun (congrFun (heq (k3 n) Blk.anch Blk.anch) ()) ()
  rw [hYon, hsum] at h
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.univ_unique, Finset.sum_singleton, smul_eq_mul] at h
  rw [← mul_assoc] at h
  exact h.symm

theorem anchor_normalization_gen (X Y : PArr K Blk Blk (BIdx n) (BIdx n) (thn n))
    (hXon : X (k3 n) Blk.anch Blk.anch = 1)
    (hXoff : ∀ k, strHn n k ≠ 3 → X k Blk.anch Blk.anch = 0)
    (hYon : Y (k3 n) Blk.anch Blk.anch () () = 1)
    (h : BlockEquiv (strHn n) X Y) :
    ∃ (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
      (R : Matrix (Fin (thn n)) (Fin (thn n)) K),
      P Blk.anch = 1 ∧ Q Blk.anch = 1 ∧ R (k3 n) (k3 n) = 1 ∧
      (∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) := by
  classical
  obtain ⟨P, Q, R, hP, hQ, hR, hBD, heq⟩ := h
  have hprod : R (k3 n) (k3 n) * (P Blk.anch () ()) * (Q Blk.anch () ()) = 1 :=
    anchor_scalar_prod_gen X Y hXon hXoff hYon P Q R heq
  have hα : P Blk.anch () () ≠ 0 := unit_entry_ne_zero (hP Blk.anch)
  have hβ : Q Blk.anch () () ≠ 0 := unit_entry_ne_zero (hQ Blk.anch)
  have hγ : R (k3 n) (k3 n) ≠ 0 := by
    intro hc
    rw [hc] at hprod
    simp at hprod
  have hinv : (R (k3 n) (k3 n))⁻¹ * (P Blk.anch () ())⁻¹ * (Q Blk.anch () ())⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, hprod, inv_one]
  have hscal : (R (k3 n) (k3 n))⁻¹ * ((P Blk.anch () ())⁻¹ * (Q Blk.anch () ())⁻¹) = 1 := by
    rw [← mul_assoc]
    exact hinv
  refine ⟨fun b => (P Blk.anch () ())⁻¹ • P b,
    fun s => (Q Blk.anch () ())⁻¹ • Q s,
    (R (k3 n) (k3 n))⁻¹ • R, ?_, ?_, ?_, ?_⟩
  · exact unit_matrix_ext (by simp [inv_mul_cancel₀ hα, Matrix.one_apply])
  · exact unit_matrix_ext (by simp [inv_mul_cancel₀ hβ, Matrix.one_apply])
  · simp [inv_mul_cancel₀ hγ]
  · intro k b s
    rw [heq k b s]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [scaled_block, Matrix.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    linear_combination (-(R k k')) * hscal

end

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

section

variable {n : ℕ}

variable (K)

def colF {J : Type} (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m : SymplecticIndex n) : Matrix (SymplecticIndex n) J K :=
  Matrix.of fun i _ => Ψ i m

def rowF {I : Type} (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m : SymplecticIndex n) : Matrix I (SymplecticIndex n) K :=
  Matrix.of fun _ j => Ψ j m

variable {K} {I J : Type}

theorem mul_colF_entry (Ψ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m i : SymplecticIndex n) (u : J) :
    (g * colF K (J := J) Ψ m) i u = ∑ i', g i i' * Ψ i' m := by
  rw [Matrix.mul_apply]
  simp [colF]

theorem rowF_mul_entry (Ψ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (m j : SymplecticIndex n) (u : I) :
    (rowF K (I := I) Ψ m * gᵀ) u j = ∑ j', Ψ j' m * g j j' := by
  rw [Matrix.mul_apply]
  simp [rowF]

theorem covF_entry {Ψ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : g * Ψ * gᵀ = Ψ) (i x : SymplecticIndex n) :
    ∑ m, (∑ i', g i i' * Ψ i' m) * g x m = Ψ i x := by
  have hx := congrFun (congrFun h i) x
  rw [Matrix.mul_apply] at hx
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hx
  exact hx

theorem colF_transport {Ψ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : g * Ψ * gᵀ = Ψ) (x : SymplecticIndex n) :
    ∑ m, g x m • (g * colF K (J := J) Ψ m) = colF K Ψ x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colF_entry]
  simp only [colF, Matrix.of_apply]
  rw [← covF_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem rowF_transport {Ψ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K} (h : g * Ψ * gᵀ = Ψ) (x : SymplecticIndex n) :
    ∑ m, g x m • (rowF K (I := I) Ψ m * gᵀ) = rowF K Ψ x := by
  ext u j
  rw [sum_smul_entry]
  simp only [rowF_mul_entry]
  simp only [rowF, Matrix.of_apply]
  rw [← covF_entry h j x]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm (g x m)]
  congr 1
  exact Finset.sum_congr rfl fun j' _ => mul_comm _ _

end

section

variable {n th : ℕ} (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (strH : Fin th → Fin 4)
  (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)
  (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (k : Fin th)

local notation "HgF" => HgadgetF (K := K) n Ψ strH e0 e1 e2

theorem HmatF_dat_dat :
    HgF A k Blk.dat Blk.dat = if h : strH k = 0 then slice A (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_dat_dat]; by_cases h : strH k = 0 <;> simp [h, slice]

theorem HmatF_dat_cop : HgF A k Blk.dat Blk.cop = 0 := rfl

theorem HmatF_dat_mid :
    HgF A k Blk.dat Blk.mid = if strH k = 3 then (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) else 0 := by
  ext i j; rw [HgadgetF_dat_mid]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all

theorem HmatF_dat_anch :
    HgF A k Blk.dat Blk.anch = if h : strH k = 1 then colF K Ψ (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_dat_anch]; by_cases h : strH k = 1 <;> simp [h, colF]

theorem HmatF_cop_dat :
    HgF A k Blk.cop Blk.dat = if strH k = 3 then Ψ else 0 := by
  ext i j; rw [HgadgetF_cop_dat]; by_cases h : strH k = 3 <;> simp [h]

theorem HmatF_cop_cop : HgF A k Blk.cop Blk.cop = 0 := rfl

theorem HmatF_cop_mid : HgF A k Blk.cop Blk.mid = 0 := rfl

theorem HmatF_cop_anch :
    HgF A k Blk.cop Blk.anch = if h : strH k = 2 then colE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_cop_anch]; by_cases h : strH k = 2 <;> simp [h, colE]

theorem HmatF_mid_dat : HgF A k Blk.mid Blk.dat = 0 := rfl

theorem HmatF_mid_cop :
    HgF A k Blk.mid Blk.cop = if strH k = 3 then (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) else 0 := by
  ext i j; rw [HgadgetF_mid_cop]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all

theorem HmatF_mid_mid : HgF A k Blk.mid Blk.mid = 0 := rfl

theorem HmatF_mid_anch :
    HgF A k Blk.mid Blk.anch = if h : strH k = 0 then colE K (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_mid_anch]; by_cases h : strH k = 0 <;> simp [h, colE]

theorem HmatF_anch_dat :
    HgF A k Blk.anch Blk.dat = if h : strH k = 2 then rowE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_anch_dat]; by_cases h : strH k = 2 <;> simp [h, rowE]

theorem HmatF_anch_cop :
    HgF A k Blk.anch Blk.cop = if h : strH k = 0 then rowF K Ψ (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_anch_cop]; by_cases h : strH k = 0 <;> simp [h, rowF]

theorem HmatF_anch_mid :
    HgF A k Blk.anch Blk.mid = if h : strH k = 1 then rowE K (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [HgadgetF_anch_mid]; by_cases h : strH k = 1 <;> simp [h, rowE]

theorem HmatF_anch_anch :
    HgF A k Blk.anch Blk.anch = if strH k = 3 then (1 : Matrix Unit Unit K) else 0 := by
  ext i j; rw [HgadgetF_anch_anch]; by_cases h : strH k = 3 <;> simp [h, Matrix.one_apply]

end

section

variable {n th : ℕ} (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (strH : Fin th → Fin 4)
  (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)

theorem blockEquiv_of_form (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (hu₁ : IsUnit g₁.det) (hu₂ : IsUnit g₂.det) (hu₃ : IsUnit g₃.det)
    (hc₁ : g₁ * Ψ * g₁ᵀ = Ψ) (hc₂ : g₂ * Ψ * g₂ᵀ = Ψ) (hc₃ : g₃ * Ψ * g₃ᵀ = Ψ)
    (A B : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) (hAB : act3D K g₁ g₂ g₃ A = B) :
    BlockEquiv strH (HgadgetF (K := K) n Ψ strH e0 e1 e2 A)
      (HgadgetF (K := K) n Ψ strH e0 e1 e2 B) := by
  subst hAB
  refine ⟨Pfwd g₁ g₂ g₃, Qfwd g₁ g₂ g₃, Rfwd strH e0 e1 e2 g₁ g₂ g₃,
    Pfwd_isUnit g₁ g₂ g₃ hu₁ hu₂ hu₃, Qfwd_isUnit g₁ g₂ g₃ hu₁ hu₂ hu₃,
    Rfwd_isUnit strH e0 e1 e2 g₁ g₂ g₃ hu₁ hu₂ hu₃, Rfwd_isBlockDiag strH e0 e1 e2 g₁ g₂ g₃,
    fun k b s => ?_⟩
  have hR0 := Rst_zero strH e0 e1 e2 g₁ g₂ g₃
  have hR1 := Rst_one strH e0 e1 e2 g₁ g₂ g₃
  have hR2 := Rst_two strH e0 e1 e2 g₁ g₂ g₃
  have hR3 := Rst_three strH e0 e1 e2 g₁ g₂ g₃
  cases b <;> cases s

  · simp only [HmatF_dat_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₁ g₂
      (fun k' => if h : strH k' = 0 then slice A (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => slice A m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      exact act3D_slice g₁ g₂ g₃ A _
    · rw [dif_neg h, dif_neg h]

  · simp [HmatF_dat_cop]

  · simp only [HmatF_dat_mid, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ g₁ (invT g₁)
      (fun k' => if strH k' = 3 then (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, mul_invT_transpose hu₁]
    · rw [if_neg h, if_neg h]

  · simp only [HmatF_dat_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₁ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 1 then colF K Ψ (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => colF K Ψ m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colF_transport hc₁ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp only [HmatF_cop_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ g₂ g₂ (fun k' => if strH k' = 3 then Ψ else 0) Ψ
      (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]
      exact hc₂.symm
    · rw [if_neg h, if_neg h]

  · simp [HmatF_cop_cop]

  · simp [HmatF_cop_mid]

  · simp only [HmatF_cop_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₂ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 2 then colE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (invT g₂) hR2 (fun m => colE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp [HmatF_mid_dat]

  · simp only [HmatF_mid_cop, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ (invT g₃) g₃
      (fun k' => if strH k' = 3 then (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, invT_mul_transpose hu₃]
    · rw [if_neg h, if_neg h]

  · simp [HmatF_mid_mid]

  · simp only [HmatF_mid_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (invT g₃) (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 0 then colE K (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => colE K m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colE_transport hu₃ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp only [HmatF_anch_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) g₂
      (fun k' => if h : strH k' = 2 then rowE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (invT g₂) hR2 (fun m => rowE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp only [HmatF_anch_cop, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) g₃
      (fun k' => if h : strH k' = 0 then rowF K Ψ (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => rowF K Ψ m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowF_transport hc₃ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp only [HmatF_anch_mid, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) (invT g₁)
      (fun k' => if h : strH k' = 1 then rowE K (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => rowE K m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowE_transport hu₁ _).symm
    · rw [dif_neg h, dif_neg h]

  · simp only [HmatF_anch_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ (1 : Matrix Unit Unit K) (1 : Matrix Unit Unit K)
      (fun k' => if strH k' = 3 then (1 : Matrix Unit Unit K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]

end

section

variable {n : ℕ} (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K)

theorem HF_dat_mid_on : HF (K := K) n Ψ A (k3 n) Blk.dat Blk.mid = 1 := by
  ext i j
  rw [HF, HgadgetF_dat_mid, if_pos (strHn_k3 n), Matrix.one_apply]

theorem HF_dat_mid_off {k : Fin (thn n)} (h : strHn n k ≠ 3) :
    HF (K := K) n Ψ A k Blk.dat Blk.mid = 0 := by
  ext i j
  rw [HF, HgadgetF_dat_mid, if_neg h]
  simp

theorem HF_mid_cop_on : HF (K := K) n Ψ A (k3 n) Blk.mid Blk.cop = 1 := by
  ext i j
  rw [HF, HgadgetF_mid_cop, if_pos (strHn_k3 n), Matrix.one_apply]

theorem HF_mid_cop_off {k : Fin (thn n)} (h : strHn n k ≠ 3) :
    HF (K := K) n Ψ A k Blk.mid Blk.cop = 0 := by
  ext i j
  rw [HF, HgadgetF_mid_cop, if_neg h]
  simp

theorem HF_cop_dat_on : HF (K := K) n Ψ A (k3 n) Blk.cop Blk.dat = Ψ := by
  ext i j
  rw [HF, HgadgetF_cop_dat, if_pos (strHn_k3 n)]

theorem HF_cop_dat_off {k : Fin (thn n)} (h : strHn n k ≠ 3) :
    HF (K := K) n Ψ A k Blk.cop Blk.dat = 0 := by
  ext i j
  rw [HF, HgadgetF_cop_dat, if_neg h]
  simp

theorem HF_dat_anch_on (k : Fin (thn n)) (h : strHn n k = 1)
    (i : BIdx n Blk.dat) (u : BIdx n Blk.anch) :
    HF (K := K) n Ψ A k Blk.dat Blk.anch i u = Ψ i ((e1n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_dat_anch, dif_pos h]

theorem HF_dat_anch_off {k : Fin (thn n)} (h : strHn n k ≠ 1) :
    HF (K := K) n Ψ A k Blk.dat Blk.anch = 0 := by
  ext i u
  rw [HF, HgadgetF_dat_anch, dif_neg h]
  simp

theorem HF_mid_anch_on (k : Fin (thn n)) (h : strHn n k = 0)
    (i : BIdx n Blk.mid) (u : BIdx n Blk.anch) :
    HF (K := K) n Ψ A k Blk.mid Blk.anch i u = (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) i ((e0n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_mid_anch, dif_pos h, Matrix.one_apply]

theorem HF_mid_anch_off {k : Fin (thn n)} (h : strHn n k ≠ 0) :
    HF (K := K) n Ψ A k Blk.mid Blk.anch = 0 := by
  ext i u
  rw [HF, HgadgetF_mid_anch, dif_neg h]
  simp

theorem HF_cop_anch_on (k : Fin (thn n)) (h : strHn n k = 2)
    (i : BIdx n Blk.cop) (u : BIdx n Blk.anch) :
    HF (K := K) n Ψ A k Blk.cop Blk.anch i u = (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) i ((e2n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_cop_anch, dif_pos h, Matrix.one_apply]

theorem HF_cop_anch_off {k : Fin (thn n)} (h : strHn n k ≠ 2) :
    HF (K := K) n Ψ A k Blk.cop Blk.anch = 0 := by
  ext i u
  rw [HF, HgadgetF_cop_anch, dif_neg h]
  simp

theorem HF_anch_cop_on (k : Fin (thn n)) (h : strHn n k = 0)
    (u : BIdx n Blk.anch) (j : BIdx n Blk.cop) :
    HF (K := K) n Ψ A k Blk.anch Blk.cop u j = Ψ j ((e0n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_anch_cop, dif_pos h]

theorem HF_anch_cop_off {k : Fin (thn n)} (h : strHn n k ≠ 0) :
    HF (K := K) n Ψ A k Blk.anch Blk.cop = 0 := by
  ext u j
  rw [HF, HgadgetF_anch_cop, dif_neg h]
  simp

theorem HF_anch_mid_on (k : Fin (thn n)) (h : strHn n k = 1)
    (u : BIdx n Blk.anch) (j : BIdx n Blk.mid) :
    HF (K := K) n Ψ A k Blk.anch Blk.mid u j = (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) j ((e1n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_anch_mid, dif_pos h, Matrix.one_apply]

theorem HF_anch_mid_off {k : Fin (thn n)} (h : strHn n k ≠ 1) :
    HF (K := K) n Ψ A k Blk.anch Blk.mid = 0 := by
  ext u j
  rw [HF, HgadgetF_anch_mid, dif_neg h]
  simp

theorem HF_anch_dat_on (k : Fin (thn n)) (h : strHn n k = 2)
    (u : BIdx n Blk.anch) (j : BIdx n Blk.dat) :
    HF (K := K) n Ψ A k Blk.anch Blk.dat u j = (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) j ((e2n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_anch_dat, dif_pos h, Matrix.one_apply]

theorem HF_anch_dat_off {k : Fin (thn n)} (h : strHn n k ≠ 2) :
    HF (K := K) n Ψ A k Blk.anch Blk.dat = 0 := by
  ext u j
  rw [HF, HgadgetF_anch_dat, dif_neg h]
  simp

theorem HF_anch_anch_entry : HF (K := K) n Ψ A (k3 n) Blk.anch Blk.anch () () = 1 := by
  rw [HF, HgadgetF_anch_anch, if_pos (strHn_k3 n)]

theorem HF_anch_anch_on : HF (K := K) n Ψ A (k3 n) Blk.anch Blk.anch = 1 :=
  unit_matrix_ext (by rw [HF_anch_anch_entry]; simp [Matrix.one_apply])

theorem HF_anch_anch_off {k : Fin (thn n)} (h : strHn n k ≠ 3) :
    HF (K := K) n Ψ A k Blk.anch Blk.anch = 0 :=
  unit_matrix_ext (by rw [HF, HgadgetF_anch_anch, if_neg h]; simp)

theorem HF_dat_dat_on (k : Fin (thn n)) (h : strHn n k = 0) (i j : BIdx n Blk.dat) :
    HF (K := K) n Ψ A k Blk.dat Blk.dat i j = A (i, j, (e0n n).symm ⟨k, h⟩) := by
  rw [HF, HgadgetF_dat_dat, dif_pos h]

theorem HF_dat_dat_off {k : Fin (thn n)} (h : strHn n k ≠ 0) :
    HF (K := K) n Ψ A k Blk.dat Blk.dat = 0 := by
  ext i j
  rw [HF, HgadgetF_dat_dat, dif_neg h]
  simp

end

section

variable {n : ℕ}

theorem covariant_of_normalised (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) {ε : K} (hε : ε ≠ 0)
    (hsym : Ψᵀ = ε • Ψ) (A B : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K)
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (hPa : P Blk.anch = 1) (hQa : Q Blk.anch = 1) (hR1 : R (k3 n) (k3 n) = 1)
    (heq : ∀ k b s, HF (K := K) n Ψ B k b s
      = ∑ k', R k k' • (P b * HF (K := K) n Ψ A k' b s * (Q s)ᵀ)) :
    (P Blk.dat) * Ψ * (P Blk.dat)ᵀ = Ψ ∧ (Q Blk.dat) * Ψ * (Q Blk.dat)ᵀ = Ψ ∧
      (Rres (e0n n) R) * Ψ * (Rres (e0n n) R)ᵀ = Ψ := by

  have h11 : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (P Blk.dat) (Q Blk.mid) :=
    anchorSlice_coupling Blk.dat Blk.mid 1 (HF n Ψ A) (HF n Ψ B) (HF_dat_mid_on Ψ A)
      (fun _ hk => HF_dat_mid_off Ψ A hk) (HF_dat_mid_on Ψ B) P Q R hR1 heq

  have h32 : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (P Blk.mid) (Q Blk.cop) :=
    anchorSlice_coupling Blk.mid Blk.cop 1 (HF n Ψ A) (HF n Ψ B) (HF_mid_cop_on Ψ A)
      (fun _ hk => HF_mid_cop_off Ψ A hk) (HF_mid_cop_on Ψ B) P Q R hR1 heq

  have h23' : Coupling Ψ (P Blk.cop) (Q Blk.dat) :=
    anchorSlice_coupling Blk.cop Blk.dat Ψ (HF n Ψ A) (HF n Ψ B) (HF_cop_dat_on Ψ A)
      (fun _ hk => HF_cop_dat_off Ψ A hk) (HF_cop_dat_on Ψ B) P Q R hR1 heq

  have h13 : Coupling Ψ (P Blk.dat) (Rres (e1n n) R) :=
    stratumRow_coupling Blk.dat (e1n n) Ψ (HF n Ψ A) (HF n Ψ B)
      (fun k h i u => HF_dat_anch_on Ψ A k h i u)
      (fun _ hk => HF_dat_anch_off Ψ A hk)
      (fun k h i u => HF_dat_anch_on Ψ B k h i u) P Q R hQa heq

  have h31' : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (P Blk.mid) (Rres (e0n n) R) :=
    stratumRow_coupling Blk.mid (e0n n) 1 (HF n Ψ A) (HF n Ψ B)
      (fun k h i u => HF_mid_anch_on Ψ A k h i u)
      (fun _ hk => HF_mid_anch_off Ψ A hk)
      (fun k h i u => HF_mid_anch_on Ψ B k h i u) P Q R hQa heq

  have h22' : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (P Blk.cop) (Rres (e2n n) R) :=
    stratumRow_coupling Blk.cop (e2n n) 1 (HF n Ψ A) (HF n Ψ B)
      (fun k h i u => HF_cop_anch_on Ψ A k h i u)
      (fun _ hk => HF_cop_anch_off Ψ A hk)
      (fun k h i u => HF_cop_anch_on Ψ B k h i u) P Q R hQa heq

  have h33' : Coupling Ψ (Q Blk.cop) (Rres (e0n n) R) :=
    stratumCol_coupling Blk.cop (e0n n) Ψ (HF n Ψ A) (HF n Ψ B)
      (fun k h u j => HF_anch_cop_on Ψ A k h u j)
      (fun _ hk => HF_anch_cop_off Ψ A hk)
      (fun k h u j => HF_anch_cop_on Ψ B k h u j) P Q R hPa heq

  have h12 : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (Q Blk.mid) (Rres (e1n n) R) :=
    stratumCol_coupling Blk.mid (e1n n) 1 (HF n Ψ A) (HF n Ψ B)
      (fun k h u j => HF_anch_mid_on Ψ A k h u j)
      (fun _ hk => HF_anch_mid_off Ψ A hk)
      (fun k h u j => HF_anch_mid_on Ψ B k h u j) P Q R hPa heq

  have h21 : Coupling (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (Q Blk.dat) (Rres (e2n n) R) :=
    stratumCol_coupling Blk.dat (e2n n) 1 (HF n Ψ A) (HF n Ψ B)
      (fun k h u j => HF_anch_dat_on Ψ A k h u j)
      (fun _ hk => HF_anch_dat_off Ψ A hk)
      (fun k h u j => HF_anch_dat_on Ψ B k h u j) P Q R hPa heq
  exact gadget_constraints_certify_form h11 h12 h13 h21 (coupling_one_symm h22')
    (coupling_symm_of_epsSym hε hsym h23') (coupling_one_symm h31') h32
    (coupling_symm_of_epsSym hε hsym h33')

theorem data_equationF (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) (A B : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K)
    (P Q : ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K)
    (R : Matrix (Fin (thn n)) (Fin (thn n)) K)
    (heq : ∀ k b s, HF (K := K) n Ψ B k b s
      = ∑ k', R k k' • (P b * HF (K := K) n Ψ A k' b s * (Q s)ᵀ)) :
    act3D K (P Blk.dat) (Q Blk.dat) (Rres (e0n n) R) A = B := by
  classical
  funext p
  obtain ⟨i, j, x⟩ := p
  have hk : strHn n (e0n n x).1 = 0 := (e0n n x).2
  have hex : (e0n n).symm ⟨(e0n n x).1, hk⟩ = x := symm_coe (e0n n) x hk
  have h := congrFun (congrFun (heq (e0n n x).1 Blk.dat Blk.dat) i) j
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (thn n),
      (R (e0n n x).1 k' • (P Blk.dat * HF (K := K) n Ψ A k' Blk.dat Blk.dat * (Q Blk.dat)ᵀ)) i j
        = R (e0n n x).1 k'
            * ∑ j', (∑ i', P Blk.dat i i' * HF (K := K) n Ψ A k' Blk.dat Blk.dat i' j')
                * Q Blk.dat j j' := by
    intro k'
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Matrix.transpose_apply, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (thn n), strHn n k' ≠ 0 →
      R (e0n n x).1 k'
          * ∑ j', (∑ i', P Blk.dat i i' * HF (K := K) n Ψ A k' Blk.dat Blk.dat i' j')
              * Q Blk.dat j j' = 0 := by
    intro k' hk'
    rw [HF_dat_dat_off Ψ A hk']
    simp
  rw [sum_fibre (strHn n) 0 _ hzero] at h
  have hre : (∑ c : Fib (strHn n) 0, R (e0n n x).1 c.1
        * ∑ j', (∑ i', P Blk.dat i i' * HF (K := K) n Ψ A c.1 Blk.dat Blk.dat i' j')
            * Q Blk.dat j j')
      = ∑ y : SymplecticIndex n, R (e0n n x).1 (e0n n y).1
        * ∑ j', (∑ i', P Blk.dat i i' * A (i', j', y)) * Q Blk.dat j j' := by
    refine (Fintype.sum_equiv (e0n n) _ _ ?_).symm
    intro y
    have hin : ∀ j' i' : BIdx n Blk.dat,
        P Blk.dat i i' * A (i', j', y)
          = P Blk.dat i i' * HF (K := K) n Ψ A (e0n n y).1 Blk.dat Blk.dat i' j' := by
      intro j' i'
      rw [HF_dat_dat_on Ψ A (e0n n y).1 (e0n n y).2 i' j', symm_coe (e0n n) y (e0n n y).2]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Finset.sum_congr rfl fun i' _ => hin j' i']
  rw [hre, HF_dat_dat_on Ψ B (e0n n x).1 hk i j, hex] at h
  rw [h]
  show (∑ i', ∑ j', ∑ y, P Blk.dat i i' * Q Blk.dat j j'
        * Rres (e0n n) R x y * A (i', j', y))
      = ∑ y : SymplecticIndex n, R (e0n n x).1 (e0n n y).1
          * ∑ j', (∑ i', P Blk.dat i i' * A (i', j', y)) * Q Blk.dat j j'
  rw [sum3_rotate]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Rres_apply]
  ring

theorem form_of_blockEquiv_HF (Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) {ε : K} (hε : ε ≠ 0)
    (hsym : Ψᵀ = ε • Ψ) (A B : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K)
    (h : BlockEquiv (strHn n) (HF (K := K) n Ψ A) (HF (K := K) n Ψ B)) :
    ∃ g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K,
      g₁ * Ψ * g₁ᵀ = Ψ ∧ g₂ * Ψ * g₂ᵀ = Ψ ∧ g₃ * Ψ * g₃ᵀ = Ψ ∧ act3D K g₁ g₂ g₃ A = B := by
  obtain ⟨P, Q, R, hPa, hQa, hR1, heq⟩ :=
    anchor_normalization_gen (HF (K := K) n Ψ A) (HF (K := K) n Ψ B)
      (HF_anch_anch_on Ψ A) (fun _ hk => HF_anch_anch_off Ψ A hk) (HF_anch_anch_entry Ψ B) h
  obtain ⟨h1, h2, h3⟩ := covariant_of_normalised Ψ hε hsym A B P Q R hPa hQa hR1 heq
  exact ⟨P Blk.dat, Q Blk.dat, Rres (e0n n) R, h1, h2, h3, data_equationF Ψ A B P Q R heq⟩

end

theorem form_rel_iff_blockEquiv {n : ℕ} (Φ Ψ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) {ε : K} (hε : ε ≠ 0)
    (hΦΨ : Φ * Ψ = 1) (hsym : Ψᵀ = ε • Ψ) (A B : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K) :
    (∃ g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K,
        g₁ᵀ * Φ * g₁ = Φ ∧ g₂ᵀ * Φ * g₂ = Φ ∧ g₃ᵀ * Φ * g₃ = Φ ∧ act3D K g₁ g₂ g₃ A = B) ↔
      BlockEquiv (strHn n) (HF (K := K) n Ψ A) (HF (K := K) n Ψ B) := by
  have hdΦ : IsUnit Φ.det := by
    have hd := congrArg Matrix.det hΦΨ
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩
  constructor
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, hact⟩
    exact blockEquiv_of_form Ψ (strHn n) (e0n n) (e1n n) (e2n n) g₁ g₂ g₃
      (isUnit_det_of_contravariant hdΦ h₁) (isUnit_det_of_contravariant hdΦ h₂)
      (isUnit_det_of_contravariant hdΦ h₃)
      ((covariant_iff_contravariant_of_inverse hΦΨ g₁).mpr h₁)
      ((covariant_iff_contravariant_of_inverse hΦΨ g₂).mpr h₂)
      ((covariant_iff_contravariant_of_inverse hΦΨ g₃).mpr h₃) A B hact
  · intro h
    obtain ⟨g₁, g₂, g₃, c₁, c₂, c₃, hact⟩ := form_of_blockEquiv_HF Ψ hε hsym A B h
    exact ⟨g₁, g₂, g₃, (covariant_iff_contravariant_of_inverse hΦΨ g₁).mp c₁,
      (covariant_iff_contravariant_of_inverse hΦΨ g₂).mp c₂,
      (covariant_iff_contravariant_of_inverse hΦΨ g₃).mp c₃, hact⟩

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

def IsIso {n : ℕ} (Φ g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) : Prop := gᵀ * Φ * g = Φ

def TIForm (K : Type u) [Field K] (Φfam : ∀ n, Matrix (SymplecticIndex n) (SymplecticIndex n) K) : CoordProblem K :=
  TIG (fun n g => IsIso (Φfam n) g)

theorem HF_srcExpr (Ψfam : ∀ n, Matrix (SymplecticIndex n) (SymplecticIndex n) K)
    (hsrc : ∀ n i j, Ψfam n i j = 0 ∨ Ψfam n i j = 1 ∨ Ψfam n i j = -1) (n : ℕ) :
    SrcExpr (fun A : SymplecticIndex n × SymplecticIndex n × SymplecticIndex n → K => toFun (HF n (Ψfam n) A)) :=
  fun z => HF_src (K := K) n (Ψfam n) (hsrc n) z

theorem tiForm_rel_iff (Φfam Ψfam : ∀ n, Matrix (SymplecticIndex n) (SymplecticIndex n) K) {ε : K} (hε : ε ≠ 0)
    (hmul : ∀ n, Φfam n * Ψfam n = 1) (hsym : ∀ n, (Ψfam n)ᵀ = ε • Ψfam n)
    (n : ℕ) (A B : (TIForm K Φfam).Idx n → K) :
    (TIForm K Φfam).Rel n A B ↔
      BlockEquiv (strHn n) (HF (K := K) n (Ψfam n) A) (HF (K := K) n (Ψfam n) B) :=
  form_rel_iff_blockEquiv (Φfam n) (Ψfam n) hε (hmul n) (hsym n) A B

noncomputable def formProjection (Φfam Ψfam : ∀ n, Matrix (SymplecticIndex n) (SymplecticIndex n) K) {ε : K} (hε : ε ≠ 0)
    (hmul : ∀ n, Φfam n * Ψfam n = 1)
    (hsym : ∀ n, (Ψfam n)ᵀ = ε • Ψfam n)
    (hsrc : ∀ n i j, Ψfam n i j = 0 ∨ Ψfam n i j = 1 ∨ Ψfam n i j = -1) :
    Projection (TIForm K Φfam) (GL3TI K) :=
  projectionOfEncoding (TIForm K Φfam) (fun n => BIdx n) (fun n => BIdx n) thn (fun _ => 4) strHn
    (fun n A => HF n (Ψfam n) A)
    (tiForm_rel_iff Φfam Ψfam hε hmul hsym)
    (HF_srcExpr Ψfam hsrc)
    ⟨Kcomp Blk Blk 4 ^ 21 * 22 ^ 24, 8,
      Nside_H_bound⟩

section

variable (n : ℕ) (ε : K)

theorem hypForm_mul_self : hypForm n ε * hypForm n ε = ε • (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) := by
  rw [show (1 : Matrix (SymplecticIndex n) (SymplecticIndex n) K) = Matrix.fromBlocks 1 0 0 1 from Matrix.fromBlocks_one.symm]
  simp only [hypForm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp

theorem hypForm_transpose (hεε : ε * ε = 1) : (hypForm n ε)ᵀ = ε • hypForm n ε := by
  simp only [hypForm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_smul, smul_zero, smul_smul, hεε, one_smul]

variable {n ε}

theorem hypForm_entry_src (hε : ε = 1 ∨ ε = -1) (i j : SymplecticIndex n) :
    hypForm n ε i j = 0 ∨ hypForm n ε i j = 1 ∨ hypForm n ε i j = -1 := by
  classical
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [hypForm, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact Or.inl (by simp)
  · by_cases h : i = j
    · exact Or.inr (Or.inl (by simp [Matrix.one_apply, h]))
    · exact Or.inl (by simp [Matrix.one_apply, h])
  · by_cases h : i = j
    · rcases hε with h1 | h1 <;> subst h1
      · exact Or.inr (Or.inl (by simp [Matrix.one_apply, h]))
      · exact Or.inr (Or.inr (by simp [Matrix.one_apply, h]))
    · exact Or.inl (by simp [Matrix.one_apply, h])
  · exact Or.inl (by simp)

theorem smul_entry_src {c : K} (hc : c = 1 ∨ c = -1) {M : Matrix (SymplecticIndex n) (SymplecticIndex n) K}
    (hM : ∀ i j, M i j = 0 ∨ M i j = 1 ∨ M i j = -1) (i j : SymplecticIndex n) :
    (c • M) i j = 0 ∨ (c • M) i j = 1 ∨ (c • M) i j = -1 := by
  have h := hM i j
  rw [Matrix.smul_apply, smul_eq_mul]
  rcases hc with hc | hc <;> rcases h with h | h | h <;> rw [hc, h] <;> simp

end

noncomputable def tiIsoProjection (ε : K) (hε : ε = 1 ∨ ε = -1) :
    Projection (TIIso ε) (GL3TI K) := by
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> subst h <;> simp
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> subst h <;> simp
  refine formProjection (K := K) (fun n => hypForm n ε) (fun n => ε • hypForm n ε) hε0 ?_ ?_ ?_
  · intro n
    rw [Matrix.mul_smul, hypForm_mul_self, smul_smul, hεε, one_smul]
  · intro n
    rw [Matrix.transpose_smul, hypForm_transpose n ε hεε]
  · intro n i j
    exact smul_entry_src hε (hypForm_entry_src hε) i j

theorem tiIso_reduces_ti (ε : K) (hε : ε = 1 ∨ ε = -1) :
    (projectionSystem K).reduces (TIIso ε) (GL3TI K) :=
  ⟨tiIsoProjection ε hε⟩

theorem ti_eq_tiIso (ε : K) (hε : ε = 1 ∨ ε = -1) :
    problemClass (projectionSystem K) (GL3TI K) = problemClass (projectionSystem K) (TIIso ε) := by
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> subst h <;> simp
  exact Set.Subset.antisymm (ti_class_le_tiIso_class ε hε0)
    ((problemClass_mono (projectionSystem K)) (tiIso_reduces_ti ε hε))

theorem ti_eq_tiOH :
    problemClass (projectionSystem K) (GL3TI K) =
      problemClass (projectionSystem K) (TIIso (1 : K)) :=
  ti_eq_tiIso 1 (Or.inl rfl)

end

end

section

section

open Matrix

universe u

variable {K : Type u} [Field K]

theorem det_hypLift {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) :
    (hypLift P).det = 1 := by
  unfold hypLift
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.mul_inverse_cancel _ hP]

end

end

section

section

open Matrix

/-- The full maximal parabolic: invertible matrices preserving the first block. -/
def IsParabolic {K : Type} [Field K] (n : ℕ) (g : Matrix (DoubledIndex n) (DoubledIndex n) K) : Prop :=
  IsUnit g.det ∧ ∀ i j : Fin n, g (Sum.inr i) (Sum.inl j) = 0

/-- Independent maximal-parabolic actions on the three tensor factors. -/
def TIPar (K : Type) [Field K] : CoordProblem K := TIG (fun n g => IsParabolic n g)

theorem hypLift_isParabolic {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
    (hP : IsUnit P.det) : IsParabolic n (hypLift P) :=
  ⟨by rw [det_hypLift P hP]; exact isUnit_one, fun i j => by simp [hypLift]⟩

noncomputable def leviProjectionPar (K : Type) [Field K] : Projection (GL3TI K) (TIPar K) :=
  leviProjection (fun n g => IsParabolic n g) (fun _ _ hg => hg.1)
    (fun _ P hP => hypLift_isParabolic P hP)

end

end

section

section

open Matrix

variable {K : Type} [Field K] {n : ℕ}

def parMark (K : Type) [Field K] (n : ℕ) : Matrix (DoubledIndex n) (DoubledIndex n) K :=
  Matrix.fromBlocks 1 0 0 0

theorem parMark_inr_row (i : Fin n) (y : DoubledIndex n) : parMark K n (Sum.inr i) y = 0 := by
  rcases y with j | j <;> rfl

theorem mul_parMark_inl (h : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) (j : Fin n) :
    (h * parMark K n) x (Sum.inl j) = h x (Sum.inl j) := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  have h2 : ∀ b : Fin n, h x (Sum.inr b) * parMark K n (Sum.inr b) (Sum.inl j) = 0 := by
    intro b; rw [parMark_inr_row, mul_zero]
  rw [Finset.sum_congr rfl (fun b _ => h2 b), Finset.sum_const_zero, add_zero]
  have h1 : ∀ a : Fin n, h x (Sum.inl a) * parMark K n (Sum.inl a) (Sum.inl j)
      = if a = j then h x (Sum.inl a) else 0 := by
    intro a
    show h x (Sum.inl a) * (1 : Matrix (Fin n) (Fin n) K) a j = _
    rw [Matrix.one_apply]
    by_cases hj : a = j <;> simp [hj]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_ite_eq' Finset.univ j]
  simp

theorem isParabolic_of_compensator {h₁ h₂ : Matrix (DoubledIndex n) (DoubledIndex n) K} {c : K}
    (hh₁ : IsUnit h₁.det) (hh₂ : IsUnit h₂.det)
    (hmul : h₁ * parMark K n * h₂ᵀ = c • parMark K n) : IsParabolic n h₁ := by
  classical
  refine ⟨hh₁, fun i j => ?_⟩
  have hT : IsUnit (h₂ᵀ).det := by rw [Matrix.det_transpose]; exact hh₂
  have hR : h₁ * parMark K n = (c • parMark K n) * (h₂ᵀ)⁻¹ := by
    rw [← hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one]
  have h0 : ((c • parMark K n) * (h₂ᵀ)⁻¹) (Sum.inr i) (Sum.inl j) = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.smul_apply, parMark_inr_row, smul_zero, zero_mul]
  have hkey := mul_parMark_inl h₁ (Sum.inr i) j
  rw [hR, h0] at hkey
  exact hkey.symm

theorem exists_compensator_of_isParabolic {h₁ : Matrix (DoubledIndex n) (DoubledIndex n) K} (h : IsParabolic n h₁) :
    ∃ h₂ : Matrix (DoubledIndex n) (DoubledIndex n) K, IsUnit h₂.det ∧ h₁ * parMark K n * h₂ᵀ = parMark K n := by
  classical
  have h21 : h₁.toBlocks₂₁ = 0 := by ext i j; exact h.2 i j
  have hblk : h₁ = Matrix.fromBlocks h₁.toBlocks₁₁ h₁.toBlocks₁₂ 0 h₁.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : h₁.det = h₁.toBlocks₁₁.det * h₁.toBlocks₂₂.det := by
    conv_lhs => rw [hblk]
    rw [Matrix.det_fromBlocks_zero₂₁]
  have hAunit : IsUnit h₁.toBlocks₁₁.det := by
    have := h.1; rw [hdet] at this; exact isUnit_of_mul_isUnit_left this
  refine ⟨Matrix.fromBlocks (h₁.toBlocks₁₁⁻¹)ᵀ 0 0 1, ?_, ?_⟩
  · rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hAunit
  · rw [Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_transpose, Matrix.transpose_zero, Matrix.transpose_one]
    conv_lhs => rw [hblk]
    rw [parMark, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv _ hAunit]

theorem isParabolic_of_compensator_right {h₁ h₂ : Matrix (DoubledIndex n) (DoubledIndex n) K} {c : K}
    (hh₁ : IsUnit h₁.det) (hh₂ : IsUnit h₂.det)
    (hmul : h₁ * parMark K n * h₂ᵀ = c • parMark K n) : IsParabolic n h₂ := by
  have hsymm : (parMark K n)ᵀ = parMark K n := by
    rw [parMark, Matrix.fromBlocks_transpose]
    simp
  refine isParabolic_of_compensator hh₂ hh₁ (c := c) ?_
  have ht := congrArg Matrix.transpose hmul
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.transpose_smul, hsymm, ← Matrix.mul_assoc] at ht
  exact ht

section

variable {t m : ℕ}

theorem sum_collapse_of_singleton_stratum {str : Fin t → Fin m}
    {R : Matrix (Fin t) (Fin t) K} (hRdiag : IsBlockDiag str R) {k₁ : Fin t}
    (hk₁ : ∀ k', k' ≠ k₁ → str k' ≠ str k₁) (f : Fin t → Matrix (DoubledIndex n) (DoubledIndex n) K) :
    ∑ k' : Fin t, R k₁ k' • f k' = R k₁ k₁ • f k₁ := by
  classical
  refine Finset.sum_eq_single k₁ (fun k' _ hne => ?_) (fun h => absurd (Finset.mem_univ k₁) h)
  rw [hRdiag k₁ k' (Ne.symm (hk₁ k' hne)), zero_smul]

theorem isParabolic_of_marker (hn : 0 < n) {str : Fin t → Fin m}
    {R : Matrix (Fin t) (Fin t) K} (hRdiag : IsBlockDiag str R) {k₁ : Fin t}
    (hk₁ : ∀ k', k' ≠ k₁ → str k' ≠ str k₁)
    {Xk : Fin t → Matrix (DoubledIndex n) (DoubledIndex n) K} {P₀ Q₀ : Matrix (DoubledIndex n) (DoubledIndex n) K}
    (hP : IsUnit P₀.det) (hQ : IsUnit Q₀.det) (hmark : Xk k₁ = parMark K n)
    (heq : parMark K n = ∑ k' : Fin t, R k₁ k' • (P₀ * Xk k' * Q₀ᵀ)) :
    IsParabolic n P₀ ∧ IsParabolic n Q₀ := by
  classical
  rw [sum_collapse_of_singleton_stratum hRdiag hk₁, hmark] at heq
  have hone : parMark K n (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩) = 1 := by
    show (1 : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩ = 1
    rw [Matrix.one_apply_eq]
  have hR0 : R k₁ k₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at heq
    rw [heq] at hone
    simp at hone
  have hkey : P₀ * parMark K n * Q₀ᵀ = (R k₁ k₁)⁻¹ • parMark K n := by
    conv_rhs => rw [heq]
    rw [smul_smul, inv_mul_cancel₀ hR0, one_smul]
  exact ⟨isParabolic_of_compensator hP hQ hkey, isParabolic_of_compensator_right hP hQ hkey⟩

end

end

end

section

section

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

def Preserves (w : ι → Bool) (g : Matrix ι ι K) : Prop :=
  ∀ i j, w i = false → w j = true → g i j = 0

end

end

section

section

open Matrix

variable {K : Type} [Field K] {α : Type} [LinearOrder α]

def lvl2 (n : ℕ) : DoubledIndex n → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

@[simp] theorem lvl2_inl (n : ℕ) (i : Fin n) : lvl2 n (Sum.inl i) = 0 := rfl

@[simp] theorem lvl2_inr (n : ℕ) (i : Fin n) : lvl2 n (Sum.inr i) = 1 := rfl

theorem isParabolic_iff_blockTriangular {n : ℕ} (g : Matrix (DoubledIndex n) (DoubledIndex n) K) :
    IsParabolic n g ↔ IsUnit g.det ∧ g.BlockTriangular (lvl2 n) := by
  constructor
  · rintro ⟨hu, h0⟩
    refine ⟨hu, ?_⟩
    rintro (i | i) (j | j) hij
    · simp at hij
    · simp at hij
    · exact h0 i j
    · simp at hij
  · rintro ⟨hu, hbt⟩
    exact ⟨hu, fun i j => hbt (by simp)⟩

def FlagData (α : Type) : Type := ∀ n : ℕ, DoubledIndex n → α

def IsFlagPar (lvl : FlagData α) (n : ℕ) (g : Matrix (DoubledIndex n) (DoubledIndex n) K) : Prop :=
  IsUnit g.det ∧ g.BlockTriangular (lvl n)

def TIFlagPar (K : Type) [Field K] (lvl : FlagData α) : CoordProblem K :=
  TIG (fun n g => IsFlagPar (K := K) lvl n g)

variable {lvl : FlagData α} {n : ℕ}

def UncutInstance (lvl : FlagData α) : Prop :=
  ∀ n (a b : Fin n), lvl n (Sum.inl a) = lvl n (Sum.inl b)

theorem blockLift_one_blockTriangular (hc : UncutInstance lvl) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) K) :
    (blockLift P (1 : Matrix (Fin n) (Fin n) K)).BlockTriangular (lvl n) := by
  rintro (i | i) (j | j) hij
  · rw [hc n j i] at hij; exact absurd hij (lt_irrefl _)
  · simp [blockLift]
  · simp [blockLift]
  · have hne : i ≠ j := by rintro rfl; exact absurd hij (lt_irrefl _)
    simp [blockLift, Matrix.one_apply_ne hne]

theorem det_blockLift_one (n : ℕ) (P : Matrix (Fin n) (Fin n) K) :
    (blockLift P (1 : Matrix (Fin n) (Fin n) K)).det = P.det := by
  simp [blockLift, Matrix.det_fromBlocks_zero₂₁]

/-- Padding realizes the lower reduction through block-diagonal lifts diag(P,I). -/
noncomputable def leviProjectionFlagPar (hc : UncutInstance lvl) :
    Projection (GL3TI K) (TIFlagPar K lvl) :=
  leviProjectionGen (fun n g => IsFlagPar (K := K) lvl n g)
    (fun _ _ hg => hg.1)
    (fun n P hP => ⟨1, by rw [det_blockLift_one]; exact hP,
      blockLift_one_blockTriangular hc n P⟩)

theorem uncutInstance_lvl2 : UncutInstance (α := Fin 2) (fun n => lvl2 n) :=
  fun _ _ _ => rfl

theorem isFlagPar_lvl2 (n : ℕ) (g : Matrix (DoubledIndex n) (DoubledIndex n) K) :
    IsFlagPar (K := K) (α := Fin 2) (fun m => lvl2 m) n g ↔ IsParabolic n g :=
  (isParabolic_iff_blockTriangular g).symm

theorem tiPar_eq_tiFlagPar : TIPar K = TIFlagPar K (α := Fin 2) (fun n => lvl2 n) := by
  have h : (fun n (g : Matrix (DoubledIndex n) (DoubledIndex n) K) => IsParabolic n g)
      = (fun n (g : Matrix (DoubledIndex n) (DoubledIndex n) K) =>
          IsFlagPar (K := K) (α := Fin 2) (fun m => lvl2 m) n g) := by
    funext n g; exact propext (isFlagPar_lvl2 n g).symm
  unfold TIPar TIFlagPar
  rw [h]

end

end

section

section

variable {K : Type} [Field K]

private theorem isUnit_inv_of_isUnit {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M) :
    IsUnit M⁻¹ := by
  rw [Matrix.isUnit_iff_isUnit_det] at hM ⊢
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact hM.inv

end

end

section

section

variable {K : Type} [Field K]

def NaiveAndFails (D : K → Prop) : Prop :=
  ∃ d e : K, D (d * e) ∧ ¬ D d ∧ ¬ D e

end

end

section

section

section

variable {K : Type} [Field K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem det_inv_eq {P : Matrix ι ι K} (hP : IsUnit P.det) : P⁻¹.det = P.det⁻¹ := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

end

end

end

section

section

variable {K : Type} [Field K]

theorem grid_counts :
    (4 + 12) * (12 + 12) + (4 + 12) = 400 ∧
      4 * 3 + 12 * 11 + 12 * (4 + 12) + 12 * 4 = 384 ∧
      (4 + 12 + 12) * (4 + 12 + 12) = 784 := by
  refine ⟨by decide, by decide, by decide⟩

end

end

section

section

open Matrix

variable {K : Type} [Field K]

inductive PBlk
  | inst
  | aux1
  | aux2
  deriving DecidableEq

instance instFintypePBlk : Fintype PBlk :=
  ⟨{PBlk.inst, PBlk.aux1, PBlk.aux2}, fun x => by cases x <;> decide⟩

instance instNonemptyPBlk : Nonempty PBlk := ⟨PBlk.inst⟩

abbrev RIdxP (n : ℕ) (_ : PBlk) : Type := DoubledIndex n

@[reducible] def CIdxP (n : ℕ) : PBlk → Type
  | PBlk.inst => DoubledIndex n
  | PBlk.aux1 => DoubledIndex n
  | PBlk.aux2 => Unit

instance instFintypeCIdxP (n : ℕ) (b : PBlk) : Fintype (CIdxP n b) := by
  cases b <;> unfold CIdxP <;> infer_instance

instance instDecEqCIdxP (n : ℕ) (b : PBlk) : DecidableEq (CIdxP n b) := by
  cases b <;> unfold CIdxP <;> infer_instance

theorem card_CIdxP (n : ℕ) (b : PBlk) :
    Fintype.card (CIdxP n b) = if b = PBlk.aux2 then 1 else n + n := by
  cases b
  · show Fintype.card (DoubledIndex n) = _
    rw [Fintype.card_sum, Fintype.card_fin]; rfl
  · show Fintype.card (DoubledIndex n) = _
    rw [Fintype.card_sum, Fintype.card_fin]; rfl
  · rfl

abbrev thp (n : ℕ) : ℕ := n + n + 1 + 1

abbrev IdxP (n : ℕ) : Type := DoubledIndex n ⊕ Unit ⊕ Unit

def tagP (n : ℕ) : IdxP n → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

theorem card_IdxP (n : ℕ) : Fintype.card (IdxP n) = thp n := by
  change Fintype.card (DoubledIndex n ⊕ Unit ⊕ Unit) = n + n + 1 + 1
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]

noncomputable def packP (n : ℕ) : IdxP n ≃ Fin (thp n) :=
  Fintype.equivFinOfCardEq (card_IdxP n)

noncomputable def strP (n : ℕ) : Fin (thp n) → Fin 3 :=
  fun k => tagP n ((packP n).symm k)

noncomputable def k₁P (n : ℕ) : Fin (thp n) := packP n (Sum.inr (Sum.inl ()))

noncomputable def k₂P (n : ℕ) : Fin (thp n) := packP n (Sum.inr (Sum.inr ()))

noncomputable def instSlice (n : ℕ) (x : DoubledIndex n) : Fin (thp n) := packP n (Sum.inl x)

@[simp] theorem strP_instSlice (n : ℕ) (x : DoubledIndex n) : strP n (instSlice n x) = 0 := by
  unfold strP instSlice
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem strP_k₁P (n : ℕ) : strP n (k₁P n) = 1 := by
  unfold strP k₁P
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem strP_k₂P (n : ℕ) : strP n (k₂P n) = 2 := by
  unfold strP k₂P
  rw [Equiv.symm_apply_apply]
  rfl

theorem k₁P_singleton (n : ℕ) : ∀ k', k' ≠ k₁P n → strP n k' ≠ strP n (k₁P n) := by
  intro k' hne
  rw [strP_k₁P]
  unfold strP
  rcases hx : (packP n).symm k' with x | u | u
  · rw [show tagP n (Sum.inl x) = 0 from rfl]; decide
  · exfalso
    apply hne
    have hk : k' = packP n (Sum.inr (Sum.inl u)) := by
      rw [← hx, Equiv.apply_symm_apply]
    rw [hk]
    unfold k₁P
    cases u
    rfl
  · rw [show tagP n (Sum.inr (Sum.inr u)) = 2 from rfl]; decide

theorem k₂P_singleton (n : ℕ) : ∀ k', k' ≠ k₂P n → strP n k' ≠ strP n (k₂P n) := by
  intro k' hne
  rw [strP_k₂P]
  unfold strP
  rcases hx : (packP n).symm k' with x | u | u
  · rw [show tagP n (Sum.inl x) = 0 from rfl]; decide
  · rw [show tagP n (Sum.inr (Sum.inl u)) = 1 from rfl]; decide
  · exfalso
    apply hne
    have hk : k' = packP n (Sum.inr (Sum.inr u)) := by
      rw [← hx, Equiv.apply_symm_apply]
    rw [hk]
    unfold k₂P
    cases u
    rfl

theorem instSlice_ne_k₁P (n : ℕ) (x : DoubledIndex n) : instSlice n x ≠ k₁P n := by
  intro h
  have := congrArg (strP n) h
  rw [strP_instSlice, strP_k₁P] at this
  exact absurd this (by decide)

theorem instSlice_ne_k₂P (n : ℕ) (x : DoubledIndex n) : instSlice n x ≠ k₂P n := by
  intro h
  have := congrArg (strP n) h
  rw [strP_instSlice, strP_k₂P] at this
  exact absurd this (by decide)

noncomputable def encBlock (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n))
    (b s : PBlk) : Matrix (RIdxP n b) (CIdxP n s) K :=
  match b, s with
  | PBlk.inst, PBlk.inst =>
      match (packP n).symm k with
      | Sum.inl x => Matrix.of fun i j => A (i, j, x)
      | _ => 0
  | PBlk.inst, PBlk.aux1 => if k = k₁P n then parMark K n else 0
  | PBlk.aux1, PBlk.inst => if k = k₂P n then parMark K n else 0
  | PBlk.aux2, PBlk.aux2 =>
      match (packP n).symm k with
      | Sum.inl x => Matrix.of fun i (_ : Unit) => parMark K n i x
      | _ => 0
  | _, _ => 0

/-- The marker tensor encoding a parabolic orbit as a partitioned tensor orbit. -/
noncomputable def encP (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    PArr K PBlk PBlk (RIdxP n) (CIdxP n) (thp n) :=
  fun k b s => encBlock n A k b s

theorem packP_symm_instSlice (n : ℕ) (x : DoubledIndex n) : (packP n).symm (instSlice n x) = Sum.inl x := by
  unfold instSlice
  rw [Equiv.symm_apply_apply]

@[simp] theorem encP_inst_inst (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x : DoubledIndex n) :
    encP n A (instSlice n x) PBlk.inst PBlk.inst = Matrix.of fun i j => A (i, j, x) := by
  simp [encP, encBlock, packP_symm_instSlice]

@[simp] theorem encP_marker₁ (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₁P n) PBlk.inst PBlk.aux1 = parMark K n := by
  simp [encP, encBlock]

@[simp] theorem encP_marker₂ (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₂P n) PBlk.aux1 PBlk.inst = parMark K n := by
  simp [encP, encBlock]

@[simp] theorem encP_marker₃ (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x : DoubledIndex n) :
    encP n A (instSlice n x) PBlk.aux2 PBlk.aux2
      = Matrix.of fun i (_ : Unit) => parMark K n i x := by
  simp [encP, encBlock, packP_symm_instSlice]

theorem encP_marker₁_zero (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) {k : Fin (thp n)} (hk : k ≠ k₁P n) :
    encP n A k PBlk.inst PBlk.aux1 = 0 := by
  simp [encP, encBlock, hk]

theorem encP_marker₂_zero (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) {k : Fin (thp n)} (hk : k ≠ k₂P n) :
    encP n A k PBlk.aux1 PBlk.inst = 0 := by
  simp [encP, encBlock, hk]

end

end

section

section

open Matrix

variable {K : Type} [Field K]

theorem packP_symm_k₁P (n : ℕ) : (packP n).symm (k₁P n) = Sum.inr (Sum.inl ()) := by
  unfold k₁P; rw [Equiv.symm_apply_apply]

theorem packP_symm_k₂P (n : ℕ) : (packP n).symm (k₂P n) = Sum.inr (Sum.inr ()) := by
  unfold k₂P; rw [Equiv.symm_apply_apply]

theorem slice_trichotomy (n : ℕ) (k : Fin (thp n)) :
    (∃ x, k = instSlice n x) ∨ k = k₁P n ∨ k = k₂P n := by
  rcases hk : (packP n).symm k with x | u | u
  · left; refine ⟨x, ?_⟩
    unfold instSlice; rw [← hk, Equiv.apply_symm_apply]
  · right; left
    unfold k₁P; rw [← hk, Equiv.apply_symm_apply]
  · right; right
    unfold k₂P; rw [← hk, Equiv.apply_symm_apply]

theorem k₁P_ne_k₂P (n : ℕ) : k₁P n ≠ k₂P n := by
  intro h
  have := congrArg (strP n) h
  rw [strP_k₁P, strP_k₂P] at this
  exact absurd this (by decide)

theorem sum_thp {M : Type} [AddCommMonoid M] (n : ℕ) (F : Fin (thp n) → M) :
    ∑ k, F k = (∑ x : DoubledIndex n, F (instSlice n x)) + (F (k₁P n) + F (k₂P n)) := by
  have hu : ∀ (G : Unit → M), ∑ u : Unit, G u = G () := fun G => by simp
  have h2 : ∑ z : Unit ⊕ Unit, F (packP n (Sum.inr z)) = F (k₁P n) + F (k₂P n) := by
    rw [Fintype.sum_sum_type, hu, hu]
    rfl
  rw [← Equiv.sum_comp (packP n), Fintype.sum_sum_type, h2]
  rfl

theorem encP_inst_inst_k₁P (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₁P n) PBlk.inst PBlk.inst = 0 := by
  simp [encP, encBlock, packP_symm_k₁P]

theorem encP_inst_inst_k₂P (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₂P n) PBlk.inst PBlk.inst = 0 := by
  simp [encP, encBlock, packP_symm_k₂P]

theorem encP_aux2_aux2_k₁P (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₁P n) PBlk.aux2 PBlk.aux2 = 0 := by
  simp [encP, encBlock, packP_symm_k₁P]

theorem encP_aux2_aux2_k₂P (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    encP n A (k₂P n) PBlk.aux2 PBlk.aux2 = 0 := by
  simp [encP, encBlock, packP_symm_k₂P]

theorem encP_inst_aux2 (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n)) :
    encP n A k PBlk.inst PBlk.aux2 = 0 := rfl
theorem encP_aux1_aux1 (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n)) :
    encP n A k PBlk.aux1 PBlk.aux1 = 0 := rfl
theorem encP_aux1_aux2 (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n)) :
    encP n A k PBlk.aux1 PBlk.aux2 = 0 := rfl
theorem encP_aux2_inst (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n)) :
    encP n A k PBlk.aux2 PBlk.inst = 0 := rfl
theorem encP_aux2_aux1 (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (k : Fin (thp n)) :
    encP n A k PBlk.aux2 PBlk.aux1 = 0 := rfl

def sliceS {n : ℕ} (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x : DoubledIndex n) : Matrix (DoubledIndex n) (DoubledIndex n) K :=
  Matrix.of fun i j => A (i, j, x)

theorem sliceS_apply {n : ℕ} (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x i j : DoubledIndex n) :
    sliceS A x i j = A (i, j, x) := rfl

theorem encP_inst_inst' (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x : DoubledIndex n) :
    encP n A (instSlice n x) PBlk.inst PBlk.inst = sliceS A x :=
  encP_inst_inst n A x

theorem sum3_rotateS {n : ℕ} (f : DoubledIndex n → DoubledIndex n → DoubledIndex n → K) :
    ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ k', ∑ j', ∑ i', f i' j' k' :=
  calc ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ j', ∑ i', ∑ k', f i' j' k' := Finset.sum_comm
    _ = ∑ j', ∑ k', ∑ i', f i' j' k' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k', ∑ j', ∑ i', f i' j' k' := Finset.sum_comm

theorem act3D_parabolicSlice {n : ℕ} (g₁ g₂ g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (x : DoubledIndex n) :
    sliceS (act3D K g₁ g₂ g₃ A) x = ∑ x', g₃ x x' • (g₁ * sliceS A x' * g₂ᵀ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [sliceS_apply, act3D, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine (sum3_rotateS (fun i' j' k' => g₁ i i' * g₂ j j' * g₃ x k' * A (i', j', k'))).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun i' _ => ?_
  ring

def colP (K : Type) [Field K] (n : ℕ) (x : DoubledIndex n) : Matrix (DoubledIndex n) Unit K :=
  Matrix.of fun i _ => parMark K n i x

theorem encP_marker₃' (n : ℕ) (A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) (x : DoubledIndex n) :
    encP n A (instSlice n x) PBlk.aux2 PBlk.aux2 = colP K n x :=
  encP_marker₃ n A x

theorem mul_colP {n : ℕ} (M : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) :
    M * colP K n x = Matrix.of fun i (_ : Unit) => (M * parMark K n) i x := by
  ext i u
  simp only [Matrix.mul_apply, colP, Matrix.of_apply]

theorem sum_smul_colP {n : ℕ} (c : DoubledIndex n → K) (N : Matrix (DoubledIndex n) (DoubledIndex n) K) :
    ∑ x', c x' • (Matrix.of fun i (_ : Unit) => N i x')
      = Matrix.of fun i (_ : Unit) => ∑ x', N i x' * c x' := by
  ext i u
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun x' _ => mul_comm _ _

def rpMat {n : ℕ} (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : Matrix (IdxP n) (IdxP n) K :=
  Matrix.fromBlocks g₃ 0 0 (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) K)

noncomputable def RP (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : Matrix (Fin (thp n)) (Fin (thp n)) K :=
  (rpMat g₃).submatrix (packP n).symm (packP n).symm

theorem RP_apply (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (k k' : Fin (thp n)) :
    RP n g₃ k k' = rpMat g₃ ((packP n).symm k) ((packP n).symm k') := rfl

theorem RP_inst_inst (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (x x' : DoubledIndex n) :
    RP n g₃ (instSlice n x) (instSlice n x') = g₃ x x' := by
  rw [RP_apply, packP_symm_instSlice, packP_symm_instSlice]
  rfl

theorem RP_inst_k₁P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) :
    RP n g₃ (instSlice n x) (k₁P n) = 0 := by
  rw [RP_apply, packP_symm_instSlice, packP_symm_k₁P]; rfl

theorem RP_inst_k₂P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) :
    RP n g₃ (instSlice n x) (k₂P n) = 0 := by
  rw [RP_apply, packP_symm_instSlice, packP_symm_k₂P]; rfl

theorem RP_k₁P_inst (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) :
    RP n g₃ (k₁P n) (instSlice n x) = 0 := by
  rw [RP_apply, packP_symm_instSlice, packP_symm_k₁P]; rfl

theorem RP_k₂P_inst (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (x : DoubledIndex n) :
    RP n g₃ (k₂P n) (instSlice n x) = 0 := by
  rw [RP_apply, packP_symm_instSlice, packP_symm_k₂P]; rfl

theorem RP_k₁P_k₁P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : RP n g₃ (k₁P n) (k₁P n) = 1 := by
  rw [RP_apply, packP_symm_k₁P]; rfl

theorem RP_k₂P_k₂P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : RP n g₃ (k₂P n) (k₂P n) = 1 := by
  rw [RP_apply, packP_symm_k₂P]; rfl

theorem RP_k₁P_k₂P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : RP n g₃ (k₁P n) (k₂P n) = 0 := by
  rw [RP_apply, packP_symm_k₁P, packP_symm_k₂P]; rfl

theorem RP_k₂P_k₁P (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : RP n g₃ (k₂P n) (k₁P n) = 0 := by
  rw [RP_apply, packP_symm_k₁P, packP_symm_k₂P]; rfl

theorem RP_isUnit (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (h : IsUnit g₃.det) :
    IsUnit (RP n g₃).det := by
  rw [RP, Matrix.det_submatrix_equiv_self, rpMat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]
  exact h

theorem RP_isBlockDiag (n : ℕ) (g₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) : IsBlockDiag (strP n) (RP n g₃) := by
  intro k k' hne
  rw [RP_apply]
  unfold strP at hne
  rcases hk : (packP n).symm k with x | u | u <;>
    rcases hk' : (packP n).symm k' with x' | u' | u' <;> rw [hk, hk'] at hne
  · exact absurd rfl hne
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hne
  · cases u; cases u'; simp [rpMat, Matrix.one_apply]
  · rfl
  · cases u; cases u'; simp [rpMat, Matrix.one_apply]
  · exact absurd rfl hne

theorem parMark_transpose (n : ℕ) : (parMark K n)ᵀ = parMark K n := by
  rw [parMark, Matrix.fromBlocks_transpose]
  simp

theorem exists_left_compensator {n : ℕ} {h : Matrix (DoubledIndex n) (DoubledIndex n) K} (hp : IsParabolic n h) :
    ∃ c : Matrix (DoubledIndex n) (DoubledIndex n) K, IsUnit c.det ∧ c * parMark K n * hᵀ = parMark K n := by
  obtain ⟨d, hd, hmul⟩ := exists_compensator_of_isParabolic hp
  refine ⟨d, hd, ?_⟩
  have ht := congrArg Matrix.transpose hmul
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, parMark_transpose,
    ← Matrix.mul_assoc] at ht
  exact ht

noncomputable def PP {n : ℕ} (g₁ c₂ c₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) :
    ∀ b : PBlk, Matrix (RIdxP n b) (RIdxP n b) K
  | PBlk.inst => g₁
  | PBlk.aux1 => c₂
  | PBlk.aux2 => c₃

noncomputable def QP {n : ℕ} (g₂ c₁ : Matrix (DoubledIndex n) (DoubledIndex n) K) :
    ∀ s : PBlk, Matrix (CIdxP n s) (CIdxP n s) K
  | PBlk.inst => g₂
  | PBlk.aux1 => c₁
  | PBlk.aux2 => (1 : Matrix Unit Unit K)

theorem PP_isUnit {n : ℕ} (g₁ c₂ c₃ : Matrix (DoubledIndex n) (DoubledIndex n) K) (h₁ : IsUnit g₁.det)
    (h₂ : IsUnit c₂.det) (h₃ : IsUnit c₃.det) : ∀ b, IsUnit (PP (n := n) g₁ c₂ c₃ b).det
  | PBlk.inst => h₁
  | PBlk.aux1 => h₂
  | PBlk.aux2 => h₃

theorem QP_isUnit {n : ℕ} (g₂ c₁ : Matrix (DoubledIndex n) (DoubledIndex n) K) (h₂ : IsUnit g₂.det)
    (h₁ : IsUnit c₁.det) : ∀ s, IsUnit (QP (n := n) g₂ c₁ s).det
  | PBlk.inst => h₂
  | PBlk.aux1 => h₁
  | PBlk.aux2 => by simp [QP]

theorem sum_single_marker {n : ℕ} {M : Type} [AddCommMonoid M] (k₀ : Fin (thp n))
    (F : Fin (thp n) → M) (hF : ∀ k', k' ≠ k₀ → F k' = 0) : ∑ k', F k' = F k₀ :=
  Finset.sum_eq_single k₀ (fun k' _ hne => hF k' hne)
    (fun h => absurd (Finset.mem_univ k₀) h)

theorem tiPar_imp_blockEquiv (n : ℕ) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (h : (TIPar K).Rel n A B) : BlockEquiv (strP n) (encP n A) (encP n B) := by
  classical
  obtain ⟨g₁, g₂, g₃, hp₁, hp₂, hp₃, hAB⟩ := h
  subst hAB
  obtain ⟨c₁, hc₁, hc₁e⟩ := exists_compensator_of_isParabolic hp₁
  obtain ⟨c₂, hc₂, hc₂e⟩ := exists_left_compensator hp₂
  obtain ⟨c₃, hc₃, hc₃e⟩ := exists_left_compensator hp₃
  refine ⟨PP g₁ c₂ c₃, QP g₂ c₁, RP n g₃, PP_isUnit g₁ c₂ c₃ hp₁.1 hc₂ hc₃,
    QP_isUnit g₂ c₁ hp₂.1 hc₁, RP_isUnit n g₃ hp₃.1, RP_isBlockDiag n g₃, fun k b s => ?_⟩
  cases b <;> cases s

  · simp only [PP, QP]
    rw [sum_thp n, encP_inst_inst_k₁P, encP_inst_inst_k₂P]
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero]
    rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · rw [encP_inst_inst', act3D_parabolicSlice]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [RP_inst_inst, encP_inst_inst']
    · rw [encP_inst_inst_k₁P]
      refine (Finset.sum_eq_zero fun x' _ => ?_).symm
      rw [RP_k₁P_inst, zero_smul]
    · rw [encP_inst_inst_k₂P]
      refine (Finset.sum_eq_zero fun x' _ => ?_).symm
      rw [RP_k₂P_inst, zero_smul]

  · simp only [PP, QP]
    rw [sum_single_marker (k₁P n) _ (fun k' hk' => by rw [encP_marker₁_zero n _ hk']; simp)]
    rw [encP_marker₁, hc₁e]
    rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · rw [encP_marker₁_zero n _ (instSlice_ne_k₁P n x), RP_inst_k₁P, zero_smul]
    · rw [encP_marker₁, RP_k₁P_k₁P, one_smul]
    · rw [encP_marker₁_zero n _ (Ne.symm (k₁P_ne_k₂P n)), RP_k₂P_k₁P, zero_smul]

  · simp only [encP_inst_aux2, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Finset.sum_const_zero]

  · simp only [PP, QP]
    rw [sum_single_marker (k₂P n) _ (fun k' hk' => by rw [encP_marker₂_zero n _ hk']; simp)]
    rw [encP_marker₂, hc₂e]
    rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · rw [encP_marker₂_zero n _ (instSlice_ne_k₂P n x), RP_inst_k₂P, zero_smul]
    · rw [encP_marker₂_zero n _ (k₁P_ne_k₂P n), RP_k₁P_k₂P, zero_smul]
    · rw [encP_marker₂, RP_k₂P_k₂P, one_smul]

  · simp only [encP_aux1_aux1, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Finset.sum_const_zero]

  · simp only [encP_aux1_aux2, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Finset.sum_const_zero]

  · simp only [encP_aux2_inst, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Finset.sum_const_zero]

  · simp only [encP_aux2_aux1, Matrix.mul_zero, Matrix.zero_mul, smul_zero, Finset.sum_const_zero]

  · simp only [PP, QP, Matrix.transpose_one, Matrix.mul_one]
    rw [sum_thp n, encP_aux2_aux2_k₁P, encP_aux2_aux2_k₂P]
    simp only [Matrix.mul_zero, smul_zero, add_zero]
    rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · rw [encP_marker₃']
      have hcol : ∀ x', c₃ * encP n A (instSlice n x') PBlk.aux2 PBlk.aux2
          = Matrix.of fun i (_ : Unit) => (c₃ * parMark K n) i x' := by
        intro x'
        rw [encP_marker₃', mul_colP]
      simp only [RP_inst_inst, hcol]
      rw [sum_smul_colP]
      ext i u
      simp only [colP, Matrix.of_apply]
      have hx := congrFun (congrFun hc₃e i) x
      rw [Matrix.mul_apply] at hx
      refine hx.symm.trans (Finset.sum_congr rfl fun x' _ => ?_)
      rw [Matrix.transpose_apply]
    · rw [encP_aux2_aux2_k₁P]
      refine (Finset.sum_eq_zero fun x' _ => ?_).symm
      rw [RP_k₁P_inst, zero_smul]
    · rw [encP_aux2_aux2_k₂P]
      refine (Finset.sum_eq_zero fun x' _ => ?_).symm
      rw [RP_k₂P_inst, zero_smul]

end

end

section

section

open Matrix

variable {K : Type} [Field K]

noncomputable def RresP (n : ℕ) (R : Matrix (Fin (thp n)) (Fin (thp n)) K) :
    Matrix (DoubledIndex n) (DoubledIndex n) K :=
  Matrix.of fun x y => R (instSlice n x) (instSlice n y)

theorem RresP_apply (n : ℕ) (R : Matrix (Fin (thp n)) (Fin (thp n)) K) (x y : DoubledIndex n) :
    RresP n R x y = R (instSlice n x) (instSlice n y) := rfl

theorem instSlice_injective (n : ℕ) : Function.Injective (instSlice n) :=
  fun x y h => Sum.inl_injective ((packP n).injective h)

theorem blockDiag_inst_k₁P {n : ℕ} {R : Matrix (Fin (thp n)) (Fin (thp n)) K}
    (hR : IsBlockDiag (strP n) R) (x : DoubledIndex n) : R (instSlice n x) (k₁P n) = 0 :=
  hR _ _ (by rw [strP_instSlice, strP_k₁P]; decide)

theorem blockDiag_inst_k₂P {n : ℕ} {R : Matrix (Fin (thp n)) (Fin (thp n)) K}
    (hR : IsBlockDiag (strP n) R) (x : DoubledIndex n) : R (instSlice n x) (k₂P n) = 0 :=
  hR _ _ (by rw [strP_instSlice, strP_k₂P]; decide)

theorem RresP_mul {n : ℕ} {R : Matrix (Fin (thp n)) (Fin (thp n)) K}
    (hR : IsBlockDiag (strP n) R) (R' : Matrix (Fin (thp n)) (Fin (thp n)) K) :
    RresP n R * RresP n R' = RresP n (R * R') := by
  ext x y
  rw [Matrix.mul_apply, RresP_apply, Matrix.mul_apply,
    sum_thp n (fun k' => R (instSlice n x) k' * R' k' (instSlice n y)),
    blockDiag_inst_k₁P hR, blockDiag_inst_k₂P hR]
  simp only [zero_mul, add_zero, RresP_apply]

theorem RresP_isUnit {n : ℕ} {R : Matrix (Fin (thp n)) (Fin (thp n)) K}
    (hR : IsBlockDiag (strP n) R) (hU : IsUnit R.det) : IsUnit (RresP n R).det := by
  have hinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have h1 : RresP n R * RresP n R⁻¹ = 1 := by
    rw [RresP_mul hR, hinv]
    ext x y
    rw [RresP_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy, if_neg (fun h => hxy (instSlice_injective n h))]
  exact Matrix.isUnit_det_of_right_inverse h1

theorem marker₁_parabolic {n : ℕ} (hn : 0 < n) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (P : ∀ b, Matrix (RIdxP n b) (RIdxP n b) K) (Q : ∀ s, Matrix (CIdxP n s) (CIdxP n s) K)
    (R : Matrix (Fin (thp n)) (Fin (thp n)) K)
    (hP : ∀ b, IsUnit (P b).det) (hQ : ∀ s, IsUnit (Q s).det) (hRdiag : IsBlockDiag (strP n) R)
    (heq : ∀ k b s, encP n B k b s = ∑ k', R k k' • (P b * encP n A k' b s * (Q s)ᵀ)) :
    IsParabolic n (P PBlk.inst) ∧ IsParabolic n (Q PBlk.aux1) := by
  have h := heq (k₁P n) PBlk.inst PBlk.aux1
  rw [encP_marker₁] at h
  exact isParabolic_of_marker hn hRdiag (k₁P_singleton n) (hP _) (hQ _) (encP_marker₁ n A) h

theorem marker₂_parabolic {n : ℕ} (hn : 0 < n) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (P : ∀ b, Matrix (RIdxP n b) (RIdxP n b) K) (Q : ∀ s, Matrix (CIdxP n s) (CIdxP n s) K)
    (R : Matrix (Fin (thp n)) (Fin (thp n)) K)
    (hP : ∀ b, IsUnit (P b).det) (hQ : ∀ s, IsUnit (Q s).det) (hRdiag : IsBlockDiag (strP n) R)
    (heq : ∀ k b s, encP n B k b s = ∑ k', R k k' • (P b * encP n A k' b s * (Q s)ᵀ)) :
    IsParabolic n (P PBlk.aux1) ∧ IsParabolic n (Q PBlk.inst) := by
  have h := heq (k₂P n) PBlk.aux1 PBlk.inst
  rw [encP_marker₂] at h
  exact isParabolic_of_marker hn hRdiag (k₂P_singleton n) (hP _) (hQ _) (encP_marker₂ n A) h

theorem mul_unit_smul {I : Type} [Fintype I] (M : Matrix I Unit K) (N : Matrix Unit Unit K) :
    M * N = N () () • M := by
  ext i u
  cases u
  simp [Matrix.mul_apply, mul_comm]

theorem marker₃_equation (n : ℕ) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (P : ∀ b, Matrix (RIdxP n b) (RIdxP n b) K) (Q : ∀ s, Matrix (CIdxP n s) (CIdxP n s) K)
    (R : Matrix (Fin (thp n)) (Fin (thp n)) K)
    (heq : ∀ k b s, encP n B k b s = ∑ k', R k k' • (P b * encP n A k' b s * (Q s)ᵀ)) :
    parMark K n = (Q PBlk.aux2 () () • P PBlk.aux2) * parMark K n * (RresP n R)ᵀ := by
  ext i x
  have h := heq (instSlice n x) PBlk.aux2 PBlk.aux2
  rw [encP_marker₃', sum_thp n, encP_aux2_aux2_k₁P, encP_aux2_aux2_k₂P] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at h
  have hterm : ∀ x', R (instSlice n x) (instSlice n x') •
      (P PBlk.aux2 * encP n A (instSlice n x') PBlk.aux2 PBlk.aux2 * (Q PBlk.aux2)ᵀ)
      = (R (instSlice n x) (instSlice n x') * Q PBlk.aux2 () ()) •
          (Matrix.of fun i (_ : Unit) => (P PBlk.aux2 * parMark K n) i x') := by
    intro x'
    rw [encP_marker₃', mul_colP, mul_unit_smul, Matrix.transpose_apply, smul_smul]
  rw [Finset.sum_congr rfl (fun x' _ => hterm x'), sum_smul_colP] at h
  have hix := congrFun (congrFun h i) ()
  simp only [colP, Matrix.of_apply] at hix
  refine hix.trans ?_
  conv_rhs => rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Matrix.transpose_apply, RresP_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem data_equation (n : ℕ) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (P : ∀ b, Matrix (RIdxP n b) (RIdxP n b) K) (Q : ∀ s, Matrix (CIdxP n s) (CIdxP n s) K)
    (R : Matrix (Fin (thp n)) (Fin (thp n)) K)
    (heq : ∀ k b s, encP n B k b s = ∑ k', R k k' • (P b * encP n A k' b s * (Q s)ᵀ)) :
    act3D K (P PBlk.inst) (Q PBlk.inst) (RresP n R) A = B := by
  funext p
  obtain ⟨i, j, x⟩ := p
  have h := heq (instSlice n x) PBlk.inst PBlk.inst
  rw [encP_inst_inst', sum_thp n, encP_inst_inst_k₁P, encP_inst_inst_k₂P] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at h
  have h2 : sliceS B x = sliceS (act3D K (P PBlk.inst) (Q PBlk.inst) (RresP n R) A) x := by
    rw [h, act3D_parabolicSlice]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [RresP_apply, encP_inst_inst']
  exact (congrFun (congrFun h2 i) j).symm

theorem tiPar_rel_zero (A B : DoubledIndex 0 × DoubledIndex 0 × DoubledIndex 0 → K) : (TIPar K).Rel 0 A B :=
  ⟨1, 1, 1, ⟨by simp, fun i _ => i.elim0⟩, ⟨by simp, fun i _ => i.elim0⟩,
    ⟨by simp, fun i _ => i.elim0⟩,
    funext fun p => (p.1.elim (fun i => i.elim0) (fun i => i.elim0) : False).elim⟩

theorem blockEquiv_imp_tiPar (n : ℕ) (hn : 0 < n) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K)
    (h : BlockEquiv (strP n) (encP n A) (encP n B)) : (TIPar K).Rel n A B := by
  obtain ⟨P, Q, R, hP, hQ, hR, hRdiag, heq⟩ := h
  obtain ⟨hp₁, -⟩ := marker₁_parabolic hn A B P Q R hP hQ hRdiag heq
  obtain ⟨-, hp₂⟩ := marker₂_parabolic hn A B P Q R hP hQ hRdiag heq
  have hR3u : IsUnit (RresP n R).det := RresP_isUnit hRdiag hR
  have hq : Q PBlk.aux2 () () ≠ 0 := by
    have := hQ PBlk.aux2
    rwa [Matrix.det_unique, isUnit_iff_ne_zero] at this
  have hqP : IsUnit (Q PBlk.aux2 () () • P PBlk.aux2).det := by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr hq).pow _).mul (hP _)
  have hp₃ : IsParabolic n (RresP n R) :=
    isParabolic_of_compensator_right hqP hR3u (c := 1)
      (by rw [one_smul]; exact (marker₃_equation n A B P Q R heq).symm)
  exact ⟨P PBlk.inst, Q PBlk.inst, RresP n R, hp₁, hp₂, hp₃, data_equation n A B P Q R heq⟩

/-- The marker encoding preserves and reflects parabolic tensor isomorphism. -/
theorem tiPar_iff_blockEquiv (n : ℕ) (A B : DoubledIndex n × DoubledIndex n × DoubledIndex n → K) :
    (TIPar K).Rel n A B ↔ BlockEquiv (strP n) (encP n A) (encP n B) := by
  refine ⟨tiPar_imp_blockEquiv n A B, fun h => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact tiPar_rel_zero A B
  · exact blockEquiv_imp_tiPar n hn A B h

end

end

section

section

open Matrix

set_option maxHeartbeats 800000

variable {K : Type} [Field K]

theorem src_of_zero_one {ι : Type} (c : K) (h : c = 0 ∨ c = 1) :
    ∃ σ : Src ι, ∀ A : ι → K, c = (evalSource A σ) := by
  rcases h with rfl | rfl
  · exact ⟨Src.zero, fun _ => rfl⟩
  · exact ⟨Src.one, fun _ => rfl⟩

theorem parMark_zero_or_one (n : ℕ) (i j : DoubledIndex n) :
    parMark K n i j = 0 ∨ parMark K n i j = 1 := by
  rcases i with a | a <;> rcases j with b | b
  · by_cases hab : a = b
    · right; subst hab; simp [parMark, Matrix.one_apply]
    · left; simp [parMark, Matrix.one_apply, hab]
  · left; rfl
  · left; rfl
  · left; rfl

theorem encP_src (n : ℕ) (z : ArrayPosition PBlk PBlk (RIdxP n) (CIdxP n) (thp n)) :
    ∃ σ : Src (DoubledIndex n × DoubledIndex n × DoubledIndex n),
      ∀ A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K, toFun (encP n A) z = (evalSource A σ) := by
  classical
  obtain ⟨k, ⟨b, i⟩, ⟨s, j⟩⟩ := z
  show ∃ σ : Src (DoubledIndex n × DoubledIndex n × DoubledIndex n), ∀ A : DoubledIndex n × DoubledIndex n × DoubledIndex n → K, encP n A k b s i j = (evalSource A σ)
  cases b <;> cases s

  · rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · exact ⟨Src.coord (i, j, x), fun A => by rw [encP_inst_inst']; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [encP_inst_inst_k₁P]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [encP_inst_inst_k₂P]; rfl⟩

  · by_cases hk : k = k₁P n
    · subst hk
      obtain ⟨σ, hσ⟩ := src_of_zero_one (ι := DoubledIndex n × DoubledIndex n × DoubledIndex n) (parMark K n i j)
        (parMark_zero_or_one n i j)
      exact ⟨σ, fun A => by rw [encP_marker₁]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [encP_marker₁_zero n A hk]; rfl⟩

  · exact ⟨Src.zero, fun _ => rfl⟩

  · by_cases hk : k = k₂P n
    · subst hk
      obtain ⟨σ, hσ⟩ := src_of_zero_one (ι := DoubledIndex n × DoubledIndex n × DoubledIndex n) (parMark K n i j)
        (parMark_zero_or_one n i j)
      exact ⟨σ, fun A => by rw [encP_marker₂]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [encP_marker₂_zero n A hk]; rfl⟩

  · exact ⟨Src.zero, fun _ => rfl⟩

  · exact ⟨Src.zero, fun _ => rfl⟩

  · exact ⟨Src.zero, fun _ => rfl⟩

  · exact ⟨Src.zero, fun _ => rfl⟩

  · rcases slice_trichotomy n k with ⟨x, rfl⟩ | rfl | rfl
    · obtain ⟨σ, hσ⟩ := src_of_zero_one (ι := DoubledIndex n × DoubledIndex n × DoubledIndex n) (parMark K n i x)
        (parMark_zero_or_one n i x)
      exact ⟨σ, fun A => by rw [encP_marker₃']; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [encP_aux2_aux2_k₁P]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [encP_aux2_aux2_k₂P]; rfl⟩

theorem encP_srcExpr (n : ℕ) :
    SrcExpr (fun A : (TIPar K).Idx n → K => toFun (encP n A)) :=
  fun z => encP_src n z

theorem card_RIdxP_sigma (n : ℕ) : Fintype.card (Σ b : PBlk, RIdxP n b) = 6 * n := by
  rw [Fintype.card_sigma]
  have huniv : (Finset.univ : Finset PBlk) = {PBlk.inst, PBlk.aux1, PBlk.aux2} := rfl
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  show Fintype.card (DoubledIndex n) + (Fintype.card (DoubledIndex n) + Fintype.card (DoubledIndex n)) = 6 * n
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

theorem card_CIdxP_sigma (n : ℕ) : Fintype.card (Σ s : PBlk, CIdxP n s) = 4 * n + 1 := by
  rw [Fintype.card_sigma]
  have huniv : (Finset.univ : Finset PBlk) = {PBlk.inst, PBlk.aux1, PBlk.aux2} := rfl
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    card_CIdxP, card_CIdxP]
  simp only [if_neg (show PBlk.inst ≠ PBlk.aux2 by decide),
    if_neg (show PBlk.aux1 ≠ PBlk.aux2 by decide), if_pos rfl, ite_true]
  omega

theorem meas₀_encP_le (n : ℕ) : meas₀ (RIdxP n) (CIdxP n) (thp n) ≤ 12 * (n + 1) := by
  unfold meas₀ meas
  rw [card_RIdxP_sigma, card_CIdxP_sigma]
  have ht : thp n = n + n + 1 + 1 := rfl
  rw [ht]
  omega

theorem card_Idx_TIPar (n : ℕ) : Fintype.card ((TIPar K).Idx n) = 8 * n ^ 3 := by
  show Fintype.card (DoubledIndex n × DoubledIndex n × DoubledIndex n) = _
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

theorem parabolicCubeBound (n : ℕ) : (n + 1) ^ 3 ≤ 8 * (n ^ 3 + 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    have h2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right h (by norm_num)
    nlinarith [h1, h2]

theorem Nside_encP_bound (n : ℕ) :
    Nside (RIdxP n) (CIdxP n) 3 (thp n) ^ 3 ≤
      (Kcomp PBlk PBlk 3 ^ 21 * 12 ^ 24 * 8 ^ 8) * (Fintype.card ((TIPar K).Idx n) + 1) ^ 8 := by
  have hm := meas₀_encP_le n
  have hN : Nside (RIdxP n) (CIdxP n) 3 (thp n) ≤
      Kcomp PBlk PBlk 3 ^ 7 * meas₀ (RIdxP n) (CIdxP n) (thp n) ^ 8 := by
    obtain ⟨ha, hb, hc⟩ := T_sides_le (RowIdx := RIdxP n) (ColIdx := CIdxP n) (n := 3) (t := thp n)
    exact max_le ha (max_le hb hc)
  rw [card_Idx_TIPar]
  have h3 := parabolicCubeBound n
  have h8 : n ^ 3 + 1 ≤ 8 * n ^ 3 + 1 := by omega
  generalize hK : Kcomp PBlk PBlk 3 = Kk at hN ⊢
  generalize hM : meas₀ (RIdxP n) (CIdxP n) (thp n) = m₀ at hN hm ⊢
  calc Nside (RIdxP n) (CIdxP n) 3 (thp n) ^ 3
      ≤ (Kk ^ 7 * m₀ ^ 8) ^ 3 := Nat.pow_le_pow_left hN 3
    _ = Kk ^ 21 * (m₀ ^ 3) ^ 8 := by ring
    _ ≤ Kk ^ 21 * ((12 * (n + 1)) ^ 3) ^ 8 := by gcongr
    _ = (Kk ^ 21 * 12 ^ 24) * ((n + 1) ^ 3) ^ 8 := by ring
    _ ≤ (Kk ^ 21 * 12 ^ 24) * (8 * (n ^ 3 + 1)) ^ 8 := by gcongr
    _ ≤ (Kk ^ 21 * 12 ^ 24) * (8 * (8 * n ^ 3 + 1)) ^ 8 := by gcongr
    _ = (Kk ^ 21 * 12 ^ 24 * 8 ^ 8) * (8 * n ^ 3 + 1) ^ 8 := by ring

/-- The upper reduction: marker encoding followed by partition removal. -/
noncomputable def tiParProjection : Projection (TIPar K) (GL3TI K) :=
  projectionOfEncoding (TIPar K) (fun n => RIdxP n) (fun n => CIdxP n) thp (fun _ => 3) strP
    (fun n A => encP n A) tiPar_iff_blockEquiv encP_srcExpr
    ⟨Kcomp PBlk PBlk 3 ^ 21 * 12 ^ 24 * 8 ^ 8, 8, Nside_encP_bound⟩

theorem tiPar_reduces_gl3ti : (projectionSystem K).reduces (TIPar K) (GL3TI K) :=
  ⟨tiParProjection⟩

end

end

section

section

variable {K : Type} [Field K]

theorem ti_reduces_tiPar : (projectionSystem K).reduces (GL3TI K) (TIPar K) := by
  rw [tiPar_eq_tiFlagPar]
  exact ⟨leviProjectionFlagPar uncutInstance_lvl2⟩

/-- Ordinary and maximal-parabolic tensor isomorphism generate the same
coordinate-projection reduction class over every field. -/
theorem ti_eq_tiPar :
    problemClass (projectionSystem K) (GL3TI K) =
      problemClass (projectionSystem K) (TIPar K) :=
  problemClass_eq_of_reduces_both (projectionSystem K) ti_reduces_tiPar tiPar_reduces_gl3ti

end

end

#print axioms ti_eq_tiPar

end ParabolicTI
