import Mathlib

/-!
# Tensor isomorphism for form-preserving groups

The main theorem `full_block_TIComplete` applies over every field to the full
isometry groups of B_a(n) ⊕ W(n), where B_a(n) = [[0,I],[aI,0]] and the dimension
of W(n) has a linear bound. Neither block needs to be symmetric or invertible.
Transporters are explicitly required to be invertible.

`named_form_families_TIComplete` gives seven concrete real families:
Sp(2n), split O(n,n), the isometries of B_2(n), B_2(n) ⊕ I_n,
B_2(n) ⊕ J_(2n), H_n ⊕ 0_n, and H_n ⊕ I_(2n).
Here H_n = B_1(n); the last form has signature (3n,n).
Groups are specified by their defining forms, without substituting a smaller
block-diagonal subgroup for the full isometry group.

`isometryToGeneral` constructs the upper reduction for every family of bilinear
forms, including singular and nonsymmetric forms. The gadget uses identity
couplings to identify transporters and their inverse transposes. Moving the
input tensor to the dual-action blocks encodes form preservation without ever
inverting the form. A concrete partition-removal compiler produces ordinary
cubic tensors. Hyperbolic padding gives the lower reduction, with orbit
reflection through intrinsic tensor supports; conciseness is not assumed.

`TIComplete` means reductions in both directions by coordinate projections with
field constants and polynomial bounds on the number of output field entries.
`full_block_class_eq` proves equality of the corresponding reduction classes.
Uniform machine running times and bit complexity are not formalized here.
The concrete families above have explicit constant-coefficient forms.

These results address specified families in Chen, Grochow, Qiao, Tang, and
Zhang's Open Question 11 (Question 1.11 in the full version), not the entire
classification question. Their classical-group upper reduction is prior work.
The partition-removal construction is based on Futorny, Grochow, and Sergeichuk.

References:
Chen et al., ITCS 2024, doi:10.4230/LIPIcs.ITCS.2024.31.
Futorny et al., Linear Algebra and its Applications 566 (2019), 212-244,
doi:10.1016/j.laa.2018.12.022.
-/

namespace FormTI

section TensorCore

section MatrixRank

universe u v

variable {K : Type u} [Field K]

section ProdSubmodule

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

end ProdSubmodule

section BlockRank

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

end BlockRank

end MatrixRank

section RankBands

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

end RankBands

section RankSeparation

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

end RankSeparation

section RankRigidity

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

end RankRigidity

section PaddedSlices

open Matrix
open Finset

universe u

variable {K : Type u} [Field K]

section Ediag

variable {s : ℕ}

def Ediag (r : ℕ) (γ : Fin s) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin s × Fin (2 ^ s * r)) K :=
  Matrix.diagonal (fun p => if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0)

end Ediag

section Gadget

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

end Gadget

section Degenerate

theorem rank_lt_of_card_rows_lt {R C : Type} [Fintype R] [Fintype C] {r : ℕ}
    (h : Fintype.card R < r) (M : Matrix R C K) : M.rank < r := by
  have h0 : Module.finrank K (R → K) = Fintype.card R := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank K (LinearMap.range M.mulVecLin) ≤ Module.finrank K (R → K) :=
    Submodule.finrank_le _
  unfold Matrix.rank
  omega

end Degenerate

end PaddedSlices

section PartitionedArrays

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

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

section Pad

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

end Pad

end PartitionedArrays

section LinkedArrays

open Matrix

universe u

variable {K : Type u} [Field K] {t n : ℕ}

abbrev Fib (str : Fin t → Fin n) (g : Fin n) : Type := {k : Fin t // str k = g}

section Assemble

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

end Assemble

section LinksDef

structure Links (Pos : Type) (Idx : Pos → Type) (Cls : Type) (ClsIdx : Cls → Type) where
  cls : Pos → Cls
  star : Cls → Cls
  star_involutive : ∀ c, star (star c) = c
  e : ∀ a : Pos, Idx a ≃ ClsIdx (cls a)
  starIdx : ∀ c, ClsIdx c ≃ ClsIdx (star c)

end LinksDef

end LinkedArrays

section HyperbolicPadding

open TensorProduct

section Hyperbolic

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

def iota : U →ₗ[K] Hyp K U := LinearMap.inl K U (Module.Dual K U)

@[simp] theorem iota_apply (u : U) : (iota u : Hyp K U) = (u, 0) := rfl

@[simp] theorem iota_isotropic (u v : U) : omegaH (iota u : Hyp K U) (iota v) = 0 := by simp

def levi (P : U ≃ₗ[K] U) : Hyp K U ≃ₗ[K] Hyp K U :=
  LinearEquiv.prodCongr P P.symm.dualMap

@[simp] theorem levi_apply (P : U ≃ₗ[K] U) (x : Hyp K U) :
    levi P x = (P x.1, P.symm.dualMap x.2) := rfl

@[simp] theorem levi_iota (P : U ≃ₗ[K] U) (u : U) :
    levi P (iota u : Hyp K U) = iota (P u) := by
  simp [iota]

end Hyperbolic

section ModeSupport

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

end ModeSupport

section Rigidity

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

end Rigidity

section ThreeTensor

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

end ThreeTensor

section Open

open scoped BigOperators

abbrev CoordHyp (K : Type*) (n : ℕ) := (Fin n → K) × (Fin n → K)

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

noncomputable def hypCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Hyp K (Fin n → K) ≃ₗ[K] CoordHyp K n :=
  (LinearEquiv.refl K (Fin n → K)).prodCongr (dualCoordEquiv K n)

@[simp] theorem hypCoordEquiv_apply (K : Type*) [Field K] (n : ℕ)
    (x : Hyp K (Fin n → K)) :
    hypCoordEquiv K n x = (x.1, dualCoordEquiv K n x.2) := rfl

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

end Open

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

end HyperbolicPadding

section CoordinatePadding

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

end CoordinatePadding

section ProjectionReductions

open Matrix

universe u

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

end

section Problems

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

def act3D {n : ℕ} (P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (A : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

end Problems

end ProjectionReductions

section PairingConstraints

open Matrix

universe u v

section General

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

end General

end PairingConstraints

section TensorSystems

open Matrix
open TensorProduct

universe u v

section Bil

variable {K : Type u} [Field K] {U : Type v} [AddCommGroup U] [Module K U]

def PreservesBil (ω : U →ₗ[K] U →ₗ[K] K) (g : U ≃ₗ[K] U) : Prop :=
  ∀ x y, ω (g x) (g y) = ω x y

end Bil

end TensorSystems

section SymplecticEncoding

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

end SymplecticEncoding

section AnchorNormalization

open Matrix

universe u

variable {K : Type u} [Field K]

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

end AnchorNormalization

section GadgetRigidity

open Matrix

universe u

variable {K : Type u} [Field K]

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

end GadgetRigidity

section ReverseTransport

open Matrix

universe u

variable {K : Type u} [Field K]

theorem sum3_rotate {α : Type} [Fintype α] (F : α → α → α → K) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ (Finset.univ : Finset α)) =>
    (Finset.sum_comm : (∑ a, ∑ c, F a b c) = ∑ c, ∑ a, F a b c)]
  rw [Finset.sum_comm]

end ReverseTransport

section ForwardTransport

open Matrix

universe u

variable {K : Type u} [Field K]

section Setup

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : SymplecticIndex n ≃ Fib strH 0) (e1 : SymplecticIndex n ≃ Fib strH 1) (e2 : SymplecticIndex n ≃ Fib strH 2)

noncomputable abbrev invT (g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) : Matrix (SymplecticIndex n) (SymplecticIndex n) K := g⁻¹ᵀ

noncomputable def Rst (g₁ g₂ g₃ : Matrix (SymplecticIndex n) (SymplecticIndex n) K) :
    ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K
  | 0 => Matrix.reindex e0 e0 g₃
  | 1 => Matrix.reindex e1 e1 g₁
  | 2 => Matrix.reindex e2 e2 (invT g₂)
  | 3 => 1

end Setup

section Sums

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

end Sums

end ForwardTransport

section ForwardEncoding

open Matrix

universe u

variable {K : Type u} [Field K]

theorem sum_smul_entry {I J ι : Type} [Fintype ι] (c : ι → K) (M : ι → Matrix I J K) (i : I)
    (j : J) : (∑ m, c m • M m) i j = ∑ m, c m * M m i j := by
  simp [Matrix.sum_apply]

section Vectors

variable {n : ℕ}

variable (K)

variable {K} {I J : Type}

theorem sum_one_smul {I : Type} [Fintype I] [DecidableEq I] {I' J' : Type} (a : I)
    (C : Matrix I' J' K) : ∑ j, (1 : Matrix I I K) a j • C = C := by
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]

end Vectors

section Steps

variable {n th : ℕ} (strH : Fin th → Fin 4)

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

end Steps

end ForwardEncoding

section ModuleCancellation

open LinearMap Submodule

universe u v

variable {R : Type u} [Ring R]

def Indecomposable (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ p q : Submodule R M, IsCompl p q → p = ⊥ ∨ q = ⊥

section Fitting

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

end Fitting

section BlockUnit

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

end BlockUnit

section Indecomposable

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

end Indecomposable

section General

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

end General

end ModuleCancellation

section RepresentationCancellation

universe u v

variable {K : Type u} [Field K]
variable {Src Snk Arr : Type} [Fintype Src] [Fintype Snk] [Fintype Arr]
variable [DecidableEq Src] [DecidableEq Snk]

structure BRep (K : Type u) [Field K] (Src Snk Arr : Type) (V : Src → Type v) (W : Snk → Type v)
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] where
  f : Arr → ∀ s t, V s →ₗ[K] W t

section Defs

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

end Defs

section Gen

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

end Gen

section Iso

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

end Iso

section DSum

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

end DSum

section Cancel

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

end Cancel

end RepresentationCancellation

section TensorCoordinates

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

noncomputable def glActMat (P Q R : Matrix ι ι K) :
    (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) →ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  TensorProduct.map (Matrix.toLin' P) (TensorProduct.map (Matrix.toLin' Q) (Matrix.toLin' R))

theorem repr_toLin'_basis (P : Matrix ι ι K) (i a : ι) :
    (e ι).repr (Matrix.toLin' P (e ι i)) a = P a i := by
  simp [Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]

noncomputable def linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) : (ι → K) ≃ₗ[K] (ι → K) :=
  Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P ((Matrix.isUnit_iff_isUnit_det P).mp hP))

theorem coe_linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) :
    (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' P :=
  Matrix.toLinearEquiv'_apply P _

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

end TensorCoordinates

section MatrixCancellation

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

section Pad

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

end Pad

end MatrixCancellation

section PartitionDeletion

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

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

end PartitionDeletion

section FlatArrays

open Matrix

universe u

variable {K : Type u} [Field K]

section Flat

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

end Flat

section Assemble

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

end Assemble

section Bridge

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

end Bridge

end FlatArrays

section Reindexing

universe u

variable {K : Type u} [Field K]

section Reindex

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

end Reindex

section Unflatten

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

end Unflatten

end Reindexing

section ThreeDeletions

universe u

variable {K : Type u} [Field K]

section Triv

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

end Triv

section Rot

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

end Rot

section Three

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

end Three

end ThreeDeletions

section CoefficientSources

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

section PArrFun

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

end PArrFun

section Pad

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

end Pad

section Perm

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

end Perm

section Composite

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

end Composite

end CoefficientSources

section SupportCancellation

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

end SupportCancellation

section CubeExtension

open TensorProduct Module

universe u

variable {K : Type u} [Field K]

section Bridge

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

end Bridge

section Inclusion

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

end Inclusion

section CubeExt

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

end CubeExt

section Main

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

end Main

end CubeExtension

section EncodingProjection

universe u

variable {K : Type u} [Field K]

section Reindex

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

end Reindex

theorem act3_eq_act {N : ℕ} (P Q R : Matrix (Fin N) (Fin N) K) (A : Fin N × Fin N × Fin N → K) :
    act3 K P Q R A = act P Q R A := by
  funext ⟨i, j, k⟩
  rfl

theorem gl3ti_rel_iff {N : ℕ} (A B : Fin N × Fin N × Fin N → K) :
    (GL3TI K).Rel N A B ↔
      ∃ P Q R : Matrix (Fin N) (Fin N) K,
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R A = B := by
  simp only [GL3TI, act3_eq_act]

section Cube

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

end Cube

end EncodingProjection

section OneStageSize

universe u

variable {K : Type u} [Field K]

section Cards

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

end Cards

section Stage

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

end Stage

end OneStageSize

section CompositeSize

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

section Composite

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

end Composite

end CompositeSize

section PaddingProjection

open Matrix
open TensorProduct

universe u

variable {K : Type u} [Field K]

abbrev DoubledIndex (n : ℕ) := Fin n ⊕ Fin n

def padSrc {n : ℕ} : DoubledIndex n × DoubledIndex n × DoubledIndex n → Src (Fin n × Fin n × Fin n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => Src.coord (i, j, k)
  | _ => Src.zero

def padCoordinates {n : ℕ} (A : Fin n × Fin n × Fin n → K) : DoubledIndex n × DoubledIndex n × DoubledIndex n → K :=
  fun j => (evalSource A (padSrc j))

@[simp] theorem padArr_inl {n : ℕ} (A : Fin n × Fin n × Fin n → K) (i j k : Fin n) :
    padCoordinates A (Sum.inl i, Sum.inl j, Sum.inl k) = A (i, j, k) := rfl

end PaddingProjection

section ReverseProjection

universe u

set_option maxHeartbeats 800000

variable {K : Type u} [Field K]

theorem cube_succ_le (n : ℕ) : (n + 1) ^ 3 ≤ 8 * n ^ 3 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    have h2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right h (by norm_num)
    nlinarith [h1, h2]

end ReverseProjection

end TensorCore

section BilinearConstraints

open Matrix

section GeneralFormEncoding

open Matrix

universe u

variable {K : Type u} [Field K]

section Couplings

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem chain_certifies_covariant {Ψ g h k : Matrix ι ι K}
    (H₁ : Coupling (1 : Matrix ι ι K) g h) (H₂ : Coupling (1 : Matrix ι ι K) h k)
    (HΨ : Coupling Ψ g k) : g * Ψ * gᵀ = Ψ := by
  have hkg : k = g := coupling_one_chain H₁ H₂
  rw [hkg] at HΨ
  exact HΨ

end Couplings

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

end GeneralFormEncoding

end BilinearConstraints

section ConstantProjections

set_option maxHeartbeats 1600000
section FormFamilies

open Matrix

universe u

variable {K : Type u} [Field K]

noncomputable def hypLift {n : ℕ} (P : Matrix (Fin n) (Fin n) K) : Matrix (SymplecticIndex n) (SymplecticIndex n) K :=
  Matrix.fromBlocks P 0 0 P⁻¹ᵀ

def hypForm (n : ℕ) (ε : K) : Matrix (SymplecticIndex n) (SymplecticIndex n) K := Matrix.fromBlocks 0 1 (ε • 1) 0

def IsIsometry (n : ℕ) (ε : K) (g : Matrix (SymplecticIndex n) (SymplecticIndex n) K) : Prop :=
  gᵀ * hypForm n ε * g = hypForm n ε

theorem hypLift_isIsometry {n : ℕ} (ε : K) (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) :
    IsIsometry n ε (hypLift P) := by
  unfold IsIsometry hypForm hypLift
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_transpose]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul P hP, Matrix.transpose_one]

structure ConstantProjection (P Q : CoordProblem K) where
  size : ℕ → ℕ
  src : ∀ n, Q.Idx (size n) → K ⊕ P.Idx n
  polyBound : ∃ c k : ℕ, ∀ n,
    Fintype.card (Q.Idx (size n)) ≤ c * (Fintype.card (P.Idx n) + 1) ^ k
  correct : ∀ n (A B : P.Idx n → K), P.Rel n A B ↔
    Q.Rel (size n) (fun j => (src n j).elim id A) (fun j => (src n j).elim id B)

def sourceWithConstants {I : Type} : Src I → K ⊕ I
  | .coord i => .inr i
  | .zero => .inl 0
  | .one => .inl 1
  | .negOne => .inl (-1)

theorem sourceWithConstants_eval {I : Type} (s : Src I) (A : I → K) :
    (sourceWithConstants s).elim id A = evalSource A s := by cases s <;> rfl

def allowConstants {P Q : CoordProblem K} (r : Projection P Q) : ConstantProjection P Q where
  size := r.size
  src := fun n j => sourceWithConstants (r.src n j)
  polyBound := r.polyBound
  correct := by intro n A B; simpa only [sourceWithConstants_eval] using r.correct n A B

def TIComplete (P : CoordProblem K) : Prop :=
  Nonempty (ConstantProjection (GL3TI K) P) ∧ Nonempty (ConstantProjection P (GL3TI K))

def ConstantSourceExpr {I J : Type} (F : (I → K) → J → K) : Prop :=
  ∀ j, ∃ s : K ⊕ I, ∀ A, F A j = s.elim id A

theorem compile_constant_sources {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    {RowIdx : β → Type} {ColIdx : γ → Type}
    [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
    [∀ c, Fintype (ColIdx c)] [∀ c, DecidableEq (ColIdx c)]
    {t q : ℕ} {I : Type} (str : Fin t → Fin q)
    (E : (I → K) → PArr K β γ RowIdx ColIdx t)
    (hE : ConstantSourceExpr (fun A => toFun (E A))) :
    ConstantSourceExpr (fun A => cube str (E A)) := by
  intro j
  obtain ⟨s, hs⟩ := cube_srcExpr (K := K) str
    (fun X : ArrayPosition β γ RowIdx ColIdx t → K => ofFun X)
    (fun p => ⟨Src.coord p, fun _ => rfl⟩) j
  cases s with
  | coord p =>
    obtain ⟨v, hv⟩ := hE p
    exact ⟨v, fun A => (hs (toFun (E A))).trans (hv A)⟩
  | zero => exact ⟨Sum.inl 0, fun A => hs (toFun (E A))⟩
  | one => exact ⟨Sum.inl 1, fun A => hs (toFun (E A))⟩
  | negOne => exact ⟨Sum.inl (-1), fun A => hs (toFun (E A))⟩

end FormFamilies

end ConstantProjections

section NondegenerateFamilies

open Matrix
set_option maxHeartbeats 400000
set_option Elab.async false
universe u
variable {K : Type u} [Field K]

section ReindexForms
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def FormOrbit (Φ : Matrix I I K) (A B : I × I × I → K) : Prop :=
  ∃ g₁ g₂ g₃ : Matrix I I K,
    g₁ᵀ * Φ * g₁ = Φ ∧ g₂ᵀ * Φ * g₂ = Φ ∧ g₃ᵀ * Φ * g₃ = Φ ∧ act g₁ g₂ g₃ A = B

theorem isometry_reindex (e : I ≃ J) (Φ g : Matrix I I K) :
    (Matrix.reindex e e g)ᵀ * Matrix.reindex e e Φ * Matrix.reindex e e g = Matrix.reindex e e Φ ↔
      gᵀ * Φ * g = Φ := by
  rw [Matrix.transpose_reindex, ← Matrix.reindexAlgEquiv_apply K K e,
    ← Matrix.reindexAlgEquiv_apply K K e, ← Matrix.reindexAlgEquiv_apply K K e, ← map_mul, ← map_mul]
  exact (Matrix.reindexAlgEquiv K K e).injective.eq_iff

end ReindexForms

section Sources
variable {I J L : Type}

theorem compose_constant_sources (F : (I → K) → J → K) (G : (J → K) → L → K)
    (hF : ConstantSourceExpr F) (hG : ConstantSourceExpr G) :
    ConstantSourceExpr (fun A => G (F A)) := by
  intro l
  obtain ⟨s, hs⟩ := hG l
  cases s with
  | inl c => exact ⟨Sum.inl c, fun A => hs (F A)⟩
  | inr j =>
    obtain ⟨r, hr⟩ := hF j
    exact ⟨r, fun A => (hs (F A)).trans (hr A)⟩

end Sources

section Families
variable (I : ℕ → Type) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

noncomputable def BilinearTI (Φ : ∀ n, Matrix (I n) (I n) K) : CoordProblem K where
  Idx := fun n => I n × I n × I n
  fin := fun _ => inferInstance
  Rel := fun n => FormOrbit (Φ n)

end Families

end NondegenerateFamilies

section BlockPadding

open Matrix
set_option maxHeartbeats 1600000

def IsIsom {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]
    (Φ g : Matrix I I K) : Prop := gᵀ * Φ * g = Φ
def padArrB {K : Type} [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (A : Fin n × Fin n × Fin n → K) : (Fin n ⊕ β) × (Fin n ⊕ β) × (Fin n ⊕ β) → K
  | (Sum.inl i, Sum.inl j, Sum.inl k) => A (i, j, k)
  | _ => 0

@[simp] theorem padArrB_inl {K : Type} [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (A : Fin n × Fin n × Fin n → K) (i j k : Fin n) :
    padArrB β A (Sum.inl i, Sum.inl j, Sum.inl k) = A (i, j, k) := rfl

def blockForm {K : Type} [Field K] (n : ℕ) (ε : K) {β : Type} [Fintype β] [DecidableEq β]
    (W : Matrix β β K) : Matrix (Fin n ⊕ (Fin n ⊕ β)) (Fin n ⊕ (Fin n ⊕ β)) K :=
  Matrix.reindex (Equiv.sumAssoc (Fin n) (Fin n) β) (Equiv.sumAssoc (Fin n) (Fin n) β)
    (Matrix.fromBlocks (hypForm n ε) 0 0 W)

noncomputable def blockLift3 {K : Type} [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (P : Matrix (Fin n) (Fin n) K) : Matrix (Fin n ⊕ (Fin n ⊕ β)) (Fin n ⊕ (Fin n ⊕ β)) K :=
  Matrix.fromBlocks P 0 0 (Matrix.fromBlocks P⁻¹ᵀ 0 0 1)

def BlockLiftPreserves (K : Type) [Field K] : Prop :=
  ∀ (n : ℕ) (ε : K) (β : Type) [Fintype β] [DecidableEq β] (W : Matrix β β K)
    (P : Matrix (Fin n) (Fin n) K), IsUnit P.det → IsIsom (blockForm n ε W) (blockLift3 β P)

def PaddingPrinciple (K : Type) [Field K] : Prop :=
  ∀ (n : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (Grp : Matrix (Fin n ⊕ β) (Fin n ⊕ β) K → Prop),
    (∀ g, Grp g → IsUnit g.det) →
    (∀ P : Matrix (Fin n) (Fin n) K, IsUnit P.det →
        ∃ X : Matrix β β K, Grp (Matrix.fromBlocks P 0 0 X)) →
    ∀ A B : Fin n × Fin n × Fin n → K,
      (GL3TI K).Rel n A B ↔
        ∃ g₁ g₂ g₃ : Matrix (Fin n ⊕ β) (Fin n ⊕ β) K,
          Grp g₁ ∧ Grp g₂ ∧ Grp g₃ ∧ act g₁ g₂ g₃ (padArrB β A) = padArrB β B

theorem blockLift_reindex (K : Type) [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (P : Matrix (Fin n) (Fin n) K) :
    blockLift3 β P = Matrix.reindex (Equiv.sumAssoc (Fin n) (Fin n) β)
      (Equiv.sumAssoc (Fin n) (Fin n) β) (Matrix.fromBlocks (hypLift P) 0 0 1) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blockLift3, hypLift, Matrix.fromBlocks, Matrix.one_apply]

theorem blockLift_preserves (K : Type) [Field K] : BlockLiftPreserves K := by
  intro n ε β _ _ W P hP
  unfold IsIsom blockForm
  rw [blockLift_reindex, Matrix.transpose_reindex]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  rw [hypLift_isIsometry ε P hP]

theorem blockLift_action (K : Type) [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (P Q R : Matrix (Fin n) (Fin n) K) (X Y Z : Matrix β β K) (A : Fin n × Fin n × Fin n → K) :
    act (Matrix.fromBlocks P 0 0 X) (Matrix.fromBlocks Q 0 0 Y) (Matrix.fromBlocks R 0 0 Z)
        (padArrB β A) = padArrB β (act3 K P Q R A) := by
  funext y
  obtain ⟨i, j, k⟩ := y
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp [act, act3, padArrB, Fintype.sum_sum_type]

noncomputable def padEquiv {n : ℕ} (β : Type) [Fintype β] :
    Fin n ⊕ β ≃ Fin (n + Fintype.card β) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Fintype.equivFin β)).trans finSumFinEquiv

theorem padding_reindex (K : Type) [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (A : Fin n × Fin n × Fin n → K) :
    reindex3 (padEquiv β) (padEquiv β) (padEquiv β) (padArrB β A) =
      cubeExt K (n + Fintype.card β) A := by
  funext y
  obtain ⟨y₁, y₂, y₃⟩ := y
  simp only [reindex3, cubeExt]
  induction y₁ using Fin.addCases <;> induction y₂ using Fin.addCases <;>
    induction y₃ using Fin.addCases <;> simp [padEquiv, padArrB]

theorem padding_reflects_general (K : Type) [Field K] {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (g₁ g₂ g₃ : Matrix (Fin n ⊕ β) (Fin n ⊕ β) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) (A B : Fin n × Fin n × Fin n → K)
    (h : act g₁ g₂ g₃ (padArrB β A) = padArrB β B) : (GL3TI K).Rel n A B := by
  have hflat : ∃ P₁ P₂ P₃ : Matrix (Fin n ⊕ β) (Fin n ⊕ β) K,
      IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧
        act P₁ P₂ P₃ (padArrB β A) = padArrB β B :=
    ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
  rw [exists_act_reindex3 (padEquiv β) (padEquiv β) (padEquiv β), padding_reindex,
    padding_reindex, exists_det_iff_isUnit] at hflat
  have hle : n ≤ n + Fintype.card β := Nat.le_add_right _ _
  exact (gl3ti_rel_iff A B).mpr ((cubeExt_equiv_iff (K := K) hle hle hle A B).mpr hflat)

theorem padding_principle (K : Type) [Field K] : PaddingPrinciple K := by
  intro n β _ _ Grp hunit hlift A B
  constructor
  · intro hAB
    obtain ⟨P, Q, R, hP, hQ, hR, hact⟩ := (gl3ti_rel_iff A B).mp hAB
    obtain ⟨X, hX⟩ := hlift P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
    obtain ⟨Y, hY⟩ := hlift Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
    obtain ⟨Z, hZ⟩ := hlift R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
    refine ⟨_, _, _, hX, hY, hZ, ?_⟩
    rw [blockLift_action, act3_eq_act, hact]
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
    exact padding_reflects_general K β g₁ g₂ g₃ (hunit g₁ h₁) (hunit g₂ h₂) (hunit g₃ h₃) A B h

section Completeness
variable {K : Type} [Field K]
variable (w : ℕ → ℕ) (a : K) (W : ∀ n, Matrix (Fin (w n)) (Fin (w n)) K)

abbrev BlockIndex (n : ℕ) := Fin n ⊕ (Fin n ⊕ Fin (w n))

noncomputable def BlockTI : CoordProblem K :=
  BilinearTI (BlockIndex w) (fun n => blockForm n a (W n))

def blockPaddingSource {n : ℕ} : BlockIndex w n × BlockIndex w n × BlockIndex w n → K ⊕ (Fin n × Fin n × Fin n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => Sum.inr (i,j,k)
  | _ => Sum.inl 0

theorem blockPaddingSource_eval (n : ℕ) (A : Fin n × Fin n × Fin n → K) :
    (fun j => (blockPaddingSource w j).elim id A) = padArrB (Fin n ⊕ Fin (w n)) A := by
  funext ⟨i,j,k⟩
  cases i <;> cases j <;> cases k <;> rfl

end Completeness

noncomputable def symplecticExtra (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℝ :=
  Matrix.reindex ((finSumFinEquiv (m := n) (n := n)).trans (finCongr (by omega)))
    ((finSumFinEquiv (m := n) (n := n)).trans (finCongr (by omega))) (stdJ ℝ n)

end BlockPadding

section GeneralFormEncoding

open Matrix
set_option maxHeartbeats 800000
section FiniteEncodingSetup
universe u
variable {K : Type u} [Field K]
abbrev finite_BIdx (n : ℕ) : Blk → Type
  | Blk.dat => Fin n
  | Blk.cop => Fin n
  | Blk.mid => Fin n
  | Blk.anch => Unit

instance finite_instFintypeBIdx (n : ℕ) : ∀ b : Blk, Fintype (finite_BIdx n b)
  | Blk.dat => inferInstanceAs (Fintype (Fin n))
  | Blk.cop => inferInstanceAs (Fintype (Fin n))
  | Blk.mid => inferInstanceAs (Fintype (Fin n))
  | Blk.anch => inferInstanceAs (Fintype Unit)

instance finite_instDecEqBIdx (n : ℕ) : ∀ b : Blk, DecidableEq (finite_BIdx n b)
  | Blk.dat => inferInstanceAs (DecidableEq (Fin n))
  | Blk.cop => inferInstanceAs (DecidableEq (Fin n))
  | Blk.mid => inferInstanceAs (DecidableEq (Fin n))
  | Blk.anch => inferInstanceAs (DecidableEq Unit)

abbrev finite_thn (n : ℕ) : ℕ := 3 * n + 1

abbrev finite_Idx3 (n : ℕ) : Type := Fin n ⊕ (Fin n ⊕ (Fin n ⊕ Unit))

def finite_tag3 (n : ℕ) : finite_Idx3 n → Fin 4
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

theorem finite_card_Idx3 (n : ℕ) : Fintype.card (finite_Idx3 n) = finite_thn n := by
  simp only [finite_Idx3, finite_thn, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

noncomputable def finite_packEquiv (n : ℕ) : finite_Idx3 n ≃ Fin (finite_thn n) :=
  Fintype.equivFinOfCardEq (finite_card_Idx3 n)

noncomputable def finite_strHn (n : ℕ) : Fin (finite_thn n) → Fin 4 :=
  fun k => finite_tag3 n ((finite_packEquiv n).symm k)

noncomputable def finite_fibEquiv (n : ℕ) (g : Fin 4) :
    Fib (finite_strHn n) g ≃ {x : finite_Idx3 n // finite_tag3 n x = g} :=
  Equiv.subtypeEquiv (finite_packEquiv n).symm (fun _ => Iff.rfl)

noncomputable def finite_sub0 (n : ℕ) : Fin n ≃ {x : finite_Idx3 n // finite_tag3 n x = 0} :=
  Equiv.ofBijective (fun v => ⟨Sum.inl v, rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · exact ⟨v, rfl⟩
      · rcases y with u | z
        · simp [finite_tag3] at hx
        · rcases z with p | q <;> simp [finite_tag3] at hx⟩

noncomputable def finite_sub1 (n : ℕ) : Fin n ≃ {x : finite_Idx3 n // finite_tag3 n x = 1} :=
  Equiv.ofBijective (fun v => ⟨Sum.inr (Sum.inl v), rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [finite_tag3] at hx
      · rcases y with u | z
        · exact ⟨u, rfl⟩
        · rcases z with p | q <;> simp [finite_tag3] at hx⟩

noncomputable def finite_sub2 (n : ℕ) : Fin n ≃ {x : finite_Idx3 n // finite_tag3 n x = 2} :=
  Equiv.ofBijective (fun v => ⟨Sum.inr (Sum.inr (Sum.inl v)), rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [finite_tag3] at hx
      · rcases y with u | z
        · simp [finite_tag3] at hx
        · rcases z with p | q
          · exact ⟨p, rfl⟩
          · simp [finite_tag3] at hx⟩

noncomputable def finite_sub3 (n : ℕ) : Unit ≃ {x : finite_Idx3 n // finite_tag3 n x = 3} :=
  Equiv.ofBijective (fun _ => ⟨Sum.inr (Sum.inr (Sum.inr ())), rfl⟩)
    ⟨fun v w _ => Subsingleton.elim v w,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [finite_tag3] at hx
      · rcases y with u | z
        · simp [finite_tag3] at hx
        · rcases z with p | q
          · simp [finite_tag3] at hx
          · exact ⟨(), by cases q; rfl⟩⟩

noncomputable def finite_e0n (n : ℕ) : Fin n ≃ Fib (finite_strHn n) 0 := (finite_sub0 n).trans (finite_fibEquiv n 0).symm
noncomputable def finite_e1n (n : ℕ) : Fin n ≃ Fib (finite_strHn n) 1 := (finite_sub1 n).trans (finite_fibEquiv n 1).symm
noncomputable def finite_e2n (n : ℕ) : Fin n ≃ Fib (finite_strHn n) 2 := (finite_sub2 n).trans (finite_fibEquiv n 2).symm

noncomputable def finite_e3n (n : ℕ) : Unit ≃ Fib (finite_strHn n) 3 := (finite_sub3 n).trans (finite_fibEquiv n 3).symm

noncomputable def finite_k3 (n : ℕ) : Fin (finite_thn n) := ((finite_e3n n) ()).1

theorem finite_strHn_k3 (n : ℕ) : finite_strHn n (finite_k3 n) = 3 := ((finite_e3n n) ()).2

theorem finite_eq_k3 (n : ℕ) {k : Fin (finite_thn n)} (h : finite_strHn n k = 3) : k = finite_k3 n := by
  have h1 : (finite_e3n n) ((finite_e3n n).symm ⟨k, h⟩) = ⟨k, h⟩ := (finite_e3n n).apply_symm_apply _
  have h2 : ((finite_e3n n).symm ⟨k, h⟩) = () := Subsingleton.elim _ _
  rw [h2] at h1
  exact (congrArg Subtype.val h1).symm

noncomputable def finite_Rres {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : Fin n ≃ Fib strH γ)
    (R : Matrix (Fin th) (Fin th) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun x y => R (e x).1 (e y).1

theorem finite_Rres_apply {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : Fin n ≃ Fib strH γ)
    (R : Matrix (Fin th) (Fin th) K) (x y : Fin n) :
    finite_Rres (K := K) e R x y = R (e x).1 (e y).1 := rfl

theorem finite_symm_coe {n th : ℕ} {strH : Fin th → Fin 4} {γ : Fin 4} (e : Fin n ≃ Fib strH γ) (x : Fin n)
    (h : strH (e x).1 = γ) : e.symm ⟨(e x).1, h⟩ = x := by
  have hs : (⟨(e x).1, h⟩ : Fib strH γ) = e x := Subtype.ext rfl
  rw [hs, Equiv.symm_apply_apply]

theorem finite_anchorSlice_coupling {n : ℕ} (b s : Blk) (M : Matrix (finite_BIdx n b) (finite_BIdx n s) K)
    (X Y : PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n))
    (hXon : X (finite_k3 n) b s = M)
    (hXoff : ∀ k, finite_strHn n k ≠ 3 → X k b s = 0)
    (hYon : Y (finite_k3 n) b s = M)
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (hR1 : R (finite_k3 n) (finite_k3 n) = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    P b * M * (Q s)ᵀ = M := by
  classical
  have hsum : (∑ k', R (finite_k3 n) k' • (P b * X k' b s * (Q s)ᵀ))
      = R (finite_k3 n) (finite_k3 n) • (P b * M * (Q s)ᵀ) := by
    rw [Finset.sum_eq_single (finite_k3 n)]
    · rw [hXon]
    · intro k' _ hk'
      have hs : finite_strHn n k' ≠ 3 := fun hc => hk' (finite_eq_k3 n hc)
      rw [hXoff k' hs]
      simp
    · intro hnot
      exact absurd (Finset.mem_univ (finite_k3 n)) hnot
  have h := heq (finite_k3 n) b s
  rw [hYon, hsum, hR1, one_smul] at h
  exact h.symm

theorem finite_stratumRow_coupling {n : ℕ} (b : Blk) {γ : Fin 4} (e : Fin n ≃ Fib (finite_strHn n) γ)
    (M : Matrix (finite_BIdx n b) (Fin n) K)
    (X Y : PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n))
    (hXon : ∀ (k : Fin (finite_thn n)) (h : finite_strHn n k = γ) (i : finite_BIdx n b) (u : finite_BIdx n Blk.anch),
      X k b Blk.anch i u = M i (e.symm ⟨k, h⟩))
    (hXoff : ∀ k, finite_strHn n k ≠ γ → X k b Blk.anch = 0)
    (hYon : ∀ (k : Fin (finite_thn n)) (h : finite_strHn n k = γ) (i : finite_BIdx n b) (u : finite_BIdx n Blk.anch),
      Y k b Blk.anch i u = M i (e.symm ⟨k, h⟩))
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (hQa : Q Blk.anch = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    P b * M * (finite_Rres e R)ᵀ = M := by
  classical
  ext i x
  have hk : finite_strHn n (e x).1 = γ := (e x).2
  have hex : e.symm ⟨(e x).1, hk⟩ = x := finite_symm_coe e x hk
  have hQt : ((Q Blk.anch)ᵀ : Matrix (finite_BIdx n Blk.anch) (finite_BIdx n Blk.anch) K) = 1 := by
    rw [hQa, Matrix.transpose_one]

  have h := congrFun (congrFun (heq (e x).1 b Blk.anch) i) (default : finite_BIdx n Blk.anch)
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (finite_thn n),
      (R (e x).1 k' • (P b * X k' b Blk.anch * (Q Blk.anch)ᵀ)) i (default : finite_BIdx n Blk.anch)
        = R (e x).1 k' * ∑ i', P b i i' * X k' b Blk.anch i' (default : finite_BIdx n Blk.anch) := by
    intro k'
    rw [hQt, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (finite_thn n), finite_strHn n k' ≠ γ →
      R (e x).1 k' * ∑ i', P b i i' * X k' b Blk.anch i' (default : finite_BIdx n Blk.anch) = 0 := by
    intro k' hk'
    rw [hXoff k' hk']
    simp
  rw [sum_fibre (finite_strHn n) γ _ hzero] at h
  have hre : (∑ c : Fib (finite_strHn n) γ,
        R (e x).1 c.1 * ∑ i', P b i i' * X c.1 b Blk.anch i' (default : finite_BIdx n Blk.anch))
      = ∑ y : Fin n, R (e x).1 (e y).1 * ∑ i', P b i i' * M i' y := by
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro y
    have hin : ∀ i' : finite_BIdx n b,
        P b i i' * M i' y
          = P b i i' * X (e y).1 b Blk.anch i' (default : finite_BIdx n Blk.anch) := by
      intro i'
      rw [hXon (e y).1 (e y).2 i' default, finite_symm_coe e y (e y).2]
    rw [Finset.sum_congr rfl fun i' _ => hin i']
  rw [hre, hYon (e x).1 hk i default, hex] at h
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.transpose_apply, finite_Rres_apply, Matrix.mul_apply, mul_comm]

theorem finite_stratumCol_coupling {n : ℕ} (s : Blk) {γ : Fin 4} (e : Fin n ≃ Fib (finite_strHn n) γ)
    (M : Matrix (finite_BIdx n s) (Fin n) K)
    (X Y : PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n))
    (hXon : ∀ (k : Fin (finite_thn n)) (h : finite_strHn n k = γ) (u : finite_BIdx n Blk.anch) (j : finite_BIdx n s),
      X k Blk.anch s u j = M j (e.symm ⟨k, h⟩))
    (hXoff : ∀ k, finite_strHn n k ≠ γ → X k Blk.anch s = 0)
    (hYon : ∀ (k : Fin (finite_thn n)) (h : finite_strHn n k = γ) (u : finite_BIdx n Blk.anch) (j : finite_BIdx n s),
      Y k Blk.anch s u j = M j (e.symm ⟨k, h⟩))
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (hPa : P Blk.anch = 1)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    Q s * M * (finite_Rres e R)ᵀ = M := by
  classical
  ext j x
  have hk : finite_strHn n (e x).1 = γ := (e x).2
  have hex : e.symm ⟨(e x).1, hk⟩ = x := finite_symm_coe e x hk
  have h := congrFun (congrFun (heq (e x).1 Blk.anch s) (default : finite_BIdx n Blk.anch)) j
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (finite_thn n),
      (R (e x).1 k' • (P Blk.anch * X k' Blk.anch s * (Q s)ᵀ))
          (default : finite_BIdx n Blk.anch) j
        = R (e x).1 k' * ∑ j', Q s j j' * X k' Blk.anch s (default : finite_BIdx n Blk.anch) j' := by
    intro k'
    rw [hPa, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Matrix.transpose_apply, mul_comm]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (finite_thn n), finite_strHn n k' ≠ γ →
      R (e x).1 k' * ∑ j', Q s j j' * X k' Blk.anch s (default : finite_BIdx n Blk.anch) j' = 0 := by
    intro k' hk'
    rw [hXoff k' hk']
    simp
  rw [sum_fibre (finite_strHn n) γ _ hzero] at h
  have hre : (∑ c : Fib (finite_strHn n) γ,
        R (e x).1 c.1 * ∑ j', Q s j j' * X c.1 Blk.anch s (default : finite_BIdx n Blk.anch) j')
      = ∑ y : Fin n, R (e x).1 (e y).1 * ∑ j', Q s j j' * M j' y := by
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro y
    have hin : ∀ j' : finite_BIdx n s,
        Q s j j' * M j' y
          = Q s j j' * X (e y).1 Blk.anch s (default : finite_BIdx n Blk.anch) j' := by
      intro j'
      rw [hXon (e y).1 (e y).2 default j', finite_symm_coe e y (e y).2]
    rw [Finset.sum_congr rfl fun j' _ => hin j']
  rw [hre, hYon (e x).1 hk default j, hex] at h
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.transpose_apply, finite_Rres_apply, Matrix.mul_apply, mul_comm]

end FiniteEncodingSetup
section ForwardTransport

open Matrix

universe u

variable {K : Type u} [Field K]

section Setup

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : Fin n ≃ Fib strH 0) (e1 : Fin n ≃ Fib strH 1) (e2 : Fin n ≃ Fib strH 2)

noncomputable abbrev finite_invT (g : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := g⁻¹ᵀ

theorem finite_isUnit_det_invT {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) : IsUnit (finite_invT g).det := by
  rw [finite_invT, Matrix.det_transpose]
  exact Matrix.isUnit_nonsing_inv_det g h

theorem finite_mul_invT_transpose {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) :
    g * (finite_invT g)ᵀ = 1 := by
  rw [finite_invT, Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv g h

theorem finite_invT_mul_transpose {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) :
    finite_invT g * gᵀ = 1 := by
  rw [finite_invT, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv g h, Matrix.transpose_one]

noncomputable def finite_Pfwd (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K
  | Blk.dat => g₁
  | Blk.cop => g₂
  | Blk.mid => finite_invT g₃
  | Blk.anch => 1

noncomputable def finite_Qfwd (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    ∀ s : Blk, Matrix (finite_BIdx n s) (finite_BIdx n s) K
  | Blk.dat => g₂
  | Blk.cop => g₃
  | Blk.mid => finite_invT g₁
  | Blk.anch => 1

theorem finite_Pfwd_isUnit (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ b, IsUnit (finite_Pfwd g₁ g₂ g₃ b).det
  | Blk.dat => h₁
  | Blk.cop => h₂
  | Blk.mid => finite_isUnit_det_invT h₃
  | Blk.anch => by simp [finite_Pfwd]

theorem finite_Qfwd_isUnit (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ s, IsUnit (finite_Qfwd g₁ g₂ g₃ s).det
  | Blk.dat => h₂
  | Blk.cop => h₃
  | Blk.mid => finite_isUnit_det_invT h₁
  | Blk.anch => by simp [finite_Qfwd]

noncomputable def finite_Rst (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K
  | 0 => Matrix.reindex e0 e0 g₃
  | 1 => Matrix.reindex e1 e1 g₁
  | 2 => Matrix.reindex e2 e2 (finite_invT g₂)
  | 3 => 1

theorem finite_Rst_zero (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    finite_Rst strH e0 e1 e2 g₁ g₂ g₃ 0 = Matrix.reindex e0 e0 g₃ := rfl
theorem finite_Rst_one (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    finite_Rst strH e0 e1 e2 g₁ g₂ g₃ 1 = Matrix.reindex e1 e1 g₁ := rfl
theorem finite_Rst_two (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    finite_Rst strH e0 e1 e2 g₁ g₂ g₃ 2 = Matrix.reindex e2 e2 (finite_invT g₂) := rfl
theorem finite_Rst_three (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    finite_Rst strH e0 e1 e2 g₁ g₂ g₃ 3 = 1 := rfl

noncomputable def finite_Rfwd (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) : Matrix (Fin th) (Fin th) K :=
  assemble strH (finite_Rst strH e0 e1 e2 g₁ g₂ g₃)

theorem finite_Rfwd_isBlockDiag (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) :
    IsBlockDiag strH (finite_Rfwd strH e0 e1 e2 g₁ g₂ g₃) :=
  isBlockDiag_assemble strH _

theorem finite_Rfwd_isUnit (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : IsUnit (finite_Rfwd strH e0 e1 e2 g₁ g₂ g₃).det := by
  rw [finite_Rfwd, isUnit_det_assemble_iff]
  intro g
  match g with
  | 0 => rw [finite_Rst_zero, Matrix.det_reindex_self]; exact h₃
  | 1 => rw [finite_Rst_one, Matrix.det_reindex_self]; exact h₁
  | 2 => rw [finite_Rst_two, Matrix.det_reindex_self]; exact finite_isUnit_det_invT h₂
  | 3 => rw [finite_Rst_three]; simp

end Setup

section Sums

variable {n th : ℕ} (strH : Fin th → Fin 4)

theorem finite_sum_assemble_smul {I J : Type} [Fintype I] [Fintype J]
    (finite_Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (M : Fin th → Matrix I J K) (g₀ : Fin 4) (hM : ∀ k', strH k' ≠ g₀ → M k' = 0) (k : Fin th) :
    ∑ k', assemble strH finite_Rst k k' • M k' =
      if h : strH k = g₀ then ∑ k' : Fib strH g₀, finite_Rst g₀ ⟨k, h⟩ k' • M k'.1 else 0 := by
  classical
  split_ifs with h
  · rw [← Finset.sum_filter_of_ne (p := fun k' => strH k' = g₀) (s := Finset.univ)
      (f := fun k' => assemble strH finite_Rst k k' • M k')]
    · rw [Finset.sum_subtype (Finset.univ.filter fun k' => strH k' = g₀)
        (p := fun k' => strH k' = g₀) (by simp)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [assemble_apply_of_eq strH finite_Rst (h.trans a.2.symm) g₀ h]
    · intro k' _ hne
      by_contra hk'
      exact hne (by rw [hM k' hk', smul_zero])
  · refine Finset.sum_eq_zero fun k' _ => ?_
    by_cases hk' : strH k' = g₀
    · have : assemble strH finite_Rst k k' = 0 :=
        isBlockDiag_assemble strH finite_Rst k k' (by rw [hk']; exact h)
      rw [this, zero_smul]
    · rw [hM k' hk', smul_zero]

theorem finite_sum_fib_reindex {I J : Type} [Fintype I] [Fintype J] {g₀ : Fin 4} (e : Fin n ≃ Fib strH g₀)
    (F : Fib strH g₀ → Matrix I J K) : ∑ k' : Fib strH g₀, F k' = ∑ m : Fin n, F (e m) :=
  (Equiv.sum_comp e F).symm

theorem finite_reindex_apply_symm {g₀ : Fin 4} (e : Fin n ≃ Fib strH g₀) (G : Matrix (Fin n) (Fin n) K)
    (a : Fib strH g₀) (m : Fin n) : Matrix.reindex e e G a (e m) = G (e.symm a) m := by
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

end Sums

section Slices

variable {n : ℕ}

def finite_slice (A : Fin n × Fin n × Fin n → K) (m : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => A (i, j, m)

theorem finite_slice_apply (A : Fin n × Fin n × Fin n → K) (m i j : Fin n) : finite_slice A m i j = A (i, j, m) := rfl

theorem finite_sum3_rotate_forward (f : Fin n → Fin n → Fin n → K) :
    ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ k', ∑ j', ∑ i', f i' j' k' :=
  calc ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ j', ∑ i', ∑ k', f i' j' k' := Finset.sum_comm
    _ = ∑ j', ∑ k', ∑ i', f i' j' k' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k', ∑ j', ∑ i', f i' j' k' := Finset.sum_comm

theorem finite_act3D_slice (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K) (k : Fin n) :
    finite_slice (act3 K g₁ g₂ g₃ A) k = ∑ m, g₃ k m • (g₁ * finite_slice A m * g₂ᵀ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [finite_slice_apply, act3D, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine (finite_sum3_rotate_forward (fun i' j' k' => g₁ i i' * g₂ j j' * g₃ k k' * A (i', j', k'))).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun i' _ => ?_
  ring

end Slices

end ForwardTransport
section IdentityVectors
universe u
variable {K : Type u} [Field K] {n : ℕ}
variable (K)
def finite_colE {J : Type} (m : Fin n) : Matrix (Fin n) J K := Matrix.of fun i _ => if i = m then 1 else 0

def finite_rowE {I : Type} (m : Fin n) : Matrix I (Fin n) K := Matrix.of fun _ j => if j = m then 1 else 0

variable {K} {I J : Type}
theorem finite_mul_colE (g : Matrix (Fin n) (Fin n) K) (m : Fin n) :
    g * finite_colE K (J := J) m = Matrix.of fun i _ => g i m := by
  ext i u
  rw [Matrix.mul_apply]
  simp [finite_colE]

theorem finite_rowE_mul (g : Matrix (Fin n) (Fin n) K) (m : Fin n) :
    finite_rowE K (I := I) m * g = Matrix.of fun _ j => g m j := by
  ext u j
  rw [Matrix.mul_apply]
  simp [finite_rowE]

theorem finite_mul_inv_entry {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) (x i : Fin n) :
    ∑ m, g x m * g⁻¹ m i = if x = i then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mul_nonsing_inv g h) x) i
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem finite_colE_transport {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) (x : Fin n) :
    ∑ m, g x m • (finite_invT g * finite_colE K (J := J) m) = finite_colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [finite_mul_colE, Matrix.of_apply, finite_invT, Matrix.transpose_apply]
  rw [finite_mul_inv_entry h, finite_colE, Matrix.of_apply]
  by_cases hx : i = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem finite_colE_transport_inv {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) (x : Fin n) :
    ∑ m, finite_invT g x m • (g * finite_colE K (J := J) m) = finite_colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [finite_mul_colE, Matrix.of_apply, finite_invT, Matrix.transpose_apply]
  rw [finite_colE, Matrix.of_apply, ← finite_mul_inv_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem finite_rowE_transport {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) (x : Fin n) :
    ∑ m, g x m • (finite_rowE K (I := I) m * (finite_invT g)ᵀ) = finite_rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [finite_invT, Matrix.transpose_transpose, finite_rowE_mul, Matrix.of_apply]
  rw [finite_mul_inv_entry h, finite_rowE, Matrix.of_apply]
  by_cases hx : j = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem finite_rowE_transport_inv {g : Matrix (Fin n) (Fin n) K} (h : IsUnit g.det) (x : Fin n) :
    ∑ m, finite_invT g x m • (finite_rowE K (I := I) m * gᵀ) = finite_rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [finite_rowE_mul, Matrix.of_apply, finite_invT, Matrix.transpose_apply]
  rw [finite_rowE, Matrix.of_apply, ← finite_mul_inv_entry h j x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

end IdentityVectors
section FormVectors
universe u
variable {K : Type u} [Field K]
section Vectors

variable {n : ℕ}

variable (K)

def finite_colF {J : Type} (Ψ : Matrix (Fin n) (Fin n) K) (m : Fin n) : Matrix (Fin n) J K :=
  Matrix.of fun i _ => Ψ i m

def finite_rowF {I : Type} (Ψ : Matrix (Fin n) (Fin n) K) (m : Fin n) : Matrix I (Fin n) K :=
  Matrix.of fun _ j => Ψ j m

variable {K} {I J : Type}

theorem finite_mul_colF_entry (Ψ g : Matrix (Fin n) (Fin n) K) (m i : Fin n) (u : J) :
    (g * finite_colF K (J := J) Ψ m) i u = ∑ i', g i i' * Ψ i' m := by
  rw [Matrix.mul_apply]
  simp [finite_colF]

theorem finite_rowF_mul_entry (Ψ g : Matrix (Fin n) (Fin n) K) (m j : Fin n) (u : I) :
    (finite_rowF K (I := I) Ψ m * gᵀ) u j = ∑ j', Ψ j' m * g j j' := by
  rw [Matrix.mul_apply]
  simp [finite_rowF]

theorem finite_covF_entry {Ψ g : Matrix (Fin n) (Fin n) K} (h : g * Ψ * gᵀ = Ψ) (i x : Fin n) :
    ∑ m, (∑ i', g i i' * Ψ i' m) * g x m = Ψ i x := by
  have hx := congrFun (congrFun h i) x
  rw [Matrix.mul_apply] at hx
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hx
  exact hx

theorem finite_colF_transport {Ψ g : Matrix (Fin n) (Fin n) K} (h : g * Ψ * gᵀ = Ψ) (x : Fin n) :
    ∑ m, g x m • (g * finite_colF K (J := J) Ψ m) = finite_colF K Ψ x := by
  ext i u
  rw [sum_smul_entry]
  simp only [finite_mul_colF_entry]
  simp only [finite_colF, Matrix.of_apply]
  rw [← finite_covF_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem finite_rowF_transport {Ψ g : Matrix (Fin n) (Fin n) K} (h : g * Ψ * gᵀ = Ψ) (x : Fin n) :
    ∑ m, g x m • (finite_rowF K (I := I) Ψ m * gᵀ) = finite_rowF K Ψ x := by
  ext u j
  rw [sum_smul_entry]
  simp only [finite_rowF_mul_entry]
  simp only [finite_rowF, Matrix.of_apply]
  rw [← finite_covF_entry h j x]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm (g x m)]
  congr 1
  exact Finset.sum_congr rfl fun j' _ => mul_comm _ _

end Vectors
section AnchorNorm

variable {n : ℕ}

theorem finite_anchor_scalar_prod_gen (X Y : PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n))
    (hXon : X (finite_k3 n) Blk.anch Blk.anch = 1)
    (hXoff : ∀ k, finite_strHn n k ≠ 3 → X k Blk.anch Blk.anch = 0)
    (hYon : Y (finite_k3 n) Blk.anch Blk.anch () () = 1)
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (heq : ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) :
    R (finite_k3 n) (finite_k3 n) * (P Blk.anch () ()) * (Q Blk.anch () ()) = 1 := by
  classical
  have hsum : (∑ k', R (finite_k3 n) k' • (P Blk.anch * X k' Blk.anch Blk.anch * (Q Blk.anch)ᵀ))
      = R (finite_k3 n) (finite_k3 n) • (P Blk.anch * (Q Blk.anch)ᵀ) := by
    rw [Finset.sum_eq_single (finite_k3 n)]
    · rw [hXon, Matrix.mul_one]
    · intro k' _ hk'
      have hs : finite_strHn n k' ≠ 3 := fun hc => hk' (finite_eq_k3 n hc)
      rw [hXoff k' hs]
      simp
    · intro hnot
      exact absurd (Finset.mem_univ (finite_k3 n)) hnot
  have h := congrFun (congrFun (heq (finite_k3 n) Blk.anch Blk.anch) ()) ()
  rw [hYon, hsum] at h
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.univ_unique, Finset.sum_singleton, smul_eq_mul] at h
  rw [← mul_assoc] at h
  exact h.symm

theorem finite_anchor_normalization_gen (X Y : PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n))
    (hXon : X (finite_k3 n) Blk.anch Blk.anch = 1)
    (hXoff : ∀ k, finite_strHn n k ≠ 3 → X k Blk.anch Blk.anch = 0)
    (hYon : Y (finite_k3 n) Blk.anch Blk.anch () () = 1)
    (h : BlockEquiv (finite_strHn n) X Y) :
    ∃ (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
      (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K),
      P Blk.anch = 1 ∧ Q Blk.anch = 1 ∧ R (finite_k3 n) (finite_k3 n) = 1 ∧
      (∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)) := by
  classical
  obtain ⟨P, Q, R, hP, hQ, hR, hBD, heq⟩ := h
  have hprod : R (finite_k3 n) (finite_k3 n) * (P Blk.anch () ()) * (Q Blk.anch () ()) = 1 :=
    finite_anchor_scalar_prod_gen X Y hXon hXoff hYon P Q R heq
  have hα : P Blk.anch () () ≠ 0 := unit_entry_ne_zero (hP Blk.anch)
  have hβ : Q Blk.anch () () ≠ 0 := unit_entry_ne_zero (hQ Blk.anch)
  have hγ : R (finite_k3 n) (finite_k3 n) ≠ 0 := by
    intro hc
    rw [hc] at hprod
    simp at hprod
  have hinv : (R (finite_k3 n) (finite_k3 n))⁻¹ * (P Blk.anch () ())⁻¹ * (Q Blk.anch () ())⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, hprod, inv_one]
  have hscal : (R (finite_k3 n) (finite_k3 n))⁻¹ * ((P Blk.anch () ())⁻¹ * (Q Blk.anch () ())⁻¹) = 1 := by
    rw [← mul_assoc]
    exact hinv
  refine ⟨fun b => (P Blk.anch () ())⁻¹ • P b,
    fun s => (Q Blk.anch () ())⁻¹ • Q s,
    (R (finite_k3 n) (finite_k3 n))⁻¹ • R, ?_, ?_, ?_, ?_⟩
  · exact unit_matrix_ext (by simp [inv_mul_cancel₀ hα, Matrix.one_apply])
  · exact unit_matrix_ext (by simp [inv_mul_cancel₀ hβ, Matrix.one_apply])
  · simp [inv_mul_cancel₀ hγ]
  · intro k b s
    rw [heq k b s]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [scaled_block, Matrix.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    linear_combination (-(R k k')) * hscal

end AnchorNorm
end FormVectors
section FiniteSteps
universe u
variable {K : Type u} [Field K] {n th : ℕ} (strH : Fin th → Fin 4)
theorem finite_block_step {I I' J J' : Type} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (finite_Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (P : Matrix I I' K) (Q : Matrix J J' K) (N : Fin th → Matrix I' J' K) (g₀ : Fin 4)
    (hN : ∀ k', strH k' ≠ g₀ → N k' = 0) (e : Fin n ≃ Fib strH g₀) (G : Matrix (Fin n) (Fin n) K)
    (hG : finite_Rst g₀ = Matrix.reindex e e G) (Nx : Fin n → Matrix I' J' K)
    (hNx : ∀ m, N (e m).1 = Nx m) (k : Fin th) :
    ∑ k', assemble strH finite_Rst k k' • (P * N k' * Qᵀ) =
      if h : strH k = g₀ then ∑ m, G (e.symm ⟨k, h⟩) m • (P * Nx m * Qᵀ) else 0 := by
  refine (finite_sum_assemble_smul strH finite_Rst (fun k' => P * N k' * Qᵀ) g₀
    (fun k' hk' => by simp [hN k' hk']) k).trans ?_
  by_cases h : strH k = g₀
  · rw [dif_pos h, dif_pos h, finite_sum_fib_reindex strH e]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hG, finite_reindex_apply_symm, hNx]
  · rw [dif_neg h, dif_neg h]

end FiniteSteps

section DegenerateFormEncoding
universe u
variable {K : Type u} [Field K]
noncomputable def dual_HgadgetF (n : ℕ) (Ψ : Matrix (Fin n) (Fin n) K) {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : Fin n ≃ Fib strH 0) (e1 : Fin n ≃ Fib strH 1) (e2 : Fin n ≃ Fib strH 2)
    (A : Fin n × Fin n × Fin n → K) :
    PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) th :=
  fun k b s =>
    match b, s with
    | Blk.dat, Blk.dat => 0
    | Blk.dat, Blk.cop => 0
    | Blk.dat, Blk.mid => Matrix.of fun (i : Fin n) (j : Fin n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.dat, Blk.anch => Matrix.of fun (i : Fin n) (_ : Unit) =>
        if h : strH k = 1 then Ψ i (e1.symm ⟨k, h⟩) else 0
    | Blk.cop, Blk.dat => Matrix.of fun (i : Fin n) (j : Fin n) =>
        if strH k = 3 then Ψ i j else 0
    | Blk.cop, Blk.cop => 0
    | Blk.cop, Blk.mid => 0
    | Blk.cop, Blk.anch => Matrix.of fun (i : Fin n) (_ : Unit) =>
        if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.mid, Blk.dat => 0
    | Blk.mid, Blk.cop => Matrix.of fun (i : Fin n) (j : Fin n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.mid, Blk.mid => Matrix.of fun (i : Fin n) (j : Fin n) =>
        if h : strH k = 2 then A (i, j, (e2.symm ⟨k, h⟩ : Fin n)) else 0
    | Blk.mid, Blk.anch => Matrix.of fun (i : Fin n) (_ : Unit) =>
        if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.dat => Matrix.of fun (_ : Unit) (j : Fin n) =>
        if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.cop => Matrix.of fun (_ : Unit) (j : Fin n) =>
        if h : strH k = 0 then Ψ j (e0.symm ⟨k, h⟩) else 0
    | Blk.anch, Blk.mid => Matrix.of fun (_ : Unit) (j : Fin n) =>
        if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.anch => Matrix.of fun (_ : Unit) (_ : Unit) =>
        if strH k = 3 then (1 : K) else 0

section Entries

variable (n : ℕ) (Ψ : Matrix (Fin n) (Fin n) K) {th : ℕ} (strH : Fin th → Fin 4)
  (e0 : Fin n ≃ Fib strH 0) (e1 : Fin n ≃ Fib strH 1) (e2 : Fin n ≃ Fib strH 2)
  (A : Fin n × Fin n × Fin n → K) (k : Fin th)

theorem dual_HgadgetF_dat_mid (i : finite_BIdx n Blk.dat) (j : finite_BIdx n Blk.mid) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.mid i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_dat_anch (i : finite_BIdx n Blk.dat) (j : finite_BIdx n Blk.anch) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.dat Blk.anch i j
      = if h : strH k = 1 then Ψ i (e1.symm ⟨k, h⟩) else 0 := rfl

theorem dual_HgadgetF_cop_dat (i : finite_BIdx n Blk.cop) (j : finite_BIdx n Blk.dat) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.dat i j
      = if strH k = 3 then Ψ i j else 0 := rfl

theorem dual_HgadgetF_cop_anch (i : finite_BIdx n Blk.cop) (j : finite_BIdx n Blk.anch) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.cop Blk.anch i j
      = if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_mid_cop (i : finite_BIdx n Blk.mid) (j : finite_BIdx n Blk.cop) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.cop i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_mid_mid (i : finite_BIdx n Blk.mid) (j : finite_BIdx n Blk.mid) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.mid i j =
      if h : strH k = 2 then A (i, j, (e2.symm ⟨k, h⟩ : Fin n)) else 0 := rfl

theorem dual_HgadgetF_mid_anch (i : finite_BIdx n Blk.mid) (j : finite_BIdx n Blk.anch) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.mid Blk.anch i j
      = if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_anch_dat (i : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.dat) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.dat i j
      = if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_anch_cop (i : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.cop) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.cop i j
      = if h : strH k = 0 then Ψ j (e0.symm ⟨k, h⟩) else 0 := rfl

theorem dual_HgadgetF_anch_mid (i : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.mid) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.mid i j
      = if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem dual_HgadgetF_anch_anch (i : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.anch) :
    dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A k Blk.anch Blk.anch i j
      = if strH k = 3 then (1 : K) else 0 := rfl

end Entries

noncomputable def dual_HF (n : ℕ) (Ψ : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K) :
    PArr K Blk Blk (finite_BIdx n) (finite_BIdx n) (finite_thn n) :=
  dual_HgadgetF n Ψ (finite_strHn n) (finite_e0n n) (finite_e1n n) (finite_e2n n) A

section Blocks

variable {n th : ℕ} (Ψ : Matrix (Fin n) (Fin n) K) (strH : Fin th → Fin 4)
  (e0 : Fin n ≃ Fib strH 0) (e1 : Fin n ≃ Fib strH 1) (e2 : Fin n ≃ Fib strH 2)
  (A : Fin n × Fin n × Fin n → K) (k : Fin th)

local notation "HgF" => dual_HgadgetF (K := K) n Ψ strH e0 e1 e2

theorem dual_HmatF_dat_dat : HgF A k Blk.dat Blk.dat = 0 := rfl

theorem dual_HmatF_dat_cop : HgF A k Blk.dat Blk.cop = 0 := rfl

theorem dual_HmatF_dat_mid :
    HgF A k Blk.dat Blk.mid = if strH k = 3 then (1 : Matrix (Fin n) (Fin n) K) else 0 := by
  ext i j; rw [dual_HgadgetF_dat_mid]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all

theorem dual_HmatF_dat_anch :
    HgF A k Blk.dat Blk.anch = if h : strH k = 1 then finite_colF K Ψ (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_dat_anch]; by_cases h : strH k = 1 <;> simp [h, finite_colF]

theorem dual_HmatF_cop_dat :
    HgF A k Blk.cop Blk.dat = if strH k = 3 then Ψ else 0 := by
  ext i j; rw [dual_HgadgetF_cop_dat]; by_cases h : strH k = 3 <;> simp [h]

theorem dual_HmatF_cop_cop : HgF A k Blk.cop Blk.cop = 0 := rfl

theorem dual_HmatF_cop_mid : HgF A k Blk.cop Blk.mid = 0 := rfl

theorem dual_HmatF_cop_anch :
    HgF A k Blk.cop Blk.anch = if h : strH k = 2 then finite_colE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_cop_anch]; by_cases h : strH k = 2 <;> simp [h, finite_colE]

theorem dual_HmatF_mid_dat : HgF A k Blk.mid Blk.dat = 0 := rfl

theorem dual_HmatF_mid_cop :
    HgF A k Blk.mid Blk.cop = if strH k = 3 then (1 : Matrix (Fin n) (Fin n) K) else 0 := by
  ext i j; rw [dual_HgadgetF_mid_cop]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all

theorem dual_HmatF_mid_mid :
    HgF A k Blk.mid Blk.mid = if h : strH k = 2 then finite_slice A (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_mid_mid]; by_cases h : strH k = 2 <;> simp [h, finite_slice]

theorem dual_HmatF_mid_anch :
    HgF A k Blk.mid Blk.anch = if h : strH k = 0 then finite_colE K (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_mid_anch]; by_cases h : strH k = 0 <;> simp [h, finite_colE]

theorem dual_HmatF_anch_dat :
    HgF A k Blk.anch Blk.dat = if h : strH k = 2 then finite_rowE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_anch_dat]; by_cases h : strH k = 2 <;> simp [h, finite_rowE]

theorem dual_HmatF_anch_cop :
    HgF A k Blk.anch Blk.cop = if h : strH k = 0 then finite_rowF K Ψ (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_anch_cop]; by_cases h : strH k = 0 <;> simp [h, finite_rowF]

theorem dual_HmatF_anch_mid :
    HgF A k Blk.anch Blk.mid = if h : strH k = 1 then finite_rowE K (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [dual_HgadgetF_anch_mid]; by_cases h : strH k = 1 <;> simp [h, finite_rowE]

theorem dual_HmatF_anch_anch :
    HgF A k Blk.anch Blk.anch = if strH k = 3 then (1 : Matrix Unit Unit K) else 0 := by
  ext i j; rw [dual_HgadgetF_anch_anch]; by_cases h : strH k = 3 <;> simp [h, Matrix.one_apply]

end Blocks

section Forward

variable {n th : ℕ} (Ψ : Matrix (Fin n) (Fin n) K) (strH : Fin th → Fin 4)
  (e0 : Fin n ≃ Fib strH 0) (e1 : Fin n ≃ Fib strH 1) (e2 : Fin n ≃ Fib strH 2)

theorem dual_blockEquiv_of_form (g₁ g₂ g₃ : Matrix (Fin n) (Fin n) K)
    (hu₁ : IsUnit g₁.det) (hu₂ : IsUnit g₂.det) (hu₃ : IsUnit g₃.det)
    (hc₁ : g₁ * Ψ * g₁ᵀ = Ψ) (hc₂ : g₂ * Ψ * g₂ᵀ = Ψ) (hc₃ : g₃ * Ψ * g₃ᵀ = Ψ)
    (A B : Fin n × Fin n × Fin n → K) (hAB : act3 K (finite_invT g₃) (finite_invT g₁) (finite_invT g₂) A = B) :
    BlockEquiv strH (dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 A)
      (dual_HgadgetF (K := K) n Ψ strH e0 e1 e2 B) := by
  subst hAB
  refine ⟨finite_Pfwd g₁ g₂ g₃, finite_Qfwd g₁ g₂ g₃, finite_Rfwd strH e0 e1 e2 g₁ g₂ g₃,
    finite_Pfwd_isUnit g₁ g₂ g₃ hu₁ hu₂ hu₃, finite_Qfwd_isUnit g₁ g₂ g₃ hu₁ hu₂ hu₃,
    finite_Rfwd_isUnit strH e0 e1 e2 g₁ g₂ g₃ hu₁ hu₂ hu₃, finite_Rfwd_isBlockDiag strH e0 e1 e2 g₁ g₂ g₃,
    fun k b s => ?_⟩
  have hR0 := finite_Rst_zero strH e0 e1 e2 g₁ g₂ g₃
  have hR1 := finite_Rst_one strH e0 e1 e2 g₁ g₂ g₃
  have hR2 := finite_Rst_two strH e0 e1 e2 g₁ g₂ g₃
  have hR3 := finite_Rst_three strH e0 e1 e2 g₁ g₂ g₃
  cases b <;> cases s
  
  · simp [dual_HmatF_dat_dat]

  · simp [dual_HmatF_dat_cop]
  
  · simp only [dual_HmatF_dat_mid, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, block_step3 strH _ g₁ (finite_invT g₁)
      (fun k' => if strH k' = 3 then (1 : Matrix (Fin n) (Fin n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, finite_mul_invT_transpose hu₁]
    · rw [if_neg h, if_neg h]
  
  · simp only [dual_HmatF_dat_anch, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ g₁ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 1 then finite_colF K Ψ (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => finite_colF K Ψ m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (finite_colF_transport hc₁ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp only [dual_HmatF_cop_dat, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, block_step3 strH _ g₂ g₂ (fun k' => if strH k' = 3 then Ψ else 0) Ψ
      (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]
      exact hc₂.symm
    · rw [if_neg h, if_neg h]
  
  · simp [dual_HmatF_cop_cop]
  
  · simp [dual_HmatF_cop_mid]
  
  · simp only [dual_HmatF_cop_anch, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ g₂ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 2 then finite_colE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (finite_invT g₂) hR2 (fun m => finite_colE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (finite_colE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp [dual_HmatF_mid_dat]
  
  · simp only [dual_HmatF_mid_cop, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, block_step3 strH _ (finite_invT g₃) g₃
      (fun k' => if strH k' = 3 then (1 : Matrix (Fin n) (Fin n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, finite_invT_mul_transpose hu₃]
    · rw [if_neg h, if_neg h]
  
  · simp only [dual_HmatF_mid_mid, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ (finite_invT g₃) (finite_invT g₁)
      (fun k' => if h : strH k' = 2 then finite_slice A (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (finite_invT g₂) hR2 (fun m => finite_slice A m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      exact finite_act3D_slice (finite_invT g₃) (finite_invT g₁) (finite_invT g₂) A _
    · rw [dif_neg h, dif_neg h]

  · simp only [dual_HmatF_mid_anch, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ (finite_invT g₃) (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 0 then finite_colE K (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => finite_colE K m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (finite_colE_transport hu₃ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp only [dual_HmatF_anch_dat, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ (1 : Matrix Unit Unit K) g₂
      (fun k' => if h : strH k' = 2 then finite_rowE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (finite_invT g₂) hR2 (fun m => finite_rowE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (finite_rowE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp only [dual_HmatF_anch_cop, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ (1 : Matrix Unit Unit K) g₃
      (fun k' => if h : strH k' = 0 then finite_rowF K Ψ (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => finite_rowF K Ψ m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (finite_rowF_transport hc₃ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp only [dual_HmatF_anch_mid, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, finite_block_step strH _ (1 : Matrix Unit Unit K) (finite_invT g₁)
      (fun k' => if h : strH k' = 1 then finite_rowE K (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => finite_rowE K m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (finite_rowE_transport hu₁ _).symm
    · rw [dif_neg h, dif_neg h]
  
  · simp only [dual_HmatF_anch_anch, finite_Pfwd, finite_Qfwd]
    rw [finite_Rfwd, block_step3 strH _ (1 : Matrix Unit Unit K) (1 : Matrix Unit Unit K)
      (fun k' => if strH k' = 3 then (1 : Matrix Unit Unit K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]

end Forward

section HFBlocks

variable {n : ℕ} (Ψ : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K)

theorem dual_HF_dat_mid_on : dual_HF (K := K) n Ψ A (finite_k3 n) Blk.dat Blk.mid = 1 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_dat_mid, if_pos (finite_strHn_k3 n), Matrix.one_apply]

theorem dual_HF_dat_mid_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 3) :
    dual_HF (K := K) n Ψ A k Blk.dat Blk.mid = 0 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_dat_mid, if_neg h]
  simp

theorem dual_HF_mid_cop_on : dual_HF (K := K) n Ψ A (finite_k3 n) Blk.mid Blk.cop = 1 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_mid_cop, if_pos (finite_strHn_k3 n), Matrix.one_apply]

theorem dual_HF_mid_cop_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 3) :
    dual_HF (K := K) n Ψ A k Blk.mid Blk.cop = 0 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_mid_cop, if_neg h]
  simp

theorem dual_HF_cop_dat_on : dual_HF (K := K) n Ψ A (finite_k3 n) Blk.cop Blk.dat = Ψ := by
  ext i j
  rw [dual_HF, dual_HgadgetF_cop_dat, if_pos (finite_strHn_k3 n)]

theorem dual_HF_cop_dat_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 3) :
    dual_HF (K := K) n Ψ A k Blk.cop Blk.dat = 0 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_cop_dat, if_neg h]
  simp

theorem dual_HF_dat_anch_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 1)
    (i : finite_BIdx n Blk.dat) (u : finite_BIdx n Blk.anch) :
    dual_HF (K := K) n Ψ A k Blk.dat Blk.anch i u = Ψ i ((finite_e1n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_dat_anch, dif_pos h]

theorem dual_HF_dat_anch_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 1) :
    dual_HF (K := K) n Ψ A k Blk.dat Blk.anch = 0 := by
  ext i u
  rw [dual_HF, dual_HgadgetF_dat_anch, dif_neg h]
  simp

theorem dual_HF_mid_anch_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 0)
    (i : finite_BIdx n Blk.mid) (u : finite_BIdx n Blk.anch) :
    dual_HF (K := K) n Ψ A k Blk.mid Blk.anch i u = (1 : Matrix (Fin n) (Fin n) K) i ((finite_e0n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_mid_anch, dif_pos h, Matrix.one_apply]

theorem dual_HF_mid_anch_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 0) :
    dual_HF (K := K) n Ψ A k Blk.mid Blk.anch = 0 := by
  ext i u
  rw [dual_HF, dual_HgadgetF_mid_anch, dif_neg h]
  simp

theorem dual_HF_cop_anch_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 2)
    (i : finite_BIdx n Blk.cop) (u : finite_BIdx n Blk.anch) :
    dual_HF (K := K) n Ψ A k Blk.cop Blk.anch i u = (1 : Matrix (Fin n) (Fin n) K) i ((finite_e2n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_cop_anch, dif_pos h, Matrix.one_apply]

theorem dual_HF_cop_anch_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 2) :
    dual_HF (K := K) n Ψ A k Blk.cop Blk.anch = 0 := by
  ext i u
  rw [dual_HF, dual_HgadgetF_cop_anch, dif_neg h]
  simp

theorem dual_HF_anch_cop_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 0)
    (u : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.cop) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.cop u j = Ψ j ((finite_e0n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_anch_cop, dif_pos h]

theorem dual_HF_anch_cop_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 0) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.cop = 0 := by
  ext u j
  rw [dual_HF, dual_HgadgetF_anch_cop, dif_neg h]
  simp

theorem dual_HF_anch_mid_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 1)
    (u : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.mid) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.mid u j = (1 : Matrix (Fin n) (Fin n) K) j ((finite_e1n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_anch_mid, dif_pos h, Matrix.one_apply]

theorem dual_HF_anch_mid_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 1) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.mid = 0 := by
  ext u j
  rw [dual_HF, dual_HgadgetF_anch_mid, dif_neg h]
  simp

theorem dual_HF_anch_dat_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 2)
    (u : finite_BIdx n Blk.anch) (j : finite_BIdx n Blk.dat) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.dat u j = (1 : Matrix (Fin n) (Fin n) K) j ((finite_e2n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_anch_dat, dif_pos h, Matrix.one_apply]

theorem dual_HF_anch_dat_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 2) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.dat = 0 := by
  ext u j
  rw [dual_HF, dual_HgadgetF_anch_dat, dif_neg h]
  simp

theorem dual_HF_anch_anch_entry : dual_HF (K := K) n Ψ A (finite_k3 n) Blk.anch Blk.anch () () = 1 := by
  rw [dual_HF, dual_HgadgetF_anch_anch, if_pos (finite_strHn_k3 n)]

theorem dual_HF_anch_anch_on : dual_HF (K := K) n Ψ A (finite_k3 n) Blk.anch Blk.anch = 1 :=
  unit_matrix_ext (by rw [dual_HF_anch_anch_entry]; simp [Matrix.one_apply])

theorem dual_HF_anch_anch_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 3) :
    dual_HF (K := K) n Ψ A k Blk.anch Blk.anch = 0 :=
  unit_matrix_ext (by rw [dual_HF, dual_HgadgetF_anch_anch, if_neg h]; simp)

theorem dual_HF_mid_mid_on (k : Fin (finite_thn n)) (h : finite_strHn n k = 2) (i j : finite_BIdx n Blk.mid) :
    dual_HF (K := K) n Ψ A k Blk.mid Blk.mid i j = A (i, j, (finite_e2n n).symm ⟨k, h⟩) := by
  rw [dual_HF, dual_HgadgetF_mid_mid, dif_pos h]

theorem dual_HF_mid_mid_off {k : Fin (finite_thn n)} (h : finite_strHn n k ≠ 2) :
    dual_HF (K := K) n Ψ A k Blk.mid Blk.mid = 0 := by
  ext i j
  rw [dual_HF, dual_HgadgetF_mid_mid, dif_neg h]
  simp

end HFBlocks

section Extraction
variable {n : ℕ}
theorem dual_covariant_units_of_normalised (Ψ : Matrix (Fin n) (Fin n) K) (A B : Fin n × Fin n × Fin n → K)
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (hPa : P Blk.anch = 1) (hQa : Q Blk.anch = 1) (hR1 : R (finite_k3 n) (finite_k3 n) = 1)
    (heq : ∀ k b s, dual_HF (K := K) n Ψ B k b s
      = ∑ k', R k k' • (P b * dual_HF (K := K) n Ψ A k' b s * (Q s)ᵀ)) :
    (P Blk.dat) * Ψ * (P Blk.dat)ᵀ = Ψ ∧ (Q Blk.dat) * Ψ * (Q Blk.dat)ᵀ = Ψ ∧
      (finite_Rres (finite_e0n n) R) * Ψ * (finite_Rres (finite_e0n n) R)ᵀ = Ψ ∧
      IsUnit (P Blk.dat).det ∧ IsUnit (Q Blk.dat).det ∧ IsUnit (finite_Rres (finite_e0n n) R).det := by
  
  have h11 : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.dat) (Q Blk.mid) :=
    finite_anchorSlice_coupling Blk.dat Blk.mid 1 (dual_HF n Ψ A) (dual_HF n Ψ B) (dual_HF_dat_mid_on Ψ A)
      (fun _ hk => dual_HF_dat_mid_off Ψ A hk) (dual_HF_dat_mid_on Ψ B) P Q R hR1 heq
  
  have h32 : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.mid) (Q Blk.cop) :=
    finite_anchorSlice_coupling Blk.mid Blk.cop 1 (dual_HF n Ψ A) (dual_HF n Ψ B) (dual_HF_mid_cop_on Ψ A)
      (fun _ hk => dual_HF_mid_cop_off Ψ A hk) (dual_HF_mid_cop_on Ψ B) P Q R hR1 heq
  
  have h23' : Coupling Ψ (P Blk.cop) (Q Blk.dat) :=
    finite_anchorSlice_coupling Blk.cop Blk.dat Ψ (dual_HF n Ψ A) (dual_HF n Ψ B) (dual_HF_cop_dat_on Ψ A)
      (fun _ hk => dual_HF_cop_dat_off Ψ A hk) (dual_HF_cop_dat_on Ψ B) P Q R hR1 heq
  
  have h13 : Coupling Ψ (P Blk.dat) (finite_Rres (finite_e1n n) R) :=
    finite_stratumRow_coupling Blk.dat (finite_e1n n) Ψ (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h i u => dual_HF_dat_anch_on Ψ A k h i u)
      (fun _ hk => dual_HF_dat_anch_off Ψ A hk)
      (fun k h i u => dual_HF_dat_anch_on Ψ B k h i u) P Q R hQa heq
  
  have h31' : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.mid) (finite_Rres (finite_e0n n) R) :=
    finite_stratumRow_coupling Blk.mid (finite_e0n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h i u => dual_HF_mid_anch_on Ψ A k h i u)
      (fun _ hk => dual_HF_mid_anch_off Ψ A hk)
      (fun k h i u => dual_HF_mid_anch_on Ψ B k h i u) P Q R hQa heq
  
  have h22' : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.cop) (finite_Rres (finite_e2n n) R) :=
    finite_stratumRow_coupling Blk.cop (finite_e2n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h i u => dual_HF_cop_anch_on Ψ A k h i u)
      (fun _ hk => dual_HF_cop_anch_off Ψ A hk)
      (fun k h i u => dual_HF_cop_anch_on Ψ B k h i u) P Q R hQa heq
  
  have h33' : Coupling Ψ (Q Blk.cop) (finite_Rres (finite_e0n n) R) :=
    finite_stratumCol_coupling Blk.cop (finite_e0n n) Ψ (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h u j => dual_HF_anch_cop_on Ψ A k h u j)
      (fun _ hk => dual_HF_anch_cop_off Ψ A hk)
      (fun k h u j => dual_HF_anch_cop_on Ψ B k h u j) P Q R hPa heq
  
  have h12 : Coupling (1 : Matrix (Fin n) (Fin n) K) (Q Blk.mid) (finite_Rres (finite_e1n n) R) :=
    finite_stratumCol_coupling Blk.mid (finite_e1n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h u j => dual_HF_anch_mid_on Ψ A k h u j)
      (fun _ hk => dual_HF_anch_mid_off Ψ A hk)
      (fun k h u j => dual_HF_anch_mid_on Ψ B k h u j) P Q R hPa heq
  
  have h21 : Coupling (1 : Matrix (Fin n) (Fin n) K) (Q Blk.dat) (finite_Rres (finite_e2n n) R) :=
    finite_stratumCol_coupling Blk.dat (finite_e2n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h u j => dual_HF_anch_dat_on Ψ A k h u j)
      (fun _ hk => dual_HF_anch_dat_off Ψ A hk)
      (fun k h u j => dual_HF_anch_dat_on Ψ B k h u j) P Q R hPa heq
  have hc₂ : Q Blk.dat = P Blk.cop :=
    coupling_one_chain h22' (coupling_one_symm h21)
  have hc₃ : finite_Rres (finite_e0n n) R = Q Blk.cop :=
    coupling_one_chain (coupling_one_symm h32) h31'
  refine ⟨chain_certifies_covariant h11 h12 h13, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hc₂] at h23'
    exact h23'
  · rw [← hc₃] at h33'
    exact h33'

  · exact Matrix.isUnit_det_of_right_inverse ((coupling_one_iff _ _).mp h11)
  · exact Matrix.isUnit_det_of_right_inverse ((coupling_one_iff _ _).mp h21)
  · exact Matrix.isUnit_det_of_right_inverse
      ((coupling_one_iff _ _).mp (coupling_one_symm h31'))

theorem dual_data_equationF (Ψ : Matrix (Fin n) (Fin n) K) (A B : Fin n × Fin n × Fin n → K)
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (heq : ∀ k b s, dual_HF (K := K) n Ψ B k b s
      = ∑ k', R k k' • (P b * dual_HF (K := K) n Ψ A k' b s * (Q s)ᵀ)) :
    act3 K (P Blk.mid) (Q Blk.mid) (finite_Rres (finite_e2n n) R) A = B := by
  classical
  funext p
  obtain ⟨i, j, x⟩ := p
  have hk : finite_strHn n (finite_e2n n x).1 = 2 := (finite_e2n n x).2
  have hex : (finite_e2n n).symm ⟨(finite_e2n n x).1, hk⟩ = x := finite_symm_coe (finite_e2n n) x hk
  have h := congrFun (congrFun (heq (finite_e2n n x).1 Blk.mid Blk.mid) i) j
  rw [Matrix.sum_apply] at h
  have hterm : ∀ k' : Fin (finite_thn n),
      (R (finite_e2n n x).1 k' • (P Blk.mid * dual_HF (K := K) n Ψ A k' Blk.mid Blk.mid * (Q Blk.mid)ᵀ)) i j
        = R (finite_e2n n x).1 k'
            * ∑ j', (∑ i', P Blk.mid i i' * dual_HF (K := K) n Ψ A k' Blk.mid Blk.mid i' j')
                * Q Blk.mid j j' := by
    intro k'
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Matrix.transpose_apply, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k' _ => hterm k'] at h
  have hzero : ∀ k' : Fin (finite_thn n), finite_strHn n k' ≠ 2 →
      R (finite_e2n n x).1 k'
          * ∑ j', (∑ i', P Blk.mid i i' * dual_HF (K := K) n Ψ A k' Blk.mid Blk.mid i' j')
              * Q Blk.mid j j' = 0 := by
    intro k' hk'
    rw [dual_HF_mid_mid_off Ψ A hk']
    simp
  rw [sum_fibre (finite_strHn n) 2 _ hzero] at h
  have hre : (∑ c : Fib (finite_strHn n) 2, R (finite_e2n n x).1 c.1
        * ∑ j', (∑ i', P Blk.mid i i' * dual_HF (K := K) n Ψ A c.1 Blk.mid Blk.mid i' j')
            * Q Blk.mid j j')
      = ∑ y : Fin n, R (finite_e2n n x).1 (finite_e2n n y).1
        * ∑ j', (∑ i', P Blk.mid i i' * A (i', j', y)) * Q Blk.mid j j' := by
    refine (Fintype.sum_equiv (finite_e2n n) _ _ ?_).symm
    intro y
    have hin : ∀ j' i' : finite_BIdx n Blk.mid,
        P Blk.mid i i' * A (i', j', y)
          = P Blk.mid i i' * dual_HF (K := K) n Ψ A (finite_e2n n y).1 Blk.mid Blk.mid i' j' := by
      intro j' i'
      rw [dual_HF_mid_mid_on Ψ A (finite_e2n n y).1 (finite_e2n n y).2 i' j', finite_symm_coe (finite_e2n n) y (finite_e2n n y).2]
    refine congrArg _ (Finset.sum_congr rfl fun j' _ => ?_)
    rw [Finset.sum_congr rfl fun i' _ => hin j' i']
  rw [hre, dual_HF_mid_mid_on Ψ B (finite_e2n n x).1 hk i j, hex] at h
  rw [h]
  show (∑ i', ∑ j', ∑ y, P Blk.mid i i' * Q Blk.mid j j'
        * finite_Rres (finite_e2n n) R x y * A (i', j', y))
      = ∑ y : Fin n, R (finite_e2n n x).1 (finite_e2n n y).1
          * ∑ j', (∑ i', P Blk.mid i i' * A (i', j', y)) * Q Blk.mid j j'
  rw [sum3_rotate]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [finite_Rres_apply]
  ring

end Extraction

end DegenerateFormEncoding

end GeneralFormEncoding

section DualityAndIsometries

open Matrix
set_option maxHeartbeats 800000
universe u
variable {K : Type u} [Field K]

section Duality
variable {I : Type} [Fintype I] [DecidableEq I]

theorem isometry_of_covariant_dual (Φ h g : Matrix I I K)
    (hc : Coupling 1 h g) (hf : g * Φ * gᵀ = Φ) : hᵀ * Φ * h = Φ := by
  have h1 := (coupling_one_iff h g).mp hc
  have h2 := (coupling_one_iff g h).mp (coupling_one_symm hc)
  calc hᵀ * Φ * h = hᵀ * (g * Φ * gᵀ) * h := by rw [hf]
    _ = (hᵀ * g) * Φ * (gᵀ * h) := by simp only [mul_assoc]
    _ = Φ := by rw [mul_eq_one_comm_sq h2, mul_eq_one_comm_sq h1, one_mul, mul_one]

theorem inverseTranspose_covariance (Φ g : Matrix I I K) (hu : IsUnit g.det)
    (h : gᵀ * Φ * g = Φ) : g⁻¹ᵀ * Φ * (g⁻¹ᵀ)ᵀ = Φ := by
  rw [Matrix.transpose_transpose]
  calc g⁻¹ᵀ * Φ * g⁻¹ = g⁻¹ᵀ * (gᵀ * Φ * g) * g⁻¹ := by rw [h]
    _ = (g⁻¹ᵀ * gᵀ) * Φ * (g * g⁻¹) := by simp only [mul_assoc]
    _ = Φ := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one, one_mul, mul_one]

def IsometryOrbit (Φ : Matrix I I K) (A B : I × I × I → K) : Prop :=
  ∃ g₁ g₂ g₃ : Matrix I I K,
    (IsUnit g₁.det ∧ g₁ᵀ * Φ * g₁ = Φ) ∧
    (IsUnit g₂.det ∧ g₂ᵀ * Φ * g₂ = Φ) ∧
    (IsUnit g₃.det ∧ g₃ᵀ * Φ * g₃ = Φ) ∧ act g₁ g₂ g₃ A = B

end Duality

section Encoding
variable {n : ℕ}

theorem finite_invT_involutive (g : Matrix (Fin n) (Fin n) K) (hu : IsUnit g.det) :
    finite_invT (finite_invT g) = g := by
  unfold finite_invT
  rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.transpose_transpose]

theorem dual_normalized_isometries (Ψ : Matrix (Fin n) (Fin n) K)
    (A B : Fin n × Fin n × Fin n → K)
    (P Q : ∀ b : Blk, Matrix (finite_BIdx n b) (finite_BIdx n b) K)
    (R : Matrix (Fin (finite_thn n)) (Fin (finite_thn n)) K)
    (hPa : P Blk.anch = 1) (hQa : Q Blk.anch = 1) (hR1 : R (finite_k3 n) (finite_k3 n) = 1)
    (heq : ∀ k b s, dual_HF n Ψ B k b s =
      ∑ k', R k k' • (P b * dual_HF n Ψ A k' b s * (Q s)ᵀ)) :
    (IsUnit (P Blk.mid).det ∧ (P Blk.mid)ᵀ * Ψ * P Blk.mid = Ψ) ∧
    (IsUnit (Q Blk.mid).det ∧ (Q Blk.mid)ᵀ * Ψ * Q Blk.mid = Ψ) ∧
    (IsUnit (finite_Rres (finite_e2n n) R).det ∧
      (finite_Rres (finite_e2n n) R)ᵀ * Ψ * finite_Rres (finite_e2n n) R = Ψ) := by
  obtain ⟨c₁,c₂,c₃,_,_,_⟩ := dual_covariant_units_of_normalised Ψ A B P Q R hPa hQa hR1 heq
  have h11 : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.dat) (Q Blk.mid) :=
    finite_anchorSlice_coupling Blk.dat Blk.mid 1 (dual_HF n Ψ A) (dual_HF n Ψ B) (dual_HF_dat_mid_on Ψ A)
      (fun _ hk => dual_HF_dat_mid_off Ψ A hk) (dual_HF_dat_mid_on Ψ B) P Q R hR1 heq
  
  have h31' : Coupling (1 : Matrix (Fin n) (Fin n) K) (P Blk.mid) (finite_Rres (finite_e0n n) R) :=
    finite_stratumRow_coupling Blk.mid (finite_e0n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h i u => dual_HF_mid_anch_on Ψ A k h i u)
      (fun _ hk => dual_HF_mid_anch_off Ψ A hk)
      (fun k h i u => dual_HF_mid_anch_on Ψ B k h i u) P Q R hQa heq
  
  have h21 : Coupling (1 : Matrix (Fin n) (Fin n) K) (Q Blk.dat) (finite_Rres (finite_e2n n) R) :=
    finite_stratumCol_coupling Blk.dat (finite_e2n n) 1 (dual_HF n Ψ A) (dual_HF n Ψ B)
      (fun k h u j => dual_HF_anch_dat_on Ψ A k h u j)
      (fun _ hk => dual_HF_anch_dat_off Ψ A hk)
      (fun k h u j => dual_HF_anch_dat_on Ψ B k h u j) P Q R hPa heq
  refine ⟨⟨?_, isometry_of_covariant_dual Ψ _ _ h31' c₃⟩,
    ⟨?_, isometry_of_covariant_dual Ψ _ _ (coupling_one_symm h11) c₁⟩,
    ⟨?_, isometry_of_covariant_dual Ψ _ _ (coupling_one_symm h21) c₂⟩⟩
  · exact Matrix.isUnit_det_of_right_inverse ((coupling_one_iff _ _).mp h31')
  · exact Matrix.isUnit_det_of_right_inverse ((coupling_one_iff _ _).mp (coupling_one_symm h11))
  · exact Matrix.isUnit_det_of_right_inverse ((coupling_one_iff _ _).mp (coupling_one_symm h21))

theorem arbitrary_isometry_encoding (Φ : Matrix (Fin n) (Fin n) K)
    (A B : Fin n × Fin n × Fin n → K) :
    IsometryOrbit Φ A B ↔ BlockEquiv (finite_strHn n) (dual_HF n Φ A) (dual_HF n Φ B) := by
  constructor
  · rintro ⟨g₁,g₂,g₃,h₁,h₂,h₃,h⟩
    apply dual_blockEquiv_of_form Φ (finite_strHn n) (finite_e0n n) (finite_e1n n) (finite_e2n n)
      (finite_invT g₂) (finite_invT g₃) (finite_invT g₁)
      (finite_isUnit_det_invT h₂.1) (finite_isUnit_det_invT h₃.1) (finite_isUnit_det_invT h₁.1)
      (inverseTranspose_covariance Φ g₂ h₂.1 h₂.2)
      (inverseTranspose_covariance Φ g₃ h₃.1 h₃.2)
      (inverseTranspose_covariance Φ g₁ h₁.1 h₁.2)
    simpa only [finite_invT_involutive _ h₁.1, finite_invT_involutive _ h₂.1,
      finite_invT_involutive _ h₃.1, act3_eq_act] using h
  · intro h
    obtain ⟨P,Q,R,hPa,hQa,hR,heq⟩ := finite_anchor_normalization_gen (dual_HF n Φ A) (dual_HF n Φ B)
      (dual_HF_anch_anch_on Φ A) (fun _ hk => dual_HF_anch_anch_off Φ A hk)
      (dual_HF_anch_anch_entry Φ B) h
    obtain ⟨h₁,h₂,h₃⟩ := dual_normalized_isometries Φ A B P Q R hPa hQa hR heq
    exact ⟨_,_,_,h₁,h₂,h₃,dual_data_equationF Φ A B P Q R heq⟩

end Encoding

end DualityAndIsometries

section UniversalUpperReduction

open Matrix
set_option maxHeartbeats 800000
universe u
variable {K : Type u} [Field K]

section Reindexing
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem IsometryOrbit_reindex_forward (e : I ≃ J) (Φ : Matrix I I K) (A B : I × I × I → K)
    (h : IsometryOrbit Φ A B) :
    IsometryOrbit (Matrix.reindex e e Φ) (reindex3 e e e A) (reindex3 e e e B) := by
  obtain ⟨g₁,g₂,g₃,h₁,h₂,h₃,h⟩ := h
  refine ⟨Matrix.reindex e e g₁, Matrix.reindex e e g₂, Matrix.reindex e e g₃,
    ⟨?_, (isometry_reindex e Φ g₁).mpr h₁.2⟩, ⟨?_, (isometry_reindex e Φ g₂).mpr h₂.2⟩,
    ⟨?_, (isometry_reindex e Φ g₃).mpr h₃.2⟩, ?_⟩
  · rw [Matrix.det_reindex_self]; exact h₁.1
  · rw [Matrix.det_reindex_self]; exact h₂.1
  · rw [Matrix.det_reindex_self]; exact h₃.1
  · rw [act_reindex3, h]

theorem IsometryOrbit_reindex (e : I ≃ J) (Φ : Matrix I I K) (A B : I × I × I → K) :
    IsometryOrbit Φ A B ↔
      IsometryOrbit (Matrix.reindex e e Φ) (reindex3 e e e A) (reindex3 e e e B) := by
  refine ⟨IsometryOrbit_reindex_forward e Φ A B, fun h => ?_⟩
  have h' := IsometryOrbit_reindex_forward e.symm _ _ _ h
  simpa [reindex3_symm_reindex3, Matrix.reindex_apply, Matrix.submatrix_submatrix] using h'

end Reindexing

section Size

theorem finite_block_card (n : ℕ) : Fintype.card (Σ b : Blk, finite_BIdx n b) = 3*n+1 := by
  rw [Fintype.card_sigma]
  have huniv : (Finset.univ : Finset Blk) = {Blk.dat, Blk.cop, Blk.mid, Blk.anch} := rfl
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [finite_BIdx, Fintype.card_fin, Fintype.card_unit]
  ring

theorem finite_meas_bound (n : ℕ) :
    meas₀ (finite_BIdx n) (finite_BIdx n) (finite_thn n) ≤ 22 * (n+1) := by
  unfold meas₀ meas
  rw [finite_block_card]
  simp only [finite_thn]
  omega

theorem finite_compiler_bound (n : ℕ) :
    Nside (finite_BIdx n) (finite_BIdx n) 4 (finite_thn n) ^ 3 ≤
      (Kcomp Blk Blk 4 ^ 21 * 22 ^ 24 * 8 ^ 8) * (n ^ 3 + 1) ^ 8 := by
  have hm := finite_meas_bound n
  have hN : Nside (finite_BIdx n) (finite_BIdx n) 4 (finite_thn n) ≤
      Kcomp Blk Blk 4 ^ 7 * meas₀ (finite_BIdx n) (finite_BIdx n) (finite_thn n) ^ 8 := by
    obtain ⟨ha,hb,hc⟩ := T_sides_le (RowIdx := finite_BIdx n) (ColIdx := finite_BIdx n)
      (n := 4) (t := finite_thn n)
    exact max_le ha (max_le hb hc)
  have h3 : (n+1)^3 ≤ 8*(n^3+1) := by have h := cube_succ_le n; omega
  generalize hK : Kcomp Blk Blk 4 = C at hN ⊢
  generalize hM : meas₀ (finite_BIdx n) (finite_BIdx n) (finite_thn n) = m at hN hm ⊢
  calc _ ≤ (C ^ 7 * m ^ 8) ^ 3 := Nat.pow_le_pow_left hN 3
    _ = C ^ 21 * (m ^ 3) ^ 8 := by ring
    _ ≤ C ^ 21 * ((22*(n+1))^3)^8 := by gcongr
    _ = (C ^ 21 * 22 ^ 24) * ((n+1)^3)^8 := by ring
    _ ≤ (C ^ 21 * 22 ^ 24) * (8*(n^3+1))^8 := by gcongr
    _ = _ := by ring

end Size

section Families
variable (I : ℕ → Type) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

noncomputable def IsometryTI (Φ : ∀ n, Matrix (I n) (I n) K) : CoordProblem K where
  Idx := fun n => I n × I n × I n
  fin := fun _ => inferInstance
  Rel := fun n => IsometryOrbit (Φ n)

noncomputable def isometryGadget (Φ : ∀ n, Matrix (I n) (I n) K) (n : ℕ)
    (A : I n × I n × I n → K) :
    PArr K Blk Blk (finite_BIdx (Fintype.card (I n))) (finite_BIdx (Fintype.card (I n)))
      (finite_thn (Fintype.card (I n))) :=
  dual_HF (Fintype.card (I n))
    (Matrix.reindex (Fintype.equivFin (I n)) (Fintype.equivFin (I n)) (Φ n))
    (reindex3 (Fintype.equivFin (I n)) (Fintype.equivFin (I n)) (Fintype.equivFin (I n)) A)

theorem isometryGadget_correct (Φ : ∀ n, Matrix (I n) (I n) K)
    (n : ℕ) (A B : I n × I n × I n → K) :
    IsometryOrbit (Φ n) A B ↔ BlockEquiv (finite_strHn (Fintype.card (I n)))
      (isometryGadget I Φ n A) (isometryGadget I Φ n B) :=
  (IsometryOrbit_reindex (Fintype.equivFin (I n)) (Φ n) A B).trans (arbitrary_isometry_encoding _ _ _)

theorem dual_HF_constant_sources (n : ℕ) (Φ : Matrix (Fin n) (Fin n) K) :
    ConstantSourceExpr (fun A => toFun (dual_HF n Φ A)) := by
  classical
  rintro ⟨k, ⟨b, i⟩, ⟨s, j⟩⟩
  cases b <;> cases s
  all_goals simp only [toFun, dual_HF, dual_HgadgetF]
  all_goals first
    | split <;> first
      | exact ⟨Sum.inr _, fun _ => rfl⟩
      | exact ⟨Sum.inl _, fun _ => rfl⟩
    | exact ⟨Sum.inl _, fun _ => rfl⟩

theorem isometryGadget_sources (Φ : ∀ n, Matrix (I n) (I n) K) (n : ℕ) :
    ConstantSourceExpr (fun A => toFun (isometryGadget I Φ n A)) := by
  apply compose_constant_sources
    (reindex3 (Fintype.equivFin (I n)) (Fintype.equivFin (I n)) (Fintype.equivFin (I n)))
    (fun X => toFun (dual_HF (Fintype.card (I n))
      (Matrix.reindex (Fintype.equivFin (I n)) (Fintype.equivFin (I n)) (Φ n)) X))
  · intro j; exact ⟨Sum.inr _, fun _ => rfl⟩
  · exact dual_HF_constant_sources _ _

noncomputable def isometryToGeneral (Φ : ∀ n, Matrix (I n) (I n) K) :
    ConstantProjection (IsometryTI I Φ) (GL3TI K) where
  size := fun n => Nside (finite_BIdx (Fintype.card (I n))) (finite_BIdx (Fintype.card (I n)))
    4 (finite_thn (Fintype.card (I n)))
  src := fun n j => Classical.choose (compile_constant_sources (finite_strHn (Fintype.card (I n)))
    (isometryGadget I Φ n) (isometryGadget_sources I Φ n) j)
  polyBound := ⟨Kcomp Blk Blk 4 ^ 21 * 22 ^ 24 * 8 ^ 8, 8, fun n => by
    have hc (d : ℕ) : Fintype.card (Fin d × Fin d × Fin d) = d ^ 3 := by
      simp only [Fintype.card_prod, Fintype.card_fin]; ring
    have hi : Fintype.card (I n × I n × I n) = Fintype.card (I n) ^ 3 := by
      simp only [Fintype.card_prod]; ring
    change Fintype.card (Fin _ × Fin _ × Fin _) ≤ _
    rw [hc]
    change _ ≤ _ * (Fintype.card (I n × I n × I n)+1)^8
    rw [hi]
    exact finite_compiler_bound _⟩
  correct := by
    intro n A B
    let hs := compile_constant_sources (finite_strHn (Fintype.card (I n)))
      (isometryGadget I Φ n) (isometryGadget_sources I Φ n)
    have hA : (fun j => (Classical.choose (hs j)).elim id A) =
        cube (finite_strHn (Fintype.card (I n))) (isometryGadget I Φ n A) :=
      funext fun j => (Classical.choose_spec (hs j) A).symm
    have hB : (fun j => (Classical.choose (hs j)).elim id B) =
        cube (finite_strHn (Fintype.card (I n))) (isometryGadget I Φ n B) :=
      funext fun j => (Classical.choose_spec (hs j) B).symm
    exact (isometryGadget_correct I Φ n A B).trans
      ((cube_equiv_iff _ _ _).trans (Iff.of_eq (congrArg₂ _ hA.symm hB.symm)))

end Families

end UniversalUpperReduction

section Completeness

open Matrix
set_option maxHeartbeats 800000
variable {K : Type} [Field K]

theorem blockLift_invertible {n : ℕ} (β : Type) [Fintype β] [DecidableEq β]
    (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) : IsUnit (blockLift3 β P).det := by
  unfold blockLift3
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose,
    Matrix.det_one, mul_one]
  exact hP.mul (Matrix.isUnit_nonsing_inv_det P hP)

theorem full_block_padding_correct (n : ℕ) (a : K) (β : Type) [Fintype β] [DecidableEq β]
    (W : Matrix β β K) (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ IsometryOrbit (blockForm n a W)
      (padArrB (Fin n ⊕ β) A) (padArrB (Fin n ⊕ β) B) := by
  apply padding_principle K n (Fin n ⊕ β)
    (fun g => IsUnit g.det ∧ IsIsom (blockForm n a W) g) (fun _ h => h.1)
  intro P hP
  exact ⟨Matrix.fromBlocks P⁻¹ᵀ 0 0 1, blockLift_invertible β P hP,
    blockLift_preserves K n a β W P hP⟩

section Families
variable (w : ℕ → ℕ) (a : K) (W : ∀ n, Matrix (Fin (w n)) (Fin (w n)) K)

noncomputable def FullBlockTI : CoordProblem K :=
  IsometryTI (BlockIndex w) (fun n => blockForm n a (W n))

noncomputable def generalToFullBlock (c : ℕ) (hw : ∀ n, w n ≤ c*n+c) :
    ConstantProjection (GL3TI K) (FullBlockTI w a W) where
  size := id
  src := fun _ => blockPaddingSource w
  polyBound := ⟨(c + 2) ^ 3, 3, fun n => by
    change Fintype.card (BlockIndex w n × BlockIndex w n × BlockIndex w n) ≤
      (c + 2) ^ 3 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 3
    simp only [BlockIndex, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    have hn : n ≤ n * (n * n) := by simpa [pow_succ, mul_assoc] using Nat.le_self_pow (by decide : 3 ≠ 0) n
    have hd : n + (n + w n) ≤ (c + 2) * (n * (n * n) + 1) := by nlinarith [hw n]
    calc (n + (n + w n)) * ((n + (n + w n)) * (n + (n + w n))) = (n + (n + w n)) ^ 3 := by ring
      _ ≤ ((c + 2) * (n * (n * n) + 1)) ^ 3 := Nat.pow_le_pow_left hd 3
      _ = _ := by ring⟩
  correct := by
    intro n A B
    have hA := blockPaddingSource_eval w n A
    have hB := blockPaddingSource_eval w n B
    exact (full_block_padding_correct n a (Fin (w n)) (W n) A B).trans
      (Iff.of_eq (congrArg₂ (IsometryOrbit (blockForm n a (W n))) hA.symm hB.symm))

theorem full_block_TIComplete (c : ℕ) (hw : ∀ n, w n ≤ c*n+c) : TIComplete (FullBlockTI w a W) :=
  ⟨⟨generalToFullBlock w a W c hw⟩,
    ⟨isometryToGeneral (BlockIndex w) (fun n => blockForm n a (W n))⟩⟩

end Families

theorem degenerate_orthogonal_TIComplete :
    TIComplete (FullBlockTI id (1 : ℝ) (fun _ => 0)) :=
  full_block_TIComplete _ _ _ 1 (fun _ => by simp)

theorem named_form_families_TIComplete :
    TIComplete (FullBlockTI (fun _ => 0) (-1 : ℝ) (fun _ => 0)) ∧
    TIComplete (FullBlockTI (fun _ => 0) (1 : ℝ) (fun _ => 0)) ∧
    TIComplete (FullBlockTI (fun _ => 0) (2 : ℝ) (fun _ => 0)) ∧
    TIComplete (FullBlockTI id (2 : ℝ) (fun _ => 1)) ∧
    TIComplete (FullBlockTI (fun n => 2*n) (2 : ℝ) symplecticExtra) ∧
    TIComplete (FullBlockTI id (1 : ℝ) (fun _ => 0)) ∧
    TIComplete (FullBlockTI (fun n => 2*n) (1 : ℝ) (fun _ => 1)) :=
  ⟨full_block_TIComplete _ _ _ 0 (fun _ => by simp),
    full_block_TIComplete _ _ _ 0 (fun _ => by simp),
    full_block_TIComplete _ _ _ 0 (fun _ => by simp),
    full_block_TIComplete _ _ _ 1 (fun _ => by simp),
    full_block_TIComplete _ _ _ 2 (fun _ => by omega),
    degenerate_orthogonal_TIComplete,
    full_block_TIComplete _ _ _ 2 (fun _ => by omega)⟩

end Completeness

section ReductionClasses

universe u
variable {K : Type u} [Field K]

def composeConstantSources {I J : Type} (f : J → K ⊕ I) (s : K ⊕ J) : K ⊕ I :=
  s.elim Sum.inl f

theorem composeConstantSources_eval {I J : Type} (f : J → K ⊕ I) (s : K ⊕ J) (A : I → K) :
    (composeConstantSources f s).elim id A = s.elim id (fun j => (f j).elim id A) := by cases s <;> rfl

def composeConstantProjections {P Q R : CoordProblem K}
    (r₁ : ConstantProjection P Q) (r₂ : ConstantProjection Q R) : ConstantProjection P R where
  size := fun n => r₂.size (r₁.size n)
  src := fun n j => composeConstantSources (r₁.src n) (r₂.src (r₁.size n) j)
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
    simp only [composeConstantSources_eval]

def constantProjectionSystem (K : Type u) [Field K] : ReductionSystem (CoordProblem K) where
  reduces := fun P Q => Nonempty (ConstantProjection P Q)
  refl := fun P => ⟨allowConstants (identityProjection P)⟩
  trans := fun ⟨r₁⟩ ⟨r₂⟩ => ⟨composeConstantProjections r₁ r₂⟩

theorem TIComplete_class_eq {P : CoordProblem K} (h : TIComplete P) :
    problemClass (constantProjectionSystem K) (GL3TI K) = problemClass (constantProjectionSystem K) P :=
  problemClass_eq_of_reduces_both (constantProjectionSystem K) h.1 h.2

theorem full_block_class_eq {K : Type} [Field K] (w : ℕ → ℕ) (a : K)
    (W : ∀ n, Matrix (Fin (w n)) (Fin (w n)) K) (c : ℕ) (hw : ∀ n, w n ≤ c*n+c) :
    problemClass (constantProjectionSystem K) (GL3TI K) =
      problemClass (constantProjectionSystem K) (FullBlockTI w a W) :=
  TIComplete_class_eq (full_block_TIComplete w a W c hw)

end ReductionClasses

#print axioms isometryToGeneral
#print axioms full_block_TIComplete
#print axioms named_form_families_TIComplete
#print axioms full_block_class_eq

end FormTI
