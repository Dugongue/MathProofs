import Mathlib

/-!
# Unitary transporter fibres (standalone, Mathlib only)

Single-file version of Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers together with
its full import closure (37 modules, concatenated in dependency order, each in its own section).
Main results: unitary_factor, unitaryTransporterEquiv, natCard_uTrans, tiUnitary_rel_pad_iff:
the Levi lift diag(P, sigma(P^-T)) and the transporter fibres for U(Phi_eps, sigma) over every
field and involution (hardness side of TI_U = TI). Assembled 2026-11-13.
-/

section Part_U1


/-!
# Rank of a block-diagonal matrix: the Mathlib gap FGS's rank count runs into

## Why this exists

FGS's Lemma `jhp` computes `rank M^A_k` for a padded slice that is, by construction, **block
diagonal**: an identity-like gadget block in one set of rows and columns, and `A_k` in a disjoint
set of rows and columns (their eq. `vei`). The count `rank M^A_k = 2^(str k) · r + rank A_k` is
therefore an instance of

  `rank (fromBlocks M 0 0 N) = rank M + rank N`.

That lemma is **not in Mathlib**, and it is not reachable from anything that is: a DAG walk
`forward Matrix.blockDiagonal 1` returns the whole `blockDiagonal` API (`blockDiagonal_mul`,
`det_blockDiagonal`, `trace_blockDiagonal`, `blockTriangular_blockDiagonal`, …) with **no** rank
lemma, and `cold rank_blockDiagonal` / `cold rank_fromBlocks` both report `no seed matched`. So it
has to be proved. This module proves it.

## The proof

`Matrix.rank M = finrank (range M.mulVecLin)`. Under the currying equivalences
`(C₁ ⊕ C₂ → K) ≃ₗ (C₁ → K) × (C₂ → K)` and likewise for rows, `mulVecLin (fromBlocks M 0 0 N)`
becomes `LinearMap.prodMap (mulVecLin M) (mulVecLin N)`, whose range is `Submodule.prod` of the two
ranges (`LinearMap.range_prodMap`, located by the DAG walk `neighbors LinearMap.range_prodMap 1`).
The dimension of a `Submodule.prod` is the sum, via the explicit equivalence
`Submodule.prodEquivProd` supplied below — that one is also absent
(`neighbors Submodule.finrank_prod 1` → `no seed matched`).

## DAG chains walked before writing

Snapshot `…/snapshots/20260902T033037Z-a57018fc/graph`.

* `forward Matrix.rank 1` → `Matrix.rank_of_isUnit`, `Matrix.rank_unit`, `Matrix.rank_reindex`,
  `Matrix.rank_submatrix`, `Matrix.rank_diagonal`, `Matrix.rank_eq_finrank_span_cols`,
  `Matrix.rank_eq_finrank_span_row`, `Matrix.exists_rank_normal_form`.
  `Matrix.rank_diagonal` is what gives the gadget block's rank once it is a diagonal `0/1` matrix —
  which is why the padded shape below uses a diagonal indicator rather than a literal `Iᵣ` in a
  smaller block: it removes an entire layer of block bookkeeping at no mathematical cost.
* `backward Matrix.rank 1` → `Matrix.mulVecLin`, `Module.finrank`, `LinearMap.range` — fixing the
  definition to unfold against.
* `neighbors Matrix.mulVecLin 1` → `Matrix.mulVecLin_reindex`, `Matrix.coe_mulVecLin`,
  `Matrix.mulVecLin_mul`, and the project's `Matrix.rank_add_le` / `Matrix.range_add_le`.
* `neighbors LinearMap.prodMap 1` → `LinearMap.coe_prodMap`, `LinearMap.prodMap_apply`,
  `LinearMap.prodMap_comp`; `neighbors LinearMap.range_prodMap 1` → `Submodule.prod`,
  `LinearMap.range`. This is the spine of the proof.
* `neighbors Matrix.fromBlocks_mulVec 1` → `Matrix.mulVec`, `Matrix.fromBlocks`, `Sum.inl`,
  `Sum.inr` — the computation rule used to identify the two maps.
* `cold rank_blockDiagonal`, `cold rank_fromBlocks`, `neighbors Submodule.finrank_prod 1` — all
  `no seed matched`; recorded so nobody looks for them again.
-/

namespace Mathproof.Meta.FGSBlockRank20260902


universe u v

variable {K : Type u} [Field K]

section ProdSubmodule

variable {M N : Type v} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A `Submodule.prod` is the product of the two submodules. Absent from Mathlib. -/
def Submodule.prodEquivProd (p : Submodule K M) (q : Submodule K N) :
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
  rw [(Submodule.prodEquivProd p q).finrank_eq, Module.finrank_prod]

end ProdSubmodule

section BlockRank

variable {R₁ R₂ C₁ C₂ : Type v}
variable [Fintype R₁] [Fintype R₂] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₁] [DecidableEq R₂] [DecidableEq C₁] [DecidableEq C₂]

/-- The currying equivalence `(ι ⊕ κ → K) ≃ₗ (ι → K) × (κ → K)`. -/
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
  -- `ext x i` here specialises to basis vectors (`Pi.single`) and leaves an awkward goal;
  -- apply the map to a general vector instead and split the sum over `C₁ ⊕ C₂`.
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

/-- **Rank of a block-diagonal matrix is the sum of the block ranks.**

This is the count FGS perform on every padded slice: gadget block plus `A_k`, in disjoint rows and
disjoint columns. Absent from Mathlib; see the module docstring for the DAG evidence. -/
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

end Mathproof.Meta.FGSBlockRank20260902

end Part_U1


section Part_U2


/-!
# The band cardinalities behind FGS's padded-slice rank formula

## What this supplies

`FGSRankStep20260902.S_blockDiagonal_of_ranks` takes the two rank formulas of FGS's Lemma `jhp` as
hypotheses. This module supplies the combinatorial half of discharging them: the **dimension of the
gadget part** of a padded slice.

In FGS's construction the padded slice carries, for the stratum `γ` of the slice, an identity block
of size `2^γ · r`. In the uniform-band presentation used here (see the deviation note below) that
block is the `0/1` diagonal indicator of *chunk* `γ`, a set of exactly `2^γ · r` row coordinates,
with chunks for different strata **disjoint**. Consequently:

* one stratum's gadget block has rank `2^γ · r` (`card_chunkF`);
* after a linear reconstruction, the gadget part's support is the union of the chunks of the strata
  actually hit, and its rank is `∑_{γ ∈ T} 2^γ · r` (`card_biUnion_chunkF`) — which is exactly the
  left-hand side of the hypothesis `hrank` in `S_blockDiagonal_of_ranks`.

Composed with `FGSBlockRank20260902.rank_fromBlocks_zero_offdiag` (gadget block ⊕ `A_k`), those two
cardinalities are the whole rank computation.

## Deviation from FGS's literal shape, and why it is now the *easy* option

FGS index the gadget rows by a dependent sum: band `γ` genuinely has `2^γ · r` rows, so the row
index is `Σ γ, Fin (2^γ · r)`. Writing the identity block then forces a cast between
`Fin (2^γ · r)` and `Fin (2^(str j) · r)` whenever the band and the column group are identified,
and dependent-type casts are the single most expensive thing to carry through a Lean development.

The uniform-band presentation used here takes the row index to be the **product**
`Fin s × Fin W` with `W := 2^s · r`, and realises band `γ` as the chunk
`{(γ, a) : (a : ℕ) < 2^γ · r}`. This is FGS's matrix padded with zero rows, so **every rank is
unchanged** and the inference in `S_blockDiagonal_of_ranks` — which consumes only rank equalities —
is untouched. The cost is one cardinality lemma (`card_lt_subtype`), proved here from an explicit
equivalence with no name risk at all.

Size bound, for the eventual `Projection.polyBound`: the gadget contributes `s · W = s · 2^s · r`
rows and `t · W` columns. `s` (the number of strata, i.e. blocks per mode) is a **constant** for the
fixed four-tensor system `(A, Φ_U, Φ_V, Φ_W)` of CGQTZ Theorem 1.4, and `r = min(m,n) + 1`, so this
is `O(min(m,n))` rows and `O(t · min(m,n))` columns — polynomial, with the exponential factor `2^s`
absorbed into the constant.

## DAG chains walked

`forward Matrix.rank 1` → `Matrix.rank_diagonal` (the rank of a diagonal matrix is the number of
nonzero diagonal entries) — the single Mathlib lemma this module is built to feed.
`neighbors Matrix.rank_diagonal 1` → `Matrix.diagonal`, `Matrix.rank`, `Fintype.card`,
`Matrix.toLin'_apply'`, confirming the statement is in terms of `Fintype.card` of the nonzero
support, which is why everything below is phrased as a cardinality.
-/

namespace Mathproof.Meta.FGSBandRank20260902

open Finset

universe u

variable {K : Type u} [Field K]

/-! ## Cardinality of an initial segment of `Fin W` -/

/-- `{a : Fin W // a < c} ≃ Fin c`. Written out rather than looked up: the round trips are `rfl`,
so this carries no dependency risk. -/
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

/-! ## Chunks -/

variable {s : ℕ}

/-- **Chunk `γ`**: the row coordinates carrying stratum `γ`'s gadget block. In the uniform-band
presentation it is `{γ} ×ˢ {a : a < 2^γ · r}` inside `Fin s × Fin W`. -/
def chunkF (W r : ℕ) (γ : Fin s) : Finset (Fin s × Fin W) :=
  ({γ} : Finset (Fin s)) ×ˢ (Finset.univ.filter (fun a : Fin W => (a : ℕ) < 2 ^ (γ : ℕ) * r))

/-- Chunk `γ` has exactly `2^γ · r` elements — FGS's band size. -/
theorem card_chunkF (W r : ℕ) (γ : Fin s) (h : 2 ^ (γ : ℕ) * r ≤ W) :
    (chunkF W r γ).card = 2 ^ (γ : ℕ) * r := by
  classical
  rw [chunkF, Finset.card_product, Finset.card_singleton, one_mul,
    card_filter_lt W (2 ^ (γ : ℕ) * r) h]

/-- Chunks belonging to different strata are disjoint: they differ in the first coordinate. -/
theorem chunkF_disjoint (W r : ℕ) {γ δ : Fin s} (hne : γ ≠ δ) :
    Disjoint (chunkF W r γ) (chunkF W r δ) := by
  classical
  rw [Finset.disjoint_left]
  rintro p hp hq
  rw [chunkF, Finset.mem_product, Finset.mem_singleton] at hp hq
  -- `hp.1 : p.1 = γ` and `hq.1 : p.1 = δ`, so the composite is `hp.1.symm.trans hq.1`.
  exact hne (hp.1.symm.trans hq.1)

/-- **The rank of the reconstructed gadget part.**

After a linear reconstruction, the gadget part is supported on the union of the chunks of exactly
the strata that are hit, so its dimension is `∑_{γ ∈ T} 2^γ · r`. This is the left-hand side of the
`hrank` hypothesis of `FGSRankStep20260902.S_blockDiagonal_of_ranks`. -/
theorem card_biUnion_chunkF (W r : ℕ) (T : Finset (Fin s))
    (h : ∀ γ ∈ T, 2 ^ (γ : ℕ) * r ≤ W) :
    (T.biUnion (fun γ => chunkF W r γ)).card = ∑ γ ∈ T, 2 ^ (γ : ℕ) * r := by
  classical
  rw [Finset.card_biUnion (fun γ _ δ _ hne => chunkF_disjoint W r hne)]
  exact Finset.sum_congr rfl fun γ hγ => card_chunkF W r γ (h γ hγ)

/-- The uniform band width `W := 2^s · r` really does contain every chunk. -/
theorem chunk_le_width (r : ℕ) (γ : Fin s) : 2 ^ (γ : ℕ) * r ≤ 2 ^ s * r :=
  Nat.mul_le_mul_right r (Nat.pow_le_pow_right (by norm_num) (le_of_lt γ.isLt))

end Mathproof.Meta.FGSBandRank20260902

end Part_U2


section Part_U3


/-!
# Superincreasing weights with slack: the arithmetic core of FGS's rank step

## What this is, and where it comes from

Futorny–Grochow–Sergeichuk (arXiv:1810.09219), Lemma `jhp`, deletes one block partition from a
partitioned three-dimensional array. The step that does the work is a **rank count**, and this
module is its arithmetic core, isolated and proved.

Their construction (general case, their eq. `vei` and the display just above it): the frontal slices
are grouped into `t̄` strata, and the padded slice `M^A_k` carries an identity block of size

  `2^(γ-1) · r × 2^(γ-1) · r`,   where `γ` is the stratum of `k` and `r := min(m,n) + 1`,

together with `A_k` in the corner. Since `A_k` is `m × n`, `rank A_k < r`. So

  `rank M^A_k = 2^(str k - 1) · r + rank A_k`,  with the second term `< r`.

After a linear reconstruction by a nonsingular `S = [s_{jk}]`, the transformed slice satisfies

  `rank N_k = ∑_{γ ∈ T(k)} 2^(γ-1) · r + rank C_k`,  `T(k) := {γ : s_{jk} ≠ 0 for some j in stratum γ}`,

again with `rank C_k < r`. Equality `rank N_k = rank M^A_k` must therefore force `T(k) = {str k}`,
which is exactly the statement that `S` is block-diagonal (FGS eq. `fwl`).

That implication is a statement of pure arithmetic: **a sum of a subset of the weights, perturbed by
less than the gap, determines the subset.** The weights `r, 2r, 4r, …, 2^(t̄-1) r` are
*superincreasing with slack `r-1`*:

  `∑_{δ < γ} 2^(δ-1) r + (r-1) = (2^(γ-1) - 1) r + r - 1 = 2^(γ-1) r - 1 < 2^(γ-1) r`.

`superIncr_geometric` checks precisely this, so the abstract lemma below instantiates to FGS's
actual construction with no gap.

## Correction recorded

An earlier design of mine used *linear* offsets `0, 2n+1, 4n+2, 6n+3`. Those do **not** separate
subset sums (`{0,2}` and `{3}` collide), and a gadget built on them would not have been rigid.
FGS's geometric weights are what make the subset sums distinct. Transcribing the source rather than
reconstructing it is what caught this.

## Contents

* `SuperIncr ρ σ` — each weight exceeds the total of all lighter ones by more than `σ`.
* `exists_max_symmDiff` — two distinct finite sets have a largest point of disagreement.
* `sum_lt_of_mem_of_max` — the one-sided estimate at that point.
* `sum_add_ne_of_ne` — perturbed subset sums of distinct sets are distinct.
* `subset_eq_of_sum_eq` — **the payoff**: the perturbed sum determines the subset.
* `superIncr_geometric` — FGS's weights `2^γ · r` are superincreasing with slack `r - 1`.

No dependency on the rest of the development; this is self-contained arithmetic.
-/

namespace Mathproof.Meta.FGSSuperIncreasing20260902

open Finset

variable {m : ℕ}

/-- **Superincreasing with slack `σ`**: every weight exceeds the total of all strictly lighter
weights by more than `σ`. -/
def SuperIncr (ρ : Fin m → ℕ) (σ : ℕ) : Prop :=
  ∀ i : Fin m, (∑ j ∈ univ.filter (fun j => j < i), ρ j) + σ < ρ i

/-- A set of indices all below `i` sums to at most the total weight below `i`. -/
theorem sum_le_of_forall_lt (ρ : Fin m → ℕ) {T : Finset (Fin m)} {i : Fin m}
    (hT : ∀ j ∈ T, j < i) :
    ∑ j ∈ T, ρ j ≤ ∑ j ∈ univ.filter (fun j => j < i), ρ j :=
  Finset.sum_le_sum_of_subset (fun j hj => mem_filter.mpr ⟨mem_univ j, hT j hj⟩)

/-- Two distinct finite sets of indices have a **largest** index of disagreement, above which they
coincide. -/
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
  · -- `rw [hD] at hmem` is a motive error here: `hne : D.Nonempty` mentions `D`.  Use `hmemD`.
    have hmem := (hmemD (D.max' hne)).mp (D.max'_mem hne)
    tauto
  · intro j hj
    by_contra hcon
    have hjD : j ∈ D := (hmemD j).mpr hcon
    exact absurd (D.le_max' j hjD) (not_le.mpr hj)

/-- The one-sided estimate at the largest index of disagreement. -/
theorem sum_lt_of_mem_of_max {ρ : Fin m → ℕ} {σ : ℕ} (hρ : SuperIncr ρ σ)
    {T T' : Finset (Fin m)} {i : Fin m} (hi : i ∈ T) (hi' : i ∉ T')
    (hmax : ∀ j, i < j → (j ∈ T ↔ j ∈ T')) :
    (∑ j ∈ T', ρ j) + σ < ∑ j ∈ T, ρ j := by
  classical
  set U : Finset (Fin m) := T.filter (fun j => i < j) with hU
  set L : Finset (Fin m) := univ.filter (fun j : Fin m => j < i) with hL
  -- `U ∪ {i} ⊆ T`, so `T` is at least as heavy as `U` plus `ρ i`.
  have hiU : i ∉ U := by simp [hU]
  have hsubT : insert i U ⊆ T := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact hi
    · exact (Finset.mem_filter.mp hj').1
  have hlowT : (∑ j ∈ U, ρ j) + ρ i ≤ ∑ j ∈ T, ρ j := by
    have := Finset.sum_le_sum_of_subset (f := ρ) hsubT
    rwa [Finset.sum_insert hiU, add_comm (ρ i)] at this
  -- `T' ⊆ U ∪ L`, and those two are disjoint.
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

/-- **Perturbed subset sums of distinct sets are distinct.** -/
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

/-- **The payoff.** A subset sum of superincreasing weights, perturbed by at most the slack,
determines the subset. This is exactly the inference `rank N_k = rank M^A_k ⟹ S block-diagonal`
in FGS's proof of Lemma `jhp` (their eq. `fwl`). -/
theorem subset_eq_of_sum_eq {ρ : Fin m → ℕ} {σ : ℕ} (hρ : SuperIncr ρ σ)
    {T T' : Finset (Fin m)} {s s' : ℕ} (hs : s ≤ σ) (hs' : s' ≤ σ)
    (h : (∑ j ∈ T, ρ j) + s = (∑ j ∈ T', ρ j) + s') : T = T' := by
  by_contra hne
  exact sum_add_ne_of_ne hρ hne hs hs' h

/-! ## FGS's actual weights -/

theorem sum_range_two_pow (n : ℕ) : (∑ j ∈ Finset.range n, 2 ^ j) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

/-- **FGS's stratum weights are superincreasing with slack `r - 1`.**

Stratum `γ` carries identity blocks of size `2^γ · r` (FGS index strata from `1`; here from `0`),
and the perturbation is `rank A_k < r`, i.e. at most `r - 1`. -/
theorem superIncr_geometric (r : ℕ) (hr : 0 < r) :
    SuperIncr (fun γ : Fin m => 2 ^ (γ : ℕ) * r) (r - 1) := by
  classical
  intro i
  -- Force the goal into beta-reduced form, so that its summand is syntactically the same atom
  -- as the one in `hle`/`hgeom` below; otherwise `omega` sees two unrelated atoms.
  show (∑ j ∈ univ.filter (fun j : Fin m => j < i), 2 ^ (j : ℕ) * r) + (r - 1)
      < 2 ^ (i : ℕ) * r
  -- `Finset.sum_image` would not unify its implicit set here; `Finset.sum_map` with the
  -- `Fin.valEmbedding` embedding is definite and carries no injectivity side goal.
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

end Mathproof.Meta.FGSSuperIncreasing20260902

end Part_U3


section Part_U4


/-!
# FGS Lemma `jhp`, step (a): the rank count forces the frontal transporter block-diagonal

## Statement being transcribed

Futorny–Grochow–Sergeichuk (arXiv:1810.09219), proof of Lemma `jhp`. After padding, the frontal
slices satisfy (their eq. `vei` and the general block-size display above it, with `r := min(m,n)+1`
and strata indexed `γ`):

* `rank M^A_k = 2^(str k) · r + rank A_k`, and `rank A_k < r`;
* after a linear reconstruction by a nonsingular `S = [s_{jk}]`,
  `rank N_k = ∑_{γ ∈ T(k)} 2^γ · r + rank C_k`, with `rank C_k < r`, where
  `T(k) = {γ : s_{jk} ≠ 0 for some j in stratum γ}`;
* simultaneous equivalence gives `rank N_k = rank M^A_k`.

FGS conclude (their eq. `fwl`) that `S` is block-diagonal with respect to the strata. That
conclusion is `S_blockDiagonal_of_ranks` below, **proved**.

## What is a hypothesis here and what is not

The two rank *formulas* are hypotheses of this theorem (`hrank`). They are not hand-waved away: they
are the block-rank computation for the explicit padded shape, and they are established separately
from `FGSGadgetRankCalculus20260902.tRank_add_of_projections` (rank additivity for row- and
column-disjoint block sums). Splitting them off keeps this module about the *inference*, which is
pure arithmetic and is where FGS's design actually pays off.

Everything else — the superincreasing separation that makes the inference valid — is proved, in
`FGSSuperIncreasing20260902`.

## Why the strata weights must be geometric

The inference is false for linear weights. With offsets `0, 1, 2, 3` the subsets `{0,2}` and `{3}`
have equal sums, so the rank would not determine the stratum. FGS's `r, 2r, 4r, …, 2^(t̄-1) r` is a
superincreasing sequence with slack `r-1`, and `superIncr_geometric` checks exactly that. This
module therefore also serves as the record that the geometric choice is *necessary*, not decorative.

## Interface note

The set `T k` of strata hit by column `k` of `S` is taken as a parameter together with its
characterisation `hT`, rather than being built with `Finset.filter`. This avoids imposing a
`DecidableEq K` instance on the statement and lets the caller supply whatever concrete description
of the support pattern it already has.
-/

namespace Mathproof.Meta.FGSRankStep20260902

open Finset
open Mathproof.Meta.FGSSuperIncreasing20260902

universe u

variable {K : Type u} [Field K] {t s : ℕ}

/-- **FGS Lemma `jhp`, eq. `fwl`.**

If the padded slice ranks match after a linear reconstruction `S`, then `S` cannot mix strata: every
entry of `S` joining two different strata vanishes.

* `str` assigns each frontal slice to its stratum;
* `r` is FGS's `min(m,n) + 1`, so `arank k = rank A_k` and `crank k = rank C_k` are both `< r`;
* `T k` is the set of strata hit by column `k` of `S`;
* `hrank` is the rank identity `rank N_k = rank M^A_k` written out. -/
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
  -- The rank identity says the subset sum for `T k`, perturbed by `crank k`, equals the subset sum
  -- for the singleton `{str k}`, perturbed by `arank k`.
  have hsingle : (∑ γ ∈ ({str k} : Finset (Fin s)), 2 ^ (γ : ℕ) * r) + arank k
      = 2 ^ ((str k : Fin s) : ℕ) * r + arank k := by
    rw [Finset.sum_singleton]
  have hsum : (∑ γ ∈ T k, 2 ^ (γ : ℕ) * r) + crank k
      = (∑ γ ∈ ({str k} : Finset (Fin s)), 2 ^ (γ : ℕ) * r) + arank k := by
    rw [hsingle]; exact hrank k
  -- `omega` cannot instantiate the `∀`-hypotheses `ha`/`hc`; specialise them first.
  have hak : arank k < r := ha k
  have hck : crank k < r := hc k
  have hTk : T k = ({str k} : Finset (Fin s)) :=
    subset_eq_of_sum_eq (superIncr_geometric r hr)
      (by omega : crank k ≤ r - 1) (by omega : arank k ≤ r - 1) hsum
  -- But `str j` is hit by column `k`, so it lies in `T k = {str k}`.
  have hmem : str j ∈ T k := (hT k (str j)).mpr ⟨j, rfl, hS⟩
  rw [hTk, Finset.mem_singleton] at hmem
  exact hjk hmem

/-- The same conclusion packaged as "the strata partition of the columns is preserved": column `k`
of `S` is supported entirely inside `k`'s own stratum. -/
theorem support_subset_stratum_of_ranks
    (str : Fin t → Fin s) (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin t) (Fin t) K)
    (T : Fin t → Finset (Fin s))
    (hT : ∀ k γ, γ ∈ T k ↔ ∃ j, str j = γ ∧ S j k ≠ 0)
    (arank crank : Fin t → ℕ)
    (ha : ∀ k, arank k < r) (hc : ∀ k, crank k < r)
    (hrank : ∀ k, (∑ γ ∈ T k, 2 ^ (γ : ℕ) * r) + crank k
              = 2 ^ ((str k : Fin s) : ℕ) * r + arank k) :
    ∀ j k, S j k ≠ 0 → str j = str k := by
  intro j k hne
  by_contra hjk
  exact hne (S_blockDiagonal_of_ranks str r hr S T hT arank crank ha hc hrank j k hjk)

end Mathproof.Meta.FGSRankStep20260902

end Part_U4


section Part_U5


/-!
# The padded slice's rank, discharging `hrank`

## Purpose

`FGSRankStep20260902.S_blockDiagonal_of_ranks` — FGS Lemma `jhp`'s eq. `fwl` — takes as a hypothesis
the rank identity

  `(∑ γ ∈ T k, 2^γ · r) + crank k = 2^(str k) · r + arank k`.

This module supplies the two computations that produce it, for the explicit padded slice.

The key observation is that **both sides come from one lemma**. Writing `Ediag γ` for the `0/1`
diagonal indicator of chunk `γ`, the gadget part of a padded slice always has the shape

  `gadget c := fun p (j, q) ↦ c j * Ediag (str j) p q`

for a coefficient vector `c : Fin t → K`:

* for the untransformed slice `M^A_k`, `c` is the indicator of `k`, and the stratum set hit is
  `{str k}`, giving `2^(str k) · r`;
* for the reconstructed slice `N_k = ∑_j s_{jk} M^C_j`, `c j = S j k`, and the stratum set hit is
  FGS's `T(k)`, giving `∑_{γ ∈ T k} 2^γ · r`.

So `rank_gadget` below does both at once, and the padded slice's total rank then follows from
`FGSBlockRank20260902.rank_fromBlocks_zero_offdiag` (gadget block ⊕ `A_k`, disjoint rows and
columns).

## Contents of this first instalment

* `restrictGroup`, `restrictGroup_surjective` — the surjection picking out one column group.
* `rank_colGroup` — **padding a matrix with zero column groups does not change its rank**, proved by
  factoring `mulVecLin` through that surjection rather than by manipulating column spans.
* `Ediag`, `rank_Ediag` — the chunk indicator and its rank `2^γ · r`, from `Matrix.rank_diagonal`
  and `FGSBandRank20260902.card_chunkF`.

`rank_gadget` for a general coefficient vector, and the `fromBlocks` assembly, follow in the next
instalment; they are stated here in the docstring so the target is on record.

## DAG chains walked

`forward Matrix.rank 1` → `Matrix.rank_diagonal`, `Matrix.rank_reindex`, `Matrix.rank_submatrix`,
`Matrix.rank_eq_finrank_span_cols`. `Matrix.rank_diagonal` is the only Mathlib rank lemma that
computes a rank outright rather than relating two ranks, which is why the whole construction is
arranged so that every gadget block is a diagonal `0/1` matrix.
`backward Matrix.rank 1` → `Matrix.mulVecLin`, `Module.finrank`, `LinearMap.range`: `Matrix.rank` is
*defined* as `finrank (range mulVecLin)`, which is what makes the factor-through-a-surjection proof
of `rank_colGroup` available at all.
`neighbors Matrix.mulVecLin 1` → `Matrix.mulVecLin_apply`, `Matrix.coe_mulVecLin`,
`Matrix.mulVecLin_reindex`.
-/

namespace Mathproof.Meta.FGSPaddedSlice20260902

open Matrix
open Finset
open Mathproof.Meta.FGSBandRank20260902

universe u

variable {K : Type u} [Field K]

/-! ## Zero column groups do not change the rank -/

section ColGroup

variable {R C J : Type} [Fintype R] [Fintype C] [Fintype J] [DecidableEq J]

/-- Pick out column group `k`: the linear surjection `(J × C → K) → (C → K)`. -/
def restrictGroup (k : J) : ((J × C) → K) →ₗ[K] (C → K) where
  toFun v := fun c => v (k, c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictGroup_surjective (k : J) :
    Function.Surjective (restrictGroup (K := K) (C := C) k) := by
  classical
  intro w
  refine ⟨fun p => if p.1 = k then w p.2 else 0, ?_⟩
  funext c
  simp [restrictGroup]

/-- The gadget matrix with a single nonzero column group, as a linear map, factors through
`restrictGroup`. -/
theorem mulVecLin_colGroup (E : Matrix R C K) (k : J) :
    (Matrix.of fun p (jq : J × C) => if jq.1 = k then E p jq.2 else 0).mulVecLin
      = E.mulVecLin ∘ₗ restrictGroup (K := K) (C := C) k := by
  classical
  apply LinearMap.ext
  intro v
  funext p
  simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, restrictGroup,
    Fintype.sum_prod_type, Finset.sum_ite_eq]

/-- **Padding with zero column groups preserves the rank.** -/
theorem rank_colGroup (E : Matrix R C K) (k : J) :
    (Matrix.of fun p (jq : J × C) => if jq.1 = k then E p jq.2 else 0).rank = E.rank := by
  classical
  unfold Matrix.rank
  rw [mulVecLin_colGroup E k, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (restrictGroup_surjective (K := K) (C := C) k),
    Submodule.map_top]

end ColGroup

/-! ## The chunk indicator and its rank -/

section Ediag

variable {s : ℕ}

/-- The `0/1` diagonal matrix supported exactly on chunk `γ`. Everything in the construction is
arranged so that gadget blocks have this shape, because `Matrix.rank_diagonal` then computes their
rank outright. -/
def Ediag (r : ℕ) (γ : Fin s) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin s × Fin (2 ^ s * r)) K :=
  Matrix.diagonal (fun p => if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0)

/-- **The chunk block has rank `2^γ · r`** — FGS's band size. -/
theorem rank_Ediag (r : ℕ) (γ : Fin s) :
    (Ediag (K := K) r γ).rank = 2 ^ (γ : ℕ) * r := by
  classical
  have hfilter : (Finset.univ.filter
      (fun p : Fin s × Fin (2 ^ s * r) =>
        (if p ∈ chunkF (2 ^ s * r) r γ then (1 : K) else 0) ≠ 0))
      = chunkF (2 ^ s * r) r γ := by
    ext p
    by_cases h : p ∈ chunkF (2 ^ s * r) r γ <;> simp [h]
  rw [Ediag, Matrix.rank_diagonal, Fintype.card_subtype, hfilter]
  exact card_chunkF (2 ^ s * r) r γ (chunk_le_width r γ)

end Ediag

/-! ## The gadget block for a general coefficient vector

Both sides of FGS's rank identity are instances of one matrix: `gadget r str c`, whose column group
`j` carries `c j • Ediag (str j)`.

* `c = ` indicator of `k` gives the untransformed padded slice `M^A_k`;
* `c j = S j k` gives the reconstructed slice `N_k`.

So `rank_gadget` computes both. -/

section Gadget

variable {s t : ℕ}

/-- The gadget part of a padded slice, for a coefficient vector `c`. -/
def gadget (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K) :
    Matrix (Fin s × Fin (2 ^ s * r)) (Fin t × (Fin s × Fin (2 ^ s * r))) K :=
  Matrix.of fun p jq => c jq.1 * Ediag r (str jq.1) p jq.2

/-- The union of the chunks of the strata in `T`. -/
def uni (r : ℕ) (T : Finset (Fin s)) : Finset (Fin s × Fin (2 ^ s * r)) :=
  T.biUnion (fun γ => chunkF (2 ^ s * r) r γ)

/-- The diagonal indicator of that union. -/
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

/-- Chunks are disjoint, so the indicator of the union is the sum of the indicators. -/
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
  -- Split the sum over `Fin t × GR` exactly ONCE: letting `simp` loose also splits `GR` itself
  -- into `Fin s × Fin _`, after which no `Finset.mul_sum` pattern matches.
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

/-- **The gadget's range is the coordinate subspace on the union of the chunks it hits.** -/
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
      -- the goal here is `0 = ∑ …`, so the sum lemma is applied symmetrically
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
      · -- `c j * ((c j)⁻¹ * u p) = u p`, i.e. `mul_inv_cancel_left₀`.
        simp [hp, mul_inv_cancel_left₀ hcj]
      · simp [hp]
    · intro j' _ hj'
      simp [hj']
    · intro hnot
      exact absurd (Finset.mem_univ j) hnot

/-- **The rank of the gadget block**, for any coefficient vector. Specialises to both sides of
FGS's rank identity. -/
theorem rank_gadget (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (T : Finset (Fin s)) (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0) :
    (gadget (K := K) r str c).rank = ∑ γ ∈ T, 2 ^ (γ : ℕ) * r := by
  unfold Matrix.rank
  rw [range_gadget r str c T hT]
  exact rank_EdiagT r T

/-- **The padded slice's rank.** Gadget block plus corner block, in disjoint rows and columns. -/
theorem rank_padded {Rows Cols : Type} [Fintype Rows] [Fintype Cols]
    [DecidableEq Rows] [DecidableEq Cols]
    (r : ℕ) (str : Fin t → Fin s) (c : Fin t → K)
    (T : Finset (Fin s)) (hT : ∀ γ, γ ∈ T ↔ ∃ j, str j = γ ∧ c j ≠ 0)
    (M : Matrix Rows Cols K) :
    (Matrix.fromBlocks (gadget (K := K) r str c) 0 0 M).rank
      = (∑ γ ∈ T, 2 ^ (γ : ℕ) * r) + M.rank := by
  rw [Mathproof.Meta.FGSBlockRank20260902.rank_fromBlocks_zero_offdiag,
    rank_gadget r str c T hT]

/-- **The `c = indicator of k` specialisation**, i.e. the untransformed padded slice `M^A_k`.

Supplied because the `hT` obligation at this instantiation, though immediate, is a real proof
obligation and would otherwise be repeated at every use site. -/
theorem rank_padded_indicator {Rows Cols : Type} [Fintype Rows] [Fintype Cols]
    [DecidableEq Rows] [DecidableEq Cols]
    (r : ℕ) (str : Fin t → Fin s) (k : Fin t) (M : Matrix Rows Cols K) :
    (Matrix.fromBlocks (gadget (K := K) r str (fun j => if j = k then (1 : K) else 0)) 0 0 M).rank
      = 2 ^ ((str k : Fin s) : ℕ) * r + M.rank := by
  classical
  have hT : ∀ γ : Fin s, γ ∈ ({str k} : Finset (Fin s))
      ↔ ∃ j, str j = γ ∧ (if j = k then (1 : K) else 0) ≠ 0 := by
    intro γ
    constructor
    · intro hγ
      exact ⟨k, (Finset.mem_singleton.mp hγ).symm, by simp⟩
    · rintro ⟨j, hj, hne⟩
      by_cases hjk : j = k
      · subst hjk
        exact Finset.mem_singleton.mpr hj.symm
      · simp [hjk] at hne
  rw [rank_padded r str _ ({str k} : Finset (Fin s)) hT M, Finset.sum_singleton]

end Gadget

/-! ## Degenerate blocks and reindexing

For a block `b ≠ b₀` the gadget rows are an empty type, so the padded block collapses to the
original one. `rank_of_isEmpty_rows` / `rank_of_isEmpty_cols` make that collapse formal, and
`rank_reindex_fromBlocks` is the transport wrapper for the `b = b₀` case, so that
`Equiv.subtypeUnivEquiv` never has to be touched at a use site. -/

section Degenerate

-- NOTE: `Matrix.rank_le_height` / `Matrix.rank_le_width` are specialised to `Fin` index types
-- (their DAG neighbour is `Fintype.card_fin`), so they do not apply to a general index type here.
-- Both lemmas therefore go through `finrank` instead.

theorem rank_of_isEmpty_rows {R C : Type} [Fintype R] [Fintype C] [IsEmpty R]
    (M : Matrix R C K) : M.rank = 0 := by
  have h0 : Module.finrank K (R → K) = 0 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hle : Module.finrank K (LinearMap.range M.mulVecLin) ≤ Module.finrank K (R → K) :=
    Submodule.finrank_le _
  unfold Matrix.rank
  omega

theorem rank_of_isEmpty_cols {R C : Type} [Fintype R] [Fintype C] [IsEmpty C]
    (M : Matrix R C K) : M.rank = 0 := by
  have hzero : M.mulVecLin = 0 := by
    apply LinearMap.ext
    intro v
    funext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  unfold Matrix.rank
  rw [hzero, LinearMap.range_zero]
  exact Submodule.finrank_eq_zero.mpr rfl

/-- **The arithmetic glue between a row-count bound and a rank bound.**

FGS's `r := min(m,n) + 1` bounds every slice's rank because it exceeds the number of rows. This is
that step, and it goes through `finrank` for the same reason as the two lemmas above:
`Matrix.rank_le_height` is `Fin`-specialised and does not apply to a general index type. -/
theorem rank_lt_of_card_rows_lt {R C : Type} [Fintype R] [Fintype C] {r : ℕ}
    (h : Fintype.card R < r) (M : Matrix R C K) : M.rank < r := by
  have h0 : Module.finrank K (R → K) = Fintype.card R := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank K (LinearMap.range M.mulVecLin) ≤ Module.finrank K (R → K) :=
    Submodule.finrank_le _
  unfold Matrix.rank
  omega

/-- The columns twin, via `LinearMap.finrank_range_le` on the domain instead. -/
theorem rank_lt_of_card_cols_lt {R C : Type} [Fintype R] [Fintype C] {r : ℕ}
    (h : Fintype.card C < r) (M : Matrix R C K) : M.rank < r := by
  have h0 : Module.finrank K (C → K) = Fintype.card C := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank K (LinearMap.range M.mulVecLin) ≤ Module.finrank K (C → K) :=
    LinearMap.finrank_range_le _
  unfold Matrix.rank
  omega

/-- **Reindexing the gadget block does not change the padded rank.** Apply with
`e₁ := (Equiv.subtypeUnivEquiv _).symm` to move between `GRb b₀` and `GR`. -/
theorem rank_reindex_fromBlocks {R₁ R₁' C₁ C₁' R₂ C₂ : Type}
    [Fintype R₁] [Fintype R₁'] [Fintype C₁] [Fintype C₁'] [Fintype R₂] [Fintype C₂]
    [DecidableEq R₁] [DecidableEq R₁'] [DecidableEq C₁] [DecidableEq C₁']
    [DecidableEq R₂] [DecidableEq C₂]
    (e₁ : R₁ ≃ R₁') (e₂ : C₁ ≃ C₁') (G : Matrix R₁ C₁ K) (M : Matrix R₂ C₂ K) :
    (Matrix.fromBlocks (Matrix.reindex e₁ e₂ G) 0 0 M).rank
      = (Matrix.fromBlocks G 0 0 M).rank := by
  rw [Mathproof.Meta.FGSBlockRank20260902.rank_fromBlocks_zero_offdiag,
    Mathproof.Meta.FGSBlockRank20260902.rank_fromBlocks_zero_offdiag, Matrix.rank_reindex]

end Degenerate

end Mathproof.Meta.FGSPaddedSlice20260902

end Part_U5


section Part_U6


-- `CStarMatrix` leaks an `HMul` instance that hijacks `Matrix` multiplication when index types
-- are subtypes; erase it for this file.
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-!
# Partitioned 3-arrays in per-block form, and the FGS padding (forward direction)

## Purpose

FGS Lemma `jhp` (arXiv 1810.09219) deletes the frontal partition of a partitioned 3-array while
keeping the row and column partitions. In its reverse direction the transporters stay
block-diagonal with respect to the OLD row/column blocks, with the gadget rows and columns merged
into a designated block `(b₀, c₀)` — FGS cancel the representation `R(Δ)` precisely because the
gadget may mix with `A`'s block-`b₀` rows. So the natural formalization is *per block*:

* `PArr K β γ RowIdx ColIdx t` — frontal slices, each given by its `(b, s)` blocks;
* `BlockEquiv str X Y` — block-equivalence: per-block invertible `P b`, `Q s`, and a frontal `R`
  that is block-diagonal for the strata `str` (`IsBlockDiag`), with
  `Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)` (the `act3` convention);
* `padArr b₀ c₀ r str X` — FGS's `M^A`: block `(b, s)` is `fromBlocks (gadgetBlock (ind k)) 0 0 (X k b s)`,
  where the gadget (`FGSPaddedSlice20260902.gadget`, uniform geometric bands) occupies the new rows
  `{p : GR n r // b = b₀}` and new columns `{jq // s = c₀}` — empty unless `b = b₀` / `s = c₀`;
* `blockEquiv_pad` — **the forward direction**: block-equivalence of `X, Y` gives equivalence of
  `padArr X, padArr Y` with NO frontal partition (`str' := fun _ => 0`). The witnesses are FGS's:
  `P' = 1 ⊕ P`, `Q' = ((R⁻¹)ᵀ ⊗ 1) ⊕ Q`, `R' = R`; the gadget identity
  `∑ k', R k k' • gadget(ind k') · ((R⁻¹)ᵀ ⊗ 1)ᵀ = gadget(ind k)` uses only that `R` is
  block-diagonal for `str`.

The reverse direction (rank step + Krull–Schmidt) is `FGSPartitionDeletion20260902`.

## DAG chain walked

`Matrix.fromBlocks_multiply → Matrix.fromBlocksZero₂₁Invertible, invertibleOfFromBlocksZero₂₁Invertible`;
`Matrix.kroneckerMap → mul_kronecker_mul, one_kronecker_one, kronecker_apply`;
`Mathproof.Meta.FGSPaddedSlice20260902.gadget/Ediag/rank_padded` (consumed);
`Matrix.det_fromBlocks_zero₂₁`, `Matrix.rank_mul_eq_left/right_of_isUnit_det` (for the reverse).
-/

namespace Mathproof.Meta.FGSBlockArrays20260902

open Matrix
open Mathproof.Meta.FGSPaddedSlice20260902 (gadget Ediag)

universe u

/-- The gadget row type of `FGSPaddedSlice20260902` (`n` strata, band width `2^n * r`). -/
abbrev GR (n r : ℕ) : Type := Fin n × Fin (2 ^ n * r)

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

/-! ### Partitioned arrays and block-equivalence -/

/-- A partitioned 3-array: frontal slices, each given by its `(b, s)` blocks. -/
abbrev PArr (K : Type u) [Field K] (β γ : Type) (RowIdx : β → Type) (ColIdx : γ → Type) (t : ℕ) :=
  Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K

/-- A square matrix is block-diagonal for a block map. -/
def IsBlockDiag {I ρ : Type} [DecidableEq ρ] (blk : I → ρ) (M : Matrix I I K) : Prop :=
  ∀ i j, blk i ≠ blk j → M i j = 0

theorem isBlockDiag_one {I ρ : Type} [DecidableEq I] [DecidableEq ρ] (blk : I → ρ) :
    IsBlockDiag blk (1 : Matrix I I K) := by
  intro i j hij
  rw [Matrix.one_apply, if_neg]
  rintro rfl
  exact hij rfl

theorem isBlockDiag_mul {I ρ : Type} [Fintype I] [DecidableEq ρ] (blk : I → ρ) {M N : Matrix I I K}
    (hM : IsBlockDiag blk M) (hN : IsBlockDiag blk N) : IsBlockDiag blk (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hil : blk i = blk l
  · rw [hN l j (hil ▸ hij), mul_zero]
  · rw [hM i l hil, zero_mul]

theorem isBlockDiag_const {I : Type} (M : Matrix I I K) :
    IsBlockDiag (fun _ : I => (0 : Fin 1)) M :=
  fun _ _ h => absurd rfl h

/-- **Block-equivalence** with frontal strata `str`. -/
def BlockEquiv (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) : Prop :=
  ∃ (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (R : Matrix (Fin t) (Fin t) K),
    (∀ b, IsUnit (P b).det) ∧ (∀ s, IsUnit (Q s).det) ∧ IsUnit R.det ∧ IsBlockDiag str R ∧
    ∀ k b s, Y k b s = ∑ k', R k k' • (P b * X k' b s * (Q s)ᵀ)

theorem BlockEquiv.refl (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X X := by
  refine ⟨fun _ => 1, fun _ => 1, 1, fun _ => by simp, fun _ => by simp, by simp,
    isBlockDiag_one str, fun k b s => ?_⟩
  simp [Matrix.one_apply, Finset.sum_ite_eq']

/-- Transport of the slice equation along a second transporter. -/
theorem transport_trans {X Y Z : PArr K β γ RowIdx ColIdx t}
    (P₁ P₂ : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q₁ Q₂ : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (R₁ R₂ : Matrix (Fin t) (Fin t) K)
    (h₁ : ∀ k b s, Y k b s = ∑ k', R₁ k k' • (P₁ b * X k' b s * (Q₁ s)ᵀ))
    (h₂ : ∀ k b s, Z k b s = ∑ k', R₂ k k' • (P₂ b * Y k' b s * (Q₂ s)ᵀ)) :
    ∀ k b s, Z k b s = ∑ k', (R₂ * R₁) k k' • ((P₂ b * P₁ b) * X k' b s * (Q₂ s * Q₁ s)ᵀ) := by
  intro k b s
  rw [h₂]
  simp only [h₁, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [Finset.sum_comm]

theorem BlockEquiv.trans {str : Fin t → Fin n} {X Y Z : PArr K β γ RowIdx ColIdx t}
    (h₁ : BlockEquiv str X Y) (h₂ : BlockEquiv str Y Z) : BlockEquiv str X Z := by
  obtain ⟨P₁, Q₁, R₁, hP₁, hQ₁, hR₁, hb₁, e₁⟩ := h₁
  obtain ⟨P₂, Q₂, R₂, hP₂, hQ₂, hR₂, hb₂, e₂⟩ := h₂
  refine ⟨fun b => P₂ b * P₁ b, fun s => Q₂ s * Q₁ s, R₂ * R₁,
    fun b => by rw [Matrix.det_mul]; exact (hP₂ b).mul (hP₁ b),
    fun s => by rw [Matrix.det_mul]; exact (hQ₂ s).mul (hQ₁ s),
    by rw [Matrix.det_mul]; exact hR₂.mul hR₁,
    isBlockDiag_mul str hb₂ hb₁, transport_trans P₁ P₂ Q₁ Q₂ R₁ R₂ e₁ e₂⟩

/-! ### The padding -/

section Pad

variable (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

/-- Gadget rows attached to block `b`: the geometric bands if `b = b₀`, nothing otherwise. -/
abbrev GRb (b : β) : Type := {p : GR n r // b = b₀}

/-- Gadget columns attached to block `s`: one group per frontal slice if `s = c₀`, nothing otherwise. -/
abbrev GCs (s : γ) : Type := {jq : Fin t × GR n r // s = c₀}

/-- Padded row index of block `b`. -/
abbrev PadRow (b : β) : Type := GRb b₀ (n := n) r b ⊕ RowIdx b

/-- Padded column index of block `s`. -/
abbrev PadCol (s : γ) : Type := GCs c₀ (n := n) (t := t) r s ⊕ ColIdx s

/-- The indicator coefficient vector of slice `k`. -/
def ind (k : Fin t) : Fin t → K := fun j => if j = k then 1 else 0

/-- The gadget block with coefficients `c`, placed in block `(b, s)`. -/
def gadgetBlock (c : Fin t → K) (b : β) (s : γ) :
    Matrix (GRb b₀ (n := n) r b) (GCs c₀ (n := n) (t := t) r s) K :=
  Matrix.of fun p jq => gadget r str c p.1 jq.1

/-- **FGS's padded array** `M^X`. -/
def padArr (X : PArr K β γ RowIdx ColIdx t) :
    PArr K β γ (PadRow b₀ r (RowIdx := RowIdx) (n := n)) (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t)) t :=
  fun k b s => Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind k) b s) 0 0 (X k b s)

/-- Gadget blocks are linear in the coefficients. -/
theorem sum_smul_gadgetBlock (b : β) (s : γ) (R : Matrix (Fin t) (Fin t) K) (k : Fin t) :
    ∑ k', R k k' • gadgetBlock b₀ c₀ r str (ind k') b s =
      gadgetBlock b₀ c₀ r str (fun j => R k j) b s := by
  ext p jq
  simp only [Matrix.sum_apply, Matrix.smul_apply, gadgetBlock, Matrix.of_apply, gadget, ind,
    smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Sums of block-diagonal `fromBlocks` are `fromBlocks` of the sums. -/
theorem sum_smul_fromBlocks {R₁ R₂ C₁ C₂ : Type} [Fintype R₁] [Fintype R₂] [Fintype C₁] [Fintype C₂]
    {ι : Type} [Fintype ι] (c : ι → K) (f : ι → Matrix R₁ C₁ K) (g : ι → Matrix R₂ C₂ K) :
    ∑ i, c i • Matrix.fromBlocks (f i) 0 0 (g i) =
      Matrix.fromBlocks (∑ i, c i • f i) 0 0 (∑ i, c i • g i) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

/-- The Kronecker normalizer on the gadget columns. -/
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

theorem isUnit_kron (X : Matrix (Fin t) (Fin t) K) (hX : IsUnit X.det) :
    IsUnit (kron (n := n) r X) := by
  refine ⟨⟨kron r X, kron r X⁻¹, ?_, ?_⟩, rfl⟩
  · rw [kron_mul, Matrix.mul_nonsing_inv X hX, kron_one]
  · rw [kron_mul, Matrix.nonsing_inv_mul X hX, kron_one]

/-- `kron` restricted to the gadget columns of block `s`. -/
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

/-- **The gadget identity.** For `R` block-diagonal on the strata,
`gadget (R k ·) · ((R⁻¹)ᵀ ⊗ 1)ᵀ = gadget (ind k)`, blockwise. -/
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
    -- ∑ j, R k j * Ediag (str j) p jq.2 * R⁻¹ j jq.1 = ind k jq.1 * Ediag (str jq.1) p jq.2
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

/-- Transport of a padded slice by block-diagonal padded transporters. -/
theorem pad_transport (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K)
    (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K) (Wq : ∀ s, Matrix (GCs c₀ (n := n) (t := t) r s) (GCs c₀ (n := n) (t := t) r s) K)
    (G : Matrix (GRb b₀ (n := n) r b) (GCs c₀ (n := n) (t := t) r s) K) (M : Matrix (RowIdx b) (ColIdx s) K) :
    Matrix.fromBlocks (1 : Matrix (GRb b₀ (n := n) r b) (GRb b₀ (n := n) r b) K) 0 0 (P b) *
        Matrix.fromBlocks G 0 0 M * (Matrix.fromBlocks (Wq s) 0 0 (Q s))ᵀ =
      Matrix.fromBlocks (G * (Wq s)ᵀ) 0 0 (P b * M * (Q s)ᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

/-- **Forward direction of FGS Lemma `jhp`.** -/
theorem blockEquiv_pad (X Y : PArr K β γ RowIdx ColIdx t) (h : BlockEquiv str X Y) :
    BlockEquiv (fun _ : Fin t => (0 : Fin 1)) (padArr b₀ c₀ r str X) (padArr b₀ c₀ r str Y) := by
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
            padArr b₀ c₀ r str X a b s * (Matrix.fromBlocks (kronS (n := n) c₀ r (R⁻¹)ᵀ s) 0 0 (Q s))ᵀ =
          Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind a) b s * (kronS (n := n) c₀ r (R⁻¹)ᵀ s)ᵀ) 0 0
            (P b * X a b s * (Q s)ᵀ) := fun a => pad_transport b₀ c₀ r P Q _ _ _
    refine Eq.trans ?_ (Finset.sum_congr rfl fun x _ =>
      (congrArg (fun M => R k x • M) (hterm x)).symm)
    rw [sum_smul_fromBlocks, padArr, Matrix.fromBlocks_inj]
    refine ⟨?_, rfl, rfl, hXY k b s⟩
    rw [← gadgetBlock_mul_kronS b₀ c₀ r str R hR hbd k b s,
      ← sum_smul_gadgetBlock b₀ c₀ r str b s R k, Matrix.sum_mul]
    simp only [Matrix.smul_mul]
    exact Finset.sum_congr rfl fun x _ => rfl

end Pad

end Mathproof.Meta.FGSBlockArrays20260902

end Part_U6


section Part_U7


/-!
# Krull–Schmidt cancellation for finite-length modules (the missing piece of `TI = TI_Sp`)

## Why

`TI_Sp ⊆ TI` (CGQTZ Theorem 1.4) rests on Futorny–Grochow–Sergeichuk's tensor-system theorem,
whose proof uses one non-elementary input: **cancellation** — if `E ⊕ A ≅ E ⊕ C` for finite-length
`E` then `A ≅ C` (the Krull–Schmidt theorem for quiver representations, used as
`(E₁,…,E₆) ⊕ (A₁,…,A₆) ≅ (E₁,…,E₆) ⊕ (C₁,…,C₆) ⟹ (A_i) ≅ (C_i)`). Mathlib has no Krull–Schmidt.
This module proves cancellation directly, for modules over an arbitrary ring, from Mathlib's
Fitting lemma (`LinearMap.eventually_isCompl_ker_pow_range_pow`, found by DAG traversal, not by
name), `IsArtinian.surjective_of_injective_endomorphism`, and `IsNilpotent.isUnit_add_one`.

## The argument (no local-ring theory needed)

Let `φ : E × A ≃ E × C` and write `α := fst ∘ φ ∘ inl : E → E` for its `(1,1)`-block.

1. **Block-unit case.** If `α` is bijective then `φ (E × 0)` is a complement of `0 × C`
   (`isCompl_image_inl_snd`), so `A ≅ (E × A)/(E × 0) ≅ (E × C)/φ(E × 0) ≅ C` — three Mathlib
   quotient equivalences, no block algebra (`cancel_of_block_unit`).
2. **Fitting dichotomy.** On an indecomposable finite-length module every endomorphism is a unit or
   nilpotent (`isUnit_or_isNilpotent`): `IsCompl (ker fⁿ) (range fⁿ)` for large `n`, and
   indecomposability kills the mixed case.
3. **Shear.** If `α` is not a unit, then `α'α` (with `α'` the `(1,1)`-block of `φ⁻¹`) is not a unit
   either, hence nilpotent, hence `β'γ = 1 − α'α` is a unit (`β' := fst ∘ φ⁻¹ ∘ inr`,
   `γ := snd ∘ φ ∘ inl`). With `λ := (β'γ)⁻¹ β'`, the shear `σ (e, c) := (e + λ c, c)` is an
   automorphism of `E × C` and the `(1,1)`-block of `σ ∘ φ` is `α + λγ = α + 1`, a unit because `α`
   is nilpotent. Apply step 1 to `σ ∘ φ`.
4. **General `E`** by strong induction on `Module.length E`: a decomposable `E` splits as
   `E₁ × E₂` with both of smaller length; cancel `E₁` then `E₂`.

## Status

Written as a single self-contained development. The `Indecomposable` predicate is the standard one
(nontrivial, and every complementary pair has a trivial member).
-/

namespace Mathproof.Meta.KrullSchmidtCancellation20260902

open LinearMap Submodule

universe u v

variable {R : Type u} [Ring R]

/-! ## Indecomposability and the Fitting dichotomy -/

/-- A module is indecomposable when it is nontrivial and admits no nontrivial complementary pair. -/
def Indecomposable (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ p q : Submodule R M, IsCompl p q → p = ⊥ ∨ q = ⊥

section Fitting

variable {M : Type v} [AddCommGroup M] [Module R M] [IsArtinian R M] [IsNoetherian R M]

/-- Fitting's lemma, existential form: `M = ker fⁿ ⊕ range fⁿ` for some `n`. -/
theorem exists_isCompl_ker_pow_range_pow (f : Module.End R M) :
    ∃ n : ℕ, 1 ≤ n ∧ IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  exact ⟨n + 1, by omega, hn (n + 1) (by omega)⟩

/-- An injective endomorphism of a finite-length module is a unit of `End`. -/
theorem isUnit_of_injective (f : Module.End R M) (hf : Function.Injective f) : IsUnit f := by
  have hs : Function.Surjective f := IsArtinian.surjective_of_injective_endomorphism f hf
  let e : M ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hf, hs⟩
  refine ⟨⟨f, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
  · ext x; exact e.apply_symm_apply x
  · ext x; exact e.symm_apply_apply x

/-- A unit of `End` is injective. -/
theorem injective_of_isUnit (f : Module.End R M) (hf : IsUnit f) : Function.Injective f := by
  obtain ⟨u, rfl⟩ := hf
  intro x y hxy
  have h := congrArg (↑u⁻¹ : Module.End R M) hxy
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply,
    Module.End.one_apply] at h

/-- **Fitting dichotomy**: on an indecomposable finite-length module every endomorphism is a unit
or nilpotent. -/
theorem isUnit_or_isNilpotent (hM : Indecomposable (R := R) M) (f : Module.End R M) :
    IsUnit f ∨ IsNilpotent f := by
  obtain ⟨n, hn1, hn⟩ := exists_isCompl_ker_pow_range_pow f
  rcases hM.2 _ _ hn with hk | hr
  · -- `ker fⁿ = ⊥` with `n ≥ 1`: `ker f ≤ ker fⁿ = ⊥`, so `f` is injective, hence a unit
    left
    apply isUnit_of_injective
    rw [← LinearMap.ker_eq_bot]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : LinearMap.ker f ≤ LinearMap.ker (f ^ (m + 1)) := by
      rw [pow_succ]
      exact LinearMap.ker_le_ker_comp f (f ^ m)
    exact le_bot_iff.mp (hk ▸ hle)
  · -- `range fⁿ = ⊥`: `fⁿ = 0`
    right
    exact ⟨n, LinearMap.range_eq_bot.mp hr⟩

end Fitting

/-! ## Step 1: cancellation when the `(1,1)`-block is a unit -/

section BlockUnit

variable {E A C : Type v} [AddCommGroup E] [Module R E] [AddCommGroup A] [Module R A]
  [AddCommGroup C] [Module R C]

/-- The `(1,1)`-block of `φ : E × A ≃ E × C`. -/
def block11 (φ : (E × A) ≃ₗ[R] (E × C)) : Module.End R E :=
  (LinearMap.fst R E C) ∘ₗ (φ : E × A →ₗ[R] E × C) ∘ₗ (LinearMap.inl R E A)

/-- The `(2,1)`-block `γ : E → C`. -/
def block21 (φ : (E × A) ≃ₗ[R] (E × C)) : E →ₗ[R] C :=
  (LinearMap.snd R E C) ∘ₗ (φ : E × A →ₗ[R] E × C) ∘ₗ (LinearMap.inl R E A)

/-- `φ (E × 0)` as a submodule of `E × C`. -/
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

/-- **If the `(1,1)`-block is bijective, `φ(E × 0)` is a complement of `0 × C`.** -/
theorem isCompl_imageInl_snd (φ : (E × A) ≃ₗ[R] (E × C)) (hα : Function.Bijective (block11 φ)) :
    IsCompl (imageInl φ) (LinearMap.range (LinearMap.inr R E C)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨e, rfl⟩ := (mem_imageInl φ x).mp hx
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hx'
    -- first component of `φ (e,0)` is `α e`, and it equals `0` since `x ∈ 0 × C`
    have h1 : block11 φ e = 0 := by
      have := congrArg Prod.fst hc
      simpa [block11] using this.symm
    have he : e = 0 := hα.1 (by simpa using h1)
    subst he; simp
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro ⟨e', c⟩
    obtain ⟨e, he⟩ := hα.2 e'
    -- `(e', c) = φ (e, 0) + (0, c - snd (φ (e,0)))`
    refine Submodule.mem_sup.mpr ⟨φ (e, 0), (mem_imageInl φ _).mpr ⟨e, rfl⟩,
      (0, c - (φ (e, 0)).2), LinearMap.mem_range.mpr ⟨c - (φ (e, 0)).2, rfl⟩, ?_⟩
    have h1 : (φ (e, 0)).1 = e' := by simpa [block11] using he
    ext <;> simp [h1]

/-- `E × 0` is a complement of `0 × A` in `E × A`. -/
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

/-- **Step 1.** Bijective `(1,1)`-block ⟹ `A ≅ C`, through three quotient identifications. -/
noncomputable def cancelOfBlockUnit (φ : (E × A) ≃ₗ[R] (E × C))
    (hα : Function.Bijective (block11 φ)) : A ≃ₗ[R] C :=
  -- `A ≅ 0 × A ≅ (E × A) / (E × 0)`
  let e₁ : A ≃ₗ[R] LinearMap.range (LinearMap.inr R E A) :=
    (LinearEquiv.ofInjective (LinearMap.inr R E A) LinearMap.inr_injective)
  let e₂ : LinearMap.range (LinearMap.inr R E A) ≃ₗ[R]
      ((E × A) ⧸ LinearMap.range (LinearMap.inl R E A)) :=
    Submodule.quotientEquivOfIsCompl _ _ isCompl_range_inl_inr |>.symm
  -- `(E × A) / (E × 0) ≅ (E × C) / φ(E × 0)`
  let e₃ : ((E × A) ⧸ LinearMap.range (LinearMap.inl R E A)) ≃ₗ[R] ((E × C) ⧸ imageInl φ) :=
    Submodule.Quotient.equiv _ _ φ rfl
  -- `(E × C) / φ(E × 0) ≅ 0 × C ≅ C`
  let e₄ : ((E × C) ⧸ imageInl φ) ≃ₗ[R] LinearMap.range (LinearMap.inr R E C) :=
    Submodule.quotientEquivOfIsCompl _ _ (isCompl_imageInl_snd φ hα)
  let e₅ : LinearMap.range (LinearMap.inr R E C) ≃ₗ[R] C :=
    (LinearEquiv.ofInjective (LinearMap.inr R E C) LinearMap.inr_injective).symm
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄ ≪≫ₗ e₅

end BlockUnit

/-! ## Step 3: the shear, and cancellation for indecomposable `E` -/

section Indecomposable

variable {E A C : Type v} [AddCommGroup E] [Module R E] [AddCommGroup A] [Module R A]
  [AddCommGroup C] [Module R C] [IsArtinian R E] [IsNoetherian R E]

/-- The shear automorphism `σ (e, c) = (e + λ c, c)` of `E × C`. -/
def shear (l : C →ₗ[R] E) : (E × C) ≃ₗ[R] (E × C) where
  toFun := fun x => (x.1 + l x.2, x.2)
  invFun := fun x => (x.1 - l x.2, x.2)
  map_add' := by intro x y; ext <;> simp [add_add_add_comm]
  map_smul' := by intro c x; ext <;> simp
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp

theorem shear_apply (l : C →ₗ[R] E) (x : E × C) : shear l x = (x.1 + l x.2, x.2) := rfl

/-- The `(1,1)`-block of `σ ∘ φ` is `α + λ ∘ γ`. -/
theorem block11_shear_trans (φ : (E × A) ≃ₗ[R] (E × C)) (l : C →ₗ[R] E) :
    block11 (φ ≪≫ₗ shear l) = block11 φ + l ∘ₗ block21 φ := by
  ext e
  simp [block11, block21, shear_apply]

/-- The `(1,1)`-block of `φ⁻¹` composed with that of `φ` plus the cross term is the identity:
`α'α + β'γ = 1`. -/
theorem block_identity (φ : (E × A) ≃ₗ[R] (E × C)) :
    block11 φ.symm ∘ₗ block11 φ +
      ((LinearMap.fst R E A) ∘ₗ (φ.symm : E × C →ₗ[R] E × A) ∘ₗ (LinearMap.inr R E C)) ∘ₗ block21 φ
      = (1 : Module.End R E) := by
  ext e
  -- `φ.symm (φ (e,0)) = (e, 0)`; decompose `φ (e,0) = (α e, 0) + (0, γ e)`
  have h : φ.symm (φ (e, 0)) = (e, 0) := φ.symm_apply_apply _
  have hsplit : φ (e, 0) = ((φ (e, 0)).1, 0) + (0, (φ (e, 0)).2) := by ext <;> simp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, block11, block21, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
    Module.End.one_apply]
  have := congrArg Prod.fst h
  rw [hsplit, map_add] at this
  simpa using this

/-- If `α'α` were a unit then `α` would be injective, hence a unit. -/
theorem isUnit_block11_of_isUnit_comp (φ : (E × A) ≃ₗ[R] (E × C))
    (h : IsUnit (block11 φ.symm ∘ₗ block11 φ)) : IsUnit (block11 φ) := by
  apply isUnit_of_injective
  intro x y hxy
  have hinj := injective_of_isUnit _ h
  exact hinj (by simp [LinearMap.comp_apply, hxy])

/-- **Cancellation with indecomposable `E`.** -/
theorem cancel_of_indecomposable (hE : Indecomposable (R := R) E)
    (φ : (E × A) ≃ₗ[R] (E × C)) : Nonempty (A ≃ₗ[R] C) := by
  rcases isUnit_or_isNilpotent hE (block11 φ) with hα | hα
  · -- block-unit case
    exact ⟨cancelOfBlockUnit φ ⟨injective_of_isUnit _ hα,
      IsArtinian.surjective_of_injective_endomorphism _ (injective_of_isUnit _ hα)⟩⟩
  · -- nilpotent case: `α'α` is not a unit, so it is nilpotent, so `β'γ = 1 - α'α` is a unit
    haveI : Nontrivial E := hE.1
    set β' : C →ₗ[R] E :=
      (LinearMap.fst R E A) ∘ₗ (φ.symm : E × C →ₗ[R] E × A) ∘ₗ (LinearMap.inr R E C) with hβ'
    have hna : ¬ IsUnit (block11 φ.symm ∘ₗ block11 φ) := fun h =>
      (IsNilpotent.not_isUnit hα) (isUnit_block11_of_isUnit_comp φ h)
    -- `IsNilpotent.not_isUnit` needs a nontrivial ring; `Nontrivial (End E)` from `hE.1`
    have hnil : IsNilpotent (block11 φ.symm ∘ₗ block11 φ) :=
      (isUnit_or_isNilpotent hE _).resolve_left hna
    have hunit : IsUnit (β' ∘ₗ block21 φ) := by
      have hid := block_identity φ
      -- `β'γ = 1 - α'α`, and `1 - nilpotent` is a unit
      have : β' ∘ₗ block21 φ = 1 - (block11 φ.symm ∘ₗ block11 φ) :=
        eq_sub_of_add_eq (by rw [add_comm]; exact hid)
      rw [this]
      have h' : IsNilpotent (-(block11 φ.symm ∘ₗ block11 φ)) := hnil.neg
      simpa [sub_eq_add_neg, add_comm] using h'.isUnit_add_one
    -- the shear with `λ = (β'γ)⁻¹ β'`
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

/-! ## Step 4: general `E` by induction on dimension

For the application (representations of a quiver over a field `K` = modules over the path algebra
`R = KQ`) every module in sight is a finite-dimensional `K`-space with `R` acting `K`-linearly
(`IsScalarTower K R E`). Finite `K`-dimension gives finite length over `R`, and `finrank K` is the
induction measure. -/

section General

variable {K : Type u} [Field K] [Algebra K R]
variable {A C : Type v} [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]

/-- A nontrivial, non-indecomposable module splits as a product of two nontrivial submodules. -/
theorem exists_split {E : Type v} [AddCommGroup E] [Module R E] (hnt : Nontrivial E)
    (hnd : ¬ Indecomposable (R := R) E) :
    ∃ p q : Submodule R E, IsCompl p q ∧ p ≠ ⊥ ∧ q ≠ ⊥ := by
  unfold Indecomposable at hnd
  push Not at hnd
  obtain ⟨p, q, hpq, hp, hq⟩ := hnd hnt
  exact ⟨p, q, hpq, hp, hq⟩

/-- Trivial `E` cancels by projection: `E × A ≅ A` when `E` is a singleton. -/
noncomputable def prodSubsingletonEquiv (E : Type v) [AddCommGroup E] [Module R E] [Subsingleton E]
    (X : Type v) [AddCommGroup X] [Module R X] : (E × X) ≃ₗ[R] X where
  toFun := Prod.snd
  invFun := fun x => (0, x)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl
  right_inv := fun _ => rfl

/-- **Krull–Schmidt cancellation**, finite-dimensional form: for `E` a finite-dimensional `K`-space
with a compatible `R`-module structure, `E × A ≅ E × C ⟹ A ≅ C`. Strong induction on
`finrank K E`; the inductive step splits a decomposable `E` and cancels the two halves in turn. -/
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
        -- `E ≅ p × q`, both of smaller `K`-dimension
        let e : (↥p × ↥q) ≃ₗ[R] E := Submodule.prodEquivOfIsCompl p q hpq
        haveI hfp : FiniteDimensional K ↥p :=
          Module.Finite.of_injective (p.subtype.restrictScalars K) Subtype.val_injective
        haveI hfq : FiniteDimensional K ↥q :=
          Module.Finite.of_injective (q.subtype.restrictScalars K) Subtype.val_injective
        -- strict dimension drop: the image of `p` is a proper `K`-subspace since `q ≠ ⊥`
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
        -- reassociate: `p × (q × A) ≅ E × A ≅ E × C ≅ p × (q × C)`
        let φ' : (↥p × (↥q × A)) ≃ₗ[R] (↥p × (↥q × C)) :=
          (LinearEquiv.prodAssoc R ↥p ↥q A).symm ≪≫ₗ e.prodCongr (LinearEquiv.refl R A) ≪≫ₗ φ ≪≫ₗ
            e.symm.prodCongr (LinearEquiv.refl R C) ≪≫ₗ LinearEquiv.prodAssoc R ↥p ↥q C
        obtain ⟨ψ⟩ := ih _ hp_lt ↥p rfl (↥q × A) (↥q × C) φ'
        exact ih _ hq_lt ↥q rfl A C ψ

end General

end Mathproof.Meta.KrullSchmidtCancellation20260902

end Part_U7


section Part_U8


/-!
# Krull–Schmidt cancellation for bipartite-quiver representations (FGS block-equivalence)

## Purpose

FGS Lemma `jhp` (arXiv 1810.09219, eq. `dfr` and the general case eq. `vei`) deletes one partition
of a partitioned 3-array while keeping the other two, so the transporters `P, Q` stay
block-diagonal with `m̄` and `n̄` diagonal blocks. The objects are therefore representations of the
bipartite quiver with `m̄` sources, `n̄` sinks and `t` arrows between every (source, sink) pair, and
the cancellation FGS invoke is Krull–Schmidt in that category. This module proves it with no
quiver theory: a representation is encoded as the module `(∀ s, V s) × (∀ t, W t)` over the free
algebra `R = FreeAlgebra K (Src ⊕ Snk ⊕ Arr × Src × Snk)`, vertex generators acting as the
coordinate projections and arrow generators as `m ↦ (0, single t (f a s t (m.1 s)))`. `R`-linear
maps are exactly the `K`-linear maps commuting with the generators (`linear_of_gen`), which is
block-diagonal simultaneous equivalence (`simEquiv_iff_nonempty`), and
`KrullSchmidtCancellation20260902.cancel_of_finiteDimensional` gives `bipartite_cancel`.

The 2-vertex Kronecker case is `KroneckerCancellation20260902`; this module is the one the
partition-deletion steps consume.

## DAG chain walked

`FreeAlgebra.lift → lift_ι_apply, induction`; `LinearMap.single`, `Pi.single_eq_same`,
`Finset.univ_sum_single`; `isArtinian_of_tower`, `isNoetherian_of_tower`;
`Mathproof.Meta.KrullSchmidtCancellation20260902.cancel_of_finiteDimensional`.
-/

namespace Mathproof.Meta.BipartiteCancellation20260902

open Mathproof.Meta.KrullSchmidtCancellation20260902

universe u v

variable {K : Type u} [Field K]
variable {Src Snk Arr : Type} [Fintype Src] [Fintype Snk] [Fintype Arr]
variable [DecidableEq Src] [DecidableEq Snk]

/-- A representation of the complete bipartite quiver `Src → Snk` with arrow set `Arr`. -/
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

/-- Block-diagonal simultaneous equivalence. -/
def BRep.SimEquiv (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W') : Prop :=
  ∃ (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t),
    ∀ a s t, (Q t : W t →ₗ[K] W' t) ∘ₗ A.f a s t = B.f a s t ∘ₗ (P s : V s →ₗ[K] V' s)

/-- Block direct sum. -/
def BRep.dsum (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W) :
    BRep K Src Snk Arr (fun s => DV s × V s) (fun t => DW t × W t) :=
  ⟨fun a s t => (D.f a s t).prodMap (A.f a s t)⟩

/-- The coefficient algebra. -/
abbrev R (K : Type u) [Field K] (Src Snk Arr : Type) : Type u :=
  FreeAlgebra K (Src ⊕ Snk ⊕ Arr × Src × Snk)

/-- The carrier. -/
abbrev Car (V : Src → Type v) (W : Snk → Type v) [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
    [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] : Type v :=
  (∀ s, V s) × (∀ t, W t)

/-- Generator actions. -/
def BRep.gen (A : BRep K Src Snk Arr V W) : Src ⊕ Snk ⊕ Arr × Src × Snk →
    Module.End K (Car (K := K) V W)
  | Sum.inl s => LinearMap.inl K _ _ ∘ₗ LinearMap.single K V s ∘ₗ LinearMap.proj s ∘ₗ LinearMap.fst K _ _
  | Sum.inr (Sum.inl t) =>
      LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t ∘ₗ LinearMap.proj t ∘ₗ LinearMap.snd K _ _
  | Sum.inr (Sum.inr (a, s, t)) =>
      LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t ∘ₗ A.f a s t ∘ₗ LinearMap.proj s ∘ₗ
        LinearMap.fst K _ _

theorem BRep.gen_src (A : BRep K Src Snk Arr V W) (s : Src) (m : Car (K := K) V W) :
    A.gen (Sum.inl s) m = (Pi.single s (m.1 s), 0) := rfl

theorem BRep.gen_snk (A : BRep K Src Snk Arr V W) (t : Snk) (m : Car (K := K) V W) :
    A.gen (Sum.inr (Sum.inl t)) m = (0, Pi.single t (m.2 t)) := rfl

theorem BRep.gen_arr (A : BRep K Src Snk Arr V W) (a : Arr) (s : Src) (t : Snk)
    (m : Car (K := K) V W) :
    A.gen (Sum.inr (Sum.inr (a, s, t))) m = (0, Pi.single t (A.f a s t (m.1 s))) := rfl

/-- The algebra map. -/
noncomputable def BRep.hom (A : BRep K Src Snk Arr V W) :
    R K Src Snk Arr →ₐ[K] Module.End K (Car (K := K) V W) :=
  FreeAlgebra.lift K A.gen

theorem BRep.hom_ι (A : BRep K Src Snk Arr V W) (g : Src ⊕ Snk ⊕ Arr × Src × Snk) :
    A.hom (FreeAlgebra.ι K g) = A.gen g :=
  FreeAlgebra.lift_ι_apply A.gen g

/-- The encoded module. -/
def BRep.M (_A : BRep K Src Snk Arr V W) : Type v := Car (K := K) V W

instance (A : BRep K Src Snk Arr V W) : AddCommGroup A.M :=
  inferInstanceAs (AddCommGroup (Car (K := K) V W))
instance (A : BRep K Src Snk Arr V W) : Module K A.M :=
  inferInstanceAs (Module K (Car (K := K) V W))
noncomputable instance (A : BRep K Src Snk Arr V W) : Module (R K Src Snk Arr) A.M :=
  Module.compHom (Car (K := K) V W) A.hom.toRingHom

theorem BRep.smul_def (A : BRep K Src Snk Arr V W) (r : R K Src Snk Arr) (m : A.M) :
    r • m = A.hom r m := rfl

instance (A : BRep K Src Snk Arr V W) : IsScalarTower K (R K Src Snk Arr) A.M :=
  ⟨fun c r m => by
    change A.hom (c • r) m = c • A.hom r m
    rw [map_smul]
    rfl⟩

/-- The identity of the carrier and `A.M`, as a `K`-linear equivalence. -/
def BRep.toM (A : BRep K Src Snk Arr V W) : Car (K := K) V W ≃ₗ[K] A.M := LinearEquiv.refl K _

theorem BRep.smul_ι (A : BRep K Src Snk Arr V W) (g : Src ⊕ Snk ⊕ Arr × Src × Snk) (m : A.M) :
    FreeAlgebra.ι K g • m = A.gen g m := by
  rw [BRep.smul_def, BRep.hom_ι]

instance (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : FiniteDimensional K A.M :=
  inferInstanceAs (FiniteDimensional K (Car (K := K) V W))

instance (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : IsArtinian (R K Src Snk Arr) A.M :=
  isArtinian_of_tower K (inferInstanceAs (IsArtinian K (Car (K := K) V W)))

instance (A : BRep K Src Snk Arr V W) [∀ s, FiniteDimensional K (V s)]
    [∀ t, FiniteDimensional K (W t)] : IsNoetherian (R K Src Snk Arr) A.M :=
  isNoetherian_of_tower K (inferInstanceAs (IsNoetherian K (Car (K := K) V W)))

end Defs

/-! ### `R`-linearity from generator commutation -/

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

/-- Upgrade a `K`-linear equivalence commuting with the generators to an `R`-linear one. -/
def LinearEquiv.ofGen (φ : M ≃ₗ[K] N)
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

/-! ### Simultaneous equivalence is `R`-isomorphism -/

section Iso

variable {V V' : Src → Type v} {W W' : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ t, AddCommGroup (W' t)]
  [∀ t, Module K (W' t)]

/-- The `K`-linear equivalence of carriers induced by `(P, Q)`. -/
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

/-- From `(P, Q)` to an `R`-isomorphism. -/
noncomputable def BRep.equivOfSim (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (P : ∀ s, V s ≃ₗ[K] V' s) (Q : ∀ t, W t ≃ₗ[K] W' t)
    (h : ∀ a s t, (Q t : W t →ₗ[K] W' t) ∘ₗ A.f a s t = B.f a s t ∘ₗ (P s : V s →ₗ[K] V' s)) :
    A.M ≃ₗ[R K Src Snk Arr] B.M :=
  LinearEquiv.ofGen (A.toM.symm ≪≫ₗ pqEquiv P Q ≪≫ₗ B.toM) (by
    intro g m
    rw [BRep.smul_ι, BRep.smul_ι]
    rcases g with s | t | ⟨a, s, t⟩
    · change pqEquiv P Q (Pi.single s (m.1 s), 0) =
        (Pi.single s ((pqEquiv P Q (A.toM.symm m)).1 s), 0)
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · exact single_map (fun s => (P s : V s →ₗ[K] V' s)) s (m.1 s)
      · funext t; simp
    · change pqEquiv P Q (0, Pi.single t (m.2 t)) =
        (0, Pi.single t ((pqEquiv P Q (A.toM.symm m)).2 t))
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · funext s; simp
      · exact single_map (fun t => (Q t : W t →ₗ[K] W' t)) t (m.2 t)
    · change pqEquiv P Q (0, Pi.single t (A.f a s t (m.1 s))) =
        (0, Pi.single t (B.f a s t ((pqEquiv P Q (A.toM.symm m)).1 s)))
      rw [pqEquiv_apply, pqEquiv_apply]
      refine Prod.ext ?_ ?_
      · funext s'; simp
      · refine (single_map (fun t => (Q t : W t →ₗ[K] W' t)) t (A.f a s t (m.1 s))).trans ?_
        have := LinearMap.congr_fun (h a s t) (m.1 s)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
        exact congrArg (Pi.single t) this)

/-- The source components of an `R`-isomorphism. -/
noncomputable def BRep.srcMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (s : Src) : V s →ₗ[K] V' s :=
  LinearMap.proj s ∘ₗ LinearMap.fst K _ _ ∘ₗ (B.toM.symm : B.M →ₗ[K] Car (K := K) V' W') ∘ₗ
    ((ψ.restrictScalars K : A.M ≃ₗ[K] B.M) : A.M →ₗ[K] B.M) ∘ₗ
    (A.toM : Car (K := K) V W →ₗ[K] A.M) ∘ₗ LinearMap.inl K _ _ ∘ₗ LinearMap.single K V s

/-- The sink components of an `R`-isomorphism. -/
noncomputable def BRep.snkMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (t : Snk) : W t →ₗ[K] W' t :=
  LinearMap.proj t ∘ₗ LinearMap.snd K _ _ ∘ₗ (B.toM.symm : B.M →ₗ[K] Car (K := K) V' W') ∘ₗ
    ((ψ.restrictScalars K : A.M ≃ₗ[K] B.M) : A.M →ₗ[K] B.M) ∘ₗ
    (A.toM : Car (K := K) V W →ₗ[K] A.M) ∘ₗ LinearMap.inr K _ _ ∘ₗ LinearMap.single K W t

theorem BRep.srcMap_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (s : Src) (v : V s) :
    A.srcMap B ψ s v = (ψ (A.toM (Pi.single s v, 0)) : Car (K := K) V' W').1 s := rfl

theorem BRep.snkMap_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (t : Snk) (w : W t) :
    A.snkMap B ψ t w = (ψ (A.toM (0, Pi.single t w)) : Car (K := K) V' W').2 t := rfl

/-- **Componentwise decomposition** of an `R`-isomorphism, from the vertex generators. -/
theorem BRep.equiv_apply (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (m : Car (K := K) V W) :
    (ψ (A.toM m) : Car (K := K) V' W') =
      (fun s => A.srcMap B ψ s (m.1 s), fun t => A.snkMap B ψ t (m.2 t)) := by
  refine Prod.ext ?_ ?_
  · funext s
    have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inl s)) (A.toM m)
    rw [BRep.smul_ι, BRep.smul_ι] at h
    change ψ (A.toM (Pi.single s (m.1 s), 0)) =
      (Pi.single s ((ψ (A.toM m) : Car (K := K) V' W').1 s), 0) at h
    show (ψ (A.toM m) : Car (K := K) V' W').1 s = A.srcMap B ψ s (m.1 s)
    rw [BRep.srcMap_apply, h]
    simp
  · funext t
    have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inr (Sum.inl t))) (A.toM m)
    rw [BRep.smul_ι, BRep.smul_ι] at h
    change ψ (A.toM (0, Pi.single t (m.2 t))) =
      (0, Pi.single t ((ψ (A.toM m) : Car (K := K) V' W').2 t)) at h
    show (ψ (A.toM m) : Car (K := K) V' W').2 t = A.snkMap B ψ t (m.2 t)
    rw [BRep.snkMap_apply, h]
    simp

theorem BRep.equiv_single_src (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (s : Src) (v : V s) :
    (ψ (A.toM (Pi.single s v, 0)) : Car (K := K) V' W') = (Pi.single s (A.srcMap B ψ s v), 0) := by
  rw [BRep.equiv_apply]
  refine Prod.ext ?_ ?_
  · exact single_map (fun s => A.srcMap B ψ s) s v
  · funext t; simp

theorem BRep.equiv_single_snk (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (t : Snk) (w : W t) :
    (ψ (A.toM (0, Pi.single t w)) : Car (K := K) V' W') = (0, Pi.single t (A.snkMap B ψ t w)) := by
  rw [BRep.equiv_apply]
  refine Prod.ext ?_ ?_
  · funext s; simp
  · exact single_map (fun t => A.snkMap B ψ t) t w

theorem BRep.srcMap_symm_srcMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (s : Src) (v : V s) :
    B.srcMap A ψ.symm s (A.srcMap B ψ s v) = v := by
  rw [BRep.srcMap_apply]
  have h : ψ.symm (B.toM (Pi.single s (A.srcMap B ψ s v), 0)) = A.toM (Pi.single s v, 0) := by
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg B.toM (A.equiv_single_src B ψ s v)).symm
  rw [h]
  exact Pi.single_eq_same s v

theorem BRep.snkMap_symm_snkMap (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) (t : Snk) (w : W t) :
    B.snkMap A ψ.symm t (A.snkMap B ψ t w) = w := by
  rw [BRep.snkMap_apply]
  have h : ψ.symm (B.toM (0, Pi.single t (A.snkMap B ψ t w))) = A.toM (0, Pi.single t w) := by
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg B.toM (A.equiv_single_snk B ψ t w)).symm
  rw [h]
  exact Pi.single_eq_same t w

/-- From an `R`-isomorphism to a block-diagonal simultaneous equivalence. -/
theorem BRep.simEquiv_of_equiv (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W')
    (ψ : A.M ≃ₗ[R K Src Snk Arr] B.M) : A.SimEquiv B := by
  refine ⟨fun s => LinearEquiv.ofLinear (A.srcMap B ψ s) (B.srcMap A ψ.symm s)
      (LinearMap.ext fun v => by
        have := B.srcMap_symm_srcMap A ψ.symm s v
        rwa [LinearEquiv.symm_symm] at this)
      (LinearMap.ext fun v => A.srcMap_symm_srcMap B ψ s v),
    fun t => LinearEquiv.ofLinear (A.snkMap B ψ t) (B.snkMap A ψ.symm t)
      (LinearMap.ext fun w => by
        have := B.snkMap_symm_snkMap A ψ.symm t w
        rwa [LinearEquiv.symm_symm] at this)
      (LinearMap.ext fun w => A.snkMap_symm_snkMap B ψ t w),
    fun a s t => ?_⟩
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply]
  have h := ψ.map_smul (FreeAlgebra.ι K (Sum.inr (Sum.inr (a, s, t)))) (A.toM (Pi.single s v, 0))
  rw [BRep.smul_ι, BRep.smul_ι] at h
  change ψ (A.toM (0, Pi.single t (A.f a s t ((Pi.single s v : ∀ s, V s) s)))) =
    (0, Pi.single t (B.f a s t ((ψ (A.toM (Pi.single s v, 0)) : Car (K := K) V' W').1 s))) at h
  rw [Pi.single_eq_same, A.equiv_single_snk B ψ, A.equiv_single_src B ψ] at h
  have h2 := congrArg (fun x : Car (K := K) V' W' => x.2 t) h
  simp only [Pi.single_eq_same] at h2
  exact h2

theorem BRep.simEquiv_iff_nonempty (A : BRep K Src Snk Arr V W) (B : BRep K Src Snk Arr V' W') :
    A.SimEquiv B ↔ Nonempty (A.M ≃ₗ[R K Src Snk Arr] B.M) :=
  ⟨fun ⟨P, Q, h⟩ => ⟨A.equivOfSim B P Q h⟩, fun ⟨ψ⟩ => A.simEquiv_of_equiv B ψ⟩

end Iso

/-! ### The direct sum is the product module -/

section DSum

variable {V DV : Src → Type v} {W DW : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (DV s)] [∀ s, Module K (DV s)] [∀ t, AddCommGroup (DW t)]
  [∀ t, Module K (DW t)]

/-- The carrier of a direct sum, regrouped as a product of carriers. -/
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

/-- `(D ⊞ A).M ≅ D.M × A.M` as `R`-modules. -/
noncomputable def BRep.dsumEquiv (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W) :
    (D.dsum A).M ≃ₗ[R K Src Snk Arr] (D.M × A.M) :=
  LinearEquiv.ofGen ((D.dsum A).toM.symm ≪≫ₗ carSplit ≪≫ₗ D.toM.prodCongr A.toM) (by
    intro g m
    rw [BRep.smul_ι]
    change carSplit ((D.dsum A).gen g m) =
      (FreeAlgebra.ι K g • D.toM (carSplit m).1, FreeAlgebra.ι K g • A.toM (carSplit m).2)
    rw [BRep.smul_ι, BRep.smul_ι]
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

/-! ### The cancellation theorem -/

section Cancel

variable {V V' DV : Src → Type v} {W W' DW : Snk → Type v}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)]
variable [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ t, AddCommGroup (W' t)]
  [∀ t, Module K (W' t)]
variable [∀ s, AddCommGroup (DV s)] [∀ s, Module K (DV s)] [∀ t, AddCommGroup (DW t)]
  [∀ t, Module K (DW t)]
variable [∀ s, FiniteDimensional K (DV s)] [∀ t, FiniteDimensional K (DW t)]

/-- **FGS block-equivalence cancellation.** A common block-direct summand cancels. -/
theorem bipartite_cancel (D : BRep K Src Snk Arr DV DW) (A : BRep K Src Snk Arr V W)
    (C : BRep K Src Snk Arr V' W') (h : (D.dsum A).SimEquiv (D.dsum C)) : A.SimEquiv C := by
  obtain ⟨ψ⟩ := (BRep.simEquiv_iff_nonempty _ _).mp h
  let e : (D.M × A.M) ≃ₗ[R K Src Snk Arr] (D.M × C.M) :=
    (D.dsumEquiv A).symm ≪≫ₗ ψ ≪≫ₗ D.dsumEquiv C
  obtain ⟨θ⟩ := cancel_of_finiteDimensional (R := R K Src Snk Arr) (K := K) _ D.M rfl A.M C.M e
  exact A.simEquiv_of_equiv C θ

end Cancel

#print axioms bipartite_cancel

end Mathproof.Meta.BipartiteCancellation20260902

end Part_U8


section Part_U9

/-
Copyright (c) 2026 MathProof. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProof
-/

/-!
# Lagrangian padding: the tensor-level core of `TI = TI_Sp`

## The problem, and where the novelty is NOT

Chen–Grochow–Qiao–Tang–Zhang, *On the complexity of isomorphism problems for tensors, groups, and
polynomials III: actions by classical groups* (ITCS 2024, arXiv:2306.03135) — hereafter CGQTZ —
introduce, for a family `G` of matrix groups, the class `TI_G` of problems polynomial-time reducible
to the `3`-tensor isomorphism problem over `G`, and ask:

> **Open Question 1.8.** Which, if any, of `TI_O`, `TI_U`, `TI_Sp` are equal to `TI`?

Two containments are at stake and they are **not** symmetric in provenance.

* `TI_Sp ⊆ TI` is **CGQTZ Theorem 1.4** — entirely prior art. Verbatim: *"Let
  `G = {G_n | G_n ≤ GL(n,F)}` be a group family preserving a polynomial-time-constructible family of
  bilinear forms, and consider one of the five actions of `GL` on 3-way arrays in Definition 1.2.
  The restricted `G`-isomorphism problem for this action reduces to the `GL`-isomorphism problem for
  this action."* They then write *"special cases of Theorem 1.4 can be reformulated as
  `TI_O, TI_Sp ⊆ TI_GL`."* **Nothing in this file re-proves or improves that direction.**

* `TI ⊆ TI_Sp` is the open one. It is what the Lagrangian-padding reduction below supplies, and it
  needs **both** implications of a single tensor-level equivalence

  `A ≅_{∏ GL(U_i)} B  ↔  Â ≅_{∏ Sp(H(U_i))} B̂`,   `H(U) = U ⊕ U*`,  `Â = (ι⊗ι⊗ι)A`.

  Of those two implications:
  - the `→` implication is the **Levi embedding** `P ↦ P ⊕ (P⁻¹)*`, i.e. the Levi subgroup of the
    Siegel parabolic of `Sp(U ⊕ U*)`. This is textbook, and CGQTZ have it in hand: they themselves
    record *"the matrix `A ⊕ B` … is symplectic iff `AB^t = I`"*. **It is not a contribution.**
    Formalized here as `levi_isSymplectic` / `levi_comp_iota`, with attribution.
  - the `←` implication is the **mode-support rigidity** argument. That is the only place where
    novelty can sit, and it is what `pad_reflect` and `msupp_padded_rigidity` below prove.

**THE SHARPEST PRIOR ART, AND IT IS SHARPER THAN THE `TI` LITERATURE.** Lysikov–Walter,
*Complexity theory of orbit closure intersection for tensors: reductions, completeness, and graph
isomorphism hardness* (arXiv:2411.04639, FOCS 2025),
[TITLE CORRECTED 2026-09-09: this line carried *"Optimization over trace polynomials … / orbit
closure intersection"*, which is a DIFFERENT paper (Klep–Magron–Volčič). The theorem numbers V.19
and V.25 and the quoted text below were and remain correct — only the title was wrong. Verified
against the PDF title page at `D:/Proof/papers/cgqtz3-citations/arxiv_2411.04639.pdf`.]
**Theorem V.19** constructs exactly this padding. Verbatim from their proof: *"let `W_i = V_i ⊕ V_i^*`
… For `f ∈ GL(V_i)` we have `f ⊕ (f^*)^{-1} ∈ O(W_i)`, which gives a homomorphism
`κ_i : GL(V_i) → O(W_i)` … Let `ι_i : V_i → W_i` be the inclusions … The map `Φ` is equivariant with
respect to `κ` and hence it **preserves** closure equivalence … To see that it also **reflects**
closure equivalence, consider any contraction invariant …"*, and the remark before their
**Theorem V.25** (`TOCI_Sp = TOCI`): *"In Theorem V.19 the symplectic form on `U_i = V_i ⊕ V_i^*`
can be defined as `g((v₁,w₁),(v₂,w₂)) = w₁·v₂ − w₂·v₁`."* That is `Hyp`, `iota`, `levi` and `omegaH`
of this file, verbatim, one year earlier, in greater generality (arbitrary mixed co/contravariant
formats).

So: **the construction, the space, the form, the group homomorphism, and the `preserves` half are
ALL published.** What is not published is the `reflects` half **for exact orbit equivalence**: their
argument reflects *closure* equivalence via contraction invariants, and invariants cannot separate
orbits inside a fibre of the quotient map, so it does not transfer. The mode-support argument does
exactly and only that missing step. Any write-up must lead with this, not bury it.

## What this file machine-checks

Everything is over an arbitrary field, in every characteristic, with no conciseness assumption.

1. `Hyp K U = U × Module.Dual K U` with `omegaH ((u,α),(v,β)) = β u − α v`: bilinear
   (`omegaH` is built as a `LinearMap.mk₂`), **alternating** (`omegaH_self`, so the form is
   symplectic in characteristic `2` as well as elsewhere), and **nondegenerate**
   (`omegaH_nondegenerate`).
2. `iota u = (u, 0)` is injective, its image is **isotropic** (`iota_isotropic`) and **maximal**
   isotropic, i.e. Lagrangian (`mem_range_iota_of_omegaH_eq_zero`).
3. The **Levi lift** `levi P = P ⊕ (P.symm).dualMap` is symplectic (`levi_isSymplectic`),
   intertwines `iota` (`levi_comp_iota`), and `levi` is an injective monoid homomorphism
   `GL(U) ↪ Sp(H U)` (`levi_one`, `levi_trans`, `levi_injective`). *(Prior art; see above.)*
4. **Mode support.** `contract T : Dual K X →ₗ V` for `T : V ⊗[K] X`, and
   `msupp T = range (contract T)`. Proved: naturality (`contract_map`), equivariance with equality
   for injective second factor (`msupp_map`), and — the fact that makes the whole argument work —
   `contract` is **injective** when `X` is finite dimensional (`contract_injective`), whence
   `msupp T = ⊥ → T = 0` (`eq_zero_of_msupp_eq_bot`; only this direction is proved, and only this
   direction is used) and the *support-determines-the-value* lemma `map_eq_of_eqOn_msupp`.
5. **Rigidity (the `←` implication's engine).** `msupp_padded_rigidity`: if the padded tensors are
   related by `(g ⊗ k)`, then `g` carries `ι(S(A))` **onto** `ι(S(B))`. So a symplectic transporter,
   free to mix `U` with `U*` anywhere else, is pinned on the tensor's actual support.
6. `pad_reflect`: the rigidity is upgraded to an honest `P ∈ GL(U)` with `g ∘ ι = ι ∘ P` on the
   support, using `Submodule.exists_linearEquiv_restrict_eq` for the extension off the support.
7. **Both implications for `3`-tensors.** The forward implication is `padded_of_gl`. The reverse is
   assembled by the mode-specialized L8--L10 substitution lemmas and L11 cancellation theorem as
   `gl_of_padded`. The unconditional equivalence is `gl_iff_padded`.

## Boundary of this formalization

This file now proves all algebraic content of the new base-problem reduction and the abstract
class-transitivity assembly. It does not formalize Turing machines or re-prove the cited CGQTZ
theorem.

1. `OPEN_pad_is_kernel_reduction` is retained as a historical API name, but its entire
   instance-wise correctness content is discharged by `pad_is_kernel_reduction_instancewise`.
   The coordinate map and its running-time audit are supplied in the accompanying proof note.
2. CGQTZ fix the skew form
   `φ(u,v) = ∑_{i∈[n]}(u_i v_{2n−i+1} − u_{n+i} v_{n−i+1})` on `F^{2n}` and set
   `Sp(2n,F) = G(F^{2n}, φ)`, whereas the padding produces the hyperbolic form `ω` on `U ⊕ U*`. The
   Gram matrix of `ω` in the basis `(e_1,…,e_n,e_1^*,…,e_n^*)` is `[[0,I],[−I,0]]` and that of `φ`
   is `[[0,J],[−J,0]]` with `J` the reversal permutation, so `diag(I,J)` carries one to the other
   and the transported instance stays a `{0,1}`-projection. Abstract group conjugacy is proved by
   `basisChange_of_congruent_forms`; `standardCoordEquiv_isometry` now checks the complete bridge
   from the abstract dual-space model to CGQTZ's fixed coordinate form, and
   `standardCoordEquiv_iota` checks that padding remains literal zero-padding through this bridge.

The other base reduction, `Sp3TI ≤ GL3TI`, is CGQTZ Theorem 1.4 and is used by citation. Given the
two base reductions, `ti_eq_tisp_from_base_reductions` checks the class equality abstractly.

## Honesty notes

* Nothing here is verified "at small `n`": every statement is a general theorem over an arbitrary
  field. The risk on this line is prior art and definition-matching, not induction on dimension.
* **Definitional check, resolved from the paper text (not a search summary).** CGQTZ Definition 1.2,
  action (1), verbatim: *"Given `A ∈ T(l × m × n, F)`, `(P,Q,R) ∈ GL(l,F) × GL(m,F) × GL(n,F)` sends
  `A` to `(P,Q,R)·A`"*, and Theorem 1.4 restricts exactly this action to `G`. So the acting group is
  a **direct product of three independent per-mode elements**, which is what the padding needs; the
  symplectic form does **not** couple the modes. The Lean statements below use three independent
  elements, matching that.
* Lysikov–Walter (arXiv:2411.04639) prove `TOCI_O = TOCI_Sp = TOCI` for **orbit-closure
  intersection**, one year earlier. That is a different equivalence relation, but the *result shape*
  is not novel and any write-up must say so up front.
-/

namespace Mathproof.SymplecticTI

open TensorProduct

/-! ## 1. The hyperbolic double and its symplectic form -/

section Hyperbolic

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

/-- The hyperbolic double `H(U) = U ⊕ U*` of a vector space. -/
abbrev Hyp (K : Type*) [Field K] (U : Type*) [AddCommGroup U] [Module K U] :=
  U × Module.Dual K U

/-- The canonical symplectic form on `H(U)`: `ω((u,α),(v,β)) = β u − α v`.

Bilinearity is part of the definition (`LinearMap.mk₂`); alternation and nondegeneracy are
`omegaH_self` and `omegaH_nondegenerate` below. -/
noncomputable def omegaH : Hyp K U →ₗ[K] Hyp K U →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => y.2 x.1 - x.2 y.1)
    (fun x₁ x₂ y => by simp; ring)
    (fun c x y => by simp [mul_sub])
    (fun x y₁ y₂ => by simp; ring)
    (fun x c y => by simp [mul_sub])

@[simp] theorem omegaH_apply (x y : Hyp K U) : omegaH x y = y.2 x.1 - x.2 y.1 := rfl

/-- **The form is alternating**, in every characteristic — including `2`, where "alternating" is
strictly stronger than "skew-symmetric". -/
@[simp] theorem omegaH_self (x : Hyp K U) : omegaH x x = 0 := sub_self _

theorem omegaH_skew (x y : Hyp K U) : omegaH x y = -omegaH y x := by simp

/-- **The form is nondegenerate.** -/
theorem omegaH_nondegenerate (x : Hyp K U) (h : ∀ y, omegaH x y = 0) : x = 0 := by
  have h1 : x.1 = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff K x.1).mp fun β => ?_
    have := h (0, β)
    simpa using this
  have h2 : x.2 = 0 := by
    ext v
    have := h (v, 0)
    simpa using this
  exact Prod.ext h1 h2

/-- A linear automorphism of `H(U)` is symplectic when it preserves `ω`. -/
def IsSymplectic (g : Hyp K U ≃ₗ[K] Hyp K U) : Prop :=
  ∀ x y, omegaH (g x) (g y) = omegaH x y

theorem isSymplectic_one : IsSymplectic (LinearEquiv.refl K (Hyp K U)) := fun _ _ => rfl

theorem IsSymplectic.trans {g h : Hyp K U ≃ₗ[K] Hyp K U} (hg : IsSymplectic g)
    (hh : IsSymplectic h) : IsSymplectic (g ≪≫ₗ h) := fun x y => by
  simpa using (hh (g x) (g y)).trans (hg x y)

/-- The Lagrangian embedding `ι : U → H(U)`, `u ↦ (u,0)`. -/
def iota : U →ₗ[K] Hyp K U := LinearMap.inl K U (Module.Dual K U)

@[simp] theorem iota_apply (u : U) : (iota u : Hyp K U) = (u, 0) := rfl

theorem iota_injective : Function.Injective (iota : U →ₗ[K] Hyp K U) :=
  LinearMap.inl_injective

/-- `ι(U)` is isotropic. -/
@[simp] theorem iota_isotropic (u v : U) : omegaH (iota u : Hyp K U) (iota v) = 0 := by simp

/-- `ι(U)` is **maximal** isotropic, i.e. Lagrangian: anything `ω`-orthogonal to all of `ι(U)`
already lies in `ι(U)`. -/
theorem mem_range_iota_of_omegaH_eq_zero (x : Hyp K U) (h : ∀ v : U, omegaH x (iota v) = 0) :
    ∃ u : U, x = iota u := by
  refine ⟨x.1, ?_⟩
  have hx2 : x.2 = 0 := by
    ext v
    have := h v
    simpa using this
  exact Prod.ext rfl (by simpa using hx2)

/-! ### The Levi lift — PRIOR ART (the Levi subgroup of the Siegel parabolic) -/

/-- **The Levi lift** `P ↦ P ⊕ (P⁻¹)^*`, the standard embedding `GL(U) ↪ Sp(U ⊕ U*)`.

**Attribution.** This is the Levi subgroup of the Siegel parabolic; it is textbook and CGQTZ have it
in hand (they state the `A ⊕ B` symplectic-iff-`AB^t = I` criterion themselves). It is formalized
here because the padding argument consumes it, **not** as a contribution. -/
def levi (P : U ≃ₗ[K] U) : Hyp K U ≃ₗ[K] Hyp K U :=
  LinearEquiv.prodCongr P P.symm.dualMap

@[simp] theorem levi_apply (P : U ≃ₗ[K] U) (x : Hyp K U) :
    levi P x = (P x.1, P.symm.dualMap x.2) := rfl

/-- The Levi lift preserves `ω`. (Prior art; see the attribution on `levi`.) -/
theorem levi_isSymplectic (P : U ≃ₗ[K] U) : IsSymplectic (levi P) := by
  intro x y
  simp [LinearEquiv.dualMap_apply]

/-- The Levi lift intertwines the padding: `levi P ∘ ι = ι ∘ P`. -/
@[simp] theorem levi_iota (P : U ≃ₗ[K] U) (u : U) :
    levi P (iota u : Hyp K U) = iota (P u) := by
  simp [iota]

theorem levi_comp_iota (P : U ≃ₗ[K] U) :
    (levi P : Hyp K U →ₗ[K] Hyp K U) ∘ₗ (iota : U →ₗ[K] Hyp K U)
      = (iota : U →ₗ[K] Hyp K U) ∘ₗ (P : U →ₗ[K] U) :=
  LinearMap.ext fun u => levi_iota P u

theorem levi_one : levi (LinearEquiv.refl K U) = LinearEquiv.refl K (Hyp K U) :=
  LinearEquiv.ext fun _ => Prod.ext rfl (LinearMap.ext fun _ => rfl)

theorem levi_trans (P Q : U ≃ₗ[K] U) : levi (P ≪≫ₗ Q) = levi P ≪≫ₗ levi Q :=
  LinearEquiv.ext fun _ => Prod.ext rfl (LinearMap.ext fun _ => rfl)

theorem levi_injective : Function.Injective (levi : (U ≃ₗ[K] U) → Hyp K U ≃ₗ[K] Hyp K U) := by
  intro P Q h
  ext u
  have := congrArg (fun f => (f (iota u : Hyp K U)).1) h
  simpa using this

end Hyperbolic

/-! ## 2. Mode support of a tensor -/

section ModeSupport

variable {K : Type*} [Field K]
variable {V W X Y : Type*}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- `evalSmul x v : Dual K X →ₗ V` is `φ ↦ φ x • v`. -/
def evalSmul (x : X) (v : V) : Module.Dual K X →ₗ[K] V where
  toFun φ := φ x • v
  map_add' φ ψ := by simp [add_smul]
  map_smul' c φ := by simp [smul_smul]

@[simp] theorem evalSmul_apply (x : X) (v : V) (φ : Module.Dual K X) :
    evalSmul x v φ = φ x • v := rfl

/-- The bilinear map underlying the contraction. -/
noncomputable def contractBil : V →ₗ[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  LinearMap.mk₂ K (fun v x => evalSmul x v)
    (fun v w x => by ext φ; simp [smul_add])
    (fun c v x => by ext φ; exact smul_comm _ _ _)
    (fun v x y => by ext φ; simp [add_smul])
    (fun v c x => by ext φ; simp [smul_smul])

/-- **Contraction in all modes but the first.** For `T : V ⊗ X`, `contract T : Dual K X →ₗ V`.
Its range is the mode support of `T` in the `V` slot. -/
noncomputable def contract : V ⊗[K] X →ₗ[K] (Module.Dual K X →ₗ[K] V) :=
  TensorProduct.lift contractBil

@[simp] theorem contract_tmul (v : V) (x : X) (φ : Module.Dual K X) :
    contract (v ⊗ₜ[K] x) φ = φ x • v := rfl

/-- **Naturality of contraction.** -/
theorem contract_map (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) (φ : Module.Dual K Y) :
    contract (TensorProduct.map f g T) φ = f (contract T (g.dualMap φ)) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [LinearMap.dualMap_apply]
  | add a b ha hb => simp [ha, hb]

/-- **The mode support** of `T : V ⊗ X` in the `V` slot: the image of the contraction against the
remaining modes.

It is a standard fact that this is the smallest subspace `S ≤ V` with `T ∈ S ⊗ X`; that
characterisation is **not proved here and is not used anywhere below**. Everything downstream runs
off `contract_injective` instead, so no unproved minimality claim is load-bearing. -/
noncomputable def msupp (T : V ⊗[K] X) : Submodule K V := LinearMap.range (contract T)

theorem mem_msupp (T : V ⊗[K] X) (φ : Module.Dual K X) : contract T φ ∈ msupp T :=
  LinearMap.mem_range_self _ _

theorem msupp_map_le (f : V →ₗ[K] W) (g : X →ₗ[K] Y) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) ≤ (msupp T).map f := by
  rintro w ⟨φ, rfl⟩
  exact ⟨contract T (g.dualMap φ), mem_msupp _ _, (contract_map f g T φ).symm⟩

/-- **Mode-support equivariance.** For `g` injective on the *other* modes the containment is an
equality. Both uses below have `g` injective (a padding, or a group element). -/
theorem msupp_map (f : V →ₗ[K] W) {g : X →ₗ[K] Y} (hg : Function.Injective g) (T : V ⊗[K] X) :
    msupp (TensorProduct.map f g T) = (msupp T).map f := by
  refine le_antisymm (msupp_map_le f g T) ?_
  rintro w ⟨v, ⟨ψ, rfl⟩, rfl⟩
  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective hg ψ
  exact ⟨φ, by rw [contract_map f g T φ, hφ]⟩

/-! ### Sealed API for the mode support (stated before the `irreducible` attribute below)

Everything downstream of the seal can only bound `msupp` from below through `mem_msupp`. The
rank calculus of the FGS gadget (sub-additivity, pure tensors have rank `≤ 1`, restriction to a
block) needs the upper bounds too, so they are proved here once, while unfolding is still
allowed, and exported as ordinary theorems. -/

theorem msupp_eq_range (T : V ⊗[K] X) : msupp T = LinearMap.range (contract T) := rfl

theorem mem_msupp_iff (T : V ⊗[K] X) (v : V) : v ∈ msupp T ↔ ∃ φ, contract T φ = v :=
  LinearMap.mem_range

theorem msupp_le_iff (T : V ⊗[K] X) (Q : Submodule K V) :
    msupp T ≤ Q ↔ ∀ φ : Module.Dual K X, contract T φ ∈ Q := by
  constructor
  · intro h φ
    exact h (mem_msupp T φ)
  · rintro h _ ⟨φ, rfl⟩
    exact h φ

theorem contract_zero : contract (0 : V ⊗[K] X) = 0 := map_zero _

theorem contract_add (S T : V ⊗[K] X) : contract (S + T) = contract S + contract T :=
  map_add _ _ _

theorem contract_smul (c : K) (T : V ⊗[K] X) : contract (c • T) = c • contract T :=
  map_smul _ _ _

theorem contract_sum {ι : Type*} (s : Finset ι) (T : ι → V ⊗[K] X) :
    contract (∑ i ∈ s, T i) = ∑ i ∈ s, contract (T i) :=
  map_sum _ _ _

theorem msupp_zero : msupp (0 : V ⊗[K] X) = ⊥ := by
  rw [msupp_eq_range, contract_zero, LinearMap.range_zero]

theorem msupp_add_le (S T : V ⊗[K] X) : msupp (S + T) ≤ msupp S ⊔ msupp T := by
  rw [msupp_le_iff]
  intro φ
  rw [contract_add, LinearMap.add_apply]
  exact Submodule.add_mem_sup (mem_msupp S φ) (mem_msupp T φ)

theorem msupp_smul_le (c : K) (T : V ⊗[K] X) : msupp (c • T) ≤ msupp T := by
  rw [msupp_le_iff]
  intro φ
  rw [contract_smul, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (mem_msupp T φ)

theorem msupp_sum_le {ι : Type*} (s : Finset ι) (T : ι → V ⊗[K] X) :
    msupp (∑ i ∈ s, T i) ≤ ⨆ i ∈ s, msupp (T i) := by
  rw [msupp_le_iff]
  intro φ
  rw [contract_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi (mem_msupp (T i) φ))

theorem msupp_tmul_le (v : V) (x : X) : msupp (v ⊗ₜ[K] x) ≤ K ∙ v := by
  rw [msupp_le_iff]
  intro φ
  rw [contract_tmul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem msupp_tmul_of_ne' (v : V) {x : X} (hx : ∃ φ : Module.Dual K X, φ x ≠ 0) :
    msupp (v ⊗ₜ[K] x) = K ∙ v := by
  refine le_antisymm (msupp_tmul_le v x) ?_
  rw [Submodule.span_singleton_le_iff_mem, mem_msupp_iff]
  obtain ⟨φ, hφ⟩ := hx
  refine ⟨(φ x)⁻¹ • φ, ?_⟩
  rw [contract_tmul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ, one_smul]

/-! ### Injectivity of the contraction -/

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

/-- **The contraction is injective** when the remaining modes are finite dimensional. This is what
turns "the mode supports agree" into "the tensors agree". -/
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

/-- **The support determines the value.** Two maps that agree on the mode support of `T` have the
same effect on `T`, whatever they do elsewhere. This replaces the informal step "`A` lies in the
tensor product of its mode supports". -/
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

/-! ### Sealing `contract` and `msupp`

Everything above this line is the API; nothing below it may unfold either definition. This is not
cosmetic. `contract` is a `TensorProduct.lift`, so its delta-reduction opens the free-module /
`AddCon` quotient machinery, and any unifier that tries to `whnf` a `msupp` term walks into it. With
the definitions transparent, a single application of `pad_reflect` or of `map_eq_of_eqOn_msupp` at
the padded `3`-tensor types exhausted 4,000,000 heartbeats (measured, isolated in a probe file:
the `spAct`/`pad3` delta and the `Module.Flat` instance searches were all fast; every timeout was on
a goal mentioning `msupp`). Sealed, the same applications are immediate.

NOTE FOR MAINTAINERS: this must be a `/-! -/` module comment, not a `/-- -/` docstring — a doc
comment may only precede a declaration, and `attribute` is not one. Written as a docstring it is a
parse error, the `attribute` command silently never runs, and the file merely gets slow again. -/
attribute [irreducible] contract msupp

end ModeSupport

/-! ## 3. Rigidity of a padded symplectic transporter — the novel half -/

section Rigidity

variable {K : Type*} [Field K]
variable {U H X Y : Type*}
variable [AddCommGroup U] [Module K U] [AddCommGroup H] [Module K H]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- **Mode-support rigidity.**

`ι` pads mode `1`; `j` pads all the remaining modes; `(g, k)` transports the padded tensor of `A`
to the padded tensor of `B`. Conclusion: `g` carries `ι(S(A))` **onto** `ι(S(B))`.

This is the engine of the reverse implication `Â ≅_Sp B̂ → A ≅_GL B`. A symplectic `g` is free to
mix `U` with `U*` anywhere in `H`; the point is that it cannot do so **on the tensor's actual mode
support**, because the target tensor's support lies in the Lagrangian.

No conciseness hypothesis is used: `msupp A` may be a proper subspace of `U`. -/
theorem msupp_padded_rigidity
    (ι : U →ₗ[K] H) {j : X →ₗ[K] Y} (hj : Function.Injective j)
    (g : H →ₗ[K] H) {k : Y →ₗ[K] Y} (hk : Function.Injective k)
    (A B : U ⊗[K] X)
    (hAB : TensorProduct.map g k (TensorProduct.map ι j A) = TensorProduct.map ι j B) :
    ((msupp A).map ι).map g = (msupp B).map ι := by
  have h1 := msupp_map g hk (TensorProduct.map ι j A)
  rw [msupp_map ι hj A] at h1
  rw [← h1, hAB, msupp_map ι hj B]

/-- **Reflection.** The rigidity statement upgraded to an honest element of `GL(U)` that agrees with
the transporter on the mode support. What the extension does off the support is arbitrary — that is
precisely why no conciseness assumption is needed: the tensor never sees it. -/
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

/-- **Substitution.** `pad_reflect` composed with `map_eq_of_eqOn_msupp`: the transporter `g` may be
replaced by an honest `P ∈ GL(U)` *inside the tensor*, for any map `m` on the remaining modes.

This is the form every application below uses, and the reason it exists is not aesthetic: its
statement does not mention `msupp`, so unifying against it never puts a `msupp` term in front of the
elaborator. Stating the two halves separately and composing them at the call site cost 4,000,000
heartbeats per application. -/
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

/-- A typed package saying that `g ∘ ι` agrees on the intrinsic support of `A` with the
Lagrangian lift of an ordinary automorphism. Keeping this package opaque to later unification
prevents `msupp` from being normalized at deeply nested tensor types. -/
structure SupportLiftWitness
    (A : U ⊗[K] X) (ι : U →ₗ[K] H) (g : H →ₗ[K] H) where
  P : U ≃ₗ[K] U
  agree : ∀ u ∈ msupp A, g (ι u) = ι (P u)

/-- Substitute a packaged support lift inside a tensor. This is `map_eq_of_eqOn_msupp` with an
interface that stays small when `X` is itself a nested tensor product. -/
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

end Rigidity

/-! ## 4. The two implications for `3`-tensors -/

section ThreeTensor

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ W₁ W₂ W₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]
  [AddCommGroup W₃] [Module K W₃]

/-- **The `GL`-action on `3`-tensors with three independent per-mode elements.**

This matches CGQTZ Definition 1.2, action (1) verbatim: *"Given `A ∈ T(l × m × n, F)`,
`(P,Q,R) ∈ GL(l,F) × GL(m,F) × GL(n,F)` sends `A` to `(P,Q,R)·A`"*. The three elements are
independent — that is the definitional point on which the whole padding reduction turns. -/
noncomputable def glAct (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] U₁ ⊗[K] (U₂ ⊗[K] U₃) :=
  TensorProduct.map (P₁ : U₁ →ₗ[K] U₁)
    (TensorProduct.map (P₂ : U₂ →ₗ[K] U₂) (P₃ : U₃ →ₗ[K] U₃))

/-- The same action shape on the padded format, with three independent elements of the symplectic
groups `Sp(H(U_i), ω)`. CGQTZ Theorem 1.4 restricts exactly action (1) to a form-preserving `G`. -/
noncomputable def spAct (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃) :
    Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) →ₗ[K]
      Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) :=
  TensorProduct.map (g₁ : Hyp K U₁ →ₗ[K] Hyp K U₁)
    (TensorProduct.map (g₂ : Hyp K U₂ →ₗ[K] Hyp K U₂) (g₃ : Hyp K U₃ →ₗ[K] Hyp K U₃))

/-- **The Lagrangian padding** `A ↦ Â = (ι ⊗ ι ⊗ ι)A`. Every coordinate of `Â` is a coordinate of
`A` or `0`, and every side length doubles: `n_i ↦ 2 n_i`. -/
noncomputable def pad3 :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] Hyp K U₁ ⊗[K] (Hyp K U₂ ⊗[K] Hyp K U₃) :=
  TensorProduct.map iota (TensorProduct.map iota iota)

theorem pad3_injective :
    Function.Injective (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _) :=
  TensorProduct.map_injective_of_flat_flat _ _ iota_injective
    (TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective)

/-! ### The forward implication (PRIOR ART: the Levi embedding) -/

/-- `Sp`-conjugation by Levi lifts is padding-equivariant. **Prior art** — this is the Levi subgroup
of the Siegel parabolic; see the module docstring. -/
theorem spAct_levi_comp_pad3 (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃) :
    spAct (levi P₁) (levi P₂) (levi P₃) ∘ₗ (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _)
      = (pad3 : U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] _) ∘ₗ glAct P₁ P₂ P₃ := by
  simp only [spAct, pad3, glAct, ← TensorProduct.map_comp, levi_comp_iota]

/-- **Forward implication**: `A ≅_GL B → Â ≅_Sp B̂`, with the explicit symplectic witnesses. -/
theorem padded_of_gl (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) (h : glAct P₁ P₂ P₃ A = B) :
    spAct (levi P₁) (levi P₂) (levi P₃) (pad3 A) = pad3 B := by
  have := DFunLike.congr_fun (spAct_levi_comp_pad3 P₁ P₂ P₃) A
  simpa [h] using this

/-! ### Mode braidings -/

/-- Move mode `2` to the front. -/
noncomputable def braid2 (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) ≃ₗ[K] U₂ ⊗[K] (U₁ ⊗[K] U₃) :=
  (TensorProduct.assoc K U₁ U₂ U₃).symm ≪≫ₗ
    TensorProduct.congr (TensorProduct.comm K U₁ U₂) (LinearEquiv.refl K U₃) ≪≫ₗ
    TensorProduct.assoc K U₂ U₁ U₃

/-- Move mode `3` to the front. -/
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

/-- **L4: padding preserves all three intrinsic mode supports.**

The first identity is the mode-`1` support statement directly. The second and third move the
corresponding mode to the front, which is how `msupp` represents the other two mode supports.
No finite-dimensionality hypothesis is needed: the result is just mode-support covariance under
the injective Lagrangian embeddings. -/
theorem pad3_msupp_all_modes (A : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    msupp (K := K) (V := Hyp K U₁) (X := Hyp K U₂ ⊗[K] Hyp K U₃) (pad3 A) =
      (msupp (K := K) (V := U₁) (X := U₂ ⊗[K] U₃) A).map
        (iota : U₁ →ₗ[K] Hyp K U₁) ∧
    msupp (K := K) (V := Hyp K U₂) (X := Hyp K U₁ ⊗[K] Hyp K U₃)
        (braid2 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃) (pad3 A)) =
      (msupp (K := K) (V := U₂) (X := U₁ ⊗[K] U₃)
        (braid2 K U₁ U₂ U₃ A)).map (iota : U₂ →ₗ[K] Hyp K U₂) ∧
    msupp (K := K) (V := Hyp K U₃) (X := Hyp K U₁ ⊗[K] Hyp K U₂)
        (braid3 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃) (pad3 A)) =
      (msupp (K := K) (V := U₃) (X := U₁ ⊗[K] U₂)
        (braid3 K U₁ U₂ U₃ A)).map (iota : U₃ →ₗ[K] Hyp K U₃) := by
  have hrest₂₃ : Function.Injective
      (TensorProduct.map (iota : U₂ →ₗ[K] Hyp K U₂) (iota : U₃ →ₗ[K] Hyp K U₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  have hrest₁₃ : Function.Injective
      (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁) (iota : U₃ →ₗ[K] Hyp K U₃)) :=
    TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  have hrest₁₂ : Function.Injective
      (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁) (iota : U₂ →ₗ[K] Hyp K U₂)) :=
    TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective
  constructor
  · simpa only [pad3] using
      (msupp_map (iota : U₁ →ₗ[K] Hyp K U₁) hrest₂₃ A)
  constructor
  · rw [show braid2 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃) (pad3 A) =
        TensorProduct.map (iota : U₂ →ₗ[K] Hyp K U₂)
          (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁)
            (iota : U₃ →ₗ[K] Hyp K U₃)) (braid2 K U₁ U₂ U₃ A) by
      simpa only [pad3] using
        (braid2_map (iota : U₁ →ₗ[K] Hyp K U₁)
          (iota : U₂ →ₗ[K] Hyp K U₂)
          (iota : U₃ →ₗ[K] Hyp K U₃) A)]
    exact msupp_map (iota : U₂ →ₗ[K] Hyp K U₂) hrest₁₃
      (braid2 K U₁ U₂ U₃ A)
  · rw [show braid3 K (Hyp K U₁) (Hyp K U₂) (Hyp K U₃) (pad3 A) =
        TensorProduct.map (iota : U₃ →ₗ[K] Hyp K U₃)
          (TensorProduct.map (iota : U₁ →ₗ[K] Hyp K U₁)
            (iota : U₂ →ₗ[K] Hyp K U₂)) (braid3 K U₁ U₂ U₃ A) by
      simpa only [pad3] using
        (braid3_map (iota : U₁ →ₗ[K] Hyp K U₁)
          (iota : U₂ →ₗ[K] Hyp K U₂)
          (iota : U₃ →ₗ[K] Hyp K U₃) A)]
    exact msupp_map (iota : U₃ →ₗ[K] Hyp K U₃) hrest₁₂
      (braid3 K U₁ U₂ U₃ A)

/-! ### The reverse implication — mode-support rigidity. THIS IS THE NOVEL HALF. -/

variable [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃]

omit [FiniteDimensional K U₁] [FiniteDimensional K U₃] in
/-- **L6: extract the ordinary mode-`2` transporter.**

If three invertible maps carry the padded tensor `A` to the padded tensor `B`, then the mode-`2`
map agrees on the intrinsic mode-`2` support of `A` with the Lagrangian lift of some
`P₂ ∈ GL(U₂)`. The proof braids mode `2` to the front, obtains the exact support equality by
mode-support covariance, descends through `iota`, and extends the resulting subspace equivalence.

This specialized proof deliberately performs the short support argument explicitly. Applying the
more general `pad_reflect` directly at these nested tensor types triggers a Lean elaborator
blow-up, even though the mathematical argument is identical. -/
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
/-- **L7: extract the ordinary mode-`3` transporter.**

This is the mode-`3` counterpart of `pad3_mode2_reflect`: braid mode `3` to the front, use
mode-support covariance to identify the transported padded support, descend that equivalence
through `iota`, and extend it to `P₃ ∈ GL(U₃)`. As in L6, the support argument is specialized
explicitly to avoid the generic elaboration blow-up. -/
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
/-- Extract the ordinary mode-`1` transporter. This is the unbraided counterpart of
`pad3_mode2_reflect` and `pad3_mode3_reflect`, specialized explicitly for predictable
elaboration. -/
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

/-- **L8: substitute the ordinary transporter in mode `1`.**

The other two modes retain their original padded transporter maps, giving the first equality in
the three-step substitution chain. -/
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

/-- **L9: substitute the ordinary transporter in mode `2`.**

The statement is uniform in the map already chosen for mode `1`, so it composes directly after
L8. The proof performs the support substitution after `braid2` and then unbraids. -/
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

/-- **L10: substitute the ordinary transporter in mode `3`.**

The statement is uniform in the maps already chosen for modes `1` and `2`, so it is the final
link in the substitution chain. The proof substitutes after `braid3` and then unbraids. -/
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
/-- **L11: normalize the fully substituted action and cancel padding.**

Once all three padded mode maps have been replaced by Lagrangian lifts, functoriality identifies
the result with `pad3 (glAct P₁ P₂ P₃ A)`. Injectivity of `pad3` then reflects the equality. -/
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

/-- **The reverse three-mode implication.** L8, L9, and L10 replace the three maps successively;
L11 normalizes the resulting Lagrangian lifts and cancels the injective padding. -/
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

/-! ### The reverse implication — discharged three-mode assembly

The direct application of generic `pad_reflect` at nested three-tensor types caused a deterministic
Lean unifier blow-up. The checked implementation above avoids it by using three small specialized
support-extraction lemmas, packaging each agreement as `SupportLiftWitness`, and substituting one
mode at a time. `gl_of_padded` then composes L8--L10, while `pad3_cancel_substituted` (L11)
normalizes and cancels the padding.

The proposition name below is retained for compatibility with files written while the assembly was
open. It is discharged immediately after its definition. -/

/-- The three-mode reverse implication, retained under its historical `OPEN_` API name. -/
def OPEN_gl_of_padded (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃]
    [FiniteDimensional K U₁] [FiniteDimensional K U₂] [FiniteDimensional K U₃] : Prop :=
  ∀ (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃))
    (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
    (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃),
    spAct g₁ g₂ g₃ (pad3 A) = pad3 B →
      ∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B

/-- The historical assembly proposition is now discharged by `gl_of_padded`. -/
theorem OPEN_gl_of_padded_proved : OPEN_gl_of_padded K U₁ U₂ U₃ := by
  intro A B g₁ g₂ g₃ hAB
  exact gl_of_padded A B g₁ g₂ g₃ hAB

/-- **The tensor-level equivalence, with its one hypothesis stated INLINE.**

`A` and `B` are isomorphic under three independent elements of the general linear groups **iff**
their Lagrangian paddings are isomorphic under three independent elements of the symplectic groups,
given the assembly proposition. That proposition is now supplied by `OPEN_gl_of_padded_proved`.

The `→` half does NOT use the hypothesis and is unconditional; it is the Levi embedding, which is
prior art (Lysikov–Walter Theorem V.19 / V.25, and standard before that). The `←` half is where the
hypothesis is consumed, and it is the half with any novelty in it. -/
theorem gl_iff_padded_of_assembly
    (hOpen : OPEN_gl_of_padded K U₁ U₂ U₃) (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
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

/-- **Unconditional tensor-level equivalence.** The forward half is the Levi lift; the reverse
half is the checked L8--L11 mode-support assembly. -/
theorem gl_iff_padded (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B) ↔
      (∃ (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
        (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃), IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
          spAct g₁ g₂ g₃ (pad3 A) = pad3 B) :=
  gl_iff_padded_of_assembly (OPEN_gl_of_padded_proved (K := K) (U₁ := U₁)
    (U₂ := U₂) (U₃ := U₃)) A B

/-- The antecedent of `OPEN_gl_of_padded` is satisfiable, so that proposition is not true for want
of instances: every `GL`-isomorphic pair supplies one, by `padded_of_gl`. -/
theorem OPEN_gl_of_padded_antecedent_satisfiable
    (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃)
    (A : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    spAct (levi P₁) (levi P₂) (levi P₃) (pad3 A) = pad3 (glAct P₁ P₂ P₃ A) :=
  padded_of_gl P₁ P₂ P₃ A _ rfl

end ThreeTensor

/-! ## 5. Discharged historical obligations and coordinate adapters -/

section Open

/-- **Historical adapter obligation.** CGQTZ fix ONE skew form on `F^{2n}`, namely
`φ(u,v) = ∑_{i ∈ [n]} (u_i v_{2n−i+1} − u_{n+i} v_{n−i+1})`, and define `Sp(2n,F) = G(F^{2n}, φ)`.
The padding above produces instead the hyperbolic form `ω` on `U ⊕ U*`. The two are congruent — the
    Gram matrix of `ω` in the basis `(e_1,…,e_n,e_1^*,…,e_n^*)` is `[[0, I], [−I, 0]]` and that of `φ`
    is `[[0, J], [−J, 0]]` with `J` the reversal permutation, so conjugating by `diag(I, J)` carries one
    to the other — hence the transported instance is still a `{0,1}`-projection and the reduction
    survives. The declarations below prove both the coordinate arithmetic and the basis bridge from
    `Module.Dual K (Fin n → K)` to its standard coordinate vector.

The statement below is the content, not a stub: it says that a linear equivalence carrying `ω` to a
form `ψ` conjugates the two form-preserving groups onto each other. It is discharged immediately
below, while the explicit coordinate calculation is discharged by `diagOneRev_isometry`. -/
def OPEN_basisChange_of_congruent_forms
    (K : Type*) [Field K] (U V : Type*) [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (ψ : V →ₗ[K] V →ₗ[K] K) : Prop :=
  ∀ M : Hyp K U ≃ₗ[K] V, (∀ x y : Hyp K U, ψ (M x) (M y) = omegaH x y) →
    ∀ g : Hyp K U ≃ₗ[K] Hyp K U,
      IsSymplectic g ↔ ∀ x y : V, ψ ((M.symm.trans (g.trans M)) x)
        ((M.symm.trans (g.trans M)) y) = ψ x y

/-- An isometry conjugates the two form-preserving groups. This discharges the abstract content of
the historical `OPEN_basisChange_of_congruent_forms` proposition; the separate coordinate fact
that `diag(I,J)` is an isometry to CGQTZ's chosen matrix is an encoding-level obligation. -/
theorem basisChange_of_congruent_forms
    (K : Type*) [Field K] (U V : Type*) [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (ψ : V →ₗ[K] V →ₗ[K] K) :
    OPEN_basisChange_of_congruent_forms K U V ψ := by
  intro M hM g
  constructor
  · intro hg x y
    calc
      ψ ((M.symm.trans (g.trans M)) x) ((M.symm.trans (g.trans M)) y) =
          omegaH (g (M.symm x)) (g (M.symm y)) := by
            simpa only [LinearEquiv.trans_apply] using hM (g (M.symm x)) (g (M.symm y))
      _ = omegaH (M.symm x) (M.symm y) := hg _ _
      _ = ψ x y := by
        simpa using (hM (M.symm x) (M.symm y)).symm
  · intro hconj x y
    calc
      omegaH (g x) (g y) = ψ (M (g x)) (M (g y)) := (hM (g x) (g y)).symm
      _ = ψ (M x) (M y) := by
        simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hconj (M x) (M y)
      _ = omegaH x y := hM x y

/-! ### The explicit coordinate adapter `diag(I,J)` -/

open scoped BigOperators

/-- Coordinate model of a hyperbolic double: primal coordinates followed by dual coordinates. -/
abbrev CoordHyp (K : Type*) (n : ℕ) := (Fin n → K) × (Fin n → K)

/-- The coordinate hyperbolic form with Gram matrix `[[0,I],[-I,0]]`. -/
def coordHyperForm {K : Type*} [Field K] {n : ℕ} (x y : CoordHyp K n) : K :=
  ∑ i : Fin n, (y.2 i * x.1 i - x.2 i * y.1 i)

/-- CGQTZ's reversed pairing, with Gram matrix `[[0,J],[-J,0]]`. -/
def cgqtzCoordForm {K : Type*} [Field K] {n : ℕ} (x y : CoordHyp K n) : K :=
  ∑ i : Fin n, (y.2 i.rev * x.1 i - x.2 i * y.1 i.rev)

/-- The coordinate action of `diag(I,J)`: fix the primal block and reverse the dual block. -/
def diagOneRev {K : Type*} {n : ℕ} (x : CoordHyp K n) : CoordHyp K n :=
  (x.1, fun i => x.2 i.rev)

/-- Reversal as a linear equivalence. -/
def revLinearEquiv (K : Type*) [Field K] (n : ℕ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) where
  toFun f i := f i.rev
  invFun f i := f i.rev
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl

/-- `diag(I,J)` as a linear equivalence. -/
def diagOneRevLinearEquiv (K : Type*) [Field K] (n : ℕ) :
    CoordHyp K n ≃ₗ[K] CoordHyp K n :=
  (LinearEquiv.refl K (Fin n → K)).prodCongr (revLinearEquiv K n)

@[simp] theorem diagOneRev_fst {K : Type*} {n : ℕ} (x : CoordHyp K n) :
    (diagOneRev x).1 = x.1 := rfl

@[simp] theorem diagOneRev_snd_apply {K : Type*} {n : ℕ} (x : CoordHyp K n) (i : Fin n) :
    (diagOneRev x).2 i = x.2 i.rev := rfl

@[simp] theorem diagOneRevLinearEquiv_apply {K : Type*} [Field K] {n : ℕ}
    (x : CoordHyp K n) : diagOneRevLinearEquiv K n x = diagOneRev x := rfl

/-- The adapter is an involutive coordinate permutation. -/
theorem diagOneRev_involutive {K : Type*} {n : ℕ} :
    Function.Involutive (diagOneRev : CoordHyp K n → CoordHyp K n) := by
  intro x
  ext i <;> simp [diagOneRev]

/-- **L13 coordinate identity.** `diag(I,J)` carries CGQTZ's fixed form to the hyperbolic form,
over every field and hence also in characteristic `2`. -/
theorem diagOneRev_isometry {K : Type*} [Field K] {n : ℕ} (x y : CoordHyp K n) :
    cgqtzCoordForm (diagOneRev x) (diagOneRev y) = coordHyperForm x y := by
  simp only [cgqtzCoordForm, coordHyperForm, diagOneRev_fst, diagOneRev_snd_apply, Fin.rev_rev]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, Fin.rev_rev]

theorem diagOneRevLinearEquiv_isometry {K : Type*} [Field K] {n : ℕ}
    (x y : CoordHyp K n) :
    cgqtzCoordForm (diagOneRevLinearEquiv K n x) (diagOneRevLinearEquiv K n y) =
      coordHyperForm x y := by
  simpa using diagOneRev_isometry x y

/-! ### Complete bridge from the abstract hyperbolic double to CGQTZ coordinates -/

/-- Standard coordinates on the dual of `K^n`: a functional is sent to its values on the standard
basis vectors. -/
noncomputable def dualCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Module.Dual K (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  (Pi.basisFun K (Fin n)).dualBasis.equivFun

@[simp] theorem dualCoordEquiv_apply (K : Type*) [Field K] (n : ℕ)
    (f : Module.Dual K (Fin n → K)) (i : Fin n) :
    dualCoordEquiv K n f i = f (Pi.single i 1) := by
  simp [dualCoordEquiv]

/-- Reconstruction of evaluation from standard dual coordinates. -/
theorem dual_eval_sum (K : Type*) [Field K] (n : ℕ)
    (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    (∑ i : Fin n, f (Pi.single i 1) * x i) = f x := by
  let b := Pi.basisFun K (Fin n)
  have h := DFunLike.congr_fun (b.sum_dual_apply_smul_coord f) x
  simpa [b, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.equivFun_apply] using h

/-- The abstract hyperbolic double in standard primal/dual coordinates. -/
noncomputable def hypCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Hyp K (Fin n → K) ≃ₗ[K] CoordHyp K n :=
  (LinearEquiv.refl K (Fin n → K)).prodCongr (dualCoordEquiv K n)

@[simp] theorem hypCoordEquiv_apply (K : Type*) [Field K] (n : ℕ)
    (x : Hyp K (Fin n → K)) :
    hypCoordEquiv K n x = (x.1, dualCoordEquiv K n x.2) := rfl

/-- In standard coordinates, the abstract form `omegaH` is exactly `[[0,I],[-I,0]]`. -/
theorem hypCoordEquiv_isometry (K : Type*) [Field K] (n : ℕ)
    (x y : Hyp K (Fin n → K)) :
    coordHyperForm (hypCoordEquiv K n x) (hypCoordEquiv K n y) = omegaH x y := by
  simp only [coordHyperForm, hypCoordEquiv_apply, dualCoordEquiv_apply,
    Finset.sum_sub_distrib]
  rw [dual_eval_sum, dual_eval_sum]
  rfl

/-- The complete coordinate adapter: standard dual coordinates followed by `diag(I,J)`. -/
noncomputable def standardCoordEquiv (K : Type*) [Field K] (n : ℕ) :
    Hyp K (Fin n → K) ≃ₗ[K] CoordHyp K n :=
  hypCoordEquiv K n ≪≫ₗ diagOneRevLinearEquiv K n

/-- The coordinate adapter sends the Lagrangian embedding to literal zero-padding. -/
@[simp] theorem standardCoordEquiv_iota (K : Type*) [Field K] (n : ℕ)
    (u : Fin n → K) :
    standardCoordEquiv K n (iota u) = (u, 0) := by
  simp only [standardCoordEquiv, LinearEquiv.trans_apply, hypCoordEquiv_apply,
    iota_apply, map_zero]
  change diagOneRev (u, 0) = (u, 0)
  ext <;> simp [diagOneRev]

/-- The complete adapter carries `omegaH` to the fixed symplectic form used by CGQTZ. -/
theorem standardCoordEquiv_isometry (K : Type*) [Field K] (n : ℕ)
    (x y : Hyp K (Fin n → K)) :
    cgqtzCoordForm (standardCoordEquiv K n x) (standardCoordEquiv K n y) =
      omegaH x y := by
  change cgqtzCoordForm
    (diagOneRevLinearEquiv K n (hypCoordEquiv K n x))
    (diagOneRevLinearEquiv K n (hypCoordEquiv K n y)) = omegaH x y
  rw [diagOneRevLinearEquiv_isometry, hypCoordEquiv_isometry]

/-- Conjugation through the complete coordinate adapter identifies the abstract symplectic group
with the group preserving CGQTZ's fixed coordinate form. -/
theorem standardCoordEquiv_conjugates (K : Type*) [Field K] (n : ℕ)
    (g : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K)) :
    IsSymplectic g ↔
      ∀ x y : CoordHyp K n,
        cgqtzCoordForm
            (((standardCoordEquiv K n).symm.trans (g.trans (standardCoordEquiv K n))) x)
            (((standardCoordEquiv K n).symm.trans (g.trans (standardCoordEquiv K n))) y) =
          cgqtzCoordForm x y := by
  constructor
  · intro hg x y
    calc
      cgqtzCoordForm
          (((standardCoordEquiv K n).symm.trans (g.trans (standardCoordEquiv K n))) x)
          (((standardCoordEquiv K n).symm.trans (g.trans (standardCoordEquiv K n))) y) =
          omegaH (g ((standardCoordEquiv K n).symm x))
            (g ((standardCoordEquiv K n).symm y)) := by
              simpa only [LinearEquiv.trans_apply] using
                standardCoordEquiv_isometry K n
                  (g ((standardCoordEquiv K n).symm x))
                  (g ((standardCoordEquiv K n).symm y))
      _ = omegaH ((standardCoordEquiv K n).symm x)
          ((standardCoordEquiv K n).symm y) := hg _ _
      _ = cgqtzCoordForm x y := by
        simpa using (standardCoordEquiv_isometry K n
          ((standardCoordEquiv K n).symm x)
          ((standardCoordEquiv K n).symm y)).symm
  · intro hconj x y
    calc
      omegaH (g x) (g y) =
          cgqtzCoordForm (standardCoordEquiv K n (g x))
            (standardCoordEquiv K n (g y)) :=
              (standardCoordEquiv_isometry K n (g x) (g y)).symm
      _ = cgqtzCoordForm (standardCoordEquiv K n x)
          (standardCoordEquiv K n y) := by
            simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
              hconj (standardCoordEquiv K n x) (standardCoordEquiv K n y)
      _ = omegaH x y := standardCoordEquiv_isometry K n x y

/-- **Historical complexity interface.** That `A ↦ Â` is a polynomial-time kernel reduction, i.e. that
`3`-Tensor-`GL`-Isomorphism reduces to `3`-Tensor-`Sp`-Isomorphism, hence `TI ⊆ TI_Sp`.

`gl_iff_padded` supplies the mathematical correctness of the kernel map, and the map itself is
literal zero-padding (every output coordinate is an input coordinate or `0`, side lengths `n_i ↦
2 n_i`). This file has no Turing-machine cost model; the accompanying proof note verifies
uniformity and running time explicitly.

The Prop below has content: it is the *decision-problem* transfer that a reduction must supply,
stated over a fixed dimension bound — `gl_iff_padded` is exactly its instance-wise content, so this
is what remains once uniformity is added. -/
def OPEN_pad_is_kernel_reduction (K : Type*) [Field K] : Prop :=
  ∀ (U₁ U₂ U₃ : Type*) [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃],
    ∀ (_ : FiniteDimensional K U₁) (_ : FiniteDimensional K U₂) (_ : FiniteDimensional K U₃),
    ∀ A B : U₁ ⊗[K] (U₂ ⊗[K] U₃),
      (∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B) ↔
      (∃ (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
        (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃), IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
          spAct g₁ g₂ g₃ (pad3 A) = pad3 B)

/-- The instancewise yes/no content of the padding reduction is now unconditional. This theorem
does not attempt to formalize Turing-machine running time; it supplies the correctness component
used by such a reduction. -/
theorem pad_is_kernel_reduction_instancewise (K : Type*) [Field K] :
    OPEN_pad_is_kernel_reduction K := by
  intro U₁ U₂ U₃ _ _ _ _ _ _ _ _ _ A B
  exact gl_iff_padded A B

/-- Every `GL`-isomorphism of `A` and `B` produces a symplectic isomorphism of the paddings. This
is the Levi half — prior art. -/
theorem pad_reduction_preserves (K : Type*) [Field K] (U₁ U₂ U₃ : Type*)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ (P₁ : U₁ ≃ₗ[K] U₁) (P₂ : U₂ ≃ₗ[K] U₂) (P₃ : U₃ ≃ₗ[K] U₃), glAct P₁ P₂ P₃ A = B) →
      (∃ (g₁ : Hyp K U₁ ≃ₗ[K] Hyp K U₁) (g₂ : Hyp K U₂ ≃ₗ[K] Hyp K U₂)
        (g₃ : Hyp K U₃ ≃ₗ[K] Hyp K U₃), IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
          spAct g₁ g₂ g₃ (pad3 A) = pad3 B) := by
  rintro ⟨P₁, P₂, P₃, hP⟩
  exact ⟨levi P₁, levi P₂, levi P₃, levi_isSymplectic P₁, levi_isSymplectic P₂,
    levi_isSymplectic P₃, padded_of_gl P₁ P₂ P₃ A B hP⟩

end Open

/-! ## 6. Reduction-class bookkeeping

The computational reductions themselves live outside Lean's algebraic tensor model.  The only
logical step needed after supplying the two base-problem reductions is transitivity.  The small
abstract interface below machine-checks that step, corresponding to leaves L18 and L19 of the
proof decomposition. -/

universe u

/-- A reflexive, transitive reduction relation on decision problems. -/
structure ReductionSystem (Problem : Type u) where
  reduces : Problem → Problem → Prop
  refl : ∀ X, reduces X X
  trans : ∀ {X Y Z}, reduces X Y → reduces Y Z → reduces X Z

namespace ReductionSystem

variable {Problem : Type u} (R : ReductionSystem Problem)

/-- The complexity class generated by a complete/base problem `B`. -/
def problemClass (B : Problem) : Set Problem := {X | R.reduces X B}

/-- A reduction `A ≤ B` lifts to containment of the classes generated by `A` and `B`. -/
theorem problemClass_mono {A B : Problem} (hAB : R.reduces A B) :
    R.problemClass A ⊆ R.problemClass B := by
  intro X hXA
  exact R.trans hXA hAB

/-- Mutually reducible base problems generate exactly the same complexity class. -/
theorem problemClass_eq_of_reduces_both {A B : Problem}
    (hAB : R.reduces A B) (hBA : R.reduces B A) :
    R.problemClass A = R.problemClass B := by
  apply Set.Subset.antisymm
  · exact R.problemClass_mono hAB
  · exact R.problemClass_mono hBA

/-- **L18/L19 assembly.** If `GL3TI` reduces to `Sp3TI` (the padding theorem) and `Sp3TI`
reduces to `GL3TI` (CGQTZ Theorem 1.4), then `TI = TI_Sp` under their definitions. -/
theorem ti_eq_tisp_from_base_reductions (GL3TI Sp3TI : Problem)
    (hGLSp : R.reduces GL3TI Sp3TI) (hSpGL : R.reduces Sp3TI GL3TI) :
    R.problemClass GL3TI = R.problemClass Sp3TI :=
  R.problemClass_eq_of_reduces_both hGLSp hSpGL

end ReductionSystem

end Mathproof.SymplecticTI

end Part_U9


section Part_U10

/-
Copyright (c) 2026 MathProof. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProof
-/

/-!
# Finite-coordinate certificate for Lagrangian tensor padding

This module makes the encoding claim used by `Mathproof.SymplecticTI` executable.  A doubled mode
is indexed by `Fin n ⊕ Fin n`; the left summand is the primal coordinate block and the right
summand is the dual block.  `coordPad3` copies an input entry exactly when all three indices are in
the primal blocks, and writes zero otherwise.

The kernel checks the complete entry formula, injectivity, and the exact factor-eight increase in
the number of dense tensor coordinates.  These facts certify that the construction is literal
zero-padding with linear output size.  This module deliberately does not claim a formal
single-tape-Turing-machine runtime theorem: no such encoding framework connects field elements and
the tensor-orbit predicates in this project.
-/

namespace Mathproof.SymplecticTI.Encoding

/-- A doubled coordinate mode, with primal coordinates on the left and dual coordinates on the
right. -/
abbrev ModeIndex (n : ℕ) := Sum (Fin n) (Fin n)

/-- Executable three-tensor Lagrangian padding in coordinates. -/
def coordPad3 {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) :
    ModeIndex n₁ → ModeIndex n₂ → ModeIndex n₃ → K
  | Sum.inl i, Sum.inl j, Sum.inl k => A i j k
  | _, _, _ => 0

/-- Entries in the three primal blocks are copied verbatim. -/
@[simp] theorem coordPad3_inl {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i j k) :
    coordPad3 A (Sum.inl i) (Sum.inl j) (Sum.inl k) = A i j k := rfl

/-- Every entry in the first dual block is zero. -/
@[simp] theorem coordPad3_inr₁ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i : Fin n₁) (j) (k) :
    coordPad3 A (Sum.inr i) j k = 0 := rfl

/-- Every entry in the second dual block is zero. -/
@[simp] theorem coordPad3_inr₂ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i) (j : Fin n₂) (k) :
    coordPad3 A i (Sum.inr j) k = 0 := by cases i <;> rfl

/-- Every entry in the third dual block is zero. -/
@[simp] theorem coordPad3_inr₃ {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ}
    (A : Fin n₁ → Fin n₂ → Fin n₃ → K) (i) (j) (k : Fin n₃) :
    coordPad3 A i j (Sum.inr k) = 0 := by cases i <;> cases j <;> rfl

/-- Coordinate padding loses no input information. -/
theorem coordPad3_injective {K : Type*} [Zero K] {n₁ n₂ n₃ : ℕ} :
    Function.Injective
      (coordPad3 : (Fin n₁ → Fin n₂ → Fin n₃ → K) →
        ModeIndex n₁ → ModeIndex n₂ → ModeIndex n₃ → K) := by
  intro A B h
  funext i j k
  have hijk := congrFun (congrFun (congrFun h (Sum.inl i)) (Sum.inl j)) (Sum.inl k)
  simpa using hijk

/-- Each padded mode has exactly twice as many coordinates. -/
theorem modeIndex_card (n : ℕ) : Fintype.card (ModeIndex n) = 2 * n := by
  simp [ModeIndex]
  omega

/-- A dense padded three-tensor has exactly eight times the input coordinate count. -/
theorem coordPad3_output_card (n₁ n₂ n₃ : ℕ) :
    Fintype.card (ModeIndex n₁ × ModeIndex n₂ × ModeIndex n₃) =
      8 * Fintype.card (Fin n₁ × Fin n₂ × Fin n₃) := by
  simp [ModeIndex]
  ring

end Mathproof.SymplecticTI.Encoding

end Part_U10


section Part_U11


/-!
# Projection reductions: the formal notion in which `TI = TI_Sp` is to be stated

## Why this exists

The `TI = TI_Sp` package proves the *instancewise* equivalence of the padding map but leaves
"polynomial-time reduction" as a meta claim, and its class-equality theorem takes both reductions as
hypotheses. CGQTZ themselves say (§Fields, verbatim): *"All our reductions are constant-free
`p`-projections (that is, the only constants they use other than copying the ones already present in
the input are `{0,1,−1}`)."* A `p`-projection is a purely combinatorial object — every output
coordinate is an input coordinate or one of `0, 1, −1`, and the output size is polynomial in the
input size — so it can be formalized without any machine model, and it is *stronger* than
polynomial-time computability. This module defines it and shows it forms a `ReductionSystem`, so
`SymplecticTI.ReductionSystem.ti_eq_tisp_from_base_reductions` can be instantiated on concrete
problems once the two base projections are supplied.

## Objects

* `CoordProblem K`: a family of isomorphism-type problems on coordinate arrays: at size `n` the
  instances are functions `Idx n → K` on a finite index type, and `Rel n A B` says `A ≅ B`.
* `Projection P Q`: a size map `s`, a source map assigning to each output coordinate either an
  input coordinate or a constant in `{0, 1, −1}`, a **polynomial size bound**
  `card (Q.Idx (s n)) ≤ c * (card (P.Idx n) + 1)^k`, and **instancewise correctness**
  `P.Rel n A B ↔ Q.Rel (s n) (map A) (map B)`.
* `projectionSystem K : ReductionSystem (CoordProblem K)` with `reduces P Q := Nonempty (Projection P Q)`;
  reflexivity and transitivity are proved (composition of projections, product of polynomial
  bounds).
* The two concrete problems: `GL3TI K` (three independent invertible matrices acting on cubic
  arrays) and `Sp3TI K` (the same, restricted to matrices preserving the standard form
  `J = [[0, I], [−I, 0]]` on doubled coordinates), both as `CoordProblem`s.

## What is NOT here

The two concrete projections `GL3TI ⟶ Sp3TI` (the padding; correctness must be transported from
the abstract `gl_iff_padded` to matrices) and `Sp3TI ⟶ GL3TI` (the FGS tensor-system gadget). They
are the next modules; this one only fixes the notion and proves the abstract plumbing.
-/

namespace Mathproof.Meta.ProjectionReductions20260902
open Matrix


universe u

/-- A family of coordinate isomorphism problems, one per size. -/
structure CoordProblem (K : Type u) where
  Idx : ℕ → Type
  fin : ∀ n, Fintype (Idx n)
  Rel : ∀ n, (Idx n → K) → (Idx n → K) → Prop

attribute [instance] CoordProblem.fin

/-- A constant-free source: an input coordinate, or one of the constants `0, 1, −1`. -/
inductive Src (I : Type) | coord (i : I) | zero | one | negOne

/-- Evaluate a source on an input array. -/
def Src.eval {K : Type u} [Zero K] [One K] [Neg K] {I : Type} (A : I → K) : Src I → K
  | .coord i => A i
  | .zero => 0
  | .one => 1
  | .negOne => -1

/-- **A `p`-projection reduction** from `P` to `Q`. -/
structure Projection {K : Type u} [Zero K] [One K] [Neg K] (P Q : CoordProblem K) where
  size : ℕ → ℕ
  src : ∀ n, Q.Idx (size n) → Src (P.Idx n)
  polyBound : ∃ c k : ℕ, ∀ n, Fintype.card (Q.Idx (size n)) ≤ c * (Fintype.card (P.Idx n) + 1) ^ k
  correct : ∀ n (A B : P.Idx n → K),
    P.Rel n A B ↔ Q.Rel (size n) (fun j => (src n j).eval A) (fun j => (src n j).eval B)

namespace Projection

variable {K : Type u} [Zero K] [One K] [Neg K]

/-- The array produced by a projection. -/
def map {P Q : CoordProblem K} (r : Projection P Q) (n : ℕ) (A : P.Idx n → K) :
    Q.Idx (r.size n) → K :=
  fun j => (r.src n j).eval A

/-- Identity projection. -/
def refl (P : CoordProblem K) : Projection P P where
  size := id
  src := fun _ i => .coord i
  polyBound := ⟨1, 1, fun n => by simp⟩
  correct := fun _ _ _ => Iff.rfl

/-- Composition of sources: substitute the first projection's source into the second's. -/
def compSrc {I J : Type} (f : J → Src I) : Src J → Src I
  | .coord j => f j
  | .zero => .zero
  | .one => .one
  | .negOne => .negOne

theorem compSrc_eval {I J : Type} (f : J → Src I) (A : I → K) (s : Src J) :
    (compSrc f s).eval A = s.eval (fun j => (f j).eval A) := by
  cases s <;> rfl

/-- `(c₁ X + 1)^k ≤ ((c₁ + 1) X)^k` for `X ≥ 1` — the arithmetic behind polynomial composition. -/
theorem poly_compose_aux (c₁ k₁ c₂ k₂ N : ℕ) (hN : 1 ≤ N) (M : ℕ) (hM : M ≤ c₁ * N ^ k₁) :
    c₂ * (M + 1) ^ k₂ ≤ c₂ * (c₁ + 1) ^ k₂ * (N ^ k₁) ^ k₂ := by
  have h1 : M + 1 ≤ (c₁ + 1) * N ^ k₁ := by
    have : 1 ≤ N ^ k₁ := Nat.one_le_pow _ _ hN
    nlinarith
  calc c₂ * (M + 1) ^ k₂ ≤ c₂ * ((c₁ + 1) * N ^ k₁) ^ k₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = c₂ * (c₁ + 1) ^ k₂ * (N ^ k₁) ^ k₂ := by rw [mul_pow]; ring

/-- Composition of projections. -/
def trans {P Q R : CoordProblem K} (r₁ : Projection P Q) (r₂ : Projection Q R) : Projection P R where
  size := fun n => r₂.size (r₁.size n)
  src := fun n i => compSrc (r₁.src n) (r₂.src (r₁.size n) i)
  polyBound := by
    obtain ⟨c₁, k₁, h₁⟩ := r₁.polyBound
    obtain ⟨c₂, k₂, h₂⟩ := r₂.polyBound
    refine ⟨c₂ * (c₁ + 1) ^ k₂, k₁ * k₂, fun n => ?_⟩
    have hN : 1 ≤ Fintype.card (P.Idx n) + 1 := Nat.le_add_left 1 _
    have := poly_compose_aux c₁ k₁ c₂ k₂ (Fintype.card (P.Idx n) + 1) hN
      (Fintype.card (Q.Idx (r₁.size n))) (h₁ n)
    calc Fintype.card (R.Idx (r₂.size (r₁.size n)))
        ≤ c₂ * (Fintype.card (Q.Idx (r₁.size n)) + 1) ^ k₂ := h₂ _
      _ ≤ c₂ * (c₁ + 1) ^ k₂ * ((Fintype.card (P.Idx n) + 1) ^ k₁) ^ k₂ := this
      _ = c₂ * (c₁ + 1) ^ k₂ * (Fintype.card (P.Idx n) + 1) ^ (k₁ * k₂) := by rw [← pow_mul]
  correct := by
    intro n A B
    rw [r₁.correct n A B, r₂.correct (r₁.size n)]
    simp only [compSrc_eval]

end Projection

/-- **Projections form a reduction system.** -/
def projectionSystem (K : Type u) [Zero K] [One K] [Neg K] :
    Mathproof.SymplecticTI.ReductionSystem (CoordProblem K) where
  reduces := fun P Q => Nonempty (Projection P Q)
  refl := fun P => ⟨Projection.refl P⟩
  trans := fun ⟨r₁⟩ ⟨r₂⟩ => ⟨r₁.trans r₂⟩

/-! ## The two concrete problems -/

section Problems

variable (K : Type u) [Field K]

/-- The action of three matrices on a cubic array: `((P,Q,R)∘A)_{ijk} = Σ P_{ii'} Q_{jj'} R_{kk'} A_{i'j'k'}`. -/
def act3 {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K) :
    Fin n × Fin n × Fin n → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

/-- **`GL3TI`**: cubic arrays under three independent invertible matrices. -/
def GL3TI : CoordProblem K where
  Idx := fun n => Fin n × Fin n × Fin n
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ P Q R : Matrix (Fin n) (Fin n) K,
    IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act3 K P Q R A = B

/-- The standard symplectic form on doubled coordinates `Fin n ⊕ Fin n`: `J = [[0, I], [−I, 0]]`. -/
def stdJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- A matrix on doubled coordinates is symplectic when it preserves `J`. -/
def IsSymplecticMat {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Prop :=
  gᵀ * stdJ K n * g = stdJ K n

/-- The action on doubled cubic arrays. -/
def act3D {n : ℕ} (P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (A : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

/-- **`Sp3TI`**: doubled cubic arrays under three independent symplectic matrices (CGQTZ's fixed
form up to the reversal permutation, which `SymplecticTI.standardCoordEquiv_isometry` supplies). -/
def Sp3TI : CoordProblem K where
  Idx := fun n => (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
    IsSymplecticMat K P ∧ IsSymplecticMat K Q ∧ IsSymplecticMat K R ∧ act3D K P Q R A = B

/-- Symplectic matrices are invertible (`det J ≠ 0`), so `Sp3TI`-isomorphic arrays are in particular
`GL`-isomorphic on the doubled index set — the trivial containment direction at the array level. -/
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

/-- The class-equality statement, now on the concrete problems, still taking the two base
projections as data: this is exactly what the next two modules must supply. -/
theorem ti_eq_tisp_of_projections
    (r₁ : Projection (GL3TI K) (Sp3TI K)) (r₂ : Projection (Sp3TI K) (GL3TI K)) :
    (projectionSystem K).problemClass (GL3TI K) = (projectionSystem K).problemClass (Sp3TI K) :=
  Mathproof.SymplecticTI.ReductionSystem.ti_eq_tisp_from_base_reductions (projectionSystem K)
    (GL3TI K) (Sp3TI K) ⟨r₁⟩ ⟨r₂⟩

end Problems

#print axioms Projection.trans
#print axioms projectionSystem
#print axioms isUnit_of_isSymplecticMat
#print axioms ti_eq_tisp_of_projections

end Mathproof.Meta.ProjectionReductions20260902

end Part_U11


section Part_U12


/-!
# Coordinate arrays as tensors, over an arbitrary finite index type

## Purpose

`CoordTensorBridge20260902` proved the array/tensor dictionary for the index type `Fin n`. The
symplectic side of the padding reduction lives on the doubled index `Fin n ⊕ Fin n`, so this module
redoes the dictionary for an arbitrary `[Fintype ι] [DecidableEq ι]` and adds the missing half of the
`GL` dictionary: invertible matrices ⟷ linear equivalences (`linEquivOfIsUnit`, `isUnit_toMatrix'`),
giving `glAct_toTensor_iff`: the matrix relation of `GL3TI`/`Sp3TI` (without the symplectic
condition) is exactly `∃ e₁ e₂ e₃, glAct e₁ e₂ e₃ (toTensor A) = toTensor B`.

`act3` and `act3D` of `ProjectionReductions20260902` are definitionally `actι` at `ι = Fin n` and
`ι = Fin n ⊕ Fin n` (`act3_eq_actι`, `act3D_eq_actι`, both `rfl`).

## DAG queries (active snapshot 20260902T033037Z-a57018fc)

`forward Matrix.toLinearEquiv'` → `toLinearEquiv'_apply`, `toLinearEquiv'_symm_apply`;
`forward Matrix.toLin'_mul` → `LinearMap.toMatrix'_comp`; `forward LinearEquiv.sumArrowLequivProdArrow`
→ the four `_apply_fst/_snd/_symm_apply_inl/_inr` lemmas. No existing tree node consumes
`IsSymplecticMat` (the snapshot predates `ProjectionReductions20260902`), so nothing here duplicates
tree content.
-/

namespace Mathproof.Meta.CoordTensorBridgeGen20260902

open Matrix
open TensorProduct Module
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.SymplecticTI

universe u

variable {K : Type u} [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The standard basis of `K^ι`. -/
noncomputable abbrev e (ι : Type) [Fintype ι] [DecidableEq ι] : Module.Basis ι K (ι → K) :=
  Pi.basisFun K ι

/-- The standard basis of the triple tensor product, indexed by `ι × ι × ι`. -/
noncomputable def tb (ι : Type) [Fintype ι] [DecidableEq ι] :
    Module.Basis (ι × ι × ι) K ((ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K))) :=
  (e ι).tensorProduct ((e ι).tensorProduct (e ι))

theorem tb_apply (i j k : ι) :
    tb ι (i, j, k) = (e ι i) ⊗ₜ[K] ((e ι j) ⊗ₜ[K] (e ι k)) := by
  simp [tb, Module.Basis.tensorProduct_apply]

/-- **Arrays as tensors**: the inverse of the coordinate representation. -/
noncomputable def toTensor (ι : Type) [Fintype ι] [DecidableEq ι] :
    (ι × ι × ι → K) ≃ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  (Finsupp.linearEquivFunOnFinite K K (ι × ι × ι)).symm.trans (tb ι).repr.symm

theorem toTensor_apply (A : ι × ι × ι → K) :
    toTensor ι A = ∑ x, A x • tb ι x := by
  simp only [toTensor, LinearEquiv.trans_apply]
  rw [Module.Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply]
  simp [Finsupp.sum_fintype]

/-- The three-matrix action on a cubic array over `ι`. -/
def actι (P Q R : Matrix ι ι K) (A : ι × ι × ι → K) : ι × ι × ι → K :=
  fun ⟨i, j, k⟩ => ∑ i', ∑ j', ∑ k', P i i' * Q j j' * R k k' * A (i', j', k')

theorem act3_eq_actι {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K) (A : Fin n × Fin n × Fin n → K) :
    act3 K P Q R A = actι P Q R A := rfl

theorem act3D_eq_actι {n : ℕ} (P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (A : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    act3D K P Q R A = actι P Q R A := rfl

/-- The abstract action of three matrices via `Matrix.toLin'`. -/
noncomputable def glActMat (P Q R : Matrix ι ι K) :
    (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) →ₗ[K] (ι → K) ⊗[K] ((ι → K) ⊗[K] (ι → K)) :=
  TensorProduct.map (Matrix.toLin' P) (TensorProduct.map (Matrix.toLin' Q) (Matrix.toLin' R))

/-- Coefficients of the standard basis: `repr (toTensor A) = A`. -/
theorem repr_toTensor (A : ι × ι × ι → K) (x : ι × ι × ι) :
    (tb ι).repr (toTensor ι A) x = A x := by
  simp [toTensor]

/-- The coefficient of `toLin' P` on a basis vector: `(P *ᵥ e_i) a = P a i`. -/
theorem repr_toLin'_basis (P : Matrix ι ι K) (i a : ι) :
    (e ι).repr (Matrix.toLin' P (e ι i)) a = P a i := by
  simp [Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]

/-- The coefficient of `glActMat` on a basis array, from the pure-tensor coefficient formula. -/
theorem repr_glActMat_tb (P Q R : Matrix ι ι K) (i j k a b c : ι) :
    (tb ι).repr (glActMat P Q R (tb ι (i, j, k))) (a, b, c) = P a i * Q b j * R c k := by
  rw [tb_apply]
  simp only [glActMat, TensorProduct.map_tmul, tb]
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [repr_toLin'_basis, smul_eq_mul]
  ring

/-- **The action dictionary**: matrices on arrays = `toLin'` maps on tensors. -/
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

/-! ### Invertible matrices ⟷ linear equivalences -/

/-- An invertible matrix as a linear equivalence of `K^ι`. -/
noncomputable def linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) : (ι → K) ≃ₗ[K] (ι → K) :=
  Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P ((Matrix.isUnit_iff_isUnit_det P).mp hP))

theorem coe_linEquivOfIsUnit (P : Matrix ι ι K) (hP : IsUnit P) :
    (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' P :=
  Matrix.toLinearEquiv'_apply P _

theorem linEquivOfIsUnit_apply (P : Matrix ι ι K) (hP : IsUnit P) (x : ι → K) :
    linEquivOfIsUnit P hP x = P *ᵥ x := by
  change (linEquivOfIsUnit P hP : (ι → K) →ₗ[K] (ι → K)) x = _
  rw [coe_linEquivOfIsUnit, Matrix.toLin'_apply]

/-- The matrix of a linear equivalence is invertible. -/
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

/-- **The `GL` dictionary**: the three-invertible-matrix relation on arrays is `glAct` on tensors. -/
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

end Mathproof.Meta.CoordTensorBridgeGen20260902

end Part_U12


section Part_U13


/-!
# The matrix face of bipartite Krull–Schmidt cancellation

## Purpose

`BipartiteCancellation20260902.bipartite_cancel` lives on representations of the bipartite quiver.
FGS's partition-deletion step (and the rank machinery of `FGSPaddedSlice20260902`) lives on
per-block matrices. This module is the dictionary and the matrix-level corollary:

* `rep X` — a per-block tuple `X : Fin t → ∀ b s, Matrix (RowIdx b) (ColIdx s) K` as a `BRep`
  (sources = column blocks `γ`, sinks = row blocks `β`, arrows = frontal slices);
* `simEquiv_of_matrices` / `matrices_of_simEquiv` — simultaneous block-equivalence
  `Y k b s = P b * X k b s * (Q s)ᵀ` (per-block invertible `P`, `Q`) is exactly `BRep.SimEquiv`;
* `simEquiv_rep_fromBlocks_dsum` — the padded tuple `fromBlocks (Δ k b s) 0 0 (X k b s)` is the
  block direct sum `(rep Δ).dsum (rep X)` up to the `Sum`-arrow/product reindexing;
* `matrix_block_cancel` — **FGS's cancellation, matrix form**: if `Δ ⊞ Y ≅ Δ ⊞ X` simultaneously by
  per-block invertible transporters, then `Y ≅ X` simultaneously by per-block invertible transporters.

## DAG chain walked

`Matrix.toLin'_mul`, `LinearMap.toMatrix'_comp`, `Matrix.toLin'_toMatrix'`, `Matrix.fromBlocks_mulVec`,
`LinearEquiv.sumArrowLequivProdArrow_apply_fst/snd`, `Matrix.isUnit_nonsing_inv_det`;
`Mathproof.Meta.CoordTensorBridgeGen20260902.linEquivOfIsUnit / isUnit_toMatrix'` (reused);
`Mathproof.Meta.BipartiteCancellation20260902.bipartite_cancel` (consumed).
-/

namespace Mathproof.Meta.FGSMatrixCancel20260902

open Matrix
open Mathproof.Meta.BipartiteCancellation20260902
open Mathproof.Meta.CoordTensorBridgeGen20260902

universe u v

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {t : ℕ}
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]

/-- A per-block matrix tuple as a bipartite-quiver representation. -/
def rep (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    BRep K γ β (Fin t) (fun s => ColIdx s → K) (fun b => RowIdx b → K) :=
  ⟨fun k s b => Matrix.toLin' (X k b s)⟩

theorem rep_f (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) (k : Fin t) (s : γ)
    (b : β) : (rep X).f k s b = Matrix.toLin' (X k b s) := rfl

/-! ### Simultaneous block-equivalence is `SimEquiv` -/

theorem isUnit_det_transpose_inv {I : Type} [Fintype I] [DecidableEq I] (Q : Matrix I I K)
    (hQ : IsUnit Q.det) : IsUnit ((Qᵀ)⁻¹).det :=
  Matrix.isUnit_nonsing_inv_det Qᵀ (by rwa [Matrix.det_transpose])

/-- Per-block invertible transporters give a `SimEquiv`. -/
theorem simEquiv_of_matrices (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (hP : ∀ b, IsUnit (P b).det) (hQ : ∀ s, IsUnit (Q s).det)
    (h : ∀ k b s, Y k b s = P b * X k b s * (Q s)ᵀ) : (rep X).SimEquiv (rep Y) := by
  refine ⟨fun s => linEquivOfIsUnit ((Q s)ᵀ)⁻¹
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_transpose_inv (Q s) (hQ s))),
    fun b => linEquivOfIsUnit (P b) ((Matrix.isUnit_iff_isUnit_det _).mpr (hP b)),
    fun k s b => ?_⟩
  rw [rep_f, rep_f, coe_linEquivOfIsUnit, coe_linEquivOfIsUnit, ← Matrix.toLin'_mul,
    ← Matrix.toLin'_mul, h k b s, Matrix.mul_assoc (P b * X k b s),
    Matrix.mul_nonsing_inv (Q s)ᵀ (by rw [Matrix.det_transpose]; exact hQ s), Matrix.mul_one]

/-- A `SimEquiv` gives per-block invertible transporters. -/
theorem matrices_of_simEquiv (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (h : (rep X).SimEquiv (rep Y)) :
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
    -- e : toMatrix' Qb * X = Y * toMatrix' Ps
    rw [Matrix.transpose_transpose]
    show Y k b s = LinearMap.toMatrix' (Qb b : (RowIdx b → K) →ₗ[K] (RowIdx b → K)) * X k b s *
      (LinearMap.toMatrix' (Ps s : (ColIdx s → K) →ₗ[K] (ColIdx s → K)))⁻¹
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]

/-! ### Padding is the block direct sum -/

section Pad

variable {DR : β → Type} {DC : γ → Type}
variable [∀ b, Fintype (DR b)] [∀ b, DecidableEq (DR b)] [∀ s, Fintype (DC s)] [∀ s, DecidableEq (DC s)]

/-- The padded tuple. -/
def padded (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    Fin t → ∀ (b : β) (s : γ), Matrix (DR b ⊕ RowIdx b) (DC s ⊕ ColIdx s) K :=
  fun k b s => Matrix.fromBlocks (Δ k b s) 0 0 (X k b s)

/-- The padded representation is the block direct sum, up to reindexing. -/
theorem simEquiv_rep_padded_dsum (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K) :
    (rep (padded Δ X)).SimEquiv ((rep Δ).dsum (rep X)) := by
  refine ⟨fun s => LinearEquiv.sumArrowLequivProdArrow (DC s) (ColIdx s) K K,
    fun b => LinearEquiv.sumArrowLequivProdArrow (DR b) (RowIdx b) K K, fun k s b => ?_⟩
  refine LinearMap.ext fun v => ?_
  refine Prod.ext ?_ ?_
  · funext i
    simp [rep, padded, BRep.dsum, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    rfl
  · funext i
    simp [rep, padded, BRep.dsum, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    rfl

/-- `SimEquiv` is symmetric and transitive (through the module isomorphisms). -/
theorem simEquiv_symm {V V' : γ → Type v} {W W' : β → Type v}
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ b, AddCommGroup (W b)] [∀ b, Module K (W b)]
    [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ b, AddCommGroup (W' b)] [∀ b, Module K (W' b)]
    {A : BRep K γ β (Fin t) V W} {B : BRep K γ β (Fin t) V' W'} (h : A.SimEquiv B) : B.SimEquiv A := by
  rw [BRep.simEquiv_iff_nonempty] at h ⊢
  exact ⟨h.some.symm⟩

theorem simEquiv_trans {V V' V'' : γ → Type v} {W W' W'' : β → Type v}
    [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ b, AddCommGroup (W b)] [∀ b, Module K (W b)]
    [∀ s, AddCommGroup (V' s)] [∀ s, Module K (V' s)] [∀ b, AddCommGroup (W' b)] [∀ b, Module K (W' b)]
    [∀ s, AddCommGroup (V'' s)] [∀ s, Module K (V'' s)] [∀ b, AddCommGroup (W'' b)]
    [∀ b, Module K (W'' b)]
    {A : BRep K γ β (Fin t) V W} {B : BRep K γ β (Fin t) V' W'} {C : BRep K γ β (Fin t) V'' W''}
    (h₁ : A.SimEquiv B) (h₂ : B.SimEquiv C) : A.SimEquiv C := by
  rw [BRep.simEquiv_iff_nonempty] at h₁ h₂ ⊢
  exact ⟨h₁.some ≪≫ₗ h₂.some⟩

/-- **FGS cancellation, matrix form.** -/
theorem matrix_block_cancel (Δ : Fin t → ∀ (b : β) (s : γ), Matrix (DR b) (DC s) K)
    (X Y : Fin t → ∀ (b : β) (s : γ), Matrix (RowIdx b) (ColIdx s) K)
    (P' : ∀ b, Matrix (DR b ⊕ RowIdx b) (DR b ⊕ RowIdx b) K)
    (Q' : ∀ s, Matrix (DC s ⊕ ColIdx s) (DC s ⊕ ColIdx s) K)
    (hP' : ∀ b, IsUnit (P' b).det) (hQ' : ∀ s, IsUnit (Q' s).det)
    (h : ∀ k b s, padded Δ Y k b s = P' b * padded Δ X k b s * (Q' s)ᵀ) :
    ∃ (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K),
      (∀ b, IsUnit (P b).det) ∧ (∀ s, IsUnit (Q s).det) ∧
      ∀ k b s, Y k b s = P b * X k b s * (Q s)ᵀ := by
  have h₁ : (rep (padded Δ X)).SimEquiv (rep (padded Δ Y)) :=
    simEquiv_of_matrices _ _ P' Q' hP' hQ' h
  have h₂ : ((rep Δ).dsum (rep X)).SimEquiv ((rep Δ).dsum (rep Y)) :=
    simEquiv_trans (simEquiv_symm (simEquiv_rep_padded_dsum Δ X))
      (simEquiv_trans h₁ (simEquiv_rep_padded_dsum Δ Y))
  have h₃ : (rep X).SimEquiv (rep Y) :=
    bipartite_cancel (K := K) (Src := γ) (Snk := β) (Arr := Fin t)
      (DV := fun s => DC s → K) (DW := fun b => DR b → K)
      (V := fun s => ColIdx s → K) (W := fun b => RowIdx b → K)
      (V' := fun s => ColIdx s → K) (W' := fun b => RowIdx b → K) (rep Δ) (rep X) (rep Y) h₂
  exact matrices_of_simEquiv X Y h₃

end Pad

#print axioms matrix_block_cancel

end Mathproof.Meta.FGSMatrixCancel20260902

end Part_U13


section Part_U14


-- see FGSBlockArrays20260902: the CStarMatrix HMul instance must not be visible here

/-!
# FGS Lemma `jhp`: deleting the frontal partition (both directions)

## Purpose

`partition_deletion` is FGS's Lemma `jhp` (arXiv 1810.09219) for a partitioned 3-array in the
per-block form of `FGSBlockArrays20260902`: with `r` larger than every row-block size,

  `BlockEquiv str X Y ↔ BlockEquiv (fun _ => 0) (padArr b₀ c₀ r str X) (padArr b₀ c₀ r str Y)`.

Forward: `FGSBlockArrays20260902.blockEquiv_pad`. Reverse, exactly FGS's proof:

1. **rank step** at the block `(b₀, c₀)`: the padded slice equation gives
   `2^(str k)·r + rank(Y k) = ∑_{γ ∈ T k} 2^γ·r + rank(C k)` with `C := ∑ R k k' • X k'`
   (`FGSPaddedSlice20260902.rank_padded` through a reindexing), and both `A`-ranks are `< r`
   because every row block has fewer than `r` rows; `FGSRankStep20260902.S_blockDiagonal_of_ranks`
   (superincreasing bands) then forces `R` block-diagonal on the strata;
2. **normalization**: `gadget (R k ·) = gadget (ind k) · (Rᵀ ⊗ 1)ᵀ` (from
   `gadgetBlock_mul_kronS`), so `padArr Y = P' · padArr C · Q''ᵀ` slice by slice — a
   *simultaneous* block-equivalence of the padded tuples;
3. **cancellation**: `FGSMatrixCancel20260902.matrix_block_cancel` (Krull–Schmidt for the bipartite
   quiver) cancels the common gadget summand, giving `Y = P · C · Qᵀ` blockwise;
4. **assembly**: `C = ∑ R k k' • X k'` with `R` block-diagonal, so `(P, Q, R)` is a block-equivalence
   `X ≅ Y`.

## DAG chain walked

`Matrix.rank_mul_eq_left_of_isUnit_det / rank_mul_eq_right_of_isUnit_det`, `Matrix.rank_reindex`,
`Matrix.rank_le_height`, `Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_transpose`,
`Matrix.nonsing_inv_mul`; consumed tree nodes: `rank_padded`, `S_blockDiagonal_of_ranks`,
`gadgetBlock_mul_kronS`, `matrix_block_cancel`.
-/

namespace Mathproof.Meta.FGSPartitionDeletion20260902

open Matrix
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSMatrixCancel20260902 (matrix_block_cancel)
open Mathproof.Meta.FGSPaddedSlice20260902 (gadget rank_padded rank_lt_of_card_rows_lt)
open Mathproof.Meta.FGSRankStep20260902 (S_blockDiagonal_of_ranks)

universe u

variable {K : Type u} [Field K]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}
variable (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

/-- The reconstructed array `C k = ∑ k', R k k' • X k'`. -/
def recon (X : PArr K β γ RowIdx ColIdx t) (R : Matrix (Fin t) (Fin t) K) :
    PArr K β γ RowIdx ColIdx t :=
  fun k b s => ∑ k', R k k' • X k' b s

theorem sum_smul_padArr (X : PArr K β γ RowIdx ColIdx t) (R : Matrix (Fin t) (Fin t) K)
    (k : Fin t) (b : β) (s : γ) :
    ∑ k', R k k' • padArr b₀ c₀ r str X k' b s =
      Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (fun j => R k j) b s) 0 0 (recon X R k b s) := by
  simp only [padArr, sum_smul_fromBlocks, sum_smul_gadgetBlock, recon]

/-! ### Ranks at the gadget block -/

/-- `fromBlocks` commutes with reindexing of the first block. -/
theorem fromBlocks_reindex {R₁ R₁' C₁ C₁' R₂ C₂ : Type} (e₁ : R₁ ≃ R₁') (e₂ : C₁ ≃ C₁')
    (G : Matrix R₁ C₁ K) (M : Matrix R₂ C₂ K) :
    Matrix.fromBlocks (Matrix.reindex e₁ e₂ G) 0 0 M =
      Matrix.reindex (e₁.sumCongr (Equiv.refl R₂)) (e₂.sumCongr (Equiv.refl C₂))
        (Matrix.fromBlocks G 0 0 M) := by
  ext (i | i) (j | j) <;> simp

/-- The gadget block at `(b₀, c₀)` is the gadget matrix, reindexed. -/
theorem gadgetBlock_eq_reindex (c : Fin t → K) :
    gadgetBlock b₀ c₀ r str c b₀ c₀ =
      Matrix.reindex (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm
        (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm (gadget (K := K) r str c) := by
  ext p jq
  rfl

/-- The rank of a padded `(b₀, c₀)` block. -/
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

/-! ### Normalization -/

/-- `gadget (R k ·) = gadget (ind k) · (Rᵀ ⊗ 1)ᵀ` for `R` block-diagonal on the strata. -/
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

/-! ### The theorem -/

/-- **FGS Lemma `jhp`, both directions.** -/
theorem partition_deletion (hr : ∀ b, Fintype.card (RowIdx b) < r)
    (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔
      BlockEquiv (fun _ : Fin t => (0 : Fin 1)) (padArr b₀ c₀ r str X) (padArr b₀ c₀ r str Y) := by
  refine ⟨blockEquiv_pad b₀ c₀ r str X Y, fun h => ?_⟩
  classical
  obtain ⟨P', Q', R, hP', hQ', hR, -, hXY⟩ := h
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) (hr b₀)
  -- the slice equation, with the sum pulled inside
  have hslice : ∀ k b s, padArr b₀ c₀ r str Y k b s =
      P' b * Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (fun j => R k j) b s) 0 0 (recon X R k b s) *
        (Q' s)ᵀ := by
    intro k b s
    rw [hXY k b s, ← sum_smul_padArr]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  -- Step 1: the rank identity at (b₀, c₀) forces `R` block-diagonal on the strata
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
    rw [padArr, rank_padBlock b₀ c₀ r str (ind k) {str k} (hT_ind str k),
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
  -- Step 2: normalization to a simultaneous block-equivalence of padded tuples
  let Q'' : ∀ s, Matrix (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t) s)
      (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t) s) K :=
    fun s => Q' s * Matrix.fromBlocks (kronS (n := n) c₀ r Rᵀ s) 0 0 (1 : Matrix (ColIdx s) (ColIdx s) K)
  have hQ'' : ∀ s, IsUnit (Q'' s).det := by
    intro s
    simp only [Q'']
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    exact (hQ' s).mul (isUnit_det_kronS_transpose c₀ r R hR s)
  have hsim : ∀ k b s, padArr b₀ c₀ r str Y k b s =
      P' b * padArr b₀ c₀ r str (recon X R) k b s * (Q'' s)ᵀ := by
    intro k b s
    have hpad : padArr b₀ c₀ r str (recon X R) k b s *
        Matrix.fromBlocks (kronS (n := n) c₀ r Rᵀ s)ᵀ 0 0 (1 : Matrix (ColIdx s) (ColIdx s) K) =
        Matrix.fromBlocks (gadgetBlock b₀ c₀ r str (ind k) b s * (kronS (n := n) c₀ r Rᵀ s)ᵀ) 0 0
          (recon X R k b s) := by
      rw [padArr, Matrix.fromBlocks_multiply]
      simp
      all_goals rfl
    rw [hslice k b s, gadgetBlock_recon b₀ c₀ r str R hR hbd, ← hpad]
    simp only [Q'', Matrix.transpose_mul, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.mul_assoc]
    all_goals rfl
  -- Step 3: cancel the gadget
  obtain ⟨P, Q, hP, hQ, hYC⟩ := matrix_block_cancel
    (DR := fun b => GRb b₀ (n := n) r b) (DC := fun s => GCs c₀ (n := n) (t := t) r s)
    (fun k b s => gadgetBlock b₀ c₀ r str (ind k) b s) (recon X R) Y P' Q'' hP' hQ'' hsim
  -- Step 4: assemble
  refine ⟨P, Q, R, hP, hQ, hR, hbd, fun k b s => ?_⟩
  rw [hYC k b s, recon]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

#print axioms partition_deletion

end Mathproof.Meta.FGSPartitionDeletion20260902

end Part_U14


section Part_U15


/-!
# Flat partitioned 3-arrays, axis rotation, and the bridge to per-block form

## Purpose

To run FGS's partition deletion (`FGSPartitionDeletion20260902`, stated on the per-block form
`PArr`) on all three axes (§4 of `D:/proof/STANDALONE_SP3TI_TO_GL3TI_PROOF.md`), the array must be
rotated so that each axis in turn is the frontal one. Rotation is awkward on the dependent
per-block type but trivial on a *flat* array `X : I₁ × I₂ × I₃ → K` with block maps
`blkᵢ : Iᵢ → ρᵢ`:

* `act P₁ P₂ P₃ X` — the three-matrix action, `act3` convention;
* `FlatEquiv blk₁ blk₂ blk₃ X Y` — three invertible transporters, each block-diagonal for its
  block map, carrying `X` to `Y`;
* `rot` — cyclic rotation of the axes, with `flatEquiv_rot` (transport is literal);
* `flatten` / `blockEquiv_iff_flat` — the bridge: per-block `BlockEquiv str X Y` is `FlatEquiv`
  on `(Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t` with block maps `Sigma.fst, Sigma.fst, str`,
  the per-block transporters assembled by `Matrix.blockDiagonal'` and, conversely, read off the
  diagonal blocks (`blockOf`) of a block-diagonal transporter;
* `flatEquiv_const` — with all three block maps constant, `FlatEquiv` is plain three-matrix
  equivalence (the `GL3TI` relation up to reindexing).

## DAG chain walked

`Matrix.blockDiagonal' → blockDiagonal'_apply_eq, blockDiagonal'_apply_ne, blockDiagonal'_mul,
blockDiagonal'_one, blockDiagonal'_transpose` (no `det_blockDiagonal'` exists; invertibility is
built from `blockDiagonal'_mul`/`_one` with explicit inverses); `Fintype.sum_sigma`;
`Mathproof.Meta.FGSBlockArrays20260902.BlockEquiv / IsBlockDiag` (bridged).
-/

namespace Mathproof.Meta.FGSFlatArrays20260902

open Matrix
open Mathproof.Meta.FGSBlockArrays20260902

universe u

variable {K : Type u} [Field K]

/-! ### Flat arrays -/

section Flat

variable {I₁ I₂ I₃ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
  [Fintype I₃] [DecidableEq I₃]

theorem sum3_swap_outer {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (g : A → B → C → K) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ b, ∑ a, ∑ c, g a b c :=
  Finset.sum_comm

theorem sum3_swap_inner {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (g : A → B → C → K) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The three-matrix action on a flat array. -/
def act (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K)
    (X : I₁ × I₂ × I₃ → K) : I₁ × I₂ × I₃ → K :=
  fun x => ∑ i', ∑ j', ∑ k', P₁ x.1 i' * P₂ x.2.1 j' * P₃ x.2.2 k' * X (i', j', k')

/-- **Flat block-equivalence.** -/
def FlatEquiv {ρ₁ ρ₂ ρ₃ : Type} [DecidableEq ρ₁] [DecidableEq ρ₂] [DecidableEq ρ₃]
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) : Prop :=
  ∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
    IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧
    IsBlockDiag blk₁ P₁ ∧ IsBlockDiag blk₂ P₂ ∧ IsBlockDiag blk₃ P₃ ∧
    act P₁ P₂ P₃ X = Y

/-- Cyclic rotation of the axes: `(i, j, k) ↦ (j, k, i)`. -/
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

/-- Rotation transports flat block-equivalence. -/
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

/-- With constant block maps, flat block-equivalence is plain three-matrix equivalence. -/
theorem flatEquiv_const (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv (fun _ : I₁ => ()) (fun _ : I₂ => ()) (fun _ : I₃ => ()) X Y ↔
      ∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
        IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ X = Y := by
  constructor
  · rintro ⟨P₁, P₂, P₃, h₁, h₂, h₃, -, -, -, hXY⟩
    exact ⟨P₁, P₂, P₃, h₁, h₂, h₃, hXY⟩
  · rintro ⟨P₁, P₂, P₃, h₁, h₂, h₃, hXY⟩
    exact ⟨P₁, P₂, P₃, h₁, h₂, h₃, fun _ _ h => absurd rfl h, fun _ _ h => absurd rfl h,
      fun _ _ h => absurd rfl h, hXY⟩

end Flat

/-! ### Block-diagonal assembly and its diagonal blocks -/

section Assemble

variable {β : Type} [Fintype β] [DecidableEq β] {RowIdx : β → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]

/-- The diagonal blocks of a matrix on a sigma type. -/
def blockOf (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K) (b : β) : Matrix (RowIdx b) (RowIdx b) K :=
  Matrix.of fun i i' => M ⟨b, i⟩ ⟨b, i'⟩

theorem isBlockDiag_blockDiagonal' (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) :
    IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) (Matrix.blockDiagonal' P) := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  exact Matrix.blockDiagonal'_apply_ne P i i' h

theorem blockOf_blockDiagonal' (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (b : β) :
    blockOf (Matrix.blockDiagonal' P) b = P b := by
  ext i i'
  simp [blockOf, Matrix.blockDiagonal'_apply_eq]

/-- A block-diagonal matrix is the assembly of its diagonal blocks. -/
theorem blockDiagonal'_blockOf (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K)
    (hM : IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) M) :
    Matrix.blockDiagonal' (blockOf M) = M := by
  ext ⟨b, i⟩ ⟨b', i'⟩
  by_cases h : b = b'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, blockOf]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, hM ⟨b, i⟩ ⟨b', i'⟩ h]

/-- Per-block invertibility assembles. -/
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

/-- The diagonal blocks of an invertible block-diagonal matrix are invertible. -/
theorem isUnit_det_blockOf (M : Matrix (Σ b, RowIdx b) (Σ b, RowIdx b) K)
    (hM : IsBlockDiag (Sigma.fst : (Σ b, RowIdx b) → β) M) (hu : IsUnit M.det) (b : β) :
    IsUnit (blockOf M b).det := by
  have hleft : blockOf M b * blockOf M⁻¹ b = 1 := by
    ext i i'
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) ⟨b, i⟩) ⟨b, i'⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma] at h
    rw [Finset.sum_eq_single b] at h
    · simpa [blockOf, Matrix.mul_apply, Matrix.one_apply] using h
    · intro b' _ hb'
      exact Finset.sum_eq_zero fun i'' _ => by rw [hM ⟨b, i⟩ ⟨b', i''⟩ (Ne.symm hb'), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : blockOf M⁻¹ b * blockOf M b = 1 := by
    ext i i'
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul M hu) ⟨b, i⟩) ⟨b, i'⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma] at h
    rw [Finset.sum_eq_single b] at h
    · simpa [blockOf, Matrix.mul_apply, Matrix.one_apply] using h
    · intro b' _ hb'
      exact Finset.sum_eq_zero fun i'' _ => by rw [hM ⟨b', i''⟩ ⟨b, i'⟩ hb', mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hleft, hright⟩, rfl⟩

end Assemble

/-! ### The bridge -/

section Bridge

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

/-- The flat array of a per-block array. -/
def flatten (X : PArr K β γ RowIdx ColIdx t) : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K :=
  fun x => X x.2.2 x.1.1 x.2.1.1 x.1.2 x.2.1.2

/-- The slice equation in entries. -/
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

/-- The flat action of assembled transporters, in entries. -/
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

/-- **The bridge**: per-block block-equivalence is flat block-equivalence. -/
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
    refine ⟨blockOf P₁, blockOf P₂, R, isUnit_det_blockOf P₁ b₁ h₁, isUnit_det_blockOf P₂ b₂ h₂,
      hR, hbd, fun k b s => ?_⟩
    ext i j
    rw [sliceEq_apply]
    have h := congrFun hXY (⟨b, i⟩, ⟨s, j⟩, k)
    rw [← blockDiagonal'_blockOf P₁ b₁, ← blockDiagonal'_blockOf P₂ b₂,
      act_blockDiagonal'_apply] at h
    simp only [flatten] at h
    exact h.symm

end Bridge

end Mathproof.Meta.FGSFlatArrays20260902

end Part_U15


section Part_U16


/-!
# Reindexing flat block-equivalence, and unflattening

## Purpose

Glue for §4 of `D:/proof/STANDALONE_SP3TI_TO_GL3TI_PROOF.md`: after a partition deletion the
array lives on `(Σ b, PadRow b) × (Σ s, PadCol s) × Fin t`; to delete the next axis it must be
rotated (`FGSFlatArrays20260902.rot`) and its new frontal axis flattened to some `Fin t'` so that
`FGSPartitionDeletion20260902.partition_deletion` applies again. This module provides

* `reindex3` and `flatEquiv_reindex3` — flat block-equivalence is invariant under reindexing the
  three index sets along equivalences (block maps and arrays transported);
* `unflatten` / `flatEquiv_iff_blockEquiv` — a flat array on `(Σ b, R b) × (Σ s, C s) × Fin t` is
  the flattening of a per-block array, and flat block-equivalence with block maps
  `Sigma.fst, Sigma.fst, str` is exactly per-block `BlockEquiv str`.

## DAG chain walked

`Matrix.reindex → reindex_apply, det_reindex_self`; `Equiv.sum_comp`;
`Mathproof.Meta.FGSFlatArrays20260902.blockEquiv_iff_flat / flatten / act`.
-/

namespace Mathproof.Meta.FGSFlatReindex20260902

open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSFlatArrays20260902

universe u

variable {K : Type u} [Field K]

section Reindex

variable {I₁ I₂ I₃ J₁ J₂ J₃ : Type}
variable [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype I₃] [DecidableEq I₃]
variable [Fintype J₁] [DecidableEq J₁] [Fintype J₂] [DecidableEq J₂] [Fintype J₃] [DecidableEq J₃]

/-- Reindex a flat array along equivalences of the three index sets. -/
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

/-- Forward transport of flat block-equivalence along reindexing. -/
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

/-- **Reindexing invariance** of flat block-equivalence. -/
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

/-- A flat array on sigma-indexed axes as a per-block array. -/
def unflatten (X : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) : PArr K β γ RowIdx ColIdx t :=
  fun k b s i j => X (⟨b, i⟩, ⟨s, j⟩, k)

theorem flatten_unflatten (X : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) :
    flatten (unflatten X) = X := by
  funext ⟨⟨b, i⟩, ⟨s, j⟩, k⟩
  rfl

theorem unflatten_flatten (X : PArr K β γ RowIdx ColIdx t) : unflatten (flatten X) = X := rfl

/-- Flat block-equivalence with sigma/sigma/strata block maps is per-block block-equivalence. -/
theorem flatEquiv_iff_blockEquiv (str : Fin t → Fin n)
    (X Y : (Σ b, RowIdx b) × (Σ s, ColIdx s) × Fin t → K) :
    FlatEquiv (Sigma.fst : (Σ b, RowIdx b) → β) (Sigma.fst : (Σ s, ColIdx s) → γ) str X Y ↔
      BlockEquiv str (unflatten X) (unflatten Y) := by
  rw [blockEquiv_iff_flat, flatten_unflatten, flatten_unflatten]

end Unflatten

end Mathproof.Meta.FGSFlatReindex20260902

end Part_U16


section Part_U17


/-!
# Three partition deletions: from a partitioned array to plain three-matrix equivalence

## Purpose

§4 of `D:/proof/STANDALONE_SP3TI_TO_GL3TI_PROOF.md`: delete the frontal partition
(`partition_deletion`), rotate the axes so the next partitioned axis is frontal, delete again, and
once more. All the plumbing is in flat form:

* `rotStep F` — a flat array on `(Σ b, R b) × (Σ s, C s) × Fin t` (frontal partition already
  deleted) rotated and re-packaged as a per-block array whose frontal axis is the old row axis
  (strata `rotStr R`, the old row blocks numbered by `Fintype.equivFin`), rows are the old
  columns, and columns are the old frontal axis as a single `Fin 1`-indexed block; `rot_step`
  transports block-equivalence;
* `flatEquiv_of_subsingleton` — with subsingleton block types, flat block-equivalence is plain
  three-matrix equivalence;
* the stage types `R₁ C₁ t₁ R₂ C₂ t₂` and the radii `rad` depend only on the index families, so
  the composite `T` is a map into a FIXED index type (needed for the source-map and size lemmas);
* `three_deletions` — `BlockEquiv str X Y ↔ ∃ P₁ P₂ P₃ invertible, act P₁ P₂ P₃ (T X) = T Y`, for
  any per-block array over nonempty finite block types. Each radius is `rad` = one more than the
  current number of rows, FGS's `r := min(m, n) + 1` up to the coarse bound.

## DAG chain walked

`Fintype.equivFin`, `Fintype.card_le_of_injective`, `sigma_mk_injective`; tree:
`partition_deletion`, `blockEquiv_iff_flat`, `flatEquiv_rot`, `flatEquiv_reindex3`,
`flatEquiv_iff_blockEquiv`.
-/

namespace Mathproof.Meta.FGSThreeDeletions20260902

open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSFlatArrays20260902
open Mathproof.Meta.FGSFlatReindex20260902
open Mathproof.Meta.FGSPartitionDeletion20260902 (partition_deletion)

universe u

variable {K : Type u} [Field K]

/-! ### Block maps up to relabeling, and trivial partitions -/

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

/-- Relabeling the strata of the third axis by an equivalence does not change block-equivalence. -/
theorem flatEquiv_comp_equiv₃ {ρ₁ ρ₂ ρ₃ ρ₃' : Type} [DecidableEq ρ₁] [DecidableEq ρ₂]
    [DecidableEq ρ₃] [DecidableEq ρ₃'] (e : ρ₃ ≃ ρ₃')
    (blk₁ : I₁ → ρ₁) (blk₂ : I₂ → ρ₂) (blk₃ : I₃ → ρ₃) (X Y : I₁ × I₂ × I₃ → K) :
    FlatEquiv blk₁ blk₂ blk₃ X Y ↔ FlatEquiv blk₁ blk₂ (e ∘ blk₃) X Y := by
  simp only [FlatEquiv, isBlockDiag_comp_equiv]

/-- With subsingleton block types, flat block-equivalence is plain three-matrix equivalence. -/
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

/-! ### The rotation step -/

section Rot

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {R : β → Type} {C : γ → Type}
variable [∀ b, Fintype (R b)] [∀ b, DecidableEq (R b)] [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]
variable {t : ℕ}

/-- The old frontal axis as a single `Fin 1`-indexed block. -/
def eFront (t : ℕ) : Fin t ≃ Σ _ : Fin 1, Fin t where
  toFun k := ⟨0, k⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := Sigma.ext (Subsingleton.elim _ _) HEq.rfl

/-- The old row axis, flattened to `Fin (card)`. -/
noncomputable def eRows (R : β → Type) [∀ b, Fintype (R b)] :
    (Σ b, R b) ≃ Fin (Fintype.card (Σ b, R b)) :=
  Fintype.equivFin _

/-- The strata of the rotated array: the old row blocks, numbered. -/
noncomputable def rotStr (R : β → Type) [∀ b, Fintype (R b)] :
    Fin (Fintype.card (Σ b, R b)) → Fin (Fintype.card β) :=
  fun k => Fintype.equivFin β ((eRows R).symm k).1

/-- Rotate a flat array (frontal partition already deleted) into per-block form with the old row
axis as the new frontal axis. -/
noncomputable def rotStep (F : (Σ b, R b) × (Σ s, C s) × Fin t → K) :
    PArr K γ (Fin 1) C (fun _ => Fin t) (Fintype.card (Σ b, R b)) :=
  unflatten (reindex3 (Equiv.refl (Σ s, C s)) (eFront t) (eRows R) (rot F))

/-- **Rotation transports block-equivalence.** -/
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

/-! ### The composite -/

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

/-- Radius for a deletion: one more than the total number of rows. -/
abbrev rad {β : Type} [Fintype β] (R : β → Type) [∀ b, Fintype (R b)] : ℕ :=
  Fintype.card (Σ b, R b) + 1

/-- A chosen block (the padding attaches there). -/
noncomputable def b₀ (β : Type) [Nonempty β] : β := Classical.arbitrary β

/-- One deletion followed by the rotation. -/
theorem delete_then_rotate {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {R : β → Type} {C : γ → Type}
    [∀ b, Fintype (R b)] [∀ b, DecidableEq (R b)] [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]
    {t m : ℕ} (b₀ : β) (c₀ : γ) (str : Fin t → Fin m) (X Y : PArr K β γ R C t) :
    BlockEquiv str X Y ↔
      BlockEquiv (rotStr (PadRow b₀ (rad R) (RowIdx := R) (n := m)))
        (rotStep (flatten (padArr b₀ c₀ (rad R) str X)))
        (rotStep (flatten (padArr b₀ c₀ (rad R) str Y))) := by
  rw [partition_deletion b₀ c₀ (rad R) str (fun b => card_lt_succ_card_sigma R b) X Y,
    blockEquiv_iff_flat, rot_step]

/-! The stage index families, depending only on the input families. -/

/-- Rows after stage 1: the padded old columns. -/
abbrev R₁ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type) (n t : ℕ)
    (c₀ : γ) : γ → Type :=
  PadCol c₀ (rad RowIdx) (ColIdx := ColIdx) (n := n) (t := t)

/-- Columns after stage 1: the old frontal axis, one block. -/
abbrev C₁ (t : ℕ) : Fin 1 → Type := fun _ => Fin t

/-- Slices after stage 1: the padded old rows. -/
abbrev t₁ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (n : ℕ) (b₀ : β) : ℕ :=
  Fintype.card (Σ b, PadRow b₀ (rad RowIdx) (RowIdx := RowIdx) (n := n) b)

/-- Stage 1: delete the frontal partition, rotate. -/
noncomputable def stage1 (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    PArr K γ (Fin 1) (R₁ RowIdx ColIdx n t (b₀ γ)) (C₁ t) (t₁ RowIdx n (b₀ β)) :=
  rotStep (flatten (padArr (b₀ β) (b₀ γ) (rad RowIdx) str X))

/-- Rows after stage 2. -/
abbrev R₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type)
    [∀ s, Fintype (ColIdx s)] (n t : ℕ) (b₀ : β) (c₀ : γ) : Fin 1 → Type :=
  PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t c₀)) (ColIdx := C₁ t) (n := Fintype.card β)
    (t := t₁ RowIdx n b₀)

/-- Columns after stage 2. -/
abbrev C₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (n : ℕ) (b₀ : β) : Fin 1 → Type :=
  fun _ => Fin (t₁ RowIdx n b₀)

/-- Slices after stage 2. -/
abbrev t₂ (RowIdx : β → Type) [∀ b, Fintype (RowIdx b)] (ColIdx : γ → Type)
    [∀ s, Fintype (ColIdx s)] (n t : ℕ) (c₀ : γ) : ℕ :=
  Fintype.card (Σ s, PadRow c₀ (rad (R₁ RowIdx ColIdx n t c₀)) (RowIdx := R₁ RowIdx ColIdx n t c₀)
    (n := Fintype.card β) s)

/-- Stage 2: delete the (old row) partition, rotate. -/
noncomputable def stage2 (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    PArr K (Fin 1) (Fin 1) (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (C₂ RowIdx n (b₀ β))
      (t₂ RowIdx ColIdx n t (b₀ γ)) :=
  rotStep (flatten (padArr (b₀ γ) (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
    (rotStr (PadRow (b₀ β) (rad RowIdx) (RowIdx := RowIdx) (n := n))) (stage1 str X)))

/-- Stage 3: delete the last (old column) partition; the result is unpartitioned. -/
noncomputable def T (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    (Σ b : Fin 1, PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ) b) ×
    (Σ s : Fin 1, PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ))
        s) ×
    Fin (t₂ RowIdx ColIdx n t (b₀ γ)) → K :=
  flatten (padArr (0 : Fin 1) (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (rotStr (PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
      (n := Fintype.card β)))
    (stage2 str X))

/-- **Three deletions**: block-equivalence is plain three-matrix equivalence of `T`. -/
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

end Mathproof.Meta.FGSThreeDeletions20260902

end Part_U17


section Part_U18


/-!
# The three-deletion transform is a constant-free source map

## Purpose

§4.2 of `D:/proof/STANDALONE_SP3TI_TO_GL3TI_PROOF.md`: every output coordinate of the composite
transform `T` is an input coordinate, `0`, or `1` (the gadget blocks are `0/1` diagonal
indicators, everything else is a copy or a zero block), so `T` composed with a constant-free
encoding is a `p`-projection in the sense of `ProjectionReductions20260902.Src`.

* `SrcExpr F` — every output coordinate of `F` is `Src.eval` of a source that does not depend on
  the input; closed under composition (`compSrc`) and under output permutations;
* per-block arrays as functions on `PArr.pos`;
* `padArr_srcExpr`, `rotStep_srcExpr`, `T_srcExpr` — the transform is `SrcExpr`.

## DAG chain walked

`Mathproof.Meta.ProjectionReductions20260902.Src / Src.eval / compSrc / compSrc_eval`;
`Mathproof.Meta.FGSPaddedSlice20260902.Ediag / gadget` (entries are `0/1`);
tree modules `FGSBlockArrays20260902`, `FGSFlatArrays20260902`, `FGSFlatReindex20260902`,
`FGSThreeDeletions20260902`.
-/

namespace Mathproof.Meta.FGSSrcExpr20260902

open Mathproof.Meta.ProjectionReductions20260902 (Src)
open Mathproof.Meta.ProjectionReductions20260902.Projection (compSrc compSrc_eval)
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSFlatArrays20260902
open Mathproof.Meta.FGSFlatReindex20260902
open Mathproof.Meta.FGSThreeDeletions20260902
open Mathproof.Meta.FGSPaddedSlice20260902 (gadget Ediag)

universe u

variable {K : Type u} [Field K]

/-! ### Source-expressible maps -/

/-- Every output coordinate is a fixed source (input coordinate or `0/1/−1`) evaluated on the input. -/
def SrcExpr {ι κ : Type} (F : (ι → K) → (κ → K)) : Prop :=
  ∀ z, ∃ s : Src ι, ∀ X, F X z = Src.eval X s

theorem SrcExpr.comp {ι κ μ : Type} {F : (ι → K) → (κ → K)} {G : (κ → K) → (μ → K)}
    (hF : SrcExpr F) (hG : SrcExpr G) : SrcExpr (fun X => G (F X)) := by
  intro z
  obtain ⟨s, hs⟩ := hG z
  choose f hf using hF
  refine ⟨compSrc f s, fun X => ?_⟩
  show G (F X) z = _
  rw [hs, compSrc_eval]
  congr 1
  funext y
  exact hf y X

theorem SrcExpr.id {ι : Type} : SrcExpr (fun X : ι → K => X) :=
  fun z => ⟨Src.coord z, fun _ => rfl⟩

/-- Precomposing the output index by any function keeps source-expressibility. -/
theorem SrcExpr.perm {ι κ κ' : Type} {F : (ι → K) → (κ → K)} (hF : SrcExpr F) (p : κ' → κ) :
    SrcExpr (fun X z => F X (p z)) :=
  fun z => hF (p z)

/-- An output coordinate that is input-independent and `0` or `1` is a constant source. -/
theorem SrcExpr.of_indep01 {ι κ : Type} {F : (ι → K) → (κ → K)}
    (hind : ∀ z X X', F X z = F X' z) (h01 : ∀ z X, F X z = 0 ∨ F X z = 1) : SrcExpr F := by
  intro z
  classical
  rcases h01 z (fun _ => 0) with h | h
  · exact ⟨Src.zero, fun X => by rw [hind z X (fun _ => 0), h]; rfl⟩
  · exact ⟨Src.one, fun X => by rw [hind z X (fun _ => 0), h]; rfl⟩

/-- Pointwise case split on the output index. -/
theorem SrcExpr.of_cases {ι κ : Type} {F : (ι → K) → (κ → K)}
    (h : ∀ z, ∃ s : Src ι, ∀ X, F X z = Src.eval X s) : SrcExpr F := h

/-! ### Per-block arrays as functions -/

section PArrFun

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

/-- The coordinate positions of a per-block array. -/
abbrev Pos (β γ : Type) (RowIdx : β → Type) (ColIdx : γ → Type) (t : ℕ) : Type :=
  Fin t × (Σ b, RowIdx b) × (Σ s, ColIdx s)

/-- A per-block array as a function on its positions. -/
def toFun (X : PArr K β γ RowIdx ColIdx t) : Pos β γ RowIdx ColIdx t → K :=
  fun p => X p.1 p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2

/-- A function on positions as a per-block array. -/
def ofFun (F : Pos β γ RowIdx ColIdx t → K) : PArr K β γ RowIdx ColIdx t :=
  fun k b s i j => F (k, ⟨b, i⟩, ⟨s, j⟩)

theorem toFun_ofFun (F : Pos β γ RowIdx ColIdx t → K) : toFun (ofFun F) = F := by
  funext ⟨k, ⟨b, i⟩, ⟨s, j⟩⟩
  rfl

theorem ofFun_toFun (X : PArr K β γ RowIdx ColIdx t) : ofFun (toFun X) = X := rfl

end PArrFun

/-! ### The padding is source-expressible -/

section Pad

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ} (b₀ : β) (c₀ : γ) (r : ℕ) (str : Fin t → Fin n)

/-- Entries of the diagonal indicator are `0` or `1`. -/
theorem Ediag_zero_or_one (γ' : Fin n) (p q : GR n r) :
    Ediag (K := K) r γ' p q = 0 ∨ Ediag (K := K) r γ' p q = 1 := by
  unfold Ediag
  rw [Matrix.diagonal_apply]
  split_ifs <;> simp

/-- Entries of the gadget with indicator coefficients are `0` or `1`. -/
theorem gadget_ind_zero_or_one (k : Fin t) (p : GR n r) (jq : Fin t × GR n r) :
    gadget (K := K) r str (ind k) p jq = 0 ∨ gadget (K := K) r str (ind k) p jq = 1 := by
  unfold gadget ind
  simp only [Matrix.of_apply]
  rcases Ediag_zero_or_one (K := K) r (str jq.1) p jq.2 with h | h <;> rw [h] <;> split_ifs <;> simp

/-- The padded array, as a map on positions, is source-expressible. -/
theorem padArr_srcExpr :
    SrcExpr (fun F : Pos β γ RowIdx ColIdx t → K =>
      toFun (padArr b₀ c₀ r str (ofFun F) :
        PArr K β γ (PadRow b₀ r (RowIdx := RowIdx) (n := n))
          (PadCol c₀ r (ColIdx := ColIdx) (n := n) (t := t)) t)) := by
  rintro ⟨k, ⟨b, i⟩, ⟨s, j⟩⟩
  rcases i with p | i <;> rcases j with jq | j
  · -- gadget block: input-independent, `0` or `1`
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

/-! ### Flattening, rotation, reindexing are permutations -/

section Perm

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {R : β → Type} {C : γ → Type}
variable [∀ b, Fintype (R b)] [∀ s, Fintype (C s)]
variable {t : ℕ}

theorem flatten_srcExpr :
    SrcExpr (fun F : Pos β γ R C t → K => flatten (ofFun F)) :=
  fun z => ⟨Src.coord (z.2.2, z.1, z.2.1), fun F => rfl⟩

theorem rotStep_srcExpr :
    SrcExpr (fun F : (Σ b, R b) × (Σ s, C s) × Fin t → K => toFun (rotStep F)) := by
  rintro ⟨k, ⟨s, j⟩, ⟨u, l⟩⟩
  refine ⟨Src.coord ((eRows R).symm k, ⟨s, j⟩, ((eFront t).symm ⟨u, l⟩)), fun F => ?_⟩
  rfl

end Perm

/-! ### The composite -/

section Composite

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable {t n : ℕ}

/-- Stage 1 as a map on positions is source-expressible. -/
theorem stage1_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : Pos β γ RowIdx ColIdx t → K => toFun (stage1 str (ofFun F))) :=
  (padArr_srcExpr (RowIdx := RowIdx) (ColIdx := ColIdx) (b₀ β) (b₀ γ) (rad RowIdx) str).comp
    (flatten_srcExpr.comp rotStep_srcExpr)

/-- Stage 2 as a map on positions is source-expressible. -/
theorem stage2_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : Pos β γ RowIdx ColIdx t → K => toFun (stage2 str (ofFun F))) :=
  (stage1_srcExpr str).comp
    ((padArr_srcExpr (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ)) (ColIdx := C₁ t) (b₀ γ) (0 : Fin 1)
        (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
        (rotStr (PadRow (b₀ β) (rad RowIdx) (RowIdx := RowIdx) (n := n)))).comp
      ((flatten_srcExpr
          (R := PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
            (n := Fintype.card β))
          (C := PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (ColIdx := C₁ t)
            (n := Fintype.card β) (t := t₁ RowIdx n (b₀ β)))
          (t := t₁ RowIdx n (b₀ β))).comp
        (rotStep_srcExpr
          (R := PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ))
            (n := Fintype.card β))
          (C := PadCol (0 : Fin 1) (rad (R₁ RowIdx ColIdx n t (b₀ γ))) (ColIdx := C₁ t)
            (n := Fintype.card β) (t := t₁ RowIdx n (b₀ β)))
          (t := t₁ RowIdx n (b₀ β)))))

/-- **`T` is source-expressible.** -/
theorem T_srcExpr (str : Fin t → Fin n) :
    SrcExpr (fun F : Pos β γ RowIdx ColIdx t → K => T str (ofFun F)) :=
  (stage2_srcExpr str).comp
    ((padArr_srcExpr (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (ColIdx := C₂ RowIdx n (b₀ β))
        (0 : Fin 1) (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
        (rotStr (PadRow (b₀ γ) (rad (R₁ RowIdx ColIdx n t (b₀ γ)))
          (RowIdx := R₁ RowIdx ColIdx n t (b₀ γ)) (n := Fintype.card β)))).comp
      (flatten_srcExpr
        (R := PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
          (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ))
        (C := PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
          (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ)))
        (t := t₂ RowIdx ColIdx n t (b₀ γ))))

end Composite

end Mathproof.Meta.FGSSrcExpr20260902

end Part_U18


section Part_U19

/-
Copyright (c) 2026 MathProof. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProof
-/

/-!
# General injective padding: reflection of exact `3`-tensor equivalence

## What this file adds

`Mathproof.SymplecticTI` proves the reflection statement

`spAct g₁ g₂ g₃ (pad3 A) = pad3 B → ∃ P₁ P₂ P₃, glAct P₁ P₂ P₃ A = B`

for **one specific padding**, the Lagrangian embedding `iota : U → Hyp K U`, and for transporters
that are linear equivalences of the doubled spaces `Hyp K U_i`.

That specialization is inessential. The engine of the argument, `pad_substitute`, is already stated
in `SymplecticTI` for an **arbitrary injective** `ι : U →ₗ[K] H`. This file completes the
generalization: the three mode-substitution lemmas and the cancellation step are re-proved for
arbitrary injective paddings

`ι₁ : U₁ →ₗ[K] H₁`,  `ι₂ : U₂ →ₗ[K] H₂`,  `ι₃ : U₃ →ₗ[K] H₃`

and arbitrary linear equivalences `g_i : H_i ≃ₗ[K] H_i`, with the `U_i` finite dimensional over the
field `K` and the `H_i` completely arbitrary (in particular of arbitrary, possibly unequal,
dimensions). The headline theorem is `gl_of_padded_general`.

## Why this is exactly §4.1 of the standalone note

§4.1 of `STANDALONE_SP3TI_TO_GL3TI_PROOF.md` needs "zero-extension preserves and reflects exact
tensor equivalence" for the rectangular-to-cubic padding, whose three coordinate inclusions are
three *different* injections into three copies of the same big space. Neither `pad3` (a single
`iota`, hence `H_i = Hyp K U_i` determined by `U_i`) nor any statement in `SymplecticTI` covers
that. `gl_of_padded_general` does, and is the reverse half of §4.1 in coordinate-free form;
`Mathproof.Meta.CubicZeroExtension20260902` instantiates it at the coordinate inclusions.

## Structure of the proof (identical to the `pad3_*` chain it generalizes)

* `padG_injective` — injectivity of `map ι₁ (map ι₂ ι₃)`, from
  `TensorProduct.map_injective_of_flat_flat` (every module over a field is flat).
* `padG_mode1_substitute` — `pad_substitute` applied verbatim with `ι := ι₁`, `j := map ι₂ ι₃`,
  `g := g₁`, `k := map g₂ g₃`.
* `padG_mode2_substitute`, `padG_mode3_substitute` — the same after braiding mode `2` (resp. `3`)
  to the front with `braid2`/`braid3`, using the naturality lemmas `braid2_map`/`braid3_map`
  unchanged. Unlike the `pad3_*` versions these take the already-chosen maps on the other modes as
  explicit arguments rather than quantifying over them inside the existential; the assembly consumes
  them in the order `1, 2, 3`, so nothing is lost and no `SupportLiftWitness` packaging is needed.
* `padG_cancel_substituted` — functoriality plus injectivity of the padding.
* `gl_of_padded_general` — the four steps composed.

`msupp` and `contract` are irreducible and are **never mentioned** in this file: every appeal to the
mode-support machinery goes through `pad_substitute`, whose statement is `msupp`-free. That is
precisely the elaboration discipline documented in `SymplecticTI`.
-/

namespace Mathproof.Meta.GLOfPaddedGeneral20260902

open TensorProduct
open Mathproof.SymplecticTI

variable {K : Type*} [Field K]
variable {U₁ U₂ U₃ H₁ H₂ H₃ : Type*}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]
variable [AddCommGroup H₁] [Module K H₁] [AddCommGroup H₂] [Module K H₂]
  [AddCommGroup H₃] [Module K H₃]

/-! ### The general padding -/

/-- **A general three-mode padding** `A ↦ (ι₁ ⊗ ι₂ ⊗ ι₃) A`. `pad3` is the case
`ι_i = iota : U_i → Hyp K U_i`. -/
noncomputable def padG (ι₁ : U₁ →ₗ[K] H₁) (ι₂ : U₂ →ₗ[K] H₂) (ι₃ : U₃ →ₗ[K] H₃) :
    U₁ ⊗[K] (U₂ ⊗[K] U₃) →ₗ[K] H₁ ⊗[K] (H₂ ⊗[K] H₃) :=
  TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃)

theorem padG_apply (ι₁ : U₁ →ₗ[K] H₁) (ι₂ : U₂ →ₗ[K] H₂) (ι₃ : U₃ →ₗ[K] H₃)
    (A : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    padG ι₁ ι₂ ι₃ A = TensorProduct.map ι₁ (TensorProduct.map ι₂ ι₃) A := rfl

/-- Three injective paddings give an injective three-mode padding. -/
theorem padG_injective {ι₁ : U₁ →ₗ[K] H₁} (hι₁ : Function.Injective ι₁)
    {ι₂ : U₂ →ₗ[K] H₂} (hι₂ : Function.Injective ι₂)
    {ι₃ : U₃ →ₗ[K] H₃} (hι₃ : Function.Injective ι₃) :
    Function.Injective (padG ι₁ ι₂ ι₃) :=
  TensorProduct.map_injective_of_flat_flat _ _ hι₁
    (TensorProduct.map_injective_of_flat_flat _ _ hι₂ hι₃)

/-! ### Mode substitution -/

/-- **Mode `1`.** Replace the padded mode-`1` transporter `g₁ ∘ ι₁` by `ι₁ ∘ P₁` for an honest
`P₁ ∈ GL(U₁)`, inside the tensor. This is `pad_substitute` with `j := map ι₂ ι₃` and
`k := map g₂ g₃`. -/
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

/-- **Mode `2`.** The mode-`1` map `m₁` already chosen is carried along unchanged; `braid2` moves
mode `2` to the front so that `pad_substitute` applies, and `braid2_map` unbraids the conclusion. -/
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

/-- **Mode `3`.** As mode `2`, with `braid3`; both previously chosen maps are carried along. -/
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

/-! ### Cancellation -/

/-- **Cancel the padding.** Once all three padded transporters have been replaced by
`ι_i ∘ P_i`, functoriality identifies the result with `padG ι₁ ι₂ ι₃ (glAct P₁ P₂ P₃ A)`, and
injectivity of the padding reflects the equality down to `U₁ ⊗ (U₂ ⊗ U₃)`. -/
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

/-! ### The general reflection theorem -/

/-- **§4.1, reverse half, in coordinate-free form.**

If three arbitrary injective paddings `ι_i : U_i →ₗ[K] H_i` of finite-dimensional spaces `U_i` into
arbitrary spaces `H_i` carry `A` and `B` to padded tensors that are related by three linear
equivalences `g_i` of the big spaces, then `A` and `B` were already related by three linear
equivalences of the small spaces.

No hypothesis of conciseness is used, the `H_i` need not be related to the `U_i` in any way, and no
hypothesis relates the three paddings to each other. The `pad3` reflection theorem
`Mathproof.SymplecticTI.gl_of_padded` is the special case `ι_i = iota`, `H_i = Hyp K U_i`. -/
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

/-! ### The forward half, for completeness

The forward half of §4.1 is elementary at this level of generality: it needs, for each mode, an
extension of `P_i ∈ GL(U_i)` to `f_i ∈ GL(H_i)` with `f_i ∘ ι_i = ι_i ∘ P_i`. That extension does
**not** exist for an arbitrary injective `ι_i` without further data (it needs a complement, i.e. a
retraction), so it is supplied at the point of use — in the coordinate setting of
`CubicZeroExtension20260902` it is the explicit block-diagonal extension by the identity. What is
unconditional is the intertwining consequence, recorded here. -/

/-- **Forward half, given intertwiners.** If each `f_i` extends `P_i` across the padding, then the
padded tensors are related by the `f_i`. -/
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

end Mathproof.Meta.GLOfPaddedGeneral20260902

end Part_U19


section Part_U20

/-
Copyright (c) 2026 MathProof. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProof
-/

/-!
# §4.1: rectangular-to-cubic zero extension preserves and reflects tensor equivalence

## The statement

`STANDALONE_SP3TI_TO_GL3TI_PROOF.md` §4.1: the three side lengths of the array produced by the
partition-deletion pipeline need not agree. Let `N` be their maximum and zero-extend the
`a × b × c` array `X` to the `N × N × N` array `cubeExt X`. Then

> Zero-extension preserves and reflects exact tensor equivalence.

That is `cubeExt_equiv_iff` below:

`(∃ P Q R invertible, (P,Q,R)·X = Y)  ↔  (∃ P' Q' R' invertible, (P',Q',R')·X̂ = Ŷ)`,

with `P : Matrix (Fin a) (Fin a) K`, `Q : Matrix (Fin b) (Fin b) K`, `R : Matrix (Fin c) (Fin c) K`
on the left and all three of `P', Q', R' : Matrix (Fin N) (Fin N) K` on the right.

## How each direction is proved

*Forward* (the note's "extend each original invertible transporter arbitrarily to an invertible map
on the larger coordinate space") is `extend`: the coordinate space `K^N` splits as
`inc(K^a) ⊕ (coordinates ≥ a)` with retraction `prj` and complementary projection `cmp`, and
`extend h e = inc ∘ e ∘ prj + cmp` is the block-diagonal extension of `e` by the identity. It is a
linear **equivalence** because `extL` is multiplicative in `e` (`extL_comp`) and sends the identity
to the identity (`extL_id`); the inverse is the extension of `e⁻¹`.

*Reverse* (the note's mode-support argument) is `gl_of_padded_general` from
`Mathproof.Meta.GLOfPaddedGeneral20260902`, applied to the three coordinate inclusions
`inc K a N`, `inc K b N`, `inc K c N`, which are injective exactly when `a, b, c ≤ N`. This is where
the actual content sits: nothing about the three inclusions being into the *same* space `K^N` is
used, and no conciseness hypothesis is needed.

The two are glued by the coordinate/tensor dictionary. `CoordTensorBridgeGen20260902` supplies it
only for **cubic** arrays over a single index type, which is not enough here: the small side is
genuinely rectangular. The rectangular *action* already exists as
`Mathproof.Meta.FGSFlatArrays20260902.act`, and is used verbatim; this file adds the missing
three-index-type *dictionary* `toTensor₃` / `toTensor₃_act` / `glAct₃_toTensor₃_iff`, proved exactly
as the cubic one, and records `act_eq_actι` and `toTensor₃_eq_toTensor` (both `rfl`) so that the
cubic API of `CoordTensorBridgeGen20260902` — hence `act3` and `GL3TI.Rel` — is literally a special
case. The bridge identity that makes zero-extension visible on the tensor side is
`toTensor₃_cubeExt`.

## Also exported

* `cubeExt_src` — every output coordinate of `cubeExt X` is one input coordinate or the constant
  `0`, in the `Src` vocabulary of `ProjectionReductions20260902`. This is the §4.2 clause for this
  step, and it is what the packaging of the whole reduction as a constant-free projection consumes.
* `card_cube` — `Fintype.card (Fin N × Fin N × Fin N) = N ^ 3`, the §4.3 size fact for this step.
-/

namespace Mathproof.Meta.CubicZeroExtension20260902

open TensorProduct Module
open Mathproof.SymplecticTI
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.CoordTensorBridgeGen20260902
open Mathproof.Meta.GLOfPaddedGeneral20260902
open Mathproof.Meta.FGSFlatArrays20260902

universe u

variable {K : Type u} [Field K]

/-! ## 1. The coordinate/tensor dictionary over three index types

`CoordTensorBridgeGen20260902` proves all of this for a single index type `ι`, i.e. for cubic
arrays. The rectangular side of §4.1 needs three independent index types; the proofs are the same
line for line. -/

section Bridge

variable {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι₃] [DecidableEq ι₃]

/-- The standard basis of `K^ι₁ ⊗ (K^ι₂ ⊗ K^ι₃)`, indexed by `ι₁ × ι₂ × ι₃`. -/
noncomputable def tb₃ (K : Type u) [Field K] (ι₁ ι₂ ι₃ : Type)
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃] :
    Module.Basis (ι₁ × ι₂ × ι₃) K ((ι₁ → K) ⊗[K] ((ι₂ → K) ⊗[K] (ι₃ → K))) :=
  (Pi.basisFun K ι₁).tensorProduct ((Pi.basisFun K ι₂).tensorProduct (Pi.basisFun K ι₃))

theorem tb₃_apply (i : ι₁) (j : ι₂) (k : ι₃) :
    tb₃ K ι₁ ι₂ ι₃ (i, j, k) =
      (Pi.basisFun K ι₁ i) ⊗ₜ[K] ((Pi.basisFun K ι₂ j) ⊗ₜ[K] (Pi.basisFun K ι₃ k)) := by
  simp [tb₃, Module.Basis.tensorProduct_apply]

/-- **Rectangular arrays as tensors.** -/
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

/-- The cubic dictionary of `CoordTensorBridgeGen20260902` is literally the diagonal case. -/
theorem toTensor₃_eq_toTensor (ι : Type) [Fintype ι] [DecidableEq ι] :
    toTensor₃ K ι ι ι = toTensor (K := K) ι := rfl

/-! The three-matrix action on a rectangular array,
`((P,Q,R)·A)_{ijk} = ∑ P_{ii'} Q_{jj'} R_{kk'} A_{i'j'k'}`, is
`Mathproof.Meta.FGSFlatArrays20260902.act`; nothing new is defined here. -/

/-- On cubic arrays `act` **is** `actι`, so `GL3TI.Rel`, `act3`, `actι` and `act` are all the same
relation. -/
theorem act_eq_actι {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q R : Matrix ι ι K) (A : ι × ι × ι → K) :
    act P Q R A = actι P Q R A := rfl

/-- The abstract action of three matrices on the rectangular tensor product. -/
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

/-- **The action dictionary, rectangular version.** -/
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

/-- **The `GL` dictionary, rectangular version.** -/
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

/-! ## 2. The coordinate inclusion `K^a → K^N` and its block-diagonal extension -/

section Inclusion

variable {a b c N : ℕ}

/-- **Zero-extension of a coordinate vector**, `K^a → K^N`: keep coordinate `I` when `I < a`, and
put `0` in the new coordinates. On basis vectors this is `e_i ↦ e_{Fin.castLE i}`
(`inc_single`). -/
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

/-- The retraction `K^N → K^a`, restriction to the first `a` coordinates. -/
def prj (K : Type u) [Field K] {a N : ℕ} (h : a ≤ N) : (Fin N → K) →ₗ[K] (Fin a → K) where
  toFun w := fun i => w (Fin.castLE h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem prj_apply (h : a ≤ N) (w : Fin N → K) (i : Fin a) :
    prj K h w i = w (Fin.castLE h i) := rfl

/-- The complementary projection of `K^N`: kill the first `a` coordinates. -/
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

/-- **The block-diagonal extension** `e ↦ e ⊕ 1`, as a linear map. -/
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

/-- **The block-diagonal extension** `e ↦ e ⊕ 1`, as a linear equivalence of `K^N`.
This is the note's "extend each original invertible transporter arbitrarily to an invertible map on
the larger coordinate space", made explicit. -/
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

/-- **The intertwining property**: the extension restricted to the embedded block is `e`. -/
theorem extend_comp_inc (h : a ≤ N) (e : (Fin a → K) ≃ₗ[K] (Fin a → K)) :
    ((extend h e : (Fin N → K) ≃ₗ[K] (Fin N → K)) : (Fin N → K) →ₗ[K] (Fin N → K)) ∘ₗ
        inc K a N = inc K a N ∘ₗ (e : (Fin a → K) →ₗ[K] (Fin a → K)) := by
  rw [coe_extend]
  exact extL_comp_inc h _

/-- On basis vectors the inclusion is `e_i ↦ e_{Fin.castLE i}`. -/
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

/-! ## 3. The cubic zero extension of an array -/

section CubeExt

variable {a b c N : ℕ}

/-- **The rectangular-to-cubic zero extension.** Output coordinate `(I,J,L)` of `cubeExt K N X` is
the input coordinate `(I,J,L)` when all three indices are in range, and `0` otherwise. Every output
coordinate is therefore an input coordinate or `0` — see `cubeExt_src`. -/
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

/-- **§4.2 for this step.** Every output coordinate of the zero extension is one input coordinate
or the constant `0`: no sums, no products, no other constants. -/
theorem cubeExt_src (z : Fin N × Fin N × Fin N) :
    ∃ s : Src (Fin a × Fin b × Fin c),
      ∀ X : Fin a × Fin b × Fin c → K, cubeExt K N X z = s.eval X := by
  by_cases h : (z.1 : ℕ) < a ∧ (z.2.1 : ℕ) < b ∧ (z.2.2 : ℕ) < c
  · exact ⟨Src.coord (⟨(z.1 : ℕ), h.1⟩, ⟨(z.2.1 : ℕ), h.2.1⟩, ⟨(z.2.2 : ℕ), h.2.2⟩),
      fun X => by rw [cubeExt_apply, dif_pos h]; rfl⟩
  · exact ⟨Src.zero, fun X => by rw [cubeExt_apply, dif_neg h]; rfl⟩

/-- **§4.3 for this step**: the cubic output has `N ^ 3` coordinates. -/
theorem card_cube (N : ℕ) : Fintype.card (Fin N × Fin N × Fin N) = N ^ 3 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  ring

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

/-- The zero extension, as a linear map. -/
def cubeExtL (K : Type u) [Field K] {a b c : ℕ} (N : ℕ) :
    (Fin a × Fin b × Fin c → K) →ₗ[K] (Fin N × Fin N × Fin N → K) where
  toFun := cubeExt K N
  map_add' := cubeExt_add
  map_smul' := cubeExt_smul

theorem cubeExtL_apply (X : Fin a × Fin b × Fin c → K) :
    cubeExtL K N X = cubeExt K N X := rfl

/-- The zero extension on a basis array. -/
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

/-- The array `Pi.single` is the standard basis vector. -/
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

/-- **The bridge identity for §4.1**: on the tensor side, zero extension of the array is exactly
the three-mode padding by the coordinate inclusions. -/
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

/-! ## 4. §4.1: zero extension preserves and reflects exact tensor equivalence -/

section Main

variable {a b c N : ℕ}

/-- **§4.1, in coordinates.**

`X` and `Y`, of shape `a × b × c`, are equivalent under three independent invertible matrices of the
three (possibly different) sizes **iff** their zero extensions to shape `N × N × N` are equivalent
under three independent invertible `N × N` matrices, whenever `a, b, c ≤ N`.

*Forward* is `extend`: block-diagonal extension by the identity.
*Reverse* is `gl_of_padded_general`, i.e. the mode-support argument, applied to the three coordinate
inclusions. -/
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
  · -- FORWARD
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
  · -- REVERSE
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

/-- The same statement with both actions written through `actι` (equivalently `act3`, equivalently
`GL3TI.Rel`) in the cubic case, for callers that only ever see square shapes. -/
theorem cubeExt_equiv_iff_cubic {n N : ℕ} (h : n ≤ N)
    (X Y : Fin n × Fin n × Fin n → K) :
    (∃ P Q R : Matrix (Fin n) (Fin n) K,
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ actι P Q R X = Y) ↔
      (∃ P' Q' R' : Matrix (Fin N) (Fin N) K,
        IsUnit P' ∧ IsUnit Q' ∧ IsUnit R' ∧
          actι P' Q' R' (cubeExt K N X) = cubeExt K N Y) := by
  simpa only [act_eq_actι] using cubeExt_equiv_iff (K := K) h h h X Y

end Main

end Mathproof.Meta.CubicZeroExtension20260902

end Part_U20


section Part_U21


/-!
# Packaging: from a block-equivalence encoding to a constant-free `p`-projection into `GL3TI`

## Purpose

§4 of `D:/proof/COMPLETE_FULL_PROOFS_SP3TI_TO_GL3TI_PROOF.md`, in the generality of any coordinate
problem `P` that admits an encoding `E` into per-block partitioned arrays with

* correctness `P.Rel m A B ↔ BlockEquiv (str m) (E m A) (E m B)`,
* source-expressibility of `E` (every coordinate of `E m A` is a coordinate of `A` or `0, 1, −1`),
* a polynomial bound on the cube side `N m` of `T (E m A)` in terms of `card (P.Idx m)`.

Then `Π m A := cubeExt N (reindex (T (str m) (E m A)))` is a `Projection P (GL3TI K)`:

* `Tf`, `T_equiv_iff` — the output of `T` reindexed to `Fin a × Fin b × Fin c`;
* `cube`, `cube_equiv_iff` — zero-extended to `Fin N × Fin N × Fin N`, equivalence transported
  (`three_deletions`, `flatEquiv_reindex3`, `cubeExt_equiv_iff`);
* `cube_srcExpr` — the whole map is source-expressible (`T_srcExpr`, `cubeExt_src`);
* `projectionOfEncoding` — the `Projection`.

## DAG chain walked

`Matrix.isUnit_iff_isUnit_det`, `Fintype.equivFin`, `Fintype.card_prod`, `Fintype.card_fin`,
`Classical.choose_spec`; tree: `three_deletions`, `flatEquiv_reindex3`, `flatEquiv_of_subsingleton`,
`cubeExt_equiv_iff`, `cubeExt_src`, `T_srcExpr`, `SrcExpr.comp/perm`.
-/

namespace Mathproof.Meta.FGSPackaging20260902

open Mathproof.Meta.ProjectionReductions20260902 (Src CoordProblem Projection GL3TI act3)
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSFlatArrays20260902
open Mathproof.Meta.FGSFlatReindex20260902
open Mathproof.Meta.FGSThreeDeletions20260902
open Mathproof.Meta.FGSSrcExpr20260902
open Mathproof.Meta.CubicZeroExtension20260902 (cubeExt cubeExt_src cubeExt_equiv_iff)

universe u

variable {K : Type u} [Field K]

/-! ### Generic reindexing of plain three-matrix equivalence -/

section Reindex

variable {I₁ I₂ I₃ J₁ J₂ J₃ : Type}
variable [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype I₃] [DecidableEq I₃]
variable [Fintype J₁] [DecidableEq J₁] [Fintype J₂] [DecidableEq J₂] [Fintype J₃] [DecidableEq J₃]

/-- Plain equivalence (unit determinants) is invariant under reindexing the three axes. -/
theorem exists_act_reindex3 (e₁ : I₁ ≃ J₁) (e₂ : I₂ ≃ J₂) (e₃ : I₃ ≃ J₃) (X Y : I₁ × I₂ × I₃ → K) :
    (∃ (P₁ : Matrix I₁ I₁ K) (P₂ : Matrix I₂ I₂ K) (P₃ : Matrix I₃ I₃ K),
        IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ X = Y) ↔
      (∃ (Q₁ : Matrix J₁ J₁ K) (Q₂ : Matrix J₂ J₂ K) (Q₃ : Matrix J₃ J₃ K),
        IsUnit Q₁.det ∧ IsUnit Q₂.det ∧ IsUnit Q₃.det ∧
          act Q₁ Q₂ Q₃ (reindex3 e₁ e₂ e₃ X) = reindex3 e₁ e₂ e₃ Y) := by
  have h := flatEquiv_reindex3 e₁ e₂ e₃ (fun _ : I₁ => ()) (fun _ : I₂ => ()) (fun _ : I₃ => ()) X Y
  rw [flatEquiv_of_subsingleton, flatEquiv_of_subsingleton] at h
  exact h

/-- `IsUnit P.det` versus `IsUnit P` in a triple of existentials. -/
theorem exists_det_iff_isUnit {φ : Matrix I₁ I₁ K → Matrix I₂ I₂ K → Matrix I₃ I₃ K → Prop} :
    (∃ P₁ P₂ P₃, IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ φ P₁ P₂ P₃) ↔
      (∃ P₁ P₂ P₃, IsUnit P₁ ∧ IsUnit P₂ ∧ IsUnit P₃ ∧ φ P₁ P₂ P₃) := by
  simp only [Matrix.isUnit_iff_isUnit_det]

end Reindex

/-- The coordinate action of `ProjectionReductions20260902` is the flat action. -/
theorem act3_eq_act {N : ℕ} (P Q R : Matrix (Fin N) (Fin N) K) (A : Fin N × Fin N × Fin N → K) :
    act3 K P Q R A = act P Q R A := by
  funext ⟨i, j, k⟩
  rfl

theorem gl3ti_rel_iff {N : ℕ} (A B : Fin N × Fin N × Fin N → K) :
    (GL3TI K).Rel N A B ↔
      ∃ P Q R : Matrix (Fin N) (Fin N) K,
        IsUnit P ∧ IsUnit Q ∧ IsUnit R ∧ act P Q R A = B := by
  simp only [GL3TI, act3_eq_act]

/-! ### The output of `T`, reindexed and cubed -/

section Cube

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable (RowIdx : β → Type) (ColIdx : γ → Type)
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]
variable (n t : ℕ)

/-- Rows of the output of `T`. -/
abbrev OutR : Type :=
  Σ b : Fin 1, PadRow (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (RowIdx := R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)) (n := Fintype.card γ) b

/-- Columns of the output of `T`. -/
abbrev OutC : Type :=
  Σ s : Fin 1, PadCol (0 : Fin 1) (rad (R₂ RowIdx ColIdx n t (b₀ β) (b₀ γ)))
    (ColIdx := C₂ RowIdx n (b₀ β)) (n := Fintype.card γ) (t := t₂ RowIdx ColIdx n t (b₀ γ)) s

/-- The three side lengths of the output of `T`. -/
noncomputable abbrev sideA : ℕ := Fintype.card (OutR RowIdx ColIdx n t)
noncomputable abbrev sideB : ℕ := Fintype.card (OutC RowIdx ColIdx n t)
noncomputable abbrev sideC : ℕ := t₂ RowIdx ColIdx n t (b₀ γ)

/-- The cube side. -/
noncomputable abbrev Nside : ℕ := max (sideA RowIdx ColIdx n t) (max (sideB RowIdx ColIdx n t) (sideC RowIdx ColIdx n t))

theorem sideA_le : sideA RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t := le_max_left _ _
theorem sideB_le : sideB RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t :=
  le_max_of_le_right (le_max_left _ _)
theorem sideC_le : sideC RowIdx ColIdx n t ≤ Nside RowIdx ColIdx n t :=
  le_max_of_le_right (le_max_right _ _)

variable {RowIdx ColIdx n t}

/-- The output of `T` on `Fin`-indexed axes. -/
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

/-- The cubed output. -/
noncomputable def cube (str : Fin t → Fin n) (X : PArr K β γ RowIdx ColIdx t) :
    Fin (Nside RowIdx ColIdx n t) × Fin (Nside RowIdx ColIdx n t) × Fin (Nside RowIdx ColIdx n t) → K :=
  cubeExt K (Nside RowIdx ColIdx n t) (Tf str X)

/-- **Correctness of the cubed transform**: block-equivalence is `GL3TI` on the cube. -/
theorem cube_equiv_iff (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    BlockEquiv str X Y ↔ (GL3TI K).Rel (Nside RowIdx ColIdx n t) (cube str X) (cube str Y) := by
  rw [T_equiv_iff, gl3ti_rel_iff,
    cubeExt_equiv_iff (sideA_le RowIdx ColIdx n t) (sideB_le RowIdx ColIdx n t)
      (sideC_le RowIdx ColIdx n t)]
  rfl

/-- **Source-expressibility of the cubed transform** given that of the encoding. -/
theorem cube_srcExpr {ι : Type} (str : Fin t → Fin n) (E : (ι → K) → PArr K β γ RowIdx ColIdx t)
    (hE : SrcExpr (fun A => toFun (E A))) :
    SrcExpr (fun A : ι → K => cube str (E A)) := by
  have h1 : SrcExpr (fun A : ι → K => Tf str (E A)) :=
    (hE.comp (T_srcExpr str)).perm fun y : Fin (sideA RowIdx ColIdx n t) ×
        Fin (sideB RowIdx ColIdx n t) × Fin (sideC RowIdx ColIdx n t) =>
      ((Fintype.equivFin (OutR RowIdx ColIdx n t)).symm y.1,
        (Fintype.equivFin (OutC RowIdx ColIdx n t)).symm y.2.1, y.2.2)
  have h2 : SrcExpr (fun X : Fin (sideA RowIdx ColIdx n t) × Fin (sideB RowIdx ColIdx n t) ×
      Fin (sideC RowIdx ColIdx n t) → K => cubeExt K (Nside RowIdx ColIdx n t) X) :=
    fun z => cubeExt_src z
  exact h1.comp h2

end Cube

/-! ### The projection -/

section Proj

variable (P : CoordProblem K)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β] [Fintype γ] [DecidableEq γ]
  [Nonempty γ]
variable (RowIdx : ℕ → β → Type) (ColIdx : ℕ → γ → Type)
variable [∀ m b, Fintype (RowIdx m b)] [∀ m b, DecidableEq (RowIdx m b)]
variable [∀ m s, Fintype (ColIdx m s)] [∀ m s, DecidableEq (ColIdx m s)]
variable (t nstr : ℕ → ℕ) (str : ∀ m, Fin (t m) → Fin (nstr m))
variable (E : ∀ m, (P.Idx m → K) → PArr K β γ (RowIdx m) (ColIdx m) (t m))

/-- **The projection built from an encoding.** -/
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
    have hA : (fun j => Src.eval A (Classical.choose (cube_srcExpr (str m) (E m) (hsrc m) j))) =
        cube (str m) (E m A) :=
      funext fun j => (Classical.choose_spec (cube_srcExpr (str m) (E m) (hsrc m) j) A).symm
    have hB : (fun j => Src.eval B (Classical.choose (cube_srcExpr (str m) (E m) (hsrc m) j))) =
        cube (str m) (E m B) :=
      funext fun j => (Classical.choose_spec (cube_srcExpr (str m) (E m) (hsrc m) j) B).symm
    show P.Rel m A B ↔ (GL3TI K).Rel _ _ _
    rw [hcorrect, cube_equiv_iff]
    exact Iff.of_eq (congrArg₂ _ hA.symm hB.symm)

end Proj

end Mathproof.Meta.FGSPackaging20260902

end Part_U21


section Part_U22


/-!
# The symplectic dictionary: `IsSymplecticMat` on doubled coordinates ⟷ `IsSymplectic` on `Hyp`

## Purpose

`ProjectionReductions20260902.Sp3TI` is stated with matrices `g` on `Fin n ⊕ Fin n` satisfying
`gᵀ * stdJ * g = stdJ`. `SymplecticTI.gl_iff_padded` is stated with linear equivalences of
`Hyp K U = U × Dual U` preserving `omegaH`. This module is the dictionary between the two:

* `formJ n x y := x ⬝ᵥ (stdJ *ᵥ y)`, and `isSymplecticMat_iff_formJ`: `g` is symplectic iff it
  preserves `formJ` (by evaluating on standard basis vectors);
* `hypVec n : Hyp K (Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)` (standard primal/dual coordinates,
  primal block first), an isometry `formJ (hypVec x) (hypVec y) = omegaH x y`, and
  `hypVec_iota : hypVec (iota u) = Sum.elim u 0` — the Lagrangian embedding is literal zero-padding
  of the coordinate vector;
* `matOf h` (the matrix of a linear equivalence of `Hyp`, invertible) and `equivOf g hg` (the linear
  equivalence of an invertible matrix), with `isSymplecticMat_matOf` and `isSymplectic_equivOf`.

## DAG queries (active snapshot 20260902T033037Z-a57018fc)

`forward Mathproof.SymplecticTI.hypCoordEquiv` → only `hypCoordEquiv_isometry`,
`standardCoordEquiv(_isometry)`; `forward Mathproof.SymplecticTI.IsSymplectic` → the abstract
consumers (`gl_iff_padded`, `standardCoordEquiv_conjugates`, `OPEN_basisChange_of_congruent_forms`,
`Consequences.SpOrbit3`), none of which reaches a matrix; `forward Matrix.fromBlocks_mulVec` → only
`Mathproof.DetRepBridge.padOne_no_common_kernel` and Mathlib's `SymplecticGroup` internals (whose
`Matrix.J = fromBlocks 0 (-1) 1 0` is `-stdJ` and whose group is `A * J * Aᵀ = J`, a different
convention, so not reused). Hence this dictionary did not exist in the tree.
-/

namespace Mathproof.Meta.SymplecticMatDictionary20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.CoordTensorBridgeGen20260902
open Mathproof.SymplecticTI

universe u

variable {K : Type u} [Field K]

/-- The coordinate form `x ⬝ᵥ (J *ᵥ y)` with `J = stdJ`. -/
def formJ (n : ℕ) (x y : Fin n ⊕ Fin n → K) : K := x ⬝ᵥ (stdJ K n *ᵥ y)

theorem dotProduct_transpose_mul_mul_mulVec {n : ℕ} (g M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (x y : Fin n ⊕ Fin n → K) :
    x ⬝ᵥ ((gᵀ * M * g) *ᵥ y) = (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- **Matrix dictionary**: `gᵀ J g = J` iff `g` preserves the coordinate form. -/
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

/-! ### Doubled coordinates -/

/-- Doubled coordinate vectors as primal/dual pairs. -/
def dbl (n : ℕ) : (Fin n ⊕ Fin n → K) ≃ₗ[K] CoordHyp K n :=
  LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) K K

theorem stdJ_mulVec_inl {n : ℕ} (y : Fin n ⊕ Fin n → K) (i : Fin n) :
    (stdJ K n *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [stdJ, Matrix.fromBlocks_mulVec]

theorem stdJ_mulVec_inr {n : ℕ} (y : Fin n ⊕ Fin n → K) (i : Fin n) :
    (stdJ K n *ᵥ y) (Sum.inr i) = -y (Sum.inl i) := by
  simp [stdJ, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]

/-- `formJ` is the hyperbolic form of `SymplecticTI` in doubled coordinates. -/
theorem coordHyperForm_dbl {n : ℕ} (x y : Fin n ⊕ Fin n → K) :
    coordHyperForm (dbl n x) (dbl n y) = formJ n x y := by
  simp only [coordHyperForm, dbl, formJ, dotProduct, Fintype.sum_sum_type, stdJ_mulVec_inl,
    stdJ_mulVec_inr, LinearEquiv.sumArrowLequivProdArrow_apply_fst,
    LinearEquiv.sumArrowLequivProdArrow_apply_snd]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The abstract hyperbolic double in doubled coordinates, primal block first. -/
noncomputable def hypVec (n : ℕ) : Hyp K (Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  hypCoordEquiv K n ≪≫ₗ (dbl n).symm

/-- `hypVec` is an isometry from `omegaH` to `formJ`. -/
theorem formJ_hypVec {n : ℕ} (x y : Hyp K (Fin n → K)) :
    formJ n (hypVec n x) (hypVec n y) = omegaH x y := by
  rw [← coordHyperForm_dbl]
  simp only [hypVec, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact hypCoordEquiv_isometry K n x y

/-- The Lagrangian embedding is zero-padding of the coordinate vector. -/
theorem hypVec_iota {n : ℕ} (u : Fin n → K) :
    hypVec n (iota u : Hyp K (Fin n → K)) = Sum.elim u 0 := by
  simp only [hypVec, LinearEquiv.trans_apply, hypCoordEquiv_apply, iota_apply, map_zero]
  funext s
  rcases s with i | i
  · simp [dbl]
  · simp [dbl]

/-! ### Symplectic matrices ⟷ symplectic equivalences -/

/-- The matrix of a linear equivalence of `Hyp`, in doubled coordinates. -/
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

theorem isUnit_matOf {n : ℕ} (h : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K)) :
    IsUnit (matOf h) :=
  isUnit_toMatrix' _

theorem isSymplecticMat_matOf {n : ℕ} (h : Hyp K (Fin n → K) ≃ₗ[K] Hyp K (Fin n → K))
    (hs : IsSymplectic h) : IsSymplecticMat K (matOf h) := by
  rw [isSymplecticMat_iff_formJ]
  intro x y
  rw [matOf_mulVec, matOf_mulVec, formJ_hypVec, hs, ← formJ_hypVec,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The linear equivalence of `Hyp` given by an invertible matrix in doubled coordinates. -/
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

/-- Symplectic matrices are invertible (restated from `ProjectionReductions20260902`). -/
theorem isUnit_of_isSymplecticMat' {n : ℕ} (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hg : IsSymplecticMat K g) : IsUnit g :=
  isUnit_of_isSymplecticMat K g hg

end Mathproof.Meta.SymplecticMatDictionary20260902

end Part_U22


section Part_U23


/-!
# The padding projection `GL3TI ⟶ Sp3TI`, in coordinates

## Purpose

This closes gap (C₁) of `TISpCertificationAudit20260902`: the abstract `SymplecticTI.gl_iff_padded`
is transported to the concrete coordinate problems of `ProjectionReductions20260902`, producing a
`Projection (GL3TI K) (Sp3TI K)` — a `p`-projection whose every output coordinate is an input
coordinate or `0` (`padSrc`), with side lengths `n ↦ 2n` and `8 n³ ≤ 8 (n³ + 1)` output cells.

* `padArr A` is literal zero-padding of a cubic array to the doubled index `Fin n ⊕ Fin n`;
* `toTensorH n` identifies doubled arrays with `Hyp ⊗ (Hyp ⊗ Hyp)` through `hypVec`;
* `toTensorH_padArr : toTensorH (padArr A) = pad3 (toTensor A)` — padding is the Lagrangian
  embedding (`hypVec_iota`);
* `sp3ti_iff` — the `Sp3TI` matrix relation is `spAct` by symplectic equivalences
  (`matOf`/`equivOf` of `SymplecticMatDictionary20260902`);
* `gl3ti_iff_sp3ti_pad` — the instancewise correctness, which is `gl_iff_padded` verbatim after the
  two dictionaries;
* `padProjection : Projection (GL3TI K) (Sp3TI K)`.

With the reverse projection (the FGS gadget, in progress in `FGSGadget*20260902`),
`ti_eq_tisp_of_projections padProjection _` gives class equality.

## DAG chain walked

`Mathproof.SymplecticTI.pad3 → gl_iff_padded / padded_of_gl / gl_of_padded` (the abstract
statement consumed here), `Mathproof.SymplecticTI.hypCoordEquiv → hypCoordEquiv_isometry`
(the only isometry into coordinates; extended by `hypVec` in the dictionary module),
`Module.Basis.map → Module.Basis.map_repr / map_apply` (basis transport used for `tbH`).
-/

namespace Mathproof.Meta.PaddingProjection20260902

open Matrix
open TensorProduct
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.CoordTensorBridgeGen20260902
open Mathproof.Meta.SymplecticMatDictionary20260902
open Mathproof.SymplecticTI

universe u

variable {K : Type u} [Field K]

/-- The doubled index. -/
abbrev S (n : ℕ) := Fin n ⊕ Fin n

/-- The hyperbolic double of `K^n`. -/
abbrev H (K : Type u) [Field K] (n : ℕ) := Hyp K (Fin n → K)

/-- The source map of the padding projection: an input coordinate on the primal block, `0`
elsewhere. -/
def padSrc {n : ℕ} : S n × S n × S n → Src (Fin n × Fin n × Fin n)
  | (Sum.inl i, Sum.inl j, Sum.inl k) => Src.coord (i, j, k)
  | _ => Src.zero

/-- Zero-padding of a cubic array to the doubled index. -/
def padArr {n : ℕ} (A : Fin n × Fin n × Fin n → K) : S n × S n × S n → K :=
  fun j => (padSrc j).eval A

@[simp] theorem padArr_inl {n : ℕ} (A : Fin n × Fin n × Fin n → K) (i j k : Fin n) :
    padArr A (Sum.inl i, Sum.inl j, Sum.inl k) = A (i, j, k) := rfl

theorem padArr_eq_zero {n : ℕ} (A : Fin n × Fin n × Fin n → K) (y : S n × S n × S n)
    (hy : ∀ i j k : Fin n, y ≠ (Sum.inl i, Sum.inl j, Sum.inl k)) : padArr A y = 0 := by
  rcases y with ⟨a | a, b | b, c | c⟩
  · exact absurd rfl (hy a b c)
  all_goals rfl

/-! ### Doubled arrays as tensors over `Hyp` -/

/-- Transport of the three tensor factors from doubled coordinates to `Hyp`. -/
noncomputable def congrH (n : ℕ) :
    (S n → K) ⊗[K] ((S n → K) ⊗[K] (S n → K)) ≃ₗ[K] H K n ⊗[K] (H K n ⊗[K] H K n) :=
  TensorProduct.congr (hypVec n).symm (TensorProduct.congr (hypVec n).symm (hypVec n).symm)

/-- Doubled arrays as tensors over `Hyp`. -/
noncomputable def toTensorH (n : ℕ) :
    (S n × S n × S n → K) ≃ₗ[K] H K n ⊗[K] (H K n ⊗[K] H K n) :=
  toTensor (S n) ≪≫ₗ congrH n

/-- The transported standard basis of `Hyp ⊗ (Hyp ⊗ Hyp)`, indexed by the doubled index. -/
noncomputable def tbH (n : ℕ) : Module.Basis (S n × S n × S n) K (H K n ⊗[K] (H K n ⊗[K] H K n)) :=
  (tb (S n)).map (congrH n)

theorem repr_toTensorH {n : ℕ} (A : S n × S n × S n → K) (y : S n × S n × S n) :
    (tbH n).repr (toTensorH n A) y = A y := by
  simp only [tbH, Module.Basis.map_repr, toTensorH, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact repr_toTensor A y

theorem hypVec_symm_single {n : ℕ} (i : Fin n) :
    (hypVec (K := K) n).symm (Pi.basisFun K (S n) (Sum.inl i)) =
      (iota (Pi.basisFun K (Fin n) i) : H K n) := by
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
  rw [show (e (S n) (Sum.inl i) : S n → K) = Pi.basisFun K (S n) (Sum.inl i) from rfl,
    show (e (S n) (Sum.inl j) : S n → K) = Pi.basisFun K (S n) (Sum.inl j) from rfl,
    show (e (S n) (Sum.inl k) : S n → K) = Pi.basisFun K (S n) (Sum.inl k) from rfl,
    hypVec_symm_single, hypVec_symm_single, hypVec_symm_single]

/-- **Padding is the Lagrangian embedding.** -/
theorem toTensorH_padArr {n : ℕ} (A : Fin n × Fin n × Fin n → K) :
    toTensorH n (padArr A) = pad3 (toTensor (Fin n) A) := by
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

/-! ### The `Sp3TI` relation as `spAct` -/

theorem matOf_equivOf {n : ℕ} (P : Matrix (S n) (S n) K) (hP : IsUnit P) :
    matOf (equivOf P hP) = P := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, matOf_mulVec, hypVec_equivOf,
    LinearEquiv.apply_symm_apply]

/-- `spAct` by equivalences of `Hyp` is `glActMat` by their matrices, through `congrH`. -/
theorem spAct_congrH {n : ℕ} (g₁ g₂ g₃ : H K n ≃ₗ[K] H K n)
    (T : (S n → K) ⊗[K] ((S n → K) ⊗[K] (S n → K))) :
    spAct g₁ g₂ g₃ (congrH n T) = congrH n (glActMat (matOf g₁) (matOf g₂) (matOf g₃) T) := by
  have hpt : ∀ (g : H K n ≃ₗ[K] H K n) (x : S n → K),
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

/-- **The `Sp` dictionary.** -/
theorem sp3ti_iff {n : ℕ} (A' B' : S n × S n × S n → K) :
    (Sp3TI K).Rel n A' B' ↔
      ∃ g₁ g₂ g₃ : H K n ≃ₗ[K] H K n, IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧
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

/-- **The `GL` dictionary**, specialised. -/
theorem gl3ti_iff {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔
      ∃ e₁ e₂ e₃ : (Fin n → K) ≃ₗ[K] (Fin n → K),
        glAct e₁ e₂ e₃ (toTensor (Fin n) A) = toTensor (Fin n) B :=
  glAct_toTensor_iff A B

/-- **Instancewise correctness of padding, in coordinates.** -/
theorem gl3ti_iff_sp3ti_pad {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (Sp3TI K).Rel n (padArr A) (padArr B) := by
  rw [gl3ti_iff, sp3ti_iff, toTensorH_padArr, toTensorH_padArr]
  exact gl_iff_padded (toTensor (Fin n) A) (toTensor (Fin n) B)

/-- **The padding projection** `GL3TI ⟶ Sp3TI`. -/
def padProjection : Projection (GL3TI K) (Sp3TI K) where
  size := id
  src := fun _ j => padSrc j
  polyBound := ⟨8, 1, fun n => by
    change Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) ≤
      8 * (Fintype.card (Fin n × Fin n × Fin n) + 1) ^ 1
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, pow_one]
    have : (n + n) * ((n + n) * (n + n)) = 8 * (n * (n * n)) := by ring
    omega⟩
  correct := fun _ A B => gl3ti_iff_sp3ti_pad A B

#print axioms gl3ti_iff_sp3ti_pad

end Mathproof.Meta.PaddingProjection20260902

end Part_U23


section Part_U24


/-!
# Linked block-equivalence, part 1: assembling per-stratum frontal transporters

## Where this sits

FGS's Theorem `kts` (their §`sss4`) is about **linked** block-equivalence: transformations
`(S_1 ⊕ … ⊕ S_m̄, S_{1'} ⊕ … ⊕ S_{n̄'}, S_{1''} ⊕ … ⊕ S_{t̄''})` in which some diagonal blocks are
*required* to be equal or mutually contragredient. Verbatim, their eq. `ghq`:

> `S_α = S_β` if `α ∼ β`,  `S_α = S_β^{-T}` if `α ⋈ β`.

That is the notion our four-tensor system needs, and plain `BlockEquiv` cannot express it: a single
(row, column) mode-pair only ever relates two transporters *contragrediently*
(`FGSGadgetCoupling20260902.coupling_solve`), and a second slice in the same pair only adds a
centraliser condition (`centralizer_of_two_couplings`). "Row block `U_i` and column block `U_i`
carry the same map" has to be imposed, not derived.

This module is part 1: the dictionary between a **single** frontal transporter `R` that is
block-diagonal for `str` — which is what `BlockEquiv` and `partition_deletion` consume — and a
**family** `Rst` of per-stratum transporters, which is what a link whose endpoint is a stratum has
to name.

## Contents

* `Fib str g` — the fibre `{k // str k = g}` of a stratum.
* `assemble` / `blockOf` — the two directions of the dictionary.
* `isBlockDiag_assemble`, `assemble_blockOf`, `blockOf_assemble` — they are mutually inverse on
  block-diagonal matrices.
* `sum_fibre` — a sum over `Fin t` collapses to the fibre when the off-fibre terms vanish. This is
  the only real computation in the module and everything multiplicative rests on it.
* `assemble_one`, `assemble_mul`, `blockOf_mul` — functoriality.
* `isUnit_det_assemble_iff` — **`assemble str Rst` is invertible iff every block is.** Both
  directions are proved without any block-determinant theory: forwards by exhibiting
  `assemble str (fun g => (Rst g)⁻¹)` as an explicit inverse, backwards by restricting the equation
  `R * R⁻¹ = 1` to a stratum, which is legitimate precisely because `R` is block-diagonal.
  `Matrix.det_blockDiagonal` is *not* used — it applies to `Matrix.blockDiagonal`, a different
  (uniform-fibre) construction, and reindexing our `str`-fibres into that shape would cost more than
  the two computations below.

## DAG chains walked

Snapshot `…/snapshots/20260902T050450Z-a5ab6e14/graph`.
`neighbors Finset.sum_subtype 1`, `neighbors Finset.sum_subset 1` — the two ingredients of
`sum_fibre`. `neighbors Matrix.det_blockDiagonal 1` and `neighbors Equiv.sigmaFiberEquiv 1` — checked
and deliberately not used, for the reason given above.
-/

namespace Mathproof.Meta.FGSLinkedBlockEquiv20260902

open Matrix
open Mathproof.Meta.FGSBlockArrays20260902

universe u

variable {K : Type u} [Field K] {t n : ℕ}

/-- The fibre of a frontal stratum. -/
abbrev Fib (str : Fin t → Fin n) (g : Fin n) : Type := {k : Fin t // str k = g}

section Assemble

variable (str : Fin t → Fin n)

/-- Assemble a per-stratum family into one block-diagonal matrix. -/
def assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    Matrix (Fin t) (Fin t) K :=
  Matrix.of fun i j => if h : str i = str j then Rst (str i) ⟨i, rfl⟩ ⟨j, h.symm⟩ else 0

/-- Restrict a matrix to one stratum. -/
def blockOf (R : Matrix (Fin t) (Fin t) K) (g : Fin n) : Matrix (Fib str g) (Fib str g) K :=
  R.submatrix Subtype.val Subtype.val

theorem isBlockDiag_assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    IsBlockDiag str (assemble str Rst) := by
  intro i j hij
  simp [assemble, dif_neg hij]

/-- The defining equation of `assemble`, stated at an arbitrary class index `g`. Phrasing it this
way — with `g` a *variable* so that `subst` applies — is what makes the two sides of
`assemble_mul` land at the same `Rst`-index instead of at `str i` versus `str ↑c`. -/
theorem assemble_apply_of_eq (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K)
    {i j : Fin t} (h : str i = str j) (g : Fin n) (hg : str i = g) :
    assemble str Rst i j = Rst g ⟨i, hg⟩ ⟨j, h.symm.trans hg⟩ := by
  subst hg
  simp [assemble, dif_pos h]

theorem assemble_blockOf {R : Matrix (Fin t) (Fin t) K} (hR : IsBlockDiag str R) :
    assemble str (blockOf str R) = R := by
  ext i j
  by_cases h : str i = str j
  · rw [assemble]
    simp only [Matrix.of_apply, dif_pos h, blockOf, Matrix.submatrix_apply]
  · rw [assemble]
    simp only [Matrix.of_apply, dif_neg h]
    exact (hR i j h).symm

theorem blockOf_assemble (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) (g : Fin n) :
    blockOf str (assemble str Rst) g = Rst g := by
  ext a b
  obtain ⟨i, hi⟩ := a
  obtain ⟨j, hj⟩ := b
  subst hi
  simp [blockOf, assemble, dif_pos hj.symm]

/-- **A sum over `Fin t` collapses to a stratum's fibre** when the off-fibre terms vanish. -/
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

/-- Restricting a product to a stratum, when the **left** factor is block-diagonal. -/
theorem blockOf_mul {M N : Matrix (Fin t) (Fin t) K} (hM : IsBlockDiag str M) (g : Fin n) :
    blockOf str (M * N) g = blockOf str M g * blockOf str N g := by
  ext a b
  simp only [blockOf, Matrix.submatrix_apply, Matrix.mul_apply]
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

theorem isUnit_det_blockOf {R : Matrix (Fin t) (Fin t) K} (hR : IsBlockDiag str R)
    (hU : IsUnit R.det) (g : Fin n) : IsUnit (blockOf str R g).det := by
  have hinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hblk : blockOf str R g * blockOf str R⁻¹ g = 1 := by
    rw [← blockOf_mul str hR, hinv]
    ext a b
    simp [blockOf, Matrix.one_apply, Subtype.ext_iff]
  have hd : (blockOf str R g).det * (blockOf str R⁻¹ g).det = 1 := by
    rw [← Matrix.det_mul, hblk, Matrix.det_one]
  exact ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩

/-- **The invertibility dictionary.** -/
theorem isUnit_det_assemble_iff (Rst : ∀ g : Fin n, Matrix (Fib str g) (Fib str g) K) :
    IsUnit (assemble str Rst).det ↔ ∀ g, IsUnit (Rst g).det := by
  constructor
  · intro h g
    have := isUnit_det_blockOf str (isBlockDiag_assemble str Rst) h g
    rwa [blockOf_assemble str Rst g] at this
  · exact isUnit_det_assemble str

end Assemble

/-! ## Part 2: link data, in structural form

FGS take `∼` and `⋈` as free relations subject to their conditions (i)–(iii), and then observe that
every admissible `⋈` arises from an **involution on `P/∼`**. Taking that observation as the
*definition* makes (i)–(iii) theorems rather than hypotheses, and makes their size condition
(eq. `chp`, `d_α = d_β` on links) automatic, because the index identifications are carried in the
data. -/

section LinksDef

/-- **Link data.** `cls` is `∼` (as a class map), `star` is `⋈` (as an involution on classes), `e`
identifies each position's index type with its class's, and `starIdx` identifies the index types of
a `⋈`-pair. -/
structure Links (Pos : Type) (Idx : Pos → Type) (Cls : Type) (ClsIdx : Cls → Type) where
  cls : Pos → Cls
  star : Cls → Cls
  star_involutive : ∀ c, star (star c) = c
  e : ∀ a : Pos, Idx a ≃ ClsIdx (cls a)
  starIdx : ∀ c, ClsIdx c ≃ ClsIdx (star c)

namespace Links

variable {Pos : Type} {Idx : Pos → Type} {Cls : Type} {ClsIdx : Cls → Type}
variable (L : Links Pos Idx Cls ClsIdx)

/-- FGS's `∼`. -/
def sim (a b : Pos) : Prop := L.cls a = L.cls b

/-- FGS's `⋈`. -/
def join (a b : Pos) : Prop := L.cls a ≠ L.star (L.cls a) ∧ L.star (L.cls a) = L.cls b

/-- **FGS condition (i)**: `∼` is an equivalence relation. -/
theorem sim_equivalence : Equivalence L.sim :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **FGS condition (ii)**: `a ⋈ b` implies `a ≁ b`. -/
theorem not_sim_of_join {a b : Pos} (h : L.join a b) : ¬ L.sim a b :=
  fun hs => h.1 (hs.trans h.2.symm)

/-- **FGS condition (iii)**: if `a ⋈ b` then `b ⋈ c ↔ a ∼ c`. -/
theorem join_iff_sim {a b : Pos} (h : L.join a b) (c : Pos) : L.join b c ↔ L.sim a c := by
  have hb : L.cls b = L.star (L.cls a) := h.2.symm
  have hsb : L.star (L.cls b) = L.cls a := by rw [hb, L.star_involutive]
  constructor
  · rintro ⟨-, h2⟩
    exact hsb.symm.trans h2
  · intro hs
    refine ⟨?_, ?_⟩
    · rw [hb, L.star_involutive]
      exact Ne.symm h.1
    · rw [hsb]
      exact hs

/-- `⋈` is symmetric — FGS's `a = c` specialisation of (iii). -/
theorem join_symm {a b : Pos} (h : L.join a b) : L.join b a :=
  (L.join_iff_sim h a).mpr rfl

variable {K : Type u} [Field K]

/-- The transporter at a position, induced by a per-class family. Because the family is indexed by
**classes**, the `∼` condition `S_α = S_β` holds by construction and never has to be transported
across a cast. -/
def transporterOf (T : ∀ c : Cls, Matrix (ClsIdx c) (ClsIdx c) K) (a : Pos) :
    Matrix (Idx a) (Idx a) K :=
  Matrix.reindex (L.e a).symm (L.e a).symm (T (L.cls a))

end Links

end LinksDef

/-! ## Part 2b: linked block-equivalence of partitioned arrays -/

section LBE

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
variable {RowIdx : β → Type} {ColIdx : γ → Type}
variable [∀ b, Fintype (RowIdx b)] [∀ b, DecidableEq (RowIdx b)]
variable [∀ s, Fintype (ColIdx s)] [∀ s, DecidableEq (ColIdx s)]

/-- The positions of a partitioned array: row blocks, column blocks, frontal strata. This is FGS's
`P = {1..m̄; 1'..n̄'; 1''..t̄''}`. -/
abbrev Pos (β γ : Type) (n : ℕ) : Type := β ⊕ γ ⊕ Fin n

/-- The index type carried by each position. `Sum.elim` rather than a `match`, so that it reduces
definitionally on constructors, and `abbrev` rather than `def` so that the reduction happens at
*reducible* transparency — otherwise the elaborator will not see
`PosIdx … (Sum.inl b) = RowIdx b` when unifying the matrix product below. -/
abbrev PosIdx (RowIdx : β → Type) (ColIdx : γ → Type) (str : Fin t → Fin n) :
    Pos β γ n → Type :=
  Sum.elim RowIdx (Sum.elim ColIdx (Fib str))

instance instFintypePosIdx (str : Fin t → Fin n) (a : Pos β γ n) :
    Fintype (PosIdx RowIdx ColIdx str a) := by
  rcases a with b | s | g
  · exact inferInstanceAs (Fintype (RowIdx b))
  · exact inferInstanceAs (Fintype (ColIdx s))
  · exact inferInstanceAs (Fintype (Fib str g))

instance instDecEqPosIdx (str : Fin t → Fin n) (a : Pos β γ n) :
    DecidableEq (PosIdx RowIdx ColIdx str a) := by
  rcases a with b | s | g
  · exact inferInstanceAs (DecidableEq (RowIdx b))
  · exact inferInstanceAs (DecidableEq (ColIdx s))
  · exact inferInstanceAs (DecidableEq (Fib str g))

/-- Bundle three transporter families into one position-indexed family. -/
def mkT (str : Fin t → Fin n)
    (P : ∀ b, Matrix (RowIdx b) (RowIdx b) K) (Q : ∀ s, Matrix (ColIdx s) (ColIdx s) K)
    (Rst : ∀ g, Matrix (Fib str g) (Fib str g) K) :
    ∀ a : Pos β γ n, Matrix (PosIdx RowIdx ColIdx str a) (PosIdx RowIdx ColIdx str a) K
  | Sum.inl b => P b
  | Sum.inr (Sum.inl s) => Q s
  | Sum.inr (Sum.inr g) => Rst g

section Extractors

variable {Cls : Type} {ClsIdx : Cls → Type}

/-! `PosIdx … (Sum.inl b)` is definitionally `RowIdx b`, but instance search does **not** unfold it,
so writing `L.transporterOf T (Sum.inl b) * X k' b s` fails with
`failed to synthesize HMul (Matrix (PosIdx … (Sum.inl b)) …) (Matrix (RowIdx b) (ColIdx s) K)`.
The three extractors below carry the reduced type in their *signature*, which forces the
defeq check once, at definition time, and lets every use site elaborate normally. -/

/-- The row-block transporter, with its type already reduced to `Matrix (RowIdx b) (RowIdx b) K`. -/
def rowT (str : Fin t → Fin n)
    (L : Links (Pos β γ n) (PosIdx RowIdx ColIdx str) Cls ClsIdx)
    (T : ∀ c : Cls, Matrix (ClsIdx c) (ClsIdx c) K) (b : β) :
    Matrix (RowIdx b) (RowIdx b) K :=
  L.transporterOf T (Sum.inl b)

/-- The column-block transporter. -/
def colT (str : Fin t → Fin n)
    (L : Links (Pos β γ n) (PosIdx RowIdx ColIdx str) Cls ClsIdx)
    (T : ∀ c : Cls, Matrix (ClsIdx c) (ClsIdx c) K) (s : γ) :
    Matrix (ColIdx s) (ColIdx s) K :=
  L.transporterOf T (Sum.inr (Sum.inl s))

/-- The per-stratum frontal transporter. -/
def frontT (str : Fin t → Fin n)
    (L : Links (Pos β γ n) (PosIdx RowIdx ColIdx str) Cls ClsIdx)
    (T : ∀ c : Cls, Matrix (ClsIdx c) (ClsIdx c) K) (g : Fin n) :
    Matrix (Fib str g) (Fib str g) K :=
  L.transporterOf T (Sum.inr (Sum.inr g))

end Extractors

/-- **Linked block-equivalence.** The transporter is given by a per-**class** family `T`, so the
`∼` conditions hold by construction; the `⋈` conditions are the single equation on `T`. -/
def LinkedBlockEquiv {Cls : Type} {ClsIdx : Cls → Type}
    [∀ c, Fintype (ClsIdx c)] [∀ c, DecidableEq (ClsIdx c)]
    (str : Fin t → Fin n)
    (L : Links (Pos β γ n) (PosIdx RowIdx ColIdx str) Cls ClsIdx)
    (X Y : PArr K β γ RowIdx ColIdx t) : Prop :=
  ∃ T : ∀ c : Cls, Matrix (ClsIdx c) (ClsIdx c) K,
    (∀ c, IsUnit (T c).det) ∧
    (∀ c, L.star c ≠ c →
        T (L.star c) = Matrix.reindex (L.starIdx c) (L.starIdx c) (((T c)⁻¹)ᵀ)) ∧
    ∀ k b s, Y k b s
      = ∑ k', assemble str (frontT str L T) k k'
          • (rowT str L T b * X k' b s * (colT str L T s)ᵀ)

/-- The trivial link data: every position is its own class and the involution is the identity. -/
def nilLinks (str : Fin t → Fin n) :
    Links (Pos β γ n) (PosIdx RowIdx ColIdx str) (Pos β γ n) (PosIdx RowIdx ColIdx str) where
  cls := id
  star := id
  star_involutive := fun _ => rfl
  e := fun _ => Equiv.refl _
  starIdx := fun _ => Equiv.refl _

theorem transporterOf_nil (str : Fin t → Fin n)
    (T : ∀ c : Pos β γ n, Matrix (PosIdx RowIdx ColIdx str c) (PosIdx RowIdx ColIdx str c) K)
    (a : Pos β γ n) :
    (nilLinks (RowIdx := RowIdx) (ColIdx := ColIdx) str).transporterOf T a = T a := by
  -- `reindex (Equiv.refl _) (Equiv.refl _)` is the identity on entries, so this is entrywise `rfl`;
  -- `simp` does not know that without `Matrix.submatrix_id_id`, so go through `ext`.
  ext i j
  rfl

theorem rowT_nil (str : Fin t → Fin n)
    (T : ∀ c : Pos β γ n, Matrix (PosIdx RowIdx ColIdx str c) (PosIdx RowIdx ColIdx str c) K)
    (b : β) : rowT str (nilLinks str) T b = T (Sum.inl b) :=
  transporterOf_nil str T (Sum.inl b)

theorem colT_nil (str : Fin t → Fin n)
    (T : ∀ c : Pos β γ n, Matrix (PosIdx RowIdx ColIdx str c) (PosIdx RowIdx ColIdx str c) K)
    (s : γ) : colT str (nilLinks str) T s = T (Sum.inr (Sum.inl s)) :=
  transporterOf_nil str T (Sum.inr (Sum.inl s))

theorem frontT_nil (str : Fin t → Fin n)
    (T : ∀ c : Pos β γ n, Matrix (PosIdx RowIdx ColIdx str c) (PosIdx RowIdx ColIdx str c) K)
    (g : Fin n) : frontT str (nilLinks str) T g = T (Sum.inr (Sum.inr g)) :=
  transporterOf_nil str T (Sum.inr (Sum.inr g))

/-- **With no links, linked block-equivalence is exactly `BlockEquiv`** — in the single-`R` form
that `partition_deletion` consumes. -/
theorem linkedBlockEquiv_of_nil (str : Fin t → Fin n) (X Y : PArr K β γ RowIdx ColIdx t) :
    LinkedBlockEquiv str (nilLinks str) X Y ↔ BlockEquiv str X Y := by
  constructor
  · rintro ⟨T, hT, -, heq⟩
    refine ⟨fun b => T (Sum.inl b), fun s => T (Sum.inr (Sum.inl s)),
      assemble str (fun g => T (Sum.inr (Sum.inr g))),
      fun b => hT _, fun s => hT _,
      isUnit_det_assemble str (fun g => hT _),
      isBlockDiag_assemble str _, fun k b s => ?_⟩
    have h := heq k b s
    rw [rowT_nil, colT_nil] at h
    -- `frontT_nil` is pointwise, but the term is `assemble str (frontT …)` — the FUNCTION, not an
    -- application — so it has to be rewritten as a function equality.
    have hfr : frontT str (nilLinks str) T = fun g => T (Sum.inr (Sum.inr g)) := by
      funext g
      exact frontT_nil str T g
    rw [hfr] at h
    exact h
  · rintro ⟨P, Q, R, hP, hQ, hR, hBD, heq⟩
    refine ⟨mkT str P Q (blockOf str R), ?_, ?_, fun k b s => ?_⟩
    · rintro (b | s | g)
      · exact hP b
      · exact hQ s
      · exact isUnit_det_blockOf str hBD hR g
    · intro c hc
      exact absurd rfl hc
    · have hfront : frontT str (nilLinks str) (mkT str P Q (blockOf str R)) = blockOf str R := by
        funext g
        rw [frontT_nil]
        rfl
      rw [rowT_nil, colT_nil, hfront, assemble_blockOf str hBD]
      exact heq k b s

end LBE

end Mathproof.Meta.FGSLinkedBlockEquiv20260902

end Part_U24


section Part_U25


/-!
# The coupling calculus of an FGS-style gadget, specialised to a form-preserving group

## What this module is, and why it is the right unit of work

`ProjectionReductions20260902.ti_eq_tisp_of_projections` needs two base projections. The direction
`Sp3TI ⟶ GL3TI` is CGQTZ Theorem 1.4 (arXiv:2306.03135), and **its proof has exactly two steps**:

1. *(CGQTZ, verbatim, one sentence)* "Let `Φ_l ∈ M(l,F)` be the matrix representation of the
   bilinear form `φ_ℓ`. Then construct `S = (Ã, Φ_l, Φ_m, Φ_n)` and `T = (B̃, Φ_l, Φ_m, Φ_n)`,
   viewed as tensor systems … It is clear that `Ã` and `B̃` are `G`-isomorphic if and only if the two
   tensor systems `S` and `T` are `GL`-isomorphic."
2. *(cited)* FGS Theorem 1.1 collapses a tensor system to a single `3`-tensor.

Step 2 is **not** a compact gadget. In Futorny–Grochow–Sergeichuk (arXiv:1810.09219) it is
Theorem `ktw1`, proved through Theorem `hep` and Lemma `jhp`: an iterated "delete one block
partition at a time" construction on partitioned three-dimensional arrays, whose correctness invokes
Krull–Schmidt for quiver representations.

This module isolates and **fully machine-checks the algebraic engine** any such gadget must contain
when the group being cut out is the stabiliser of a bilinear form: the *coupling calculus*.
Everything here is proved; nothing is cited.

## The finding that fixes the gadget's shape

A slice of a `3`-tensor occupying mode-`i` block `M` and mode-`j` block `N` (`i ≠ j`), with a fresh
basis vector in the third mode, imposes on the two *independent* mode transporters `g` (on `M`) and
`h` (on `N`) exactly the relation `g * Ψ * hᵀ = Ψ`, where `Ψ` is the slice. This is forced by
`ProjectionReductions20260902.act3D`: `(∑_{i'} ∑_{j'} g_{i i'} h_{j j'} Ψ_{i' j'}) = (g * Ψ * hᵀ)_{ij}`.

Proved below:

* `coupling_solve`, `Coupling.snd_unique`, `centralizer_of_two_couplings`: **a single mode-pair can
  never express a form condition.** For invertible `Ψ` the relation *determines* `h` from `g`, as a
  contragredient `hᵀ = Ψ⁻¹ g⁻¹ Ψ`; a *second* slice `Ψ'` in the *same* mode-pair only adds
  "`g` commutes with `Ψ' Ψ⁻¹`" — a centraliser condition, never `g J gᵀ = J`. So no one-pair gadget
  can cut `GL` down to `Sp`. This is why the gadget must route through the third mode, a point the
  sources use implicitly and never state.
* `coupling_one_chain`: **two identity couplings in series return the same transporter**,
  `k = g`, with **no hypotheses at all** — invertibility is produced by the relation itself.
  Contragredience is an involution, so the chain has length two and therefore visits all three
  modes.
* `chain_certifies_symplectic`: chain plus one further slice carrying `stdJ` across the two *ends*
  of the chain gives exactly `IsSymplecticMat`. Unconditional.
* `chain_of_symplectic` / `symplectic_iff_chain`: the converse, with the explicit witness
  `h = (g⁻¹)ᵀ`, hence an **equivalence**.

## Variance bookkeeping (checked, not assumed)

`ProjectionReductions20260902.IsSymplecticMat K g` is `gᵀ * stdJ * g = stdJ` (*contravariant*:
`g` preserves `x,y ↦ xᵀ J y`). A gadget slice transformed by `act3D` produces the *covariant*
relation `g * J * gᵀ = J`. These are **not** the same statement for a general invertible `J`; they
agree here only because `stdJ * (-stdJ) = 1` (`stdJ_mul_neg_self`, i.e. `stdJ² = -1`). That is
`covariant_iff_contravariant`, proved from a two-sided inverse and a proportionality hypothesis and
nothing else — no field, no characteristic assumption, no invertibility assumption on `g`.

## Mathlib is the default library

The DAG walk below turned up `Matrix.J`, `Matrix.J_squared`, `Matrix.J_inv`, `Matrix.J_transpose`,
`Matrix.symplecticGroup`, `SymplecticGroup.mem_iff`, `SymplecticGroup.transpose_mem_iff`,
`SymplecticGroup.symplectic_det` — Mathlib already has the symplectic group, and
`SymplecticGroup.transpose_mem_iff` is the `stdJ` case of `covariant_iff_contravariant`. The bridge
`isSymplecticMat_iff_mem_symplecticGroup` is therefore supplied, so that the whole Mathlib
`SymplecticGroup` API (inverses, `det = 1`, group structure) becomes available to
`ProjectionReductions20260902.IsSymplecticMat` downstream. The general
`covariant_iff_contravariant` is kept because CGQTZ Theorem 1.4 is stated for an *arbitrary*
polynomial-time-constructible family of bilinear forms, which Mathlib's `Matrix.J` does not cover.

## DAG chains walked before writing (structural, not by name)

Snapshot `D:/proof/proof_factory/state/research_graph/snapshots/20260902T033037Z-a57018fc/graph`.

* `backward Matrix.transpose 2`, `backward Matrix.inv_eq_right_inv 2`,
  `backward Matrix.nonsing_inv_mul 2` — established the primitive layer this file consumes
  (`mul_eq_one_comm`, `Matrix.inv_eq_left_inv`, `Matrix.isUnit_iff_isUnit_det`,
  `Matrix.invOf_eq_nonsing_inv`, `Matrix.detInvertibleOfInvertible`).
* `forward mul_eq_one_comm 1` → `Matrix.inv_eq_right_inv`, `Matrix.mul_eq_one_comm_of_equiv`,
  `Matrix.mem_unitaryGroup_iff`, `LinearMap.comp_eq_id_comm`. This is how the one-sided-inverse
  step of `coupling_one_chain` was located: the chain lemma is the matrix analogue of
  `LinearMap.comp_eq_id_comm`.
* `forward Matrix.inv_eq_right_inv 2` → `Matrix.J_inv` → **`SymplecticGroup.transpose_mem`**. The
  symplectic-group API was found by *following consumers*, not by searching for the word
  "symplectic".
* `neighbors SymplecticGroup.transpose_mem 2`, `neighbors Matrix.J 2`, `neighbors Matrix.J_inv 2`,
  `neighbors Matrix.mul_eq_one_comm_of_equiv 2` — read off `Matrix.J_squared`,
  `Matrix.isUnit_det_J`, `SymplecticGroup.mem_iff`, `SymplecticGroup.symplectic_det`,
  `Matrix.fromBlocks_transpose`, `Matrix.fromBlocks_multiply`, and confirmed the sign convention
  `Matrix.J = fromBlocks 0 (-1) 1 0`, i.e. `stdJ = -Matrix.J`.
* `neighbors Mathproof.SymplecticTI.Consequences.SpOrbit3 1`,
  `neighbors ….recoverGLTransporter 1`, `neighbors ….pad3_exactOrbitEmbedding 1`,
  `neighbors ….paddedOrbitSection 1`, `neighbors Mathproof.SymplecticTI.pad_reduction_preserves 1`
  — the existing symplectic cluster; it contains no coupling or tensor-system material, so this
  file duplicates nothing.
-/

namespace Mathproof.Meta.FGSGadgetCoupling20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902

universe u v

section General

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **A coupling constraint.** The relation imposed on two *independent* mode transporters `g`
(mode `i`) and `h` (mode `j`), `i ≠ j`, by a single gadget slice equal to `Ψ` sitting in the
mode-`i` × mode-`j` blocks with a fresh basis vector in the remaining mode.

The transpose on the second argument is not a convention: it is what
`ProjectionReductions20260902.act3D` does. -/
def Coupling (Ψ : Matrix ι ι R) (g h : Matrix ι ι R) : Prop :=
  g * Ψ * hᵀ = Ψ

omit [DecidableEq ι] in
theorem coupling_def (Ψ g h : Matrix ι ι R) : Coupling Ψ g h ↔ g * Ψ * hᵀ = Ψ := Iff.rfl

/-- **One-sided inverses of square matrices are two-sided.**

Mathlib states this as `Matrix.mul_eq_one_comm_of_equiv`/`_of_card_eq` for matrices between
*different* index types; the same-index specialisation is derived here in three lines from
`Matrix.det_mul`, `Matrix.inv_eq_right_inv` and `Matrix.nonsing_inv_mul` — all three located by the
DAG walk `backward Matrix.inv_eq_right_inv 2` / `backward Matrix.nonsing_inv_mul 2`. This is the
only step of `coupling_one_chain` that is not pure rewriting, and it is what makes that lemma
hypothesis-free. -/
theorem mul_eq_one_comm_sq {A B : Matrix ι ι R} (h : A * B = 1) : B * A = 1 := by
  have hd : A.det * B.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have hu : IsUnit A.det := ⟨Units.mkOfMulEqOne _ _ hd, rfl⟩
  have hAB : A⁻¹ = B := Matrix.inv_eq_right_inv h
  rw [← hAB]
  exact Matrix.nonsing_inv_mul _ hu

/-! ### A single mode-pair cannot express a form condition -/

/-- **Explicit solution of a coupling**: `hᵀ = Ψ⁻¹ * g⁻¹ * Ψ`.

This makes visible that a coupling transports `g` to a **contragredient**, never to `g` itself —
the structural fact that dictates the length-two chain below. -/
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

/-- **The second transporter is determined by the first.** -/
theorem Coupling.snd_unique {Ψ g h h' : Matrix ι ι R} (hΨ : IsUnit Ψ.det) (hg : IsUnit g.det)
    (H : Coupling Ψ g h) (H' : Coupling Ψ g h') : h = h' := by
  have e : hᵀ = h'ᵀ := (coupling_solve hΨ hg H).trans (coupling_solve hΨ hg H').symm
  simpa using congrArg Matrix.transpose e

/-- **Two slices in the same mode-pair give a centraliser condition, never a form condition.**

If `g` is coupled to the *same* `h` through two slices `Ψ` (invertible) and `Ψ'`, then all that is
imposed on `g` is that it commutes with `Ψ' Ψ⁻¹`. A symplectic condition `g J gᵀ = J` is quadratic
in `g` alone; no number of slices in one mode-pair can produce one. This is why the gadget below
must route through the third mode. -/
theorem centralizer_of_two_couplings {Ψ Ψ' g h : Matrix ι ι R}
    (hΨ : IsUnit Ψ.det) (hg : IsUnit g.det)
    (H : Coupling Ψ g h) (H' : Coupling Ψ' g h) :
    g * (Ψ' * Ψ⁻¹) * g⁻¹ = Ψ' * Ψ⁻¹ := by
  have hT : hᵀ = Ψ⁻¹ * g⁻¹ * Ψ := coupling_solve hΨ hg H
  have h2 : g * Ψ' * (Ψ⁻¹ * g⁻¹ * Ψ) = Ψ' := by rw [← hT]; exact H'
  have h3 : (g * (Ψ' * Ψ⁻¹) * g⁻¹) * Ψ = Ψ' := by
    calc (g * (Ψ' * Ψ⁻¹) * g⁻¹) * Ψ = g * Ψ' * (Ψ⁻¹ * g⁻¹ * Ψ) := by simp only [mul_assoc]
      _ = Ψ' := h2
  have h4 : (g * (Ψ' * Ψ⁻¹) * g⁻¹) * (Ψ * Ψ⁻¹) = Ψ' * Ψ⁻¹ := by
    rw [← mul_assoc, h3]
  rwa [Matrix.mul_nonsing_inv _ hΨ, mul_one] at h4

/-! ### The identity coupling and the length-two chain -/

/-- An identity slice couples `g` to `h` exactly when `g * hᵀ = 1`. -/
theorem coupling_one_iff (g h : Matrix ι ι R) :
    Coupling (1 : Matrix ι ι R) g h ↔ g * hᵀ = 1 := by
  simp [Coupling]

/-- **The chain lemma — the heart of the gadget, and it needs no hypotheses at all.**

Two identity couplings in series, `g ⟶ h` (in one mode-pair) and `h ⟶ k` (in another), return the
*same* transporter: `k = g`. Contragredience is an involution, so a chain of length two — hence a
route through the third mode — is exactly what brings a copy of `g` into a mode other than its own,
which is the only way a form condition on `g` can be written inside a `3`-tensor.

Invertibility is *derived*, not assumed: `g * hᵀ = 1` gives `hᵀ` a left inverse, and a square
matrix with a one-sided inverse is invertible (`Matrix.mul_eq_one_comm`). -/
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

/-- The forward witness for the first link: `h = (g⁻¹)ᵀ` couples to an invertible `g`. -/
theorem coupling_one_contragredient {g : Matrix ι ι R} (hg : IsUnit g.det) :
    Coupling (1 : Matrix ι ι R) g (g⁻¹)ᵀ := by
  rw [coupling_one_iff, Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv _ hg

/-- The forward witness for the second link: `(g⁻¹)ᵀ` couples back to `g`. -/
theorem coupling_one_contragredient' {g : Matrix ι ι R} (hg : IsUnit g.det) :
    Coupling (1 : Matrix ι ι R) (g⁻¹)ᵀ g := by
  rw [coupling_one_iff]
  have e : (g⁻¹)ᵀ * gᵀ = (g * g⁻¹)ᵀ := by rw [Matrix.transpose_mul]
  rw [e, Matrix.mul_nonsing_inv _ hg, Matrix.transpose_one]

/-- The chain pins the *middle* transporter too, which is what lets one gadget shape be reused for
all three modes. -/
theorem chain_middle_determined {g h k : Matrix ι ι R}
    (H₁ : Coupling (1 : Matrix ι ι R) g h) (H₂ : Coupling (1 : Matrix ι ι R) h k) :
    h = (g⁻¹)ᵀ ∧ k = g := by
  have hkg : k = g := coupling_one_chain H₁ H₂
  rw [coupling_one_iff] at H₁
  have hginv : g⁻¹ = hᵀ := Matrix.inv_eq_right_inv H₁
  exact ⟨by rw [hginv, Matrix.transpose_transpose], hkg⟩

/-! ### Covariant versus contravariant form preservation -/

/-- **The variance bridge.** When the *negative* of the form matrix is a two-sided inverse for it —
exactly the situation of `stdJ`, since `stdJ² = -1` — the covariant relation produced by a gadget
slice and the contravariant relation defining `IsSymplecticMat` are the same condition.

No invertibility hypothesis on `g`: the relation itself forces it. -/
theorem covariant_iff_contravariant {J Ji : Matrix ι ι R} (hJ : J * Ji = 1) (hprop : Ji = -J)
    (g : Matrix ι ι R) : g * J * gᵀ = J ↔ gᵀ * J * g = J := by
  subst hprop
  have h2 : (-J) * J = 1 := mul_eq_one_comm_sq hJ
  have key : ∀ a : Matrix ι ι R, a * J * aᵀ = J → aᵀ * J * a = J := by
    intro a ha
    have e1 : a * (J * aᵀ * (-J)) = 1 := by
      rw [← mul_assoc, ← mul_assoc, ha]; exact hJ
    have e2 : (J * aᵀ * (-J)) * a = 1 := mul_eq_one_comm_sq e1
    have e3 : J * (aᵀ * (-J) * a) = 1 := by simpa only [mul_assoc] using e2
    have e4 : aᵀ * (-J) * a = -J := by
      calc aᵀ * (-J) * a = ((-J) * J) * (aᵀ * (-J) * a) := by rw [h2, one_mul]
        _ = (-J) * (J * (aᵀ * (-J) * a)) := by rw [mul_assoc]
        _ = (-J) * 1 := by rw [e3]
        _ = -J := mul_one _
    have e5 : -(aᵀ * J * a) = -J := by
      rw [← e4, Matrix.mul_neg, Matrix.neg_mul]
    exact neg_injective e5
  refine ⟨key g, fun h => ?_⟩
  have := key gᵀ (by simpa only [Matrix.transpose_transpose] using h)
  simpa only [Matrix.transpose_transpose] using this

end General

/-! ## Specialisation to `stdJ` and `IsSymplecticMat` -/

section Std

variable {K : Type u} [Field K] {n : ℕ}

theorem neg_stdJ_mul_stdJ : (-(stdJ K n)) * stdJ K n = 1 :=
  mul_eq_one_comm_sq (stdJ_mul_neg_self K n)

/-- The covariant form of `IsSymplecticMat`, which is the shape a gadget slice produces. -/
theorem isSymplecticMat_iff_covariant (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    IsSymplecticMat K g ↔ g * stdJ K n * gᵀ = stdJ K n :=
  (covariant_iff_contravariant (J := stdJ K n) (Ji := -(stdJ K n))
    (stdJ_mul_neg_self K n) rfl g).symm

/-- A `stdJ`-slice across the two ends of a chain is exactly `IsSymplecticMat` on `g`. -/
theorem coupling_stdJ_self_iff (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Coupling (stdJ K n) g g ↔ IsSymplecticMat K g :=
  (isSymplecticMat_iff_covariant g).symm

/-! ### The gadget's constraint system, both directions -/

/-- **The gadget certifies membership in `Sp`.**

Three slices — an identity in the mode-`(1,2)` blocks, an identity in the mode-`(2,3)` blocks, and
`stdJ` across the mode-`(1,3)` blocks — force the mode-`1` transporter to be symplectic. No
hypotheses: invertibility is produced by the chain itself.

This is the entire algebraic content of an FGS-style gadget in the form-preserving case. What it
does *not* supply is that a transporter of the assembled gadget tensor respects the block
decomposition, so that the three relations may be read off block by block; that is the separate
rigidity statement. -/
theorem chain_certifies_symplectic
    {g h k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (H₁ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) g h)
    (H₂ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) h k)
    (HJ : Coupling (stdJ K n) g k) :
    IsSymplecticMat K g := by
  have hkg : k = g := coupling_one_chain H₁ H₂
  rw [hkg] at HJ
  exact (coupling_stdJ_self_iff g).mp HJ

/-- **The converse: every symplectic `g` satisfies the gadget's constraint system**, with the
explicit chain witness `h = (g⁻¹)ᵀ`. -/
theorem chain_of_symplectic {g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hg : IsSymplecticMat K g) :
    Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) g (g⁻¹)ᵀ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (g⁻¹)ᵀ g ∧
      Coupling (stdJ K n) g g := by
  have hu : IsUnit g.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_isSymplecticMat K g hg)
  exact ⟨coupling_one_contragredient hu, coupling_one_contragredient' hu,
    (coupling_stdJ_self_iff g).mpr hg⟩

/-- **The gadget constraint system is equivalent to symplecticity.** Both directions, no
hypotheses. -/
theorem symplectic_iff_chain (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    IsSymplecticMat K g ↔
      ∃ h k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
        Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) g h ∧
        Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) h k ∧
        Coupling (stdJ K n) g k := by
  constructor
  · intro hg
    obtain ⟨c₁, c₂, c₃⟩ := chain_of_symplectic hg
    exact ⟨(g⁻¹)ᵀ, g, c₁, c₂, c₃⟩
  · rintro ⟨h, k, H₁, H₂, HJ⟩
    exact chain_certifies_symplectic H₁ H₂ HJ

/-! ### Bridge to Mathlib's `SymplecticGroup`

Found by walking `forward Matrix.inv_eq_right_inv 2` into `Matrix.J_inv` and
`SymplecticGroup.transpose_mem`. `Matrix.J l R = fromBlocks 0 (-1) 1 0`, whereas
`ProjectionReductions20260902.stdJ K n = fromBlocks 0 1 (-1) 0`, so `stdJ = -Matrix.J`. -/

theorem stdJ_eq_neg_J : stdJ K n = -(Matrix.J (Fin n) K) := by
  unfold stdJ Matrix.J
  rw [Matrix.fromBlocks_neg]
  simp

/-- `IsSymplecticMat` is membership in Mathlib's `Matrix.symplecticGroup`, so the whole Mathlib
`SymplecticGroup` API applies to it. -/
theorem isSymplecticMat_iff_mem_symplecticGroup
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    IsSymplecticMat K g ↔ g ∈ Matrix.symplecticGroup (Fin n) K := by
  rw [isSymplecticMat_iff_covariant, _root_.SymplecticGroup.mem_iff, stdJ_eq_neg_J]
  constructor
  · intro h
    have e : -(g * Matrix.J (Fin n) K * gᵀ) = -(Matrix.J (Fin n) K) := by
      rw [← h, Matrix.mul_neg, Matrix.neg_mul]
    exact neg_injective e
  · intro h
    rw [Matrix.mul_neg, Matrix.neg_mul, h]

end Std

#print axioms coupling_solve
#print axioms Coupling.snd_unique
#print axioms centralizer_of_two_couplings
#print axioms coupling_one_chain
#print axioms chain_middle_determined
#print axioms covariant_iff_contravariant
#print axioms chain_certifies_symplectic
#print axioms chain_of_symplectic
#print axioms symplectic_iff_chain
#print axioms isSymplecticMat_iff_mem_symplecticGroup

end Mathproof.Meta.FGSGadgetCoupling20260902

end Part_U25


section Part_U26


/-!
# Tensor systems for CGQTZ Theorem 1.4, and its first step, proved

## Scope

CGQTZ (arXiv:2306.03135) prove `TI_G ⊆ TI` — in particular `TI_Sp ⊆ TI` — in two steps. This module
formalises the objects of step 1 and **proves step 1**, which the paper disposes of in one sentence:

> "Let `Φ_l ∈ M(l,F)` be the matrix representation of the bilinear form `φ_ℓ`. Then construct
> `S = (Ã, Φ_l, Φ_m, Φ_n)` and `T = (B̃, Φ_l, Φ_m, Φ_n)`, viewed as tensor systems as follows. Let
> `U' = F^l`, `V' = F^m`, and `W' = F^n`. Then `Ã ∈ U'⊗V'⊗W'`, `Φ_l ∈ U'⊗U'`, `Φ_m ∈ V'⊗V'`, and
> `Φ_n ∈ W'⊗W'`. **It is clear that `Ã` and `B̃` are `G`-isomorphic if and only if the two tensor
> systems `S` and `T` are `GL`-isomorphic.**"

Step 2 (collapse a tensor system to a single `3`-tensor, FGS arXiv:1810.09219 Theorem 1.1) is not
here; its algebraic engine is `FGSGadgetCoupling20260902`.

The general FGS notion of a tensor system is a representation of a directed bipartite graph
(FGS §1; CGQTZ's Figure "fig:system"). Only one shape of that notion is needed for Theorem 1.4 —
**one order-`3` tensor together with one bilinear form per mode** — and that shape is what
`FormSystem3` is. Formalising the general graph-indexed notion would add no content to Theorem 1.4
and is deliberately omitted; the docstring of `FormSystem3` records exactly which FGS bipartite
graph it is.

## What is proved here

* `PreservesBil` and `preservesBil_iff_isSymplectic`: the abstract form-preservation predicate,
  and the fact that on `Hyp K U` with `omegaH` it is *definitionally* `SymplecticTI.IsSymplectic`.
  So the tensor-system language and the padding file's language are the same language.
* `restrictedIso_iff_systemIso3`: **CGQTZ step 1**, at the abstract tensor level, over an arbitrary
  field, for arbitrary bilinear forms (no nondegeneracy, no skewness, no finite dimension).
* `sp3ti_rel_iff_couplingSystem`: the same step in the coordinates the complexity classes actually
  use — `ProjectionReductions20260902.Sp3TI.Rel` is exactly "the matrix system
  `(A, stdJ, stdJ, stdJ)` is `GL`-isomorphic to `(B, stdJ, stdJ, stdJ)`", with form preservation
  expressed as the `Coupling` relation a gadget slice produces. This is the interface the gadget
  consumes.
* `gadget_constraints_certify` / `gadget_constraints_of_sp3ti`: the **full nine-slice constraint
  system** of the three-mode gadget, and its equivalence with the three symplectic conditions.
  Three chains, one per mode; unconditional in both directions.

Nothing in this module is cited and nothing is assumed.

## DAG chains walked before writing (structural)

Snapshot `…/snapshots/20260902T033037Z-a57018fc/graph`.

* `backward Mathproof.SymplecticTI.msupp 1` → `Mathproof.SymplecticTI.contract`, `Submodule`,
  `LinearMap.range`; `backward Mathproof.SymplecticTI.msupp_map 1` → `TensorProduct.map`,
  `Submodule.map`, `Mathproof.SymplecticTI.contract_map`, `LinearMap.dualMap_surjective_of_injective`.
  This fixed the primitive layer the tensor-level statements below must live on
  (`TensorProduct.map`, `LinearMap.dualMap`) and confirmed `glAct` is the right action to reuse.
* `forward Mathproof.SymplecticTI.msupp 2` and `forward Mathproof.SymplecticTI.msupp_map 2` →
  `pad3_mode1_reflect`, `pad3_mode2_reflect`, `pad3_mode3_reflect`, `pad3_msupp_all_modes`,
  `msupp_padded_rigidity`, and `SymplecticTI.ResidualSLDegeneration.mode2Support_X /
  mode2SupportFinrank_Y / mode2SupportFinrank_eq_of_GLOrbit3 / not_GLOrbit3_X_Y`. The last cluster
  is the existing evidence that *mode-support dimension is a `GL`-orbit invariant*; it is the tool
  the block-rigidity grind will need, and it is recorded here so the next module can find it.
* `forward Mathproof.SymplecticTI.map_eq_of_eqOn_msupp 2` → `pad_substitute`,
  `substitute_of_supportLiftWitness` — the substitution idiom to imitate if rigidity is attacked by
  mode support rather than by slice ranks.
* `forward Matrix.inv_eq_right_inv 2` → `Matrix.J_inv` → `SymplecticGroup.transpose_mem`, and
  `neighbors Matrix.J 2` → `Matrix.J_squared`, `Matrix.isUnit_det_J`, `SymplecticGroup.mem_iff`.
  Used in the companion coupling module.
-/

namespace Mathproof.Meta.FGSGadgetSystem20260902

open Matrix
open TensorProduct
open Mathproof.SymplecticTI
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.FGSGadgetCoupling20260902

universe u v

/-! ## 1. Form preservation -/

section Bil

variable {K : Type u} [Field K] {U : Type v} [AddCommGroup U] [Module K U]

/-- `g` preserves the bilinear form `ω`. For an isomorphism of tensor systems this is the
"`g` carries the form-component to the form-component" clause. -/
def PreservesBil (ω : U →ₗ[K] U →ₗ[K] K) (g : U ≃ₗ[K] U) : Prop :=
  ∀ x y, ω (g x) (g y) = ω x y

/-- On the hyperbolic double with its canonical form, form preservation **is**
`SymplecticTI.IsSymplectic` — definitionally, so the tensor-system language and the padding file's
language are literally the same. -/
theorem preservesBil_iff_isSymplectic {U : Type v} [AddCommGroup U] [Module K U]
    (g : Hyp K U ≃ₗ[K] Hyp K U) :
    PreservesBil (omegaH : Hyp K U →ₗ[K] Hyp K U →ₗ[K] K) g ↔ IsSymplectic g := Iff.rfl

theorem preservesBil_one (ω : U →ₗ[K] U →ₗ[K] K) :
    PreservesBil ω (LinearEquiv.refl K U) := fun _ _ => rfl

theorem PreservesBil.trans {ω : U →ₗ[K] U →ₗ[K] K} {g h : U ≃ₗ[K] U}
    (hg : PreservesBil ω g) (hh : PreservesBil ω h) : PreservesBil ω (g ≪≫ₗ h) := fun x y => by
  simpa using (hh (g x) (g y)).trans (hg x y)

end Bil

/-! ## 2. The CGQTZ tensor system and step 1 -/

section System

variable {K : Type u} [Field K]
variable {U₁ U₂ U₃ : Type v}
variable [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup U₃] [Module K U₃]

/-- **The tensor system of CGQTZ Theorem 1.4.**

In FGS's bipartite-graph language (FGS §1, CGQTZ Figure `fig:system`) this is the graph with three
right vertices `U₁, U₂, U₃` and four left vertices: one tensor `t₀` with one arc from each of
`U₁, U₂, U₃`, and one tensor `t_i` with two arcs from `U_i`, for each `i`. Every left vertex has at
most three arcs, so it is in the scope of FGS Theorem `ktw1`.

The forms are stored as bilinear maps rather than as elements of `U_i ⊗ U_i`; this is the
`(0,2)`-tensor convention, and it is the one that makes `PreservesBil` definitionally equal to
`SymplecticTI.IsSymplectic`. -/
structure FormSystem3 (K : Type u) [Field K] (U₁ U₂ U₃ : Type v)
    [AddCommGroup U₁] [Module K U₁] [AddCommGroup U₂] [Module K U₂]
    [AddCommGroup U₃] [Module K U₃] where
  /-- The order-`3` component. -/
  tensor : U₁ ⊗[K] (U₂ ⊗[K] U₃)
  /-- The form on mode `1`. -/
  form₁ : U₁ →ₗ[K] U₁ →ₗ[K] K
  /-- The form on mode `2`. -/
  form₂ : U₂ →ₗ[K] U₂ →ₗ[K] K
  /-- The form on mode `3`. -/
  form₃ : U₃ →ₗ[K] U₃ →ₗ[K] K

/-- **Isomorphism of tensor systems** (CGQTZ, verbatim): "there exists
`A = (A_1, …, A_c) ∈ GL(V_1) × ⋯ × GL(V_c)` such that (the relevant components of) `A` sends `S_i`
to `T_i` for every `i ∈ [c]`."

Three *independent* per-mode elements, matching CGQTZ Definition 1.2 action (1). Each component is
carried: the order-`3` component by `glAct`, and each form by pullback. -/
def SystemIso3 (S T : FormSystem3 K U₁ U₂ U₃) : Prop :=
  ∃ (g₁ : U₁ ≃ₗ[K] U₁) (g₂ : U₂ ≃ₗ[K] U₂) (g₃ : U₃ ≃ₗ[K] U₃),
    (∀ x y, T.form₁ (g₁ x) (g₁ y) = S.form₁ x y) ∧
    (∀ x y, T.form₂ (g₂ x) (g₂ y) = S.form₂ x y) ∧
    (∀ x y, T.form₃ (g₃ x) (g₃ y) = S.form₃ x y) ∧
    glAct g₁ g₂ g₃ S.tensor = T.tensor

/-- **CGQTZ Theorem 1.4, step 1 — proved.**

For a *fixed* triple of bilinear forms, `A` and `B` are isomorphic under the subgroups preserving
those forms **iff** the tensor systems `(A, ω₁, ω₂, ω₃)` and `(B, ω₁, ω₂, ω₃)` are `GL`-isomorphic.

Over an arbitrary field, for arbitrary bilinear forms: no nondegeneracy, no skewness, no finite
dimension. The proof is the observation that "carries `ω_i` to `ω_i`" and "preserves `ω_i`" are the
same clause — which is exactly why CGQTZ can say "it is clear". Stating it is not idle: it is what
pins down that the acting group is a **direct product of three independent per-mode elements**, the
definitional point on which the entire reduction turns. -/
theorem restrictedIso_iff_systemIso3
    (ω₁ : U₁ →ₗ[K] U₁ →ₗ[K] K) (ω₂ : U₂ →ₗ[K] U₂ →ₗ[K] K) (ω₃ : U₃ →ₗ[K] U₃ →ₗ[K] K)
    (A B : U₁ ⊗[K] (U₂ ⊗[K] U₃)) :
    (∃ (g₁ : U₁ ≃ₗ[K] U₁) (g₂ : U₂ ≃ₗ[K] U₂) (g₃ : U₃ ≃ₗ[K] U₃),
        PreservesBil ω₁ g₁ ∧ PreservesBil ω₂ g₂ ∧ PreservesBil ω₃ g₃ ∧
          glAct g₁ g₂ g₃ A = B) ↔
      SystemIso3 (⟨A, ω₁, ω₂, ω₃⟩ : FormSystem3 K U₁ U₂ U₃) ⟨B, ω₁, ω₂, ω₃⟩ := by
  constructor
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, hA⟩
    exact ⟨g₁, g₂, g₃, h₁, h₂, h₃, hA⟩
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, hA⟩
    exact ⟨g₁, g₂, g₃, h₁, h₂, h₃, hA⟩

/-- The symplectic instance of step 1: `Sp`-isomorphism of padded tensors is `GL`-isomorphism of the
tensor systems that carry `omegaH` on each mode. -/
theorem spIso_iff_systemIso3_omegaH
    {V₁ V₂ V₃ : Type v} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (A B : Hyp K V₁ ⊗[K] (Hyp K V₂ ⊗[K] Hyp K V₃)) :
    (∃ (g₁ : Hyp K V₁ ≃ₗ[K] Hyp K V₁) (g₂ : Hyp K V₂ ≃ₗ[K] Hyp K V₂)
        (g₃ : Hyp K V₃ ≃ₗ[K] Hyp K V₃),
        IsSymplectic g₁ ∧ IsSymplectic g₂ ∧ IsSymplectic g₃ ∧ glAct g₁ g₂ g₃ A = B) ↔
      SystemIso3 (⟨A, omegaH, omegaH, omegaH⟩ : FormSystem3 K (Hyp K V₁) (Hyp K V₂) (Hyp K V₃))
        ⟨B, omegaH, omegaH, omegaH⟩ := by
  exact restrictedIso_iff_systemIso3
    (omegaH : Hyp K V₁ →ₗ[K] Hyp K V₁ →ₗ[K] K)
    (omegaH : Hyp K V₂ →ₗ[K] Hyp K V₂ →ₗ[K] K)
    (omegaH : Hyp K V₃ →ₗ[K] Hyp K V₃ →ₗ[K] K) A B

end System

/-! ## 3. The same step in the coordinates the complexity classes use -/

section Coord

variable {K : Type u} [Field K] {n : ℕ}

/-- **`Sp3TI` is exactly a matrix tensor-system isomorphism problem**, with form preservation
written as the `Coupling` relation that a gadget slice produces.

This is the interface the gadget consumes: it converts the `IsSymplecticMat` side conditions of
`ProjectionReductions20260902.Sp3TI` into coupling constraints, which is the only form in which a
`3`-tensor can express them. -/
theorem sp3ti_rel_iff_couplingSystem
    (A B : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) → K) :
    (Sp3TI K).Rel n A B ↔
      ∃ P Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
        Coupling (stdJ K n) P P ∧ Coupling (stdJ K n) Q Q ∧ Coupling (stdJ K n) R R ∧
          act3D K P Q R A = B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, hact⟩
    exact ⟨P, Q, R, (coupling_stdJ_self_iff P).mpr hP, (coupling_stdJ_self_iff Q).mpr hQ,
      (coupling_stdJ_self_iff R).mpr hR, hact⟩
  · rintro ⟨P, Q, R, hP, hQ, hR, hact⟩
    exact ⟨P, Q, R, (coupling_stdJ_self_iff P).mp hP, (coupling_stdJ_self_iff Q).mp hQ,
      (coupling_stdJ_self_iff R).mp hR, hact⟩

/-! ### The nine-slice constraint system of the three-mode gadget

The gadget enlarges each mode to `V ⊕ V ⊕ V ⊕ K³` with `V = K^{2n}`, and carries nine slices:
for each mode `i` a two-step identity chain running through the other two modes, plus one `stdJ`
slice across the two *ends* of that chain. Writing `aᵢ` for the transporter of mode `i`'s own block
and `bᵢ, cᵢ` for the two chain blocks, the slices impose exactly the nine relations below.

`chain_certifies_symplectic` is applied three times. Nothing else is used, and no hypotheses
(invertibility included) are assumed. -/

/-- **The gadget's constraint system forces all three transporters to be symplectic.** -/
theorem gadget_constraints_certify
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h₁₁ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₁ b₁)
    (h₁₂ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₁ c₁)
    (h₁₃ : Coupling (stdJ K n) a₁ c₁)
    (h₂₁ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₂ b₂)
    (h₂₂ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₂ c₂)
    (h₂₃ : Coupling (stdJ K n) a₂ c₂)
    (h₃₁ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₃ b₃)
    (h₃₂ : Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₃ c₃)
    (h₃₃ : Coupling (stdJ K n) a₃ c₃) :
    IsSymplecticMat K a₁ ∧ IsSymplecticMat K a₂ ∧ IsSymplecticMat K a₃ :=
  ⟨chain_certifies_symplectic h₁₁ h₁₂ h₁₃,
   chain_certifies_symplectic h₂₁ h₂₂ h₂₃,
   chain_certifies_symplectic h₃₁ h₃₂ h₃₃⟩

/-- **The converse**: three symplectic transporters extend to a solution of the gadget's whole
constraint system, with the explicit chain blocks `bᵢ = (aᵢ⁻¹)ᵀ`, `cᵢ = aᵢ`. -/
theorem gadget_constraints_of_symplectic
    {a₁ a₂ a₃ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h₁ : IsSymplecticMat K a₁) (h₂ : IsSymplecticMat K a₂) (h₃ : IsSymplecticMat K a₃) :
    ∃ b₁ c₁ b₂ c₂ b₃ c₃ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₁ b₁ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₁ c₁ ∧
      Coupling (stdJ K n) a₁ c₁ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₂ b₂ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₂ c₂ ∧
      Coupling (stdJ K n) a₂ c₂ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a₃ b₃ ∧
      Coupling (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b₃ c₃ ∧
      Coupling (stdJ K n) a₃ c₃ := by
  obtain ⟨p₁, p₂, p₃⟩ := chain_of_symplectic h₁
  obtain ⟨q₁, q₂, q₃⟩ := chain_of_symplectic h₂
  obtain ⟨r₁, r₂, r₃⟩ := chain_of_symplectic h₃
  exact ⟨(a₁⁻¹)ᵀ, a₁, (a₂⁻¹)ᵀ, a₂, (a₃⁻¹)ᵀ, a₃,
    p₁, p₂, p₃, q₁, q₂, q₃, r₁, r₂, r₃⟩

end Coord

#print axioms restrictedIso_iff_systemIso3
#print axioms spIso_iff_systemIso3_omegaH
#print axioms sp3ti_rel_iff_couplingSystem
#print axioms gadget_constraints_certify
#print axioms gadget_constraints_of_symplectic

end Mathproof.Meta.FGSGadgetSystem20260902

end Part_U26


section Part_U27


/-!
# The symplectic system as a partitioned array, and its link-free augmentation `H`

`FGSGadgetSystem20260902.sp3ti_rel_iff_couplingSystem` turns `Sp3TI` into a statement about the
four-component tensor system `(A, Φ_U, Φ_V, Φ_W)` with `Φ_i = stdJ`. This module realises that
system as a partitioned three-dimensional array and applies the link-removal construction, giving
`Hgadget`, whose *plain* block-equivalence is what the partition deletions consume.

## The array

All three axes carry the same four blocks (`Blk`), with `BIdx n = S n` (`= Fin n ⊕ Fin n`, card `2n`)
on `dat`, `cop`, `mid`, and `Unit` on `anch`:

| axis | `dat` | `cop` | `mid` | `anch` |
|------|-------|-------|-------|--------|
| 1 (rows)    | `a₁` | `c₂` | `b₃` | `x*` |
| 2 (cols)    | `a₂` | `c₃` | `b₁` | `y*` |
| 3 (strata)  | `a₃` | `c₁` | `b₂` | `z*` |

Eleven nonzero spatial blocks: content `(a₁,a₂,a₃) = A`; forms `(a₁,y*,c₁) = J`, `(c₂,a₂,z*) = J`,
`(x*,c₃,a₃) = J`; anchor `(x*,y*,z*) = [1]`; and six identity blocks realising `a_i ∼ c_i`,
two per link — `(a₁,b₁,z*)`, `(x*,b₁,c₁)`; `(x*,a₂,b₂)`, `(c₂,y*,b₂)`; `(b₃,y*,a₃)`, `(b₃,c₃,z*)`.

Every form and identity block puts its **third** slot on an anchor: for the identity blocks that
makes the constraint read `S_a S_bᵀ = I` (the shape of `FGSGadgetCoupling20260902.coupling_one_iff`),
and for the form blocks it pins the corresponding scalar to `1` once the anchor transporters are
normalised, so the forms need no extra link.

## Design notes paid for in build rounds

* `Blk` is a four-constructor inductive, not `Fin 4`: with `![S n, S n, S n, Unit]` neither the
  `Fintype` instance search nor the `match` in `Hgadget` reduces.
* The `Fintype Blk` instance is written by hand. `deriving Fintype` produced an instance whose
  internal completeness proof failed here (`Blk.enumList` / `Blk.enumList_nodup`).
* `Fintype.card_sum` is **not** in the default simp set, so `card_S` is stated on the unfolded
  `Fin n ⊕ Fin n` — `S` is an `abbrev`, so `simp` unfolds it before a lemma stated on `S n` could
  fire.
* The per-block **entry lemmas** below (`Hgadget_apply_*`, all `rfl`) exist because `Matrix.of_apply`
  did not fire inside the `dite` bodies, and because a `first | …` combinator over the sixteen
  blocks silently selected wrong branches — it commits to the first alternative that does not fail
  *structurally*, even when the arithmetic inside is unprovable. Explicit per-block lemmas remove
  both problems, and the four theorems downstream need them anyway.
-/

namespace Mathproof.Meta.FGSSymplecticEncoding20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSLinkedBlockEquiv20260902

universe u

variable {K : Type u} [Field K]

/-- The mode index of `V = K^{2n}`; `card (S n) = 2n`. -/
abbrev S (n : ℕ) : Type := Fin n ⊕ Fin n

/-- The four blocks carried by each axis. -/
inductive Blk where
  /-- `aᵢ`: carries the content tensor and the forms. -/
  | dat : Blk
  /-- `cᵢ`: the copy linked to `aᵢ`. -/
  | cop : Blk
  /-- `bᵢ`: the fresh middle block realising the link. -/
  | mid : Blk
  /-- the one-dimensional anchor. -/
  | anch : Blk
  deriving DecidableEq

instance : Nonempty Blk := ⟨Blk.dat⟩

instance : Inhabited Blk := ⟨Blk.dat⟩

instance : Fintype Blk where
  elems := {Blk.dat, Blk.cop, Blk.mid, Blk.anch}
  complete := by intro x; cases x <;> decide

/-- The index type of each block. `abbrev`, not `def`: instance search must be able to see
`BIdx n Blk.dat = S n` at reducible transparency, otherwise `Decidable (i = j)` cannot be
synthesised for `i j : BIdx n Blk.dat`. -/
abbrev BIdx (n : ℕ) : Blk → Type
  | Blk.dat => S n
  | Blk.cop => S n
  | Blk.mid => S n
  | Blk.anch => Unit

instance instFintypeBIdx (n : ℕ) : ∀ b : Blk, Fintype (BIdx n b)
  | Blk.dat => inferInstanceAs (Fintype (S n))
  | Blk.cop => inferInstanceAs (Fintype (S n))
  | Blk.mid => inferInstanceAs (Fintype (S n))
  | Blk.anch => inferInstanceAs (Fintype Unit)

instance instDecEqBIdx (n : ℕ) : ∀ b : Blk, DecidableEq (BIdx n b)
  | Blk.dat => inferInstanceAs (DecidableEq (S n))
  | Blk.cop => inferInstanceAs (DecidableEq (S n))
  | Blk.mid => inferInstanceAs (DecidableEq (S n))
  | Blk.anch => inferInstanceAs (DecidableEq Unit)

/-! ## Cardinalities -/

theorem card_S (n : ℕ) : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
  rw [Fintype.card_sum, Fintype.card_fin, two_mul]

theorem card_BIdx (n : ℕ) (b : Blk) :
    Fintype.card (BIdx n b) = if b = Blk.anch then 1 else 2 * n := by
  cases b
  · exact card_S n
  · exact card_S n
  · exact card_S n
  · rfl

/-- **Each axis of `H` carries `6n+1` coordinates.** -/
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

/-! ## The augmented array -/

/-- The augmented array `H(L(A))`. -/
noncomputable def Hgadget (n : ℕ) {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)
    (A : S n × S n × S n → K) :
    PArr K Blk Blk (BIdx n) (BIdx n) th :=
  fun k b s =>
    match b, s with
    | Blk.dat, Blk.dat => Matrix.of fun (i : S n) (j : S n) =>
        if h : strH k = 0 then A (i, j, (e0.symm ⟨k, h⟩ : S n)) else 0
    | Blk.dat, Blk.cop => 0
    | Blk.dat, Blk.mid => Matrix.of fun (i : S n) (j : S n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.dat, Blk.anch => Matrix.of fun (i : S n) (_ : Unit) =>
        if h : strH k = 1 then stdJ K n i (e1.symm ⟨k, h⟩) else 0
    | Blk.cop, Blk.dat => Matrix.of fun (i : S n) (j : S n) =>
        if strH k = 3 then stdJ K n i j else 0
    | Blk.cop, Blk.cop => 0
    | Blk.cop, Blk.mid => 0
    | Blk.cop, Blk.anch => Matrix.of fun (i : S n) (_ : Unit) =>
        if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.mid, Blk.dat => 0
    | Blk.mid, Blk.cop => Matrix.of fun (i : S n) (j : S n) =>
        if strH k = 3 then (if i = j then (1 : K) else 0) else 0
    | Blk.mid, Blk.mid => 0
    | Blk.mid, Blk.anch => Matrix.of fun (i : S n) (_ : Unit) =>
        if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.dat => Matrix.of fun (_ : Unit) (j : S n) =>
        if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.cop => Matrix.of fun (_ : Unit) (j : S n) =>
        if h : strH k = 0 then stdJ K n j (e0.symm ⟨k, h⟩) else 0
    | Blk.anch, Blk.mid => Matrix.of fun (_ : Unit) (j : S n) =>
        if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0
    | Blk.anch, Blk.anch => Matrix.of fun (_ : Unit) (_ : Unit) =>
        if strH k = 3 then (1 : K) else 0

/-! ### Per-block entry lemmas

All `rfl`: the `match` and `Matrix.of` are both definitional. These exist so that no downstream
proof has to unfold `Hgadget`, and so that `Matrix.of_apply` — which does not fire inside the
`dite` bodies — is never needed. -/

section Entries

variable (n : ℕ) {th : ℕ} (strH : Fin th → Fin 4)
  (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)
  (A : S n × S n × S n → K) (k : Fin th)

theorem Hgadget_dat_dat (i : BIdx n Blk.dat) (j : BIdx n Blk.dat) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.dat Blk.dat i j
      = if h : strH k = 0 then A (i, j, (e0.symm ⟨k, h⟩ : S n)) else 0 := rfl

theorem Hgadget_dat_cop (i : BIdx n Blk.dat) (j : BIdx n Blk.cop) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.dat Blk.cop i j = 0 := rfl

theorem Hgadget_dat_mid (i : BIdx n Blk.dat) (j : BIdx n Blk.mid) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.dat Blk.mid i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem Hgadget_dat_anch (i : BIdx n Blk.dat) (j : BIdx n Blk.anch) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.dat Blk.anch i j
      = if h : strH k = 1 then stdJ K n i (e1.symm ⟨k, h⟩) else 0 := rfl

theorem Hgadget_cop_dat (i : BIdx n Blk.cop) (j : BIdx n Blk.dat) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.cop Blk.dat i j
      = if strH k = 3 then stdJ K n i j else 0 := rfl

theorem Hgadget_cop_cop (i : BIdx n Blk.cop) (j : BIdx n Blk.cop) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.cop Blk.cop i j = 0 := rfl

theorem Hgadget_cop_mid (i : BIdx n Blk.cop) (j : BIdx n Blk.mid) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.cop Blk.mid i j = 0 := rfl

theorem Hgadget_cop_anch (i : BIdx n Blk.cop) (j : BIdx n Blk.anch) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.cop Blk.anch i j
      = if h : strH k = 2 then (if i = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem Hgadget_mid_dat (i : BIdx n Blk.mid) (j : BIdx n Blk.dat) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.mid Blk.dat i j = 0 := rfl

theorem Hgadget_mid_cop (i : BIdx n Blk.mid) (j : BIdx n Blk.cop) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.mid Blk.cop i j
      = if strH k = 3 then (if i = j then (1 : K) else 0) else 0 := rfl

theorem Hgadget_mid_mid (i : BIdx n Blk.mid) (j : BIdx n Blk.mid) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.mid Blk.mid i j = 0 := rfl

theorem Hgadget_mid_anch (i : BIdx n Blk.mid) (j : BIdx n Blk.anch) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.mid Blk.anch i j
      = if h : strH k = 0 then (if i = e0.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem Hgadget_anch_dat (i : BIdx n Blk.anch) (j : BIdx n Blk.dat) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.anch Blk.dat i j
      = if h : strH k = 2 then (if j = e2.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem Hgadget_anch_cop (i : BIdx n Blk.anch) (j : BIdx n Blk.cop) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.anch Blk.cop i j
      = if h : strH k = 0 then stdJ K n j (e0.symm ⟨k, h⟩) else 0 := rfl

theorem Hgadget_anch_mid (i : BIdx n Blk.anch) (j : BIdx n Blk.mid) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.anch Blk.mid i j
      = if h : strH k = 1 then (if j = e1.symm ⟨k, h⟩ then (1 : K) else 0) else 0 := rfl

theorem Hgadget_anch_anch (i : BIdx n Blk.anch) (j : BIdx n Blk.anch) :
    Hgadget (K := K) n strH e0 e1 e2 A k Blk.anch Blk.anch i j
      = if strH k = 3 then (1 : K) else 0 := rfl

end Entries

/-! ## Every entry is a constant-free source -/

/-- Every entry of `stdJ` is `0`, `1` or `-1`. -/
theorem stdJ_entry_src (n : ℕ) (i j : S n) :
    ∃ σ : Src (S n × S n × S n), ∀ A : S n × S n × S n → K, stdJ K n i j = σ.eval A := by
  classical
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [stdJ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact ⟨Src.zero, fun _ => rfl⟩
  · by_cases h : i = j
    · exact ⟨Src.one, fun _ => by simp [Matrix.one_apply, h]; rfl⟩
    · exact ⟨Src.zero, fun _ => by simp [Matrix.one_apply, h]; rfl⟩
  · by_cases h : i = j
    · exact ⟨Src.negOne, fun _ => by simp [Matrix.one_apply, h]; rfl⟩
    · exact ⟨Src.zero, fun _ => by simp [Matrix.one_apply, h]; rfl⟩
  · exact ⟨Src.zero, fun _ => rfl⟩

/-- A `0/1` entry is `Src`-expressible. -/
theorem ite_one_src (n : ℕ) (P : Prop) [Decidable P] :
    ∃ σ : Src (S n × S n × S n),
      ∀ A : S n × S n × S n → K, (if P then (1 : K) else 0) = σ.eval A := by
  by_cases h : P
  · exact ⟨Src.one, fun _ => by rw [if_pos h]; rfl⟩
  · exact ⟨Src.zero, fun _ => by rw [if_neg h]; rfl⟩

/-- The zero entry. -/
theorem zero_src (n : ℕ) :
    ∃ σ : Src (S n × S n × S n), ∀ A : S n × S n × S n → K, (0 : K) = σ.eval A :=
  ⟨Src.zero, fun _ => rfl⟩

/-- **Every entry of `H(L(A))` is an input coordinate, `0`, `1` or `-1`.**

Stated per flat position `(k, b, s, i, j)` and *uniformly in `A`*, so the projection's `src` field
can be read off without ever unfolding `Hgadget`. Each of the sixteen blocks is handled explicitly:
a `first | …` combinator over them silently commits to wrong branches. -/
theorem Hgadget_src (n : ℕ) {th : ℕ} (strH : Fin th → Fin 4)
    (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)
    (k : Fin th) (b s : Blk) (i : BIdx n b) (j : BIdx n s) :
    ∃ σ : Src (S n × S n × S n),
      ∀ A : S n × S n × S n → K,
        Hgadget (K := K) n strH e0 e1 e2 A k b s i j = σ.eval A := by
  classical
  cases b <;> cases s
  -- dat, dat : the content block
  · by_cases h : strH k = 0
    · exact ⟨Src.coord (i, j, (e0.symm ⟨k, h⟩ : S n)), fun A => by
        rw [Hgadget_dat_dat, dif_pos h]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_dat_dat, dif_neg h]; rfl⟩
  -- dat, cop : zero
  · exact ⟨Src.zero, fun A => by rw [Hgadget_dat_cop]; rfl⟩
  -- dat, mid : identity at stratum 3
  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = j)
      exact ⟨σ, fun A => by rw [Hgadget_dat_mid, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_dat_mid, if_neg h]; rfl⟩
  -- dat, anch : form block at stratum 1
  · by_cases h : strH k = 1
    · obtain ⟨σ, hσ⟩ := stdJ_entry_src (K := K) n i (e1.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_dat_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_dat_anch, dif_neg h]; rfl⟩
  -- cop, dat : form block at stratum 3
  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := stdJ_entry_src (K := K) n i j
      exact ⟨σ, fun A => by rw [Hgadget_cop_dat, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_cop_dat, if_neg h]; rfl⟩
  -- cop, cop : zero
  · exact ⟨Src.zero, fun A => by rw [Hgadget_cop_cop]; rfl⟩
  -- cop, mid : zero
  · exact ⟨Src.zero, fun A => by rw [Hgadget_cop_mid]; rfl⟩
  -- cop, anch : identity at stratum 2
  · by_cases h : strH k = 2
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = e2.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_cop_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_cop_anch, dif_neg h]; rfl⟩
  -- mid, dat : zero
  · exact ⟨Src.zero, fun A => by rw [Hgadget_mid_dat]; rfl⟩
  -- mid, cop : identity at stratum 3
  · by_cases h : strH k = 3
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = j)
      exact ⟨σ, fun A => by rw [Hgadget_mid_cop, if_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_mid_cop, if_neg h]; rfl⟩
  -- mid, mid : zero
  · exact ⟨Src.zero, fun A => by rw [Hgadget_mid_mid]; rfl⟩
  -- mid, anch : identity at stratum 0
  · by_cases h : strH k = 0
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (i = e0.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_mid_anch, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_mid_anch, dif_neg h]; rfl⟩
  -- anch, dat : identity at stratum 2
  · by_cases h : strH k = 2
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (j = e2.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_anch_dat, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_anch_dat, dif_neg h]; rfl⟩
  -- anch, cop : form block at stratum 0
  · by_cases h : strH k = 0
    · obtain ⟨σ, hσ⟩ := stdJ_entry_src (K := K) n j (e0.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_anch_cop, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_anch_cop, dif_neg h]; rfl⟩
  -- anch, mid : identity at stratum 1
  · by_cases h : strH k = 1
    · obtain ⟨σ, hσ⟩ := ite_one_src (K := K) n (j = e1.symm ⟨k, h⟩)
      exact ⟨σ, fun A => by rw [Hgadget_anch_mid, dif_pos h]; exact hσ A⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_anch_mid, dif_neg h]; rfl⟩
  -- anch, anch : the anchor block
  · by_cases h : strH k = 3
    · exact ⟨Src.one, fun A => by rw [Hgadget_anch_anch, if_pos h]; rfl⟩
    · exact ⟨Src.zero, fun A => by rw [Hgadget_anch_anch, if_neg h]; rfl⟩

end Mathproof.Meta.FGSSymplecticEncoding20260902

end Part_U27


section Part_U28


/-!
# A concrete frontal packing, and `H` as a single-parameter family in `n`

`FGSSymplecticEncoding20260902.Hgadget` takes the frontal packing as parameters — a stratum map
`strH : Fin th → Fin 4` and identifications of each stratum's fibre with the corresponding block's
index type. That is the right shape for the theory, but the projection packaging needs **one**
concrete family in `n`. This module supplies it.

## The packing

Each axis carries `6n+1` coordinates (`Hgadget_card`), so the frontal axis has `th n = 6n+1` slices
grouped into strata of sizes `2n, 2n, 2n, 1`. The packing is obtained by transporting the tagged
disjoint union

  `Idx3 n = S n ⊕ (S n ⊕ (S n ⊕ Unit))`

to `Fin (6n+1)` along *any* bijection — `Fintype.equivFinOfCardEq` — and letting `strHn` be the tag
read back through it. Which bijection is irrelevant: every statement downstream is invariant under
relabelling the slices, so nothing is lost by using choice here.

`noncomputable` throughout. That is fine: `Projection.src` is a plain function field inside a
`Prop`-level proof, and nothing downstream evaluates it.

## Why the fibre equivalences are built by `Equiv.ofBijective`

The fibre of stratum `g` is `{k // strHn n k = g}`, which transports to `{x : Idx3 n // tag3 n x = g}`
by `Equiv.subtypeEquiv` — the side condition is `Iff.rfl`, since `strHn` is *defined* as the tag of
the transported point. Identifying that subtype with `S n` by a direct `match` would need a branch
producing an element of `S n` from an impossible case, and `S n` can be **empty** (at `n = 0`), so
there is no default to fall back on. Going through `Equiv.ofBijective` on `v ↦ ⟨Sum.inl v, rfl⟩`
avoids the issue entirely: the impossible cases appear only inside a *surjectivity* proof, where
they are discharged by `simp`/`decide` on the tag.
-/

namespace Mathproof.Meta.FGSConcretePacking20260902

open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSLinkedBlockEquiv20260902
open Mathproof.Meta.FGSSymplecticEncoding20260902

universe u

variable {K : Type u} [Field K]

/-- The number of frontal slices: `2n + 2n + 2n + 1`. -/
abbrev thn (n : ℕ) : ℕ := 6 * n + 1

/-- The tagged disjoint union that the frontal axis packs. -/
abbrev Idx3 (n : ℕ) : Type := S n ⊕ (S n ⊕ (S n ⊕ Unit))

/-- Which stratum a tagged point belongs to. -/
def tag3 (n : ℕ) : Idx3 n → Fin 4
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

theorem card_Idx3 (n : ℕ) : Fintype.card (Idx3 n) = thn n := by
  simp only [Idx3, thn, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

/-- Any bijection `Idx3 n ≃ Fin (6n+1)`; which one is irrelevant. -/
noncomputable def packEquiv (n : ℕ) : Idx3 n ≃ Fin (thn n) :=
  Fintype.equivFinOfCardEq (card_Idx3 n)

/-- The concrete stratum map. -/
noncomputable def strHn (n : ℕ) : Fin (thn n) → Fin 4 :=
  fun k => tag3 n ((packEquiv n).symm k)

/-- The fibre of a stratum, transported back to the tagged union. -/
noncomputable def fibEquiv (n : ℕ) (g : Fin 4) :
    Fib (strHn n) g ≃ {x : Idx3 n // tag3 n x = g} :=
  Equiv.subtypeEquiv (packEquiv n).symm (fun _ => Iff.rfl)

/-! ### Identifying each tagged fibre with its block's index type -/

noncomputable def sub0 (n : ℕ) : S n ≃ {x : Idx3 n // tag3 n x = 0} :=
  Equiv.ofBijective (fun v => ⟨Sum.inl v, rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · exact ⟨v, rfl⟩
      · rcases y with u | z
        · simp [tag3] at hx
        · rcases z with p | q <;> simp [tag3] at hx⟩

noncomputable def sub1 (n : ℕ) : S n ≃ {x : Idx3 n // tag3 n x = 1} :=
  Equiv.ofBijective (fun v => ⟨Sum.inr (Sum.inl v), rfl⟩)
    ⟨fun v w h => by simpa using congrArg Subtype.val h,
     by
      rintro ⟨x, hx⟩
      rcases x with v | y
      · simp [tag3] at hx
      · rcases y with u | z
        · exact ⟨u, rfl⟩
        · rcases z with p | q <;> simp [tag3] at hx⟩

noncomputable def sub2 (n : ℕ) : S n ≃ {x : Idx3 n // tag3 n x = 2} :=
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

/-- The three fibre identifications `Hgadget` needs. -/
noncomputable def e0n (n : ℕ) : S n ≃ Fib (strHn n) 0 := (sub0 n).trans (fibEquiv n 0).symm
noncomputable def e1n (n : ℕ) : S n ≃ Fib (strHn n) 1 := (sub1 n).trans (fibEquiv n 1).symm
noncomputable def e2n (n : ℕ) : S n ≃ Fib (strHn n) 2 := (sub2 n).trans (fibEquiv n 2).symm

/-- The anchor stratum is a single slice — this is what pins the form blocks' scalars. -/
noncomputable def e3n (n : ℕ) : Unit ≃ Fib (strHn n) 3 := (sub3 n).trans (fibEquiv n 3).symm

/-! ## `H` as a single family in `n` -/

/-- The augmented array at the concrete packing. -/
noncomputable def H (n : ℕ) (A : S n × S n × S n → K) :
    PArr K Blk Blk (BIdx n) (BIdx n) (thn n) :=
  Hgadget n (strHn n) (e0n n) (e1n n) (e2n n) A

/-- **Every entry of `H n A` is an input coordinate, `0`, `1` or `-1`**, in the flat position form
`(k, ⟨b,i⟩, ⟨s,j⟩)` that `toFun : PArr → (Pos → K)` consumes. -/
theorem H_src (n : ℕ)
    (z : Fin (thn n) × (Σ b : Blk, BIdx n b) × (Σ s : Blk, BIdx n s)) :
    ∃ σ : Src (S n × S n × S n),
      ∀ A : S n × S n × S n → K,
        H (K := K) n A z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2 = σ.eval A :=
  Hgadget_src n (strHn n) (e0n n) (e1n n) (e2n n) z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2

/-- Each axis of `H n A` carries `6n+1` coordinates, in the `Σ`-form the flattening uses. -/
theorem H_card (n : ℕ) : Fintype.card (Σ b : Blk, BIdx n b) = thn n := by
  rw [Fintype.card_sigma]
  exact Hgadget_card n

/-- The number of blocks per axis, for the size bound. -/
theorem card_Blk : Fintype.card Blk = 4 := rfl

/-- Alias in the naming the size bound uses. -/
theorem H_card_row (n : ℕ) : Fintype.card (Σ b : Blk, BIdx n b) = 6 * n + 1 := H_card n

/-- The column axis has the same shape as the row axis. -/
theorem H_card_col (n : ℕ) : Fintype.card (Σ s : Blk, BIdx n s) = 6 * n + 1 := H_card n

end Mathproof.Meta.FGSConcretePacking20260902

end Part_U28


section Part_U29


/-!
# The forward direction of the encoding theorem: infrastructure

## Purpose

§2.2 of `D:/proof/COMPLETE_FULL_PROOFS_SP3TI_TO_GL3TI_PROOF.md`: from a symplectic triple
`(g₁, g₂, g₃)` carrying `A` to `B`, build the block transporters

* rows `(g₁, g₂, g₃⁻ᵀ, 1)`, columns `(g₂, g₃, g₁⁻ᵀ, 1)` on the blocks `(dat, cop, mid, anch)`;
* frontal `R = assemble (g₃, g₁, g₂⁻ᵀ, 1)` on the strata `(0, 1, 2, 3)`, each block transported
  along the fibre identifications `e0, e1, e2` (untransposed: `R` acts on the column side);

and prove they are invertible and `R` is block-diagonal. The slice-sum lemma
`sum_assemble_smul` collapses `∑ k', R k k' • M k'` to the single stratum carrying `M`, and
`sum_fib_reindex` moves that sum to `S n`. `act3D_slice` is the slice form of the `Sp3TI` action.

## DAG chain walked

`Matrix.reindex`, `Matrix.det_reindex_self`, `Matrix.det_transpose`, `Matrix.isUnit_nonsing_inv_det`,
`Finset.sum_filter_of_ne`, `Finset.sum_subtype`, `Equiv.sum_comp`, `Finset.sum_comm`; tree:
`FGSLinkedBlockEquiv20260902.assemble / isBlockDiag_assemble / assemble_apply_of_eq /
isUnit_det_assemble_iff`, `FGSSymplecticEncoding20260902.Hgadget`.
-/

namespace Mathproof.Meta.FGSEncodingForward20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSLinkedBlockEquiv20260902
open Mathproof.Meta.FGSSymplecticEncoding20260902

universe u

variable {K : Type u} [Field K]

section Setup

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)

/-- Inverse transpose. -/
noncomputable abbrev invT (g : Matrix (S n) (S n) K) : Matrix (S n) (S n) K := g⁻¹ᵀ

theorem isUnit_det_invT {g : Matrix (S n) (S n) K} (h : IsUnit g.det) : IsUnit (invT g).det := by
  rw [invT, Matrix.det_transpose]
  exact Matrix.isUnit_nonsing_inv_det g h

/-- `g * (g⁻ᵀ)ᵀ = 1`. -/
theorem mul_invT_transpose {g : Matrix (S n) (S n) K} (h : IsUnit g.det) :
    g * (invT g)ᵀ = 1 := by
  rw [invT, Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv g h

/-- `g⁻ᵀ * gᵀ = 1`. -/
theorem invT_mul_transpose {g : Matrix (S n) (S n) K} (h : IsUnit g.det) :
    invT g * gᵀ = 1 := by
  rw [invT, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv g h, Matrix.transpose_one]

/-- Row transporters `(g₁, g₂, g₃⁻ᵀ, 1)`. -/
noncomputable def Pfwd (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    ∀ b : Blk, Matrix (BIdx n b) (BIdx n b) K
  | Blk.dat => g₁
  | Blk.cop => g₂
  | Blk.mid => invT g₃
  | Blk.anch => 1

/-- Column transporters `(g₂, g₃, g₁⁻ᵀ, 1)`. -/
noncomputable def Qfwd (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    ∀ s : Blk, Matrix (BIdx n s) (BIdx n s) K
  | Blk.dat => g₂
  | Blk.cop => g₃
  | Blk.mid => invT g₁
  | Blk.anch => 1

theorem Pfwd_isUnit (g₁ g₂ g₃ : Matrix (S n) (S n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ b, IsUnit (Pfwd g₁ g₂ g₃ b).det
  | Blk.dat => h₁
  | Blk.cop => h₂
  | Blk.mid => isUnit_det_invT h₃
  | Blk.anch => by simp [Pfwd]

theorem Qfwd_isUnit (g₁ g₂ g₃ : Matrix (S n) (S n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : ∀ s, IsUnit (Qfwd g₁ g₂ g₃ s).det
  | Blk.dat => h₂
  | Blk.cop => h₃
  | Blk.mid => isUnit_det_invT h₁
  | Blk.anch => by simp [Qfwd]

/-- Per-stratum frontal blocks `(g₃, g₁, g₂⁻ᵀ, 1)`, transported along the fibre identifications. -/
noncomputable def Rst (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K
  | 0 => Matrix.reindex e0 e0 g₃
  | 1 => Matrix.reindex e1 e1 g₁
  | 2 => Matrix.reindex e2 e2 (invT g₂)
  | 3 => 1

theorem Rst_zero (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 0 = Matrix.reindex e0 e0 g₃ := rfl
theorem Rst_one (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 1 = Matrix.reindex e1 e1 g₁ := rfl
theorem Rst_two (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 2 = Matrix.reindex e2 e2 (invT g₂) := rfl
theorem Rst_three (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    Rst strH e0 e1 e2 g₁ g₂ g₃ 3 = 1 := rfl

/-- The frontal transporter. -/
noncomputable def Rfwd (g₁ g₂ g₃ : Matrix (S n) (S n) K) : Matrix (Fin th) (Fin th) K :=
  assemble strH (Rst strH e0 e1 e2 g₁ g₂ g₃)

theorem Rfwd_isBlockDiag (g₁ g₂ g₃ : Matrix (S n) (S n) K) :
    IsBlockDiag strH (Rfwd strH e0 e1 e2 g₁ g₂ g₃) :=
  isBlockDiag_assemble strH _

theorem Rfwd_isUnit (g₁ g₂ g₃ : Matrix (S n) (S n) K) (h₁ : IsUnit g₁.det) (h₂ : IsUnit g₂.det)
    (h₃ : IsUnit g₃.det) : IsUnit (Rfwd strH e0 e1 e2 g₁ g₂ g₃).det := by
  rw [Rfwd, isUnit_det_assemble_iff]
  intro g
  match g with
  | 0 => rw [Rst_zero, Matrix.det_reindex_self]; exact h₃
  | 1 => rw [Rst_one, Matrix.det_reindex_self]; exact h₁
  | 2 => rw [Rst_two, Matrix.det_reindex_self]; exact isUnit_det_invT h₂
  | 3 => rw [Rst_three]; simp

end Setup

/-! ### Collapsing the slice sum to one stratum -/

section Sums

variable {n th : ℕ} (strH : Fin th → Fin 4)

/-- With `R = assemble Rst` and `M` supported on stratum `g₀`, the slice sum lives on that stratum. -/
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

/-- Move a fibre sum to `S n`. -/
theorem sum_fib_reindex {I J : Type} [Fintype I] [Fintype J] {g₀ : Fin 4} (e : S n ≃ Fib strH g₀)
    (F : Fib strH g₀ → Matrix I J K) : ∑ k' : Fib strH g₀, F k' = ∑ m : S n, F (e m) :=
  (Equiv.sum_comp e F).symm

theorem reindex_apply_symm {g₀ : Fin 4} (e : S n ≃ Fib strH g₀) (G : Matrix (S n) (S n) K)
    (a : Fib strH g₀) (m : S n) : Matrix.reindex e e G a (e m) = G (e.symm a) m := by
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

end Sums

/-! ### Slices of the `Sp3TI` action -/

section Slices

variable {n : ℕ}

/-- The `m`-th frontal slice of a doubled cubic array. -/
def slice (A : S n × S n × S n → K) (m : S n) : Matrix (S n) (S n) K :=
  Matrix.of fun i j => A (i, j, m)

theorem slice_apply (A : S n × S n × S n → K) (m i j : S n) : slice A m i j = A (i, j, m) := rfl

theorem sum3_rotate (f : S n → S n → S n → K) :
    ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ k', ∑ j', ∑ i', f i' j' k' :=
  calc ∑ i', ∑ j', ∑ k', f i' j' k' = ∑ j', ∑ i', ∑ k', f i' j' k' := Finset.sum_comm
    _ = ∑ j', ∑ k', ∑ i', f i' j' k' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k', ∑ j', ∑ i', f i' j' k' := Finset.sum_comm

/-- The slice form of `act3D`: slice `k` of the image is `∑ m, g₃ k m • (g₁ * A_m * g₂ᵀ)`. -/
theorem act3D_slice (g₁ g₂ g₃ : Matrix (S n) (S n) K) (A : S n × S n × S n → K) (k : S n) :
    slice (act3D K g₁ g₂ g₃ A) k = ∑ m, g₃ k m • (g₁ * slice A m * g₂ᵀ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [slice_apply, act3D, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine (sum3_rotate (fun i' j' k' => g₁ i i' * g₂ j j' * g₃ k k' * A (i', j', k'))).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun i' _ => ?_
  ring

end Slices

end Mathproof.Meta.FGSEncodingForward20260902

end Part_U29


section Part_U30


/-!
# The forward direction of the encoding theorem

## Purpose

§2.2 of `D:/proof/COMPLETE_FULL_PROOFS_SP3TI_TO_GL3TI_PROOF.md`: if `(g₁, g₂, g₃)` is a symplectic
triple with `act3D g₁ g₂ g₃ A = B`, then `H(A)` and `H(B)` are block-equivalent, with the
transporters of `FGSEncodingForward20260902`. Each of the sixteen blocks of `H` is checked: the
five zero blocks trivially, the four stratum-3 blocks by `g · 1 · g⁻¹ = 1` and `g J gᵀ = J`, the
data block by the slice form of the action, and the six stratum-supported vector blocks by
`g · g⁻¹ = 1` (identity links) or `g J gᵀ = J` (form links).

* `Hmat_*` — the sixteen blocks as matrices;
* `block_step`, `block_step3` — the slice sum collapsed to one stratum and moved to `S n`;
* the transport identities `colE_transport`, `rowE_transport`, `colJ_transport`, `rowJ_transport`;
* `blockEquiv_of_sp3ti` — the forward direction;
* `sp3ti_rel_imp_blockEquiv_H` — specialised to the concrete packing `H n`.

## DAG chain walked

`Matrix.mul_nonsing_inv`, `Matrix.det_mul`, `Matrix.det_transpose`, `isUnit_iff_ne_zero`,
`Finset.sum_ite_eq`, `Matrix.one_apply`; tree: `FGSEncodingForward20260902.*`,
`FGSGadgetCoupling20260902.isSymplecticMat_iff_covariant`, `ProjectionReductions20260902.isUnit_det_stdJ`.
-/

namespace Mathproof.Meta.FGSEncodingForwardMain20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.FGSBlockArrays20260902
open Mathproof.Meta.FGSLinkedBlockEquiv20260902
open Mathproof.Meta.FGSSymplecticEncoding20260902
open Mathproof.Meta.FGSConcretePacking20260902
open Mathproof.Meta.FGSEncodingForward20260902
open Mathproof.Meta.FGSGadgetCoupling20260902 (isSymplecticMat_iff_covariant)

universe u

variable {K : Type u} [Field K]

/-! ### Symplectic matrices are invertible -/

theorem isUnit_det_of_symplectic {n : ℕ} {g : Matrix (S n) (S n) K} (h : IsSymplecticMat K g) :
    IsUnit g.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hJ : (stdJ K n).det ≠ 0 := (isUnit_det_stdJ K n).ne_zero
  have h2 : (g.det * g.det) * (stdJ K n).det = 1 * (stdJ K n).det := by
    rw [one_mul]
    calc (g.det * g.det) * (stdJ K n).det = g.det * (stdJ K n).det * g.det := by ring
      _ = (stdJ K n).det := hd
  have h3 : g.det * g.det = 1 := mul_right_cancel₀ hJ h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h3
  exact zero_ne_one h3

/-! ### Entries of slice sums -/

theorem sum_smul_entry {I J ι : Type} [Fintype ι] (c : ι → K) (M : ι → Matrix I J K) (i : I)
    (j : J) : (∑ m, c m • M m) i j = ∑ m, c m * M m i j := by
  simp [Matrix.sum_apply]

/-! ### Vector blocks -/

section Vectors

variable {n : ℕ}

/- The extra index type `I`/`J` is kept generic (it is `Unit` in use): elaborating these statements
directly at `Matrix Unit (S n) K` lets a stray `CStarMatrix` instance capture the `•`, after which no
`Matrix` lemma fires. -/

variable (K)

/-- The column indicator of `m`. -/
def colE {J : Type} (m : S n) : Matrix (S n) J K := Matrix.of fun i _ => if i = m then 1 else 0
/-- The row indicator of `m`. -/
def rowE {I : Type} (m : S n) : Matrix I (S n) K := Matrix.of fun _ j => if j = m then 1 else 0
/-- Column `m` of `J`. -/
def colJ {J : Type} (m : S n) : Matrix (S n) J K := Matrix.of fun i _ => stdJ K n i m
/-- Column `m` of `J`, laid out as a row. -/
def rowJ {I : Type} (m : S n) : Matrix I (S n) K := Matrix.of fun _ j => stdJ K n j m

variable {K} {I J : Type}

theorem mul_colE (g : Matrix (S n) (S n) K) (m : S n) :
    g * colE K (J := J) m = Matrix.of fun i _ => g i m := by
  ext i u
  rw [Matrix.mul_apply]
  simp [colE]

theorem rowE_mul (g : Matrix (S n) (S n) K) (m : S n) :
    rowE K (I := I) m * g = Matrix.of fun _ j => g m j := by
  ext u j
  rw [Matrix.mul_apply]
  simp [rowE]

theorem mul_colJ_entry (g : Matrix (S n) (S n) K) (m i : S n) (u : J) :
    (g * colJ K (J := J) m) i u = ∑ i', g i i' * stdJ K n i' m := by
  rw [Matrix.mul_apply]
  simp [colJ]

theorem rowJ_mul_entry (g : Matrix (S n) (S n) K) (m j : S n) (u : I) :
    (rowJ K (I := I) m * gᵀ) u j = ∑ j', stdJ K n j' m * g j j' := by
  rw [Matrix.mul_apply]
  simp [rowJ]

/-- `(g * g⁻¹) x i` in expanded form. -/
theorem mul_inv_entry {g : Matrix (S n) (S n) K} (h : IsUnit g.det) (x i : S n) :
    ∑ m, g x m * g⁻¹ m i = if x = i then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mul_nonsing_inv g h) x) i
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

/-- `(g * J * gᵀ) i x` in expanded form. -/
theorem cov_entry {g : Matrix (S n) (S n) K} (h : g * stdJ K n * gᵀ = stdJ K n) (i x : S n) :
    ∑ m, (∑ i', g i i' * stdJ K n i' m) * g x m = stdJ K n i x := by
  have := congrFun (congrFun h i) x
  rw [Matrix.mul_apply] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
  exact this

/-- `∑ m, g x m • (g⁻ᵀ * e_m) = e_x`. -/
theorem colE_transport {g : Matrix (S n) (S n) K} (h : IsUnit g.det) (x : S n) :
    ∑ m, g x m • (invT g * colE K (J := J) m) = colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colE, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [mul_inv_entry h, colE, Matrix.of_apply]
  by_cases hx : i = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

/-- `∑ m, g⁻ᵀ x m • (g * e_m) = e_x`. -/
theorem colE_transport_inv {g : Matrix (S n) (S n) K} (h : IsUnit g.det) (x : S n) :
    ∑ m, invT g x m • (g * colE K (J := J) m) = colE K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colE, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [colE, Matrix.of_apply, ← mul_inv_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- `∑ m, g x m • (e_mᵀ * (g⁻ᵀ)ᵀ) = e_xᵀ`. -/
theorem rowE_transport {g : Matrix (S n) (S n) K} (h : IsUnit g.det) (x : S n) :
    ∑ m, g x m • (rowE K (I := I) m * (invT g)ᵀ) = rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [invT, Matrix.transpose_transpose, rowE_mul, Matrix.of_apply]
  rw [mul_inv_entry h, rowE, Matrix.of_apply]
  by_cases hx : j = x
  · simp [hx]
  · simp [hx, Ne.symm hx]

/-- `∑ m, g⁻ᵀ x m • (e_mᵀ * gᵀ) = e_xᵀ`. -/
theorem rowE_transport_inv {g : Matrix (S n) (S n) K} (h : IsUnit g.det) (x : S n) :
    ∑ m, invT g x m • (rowE K (I := I) m * gᵀ) = rowE K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [rowE_mul, Matrix.of_apply, invT, Matrix.transpose_apply]
  rw [rowE, Matrix.of_apply, ← mul_inv_entry h j x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- `∑ m, g x m • (g * J_m) = J_x` when `g J gᵀ = J`. -/
theorem colJ_transport {g : Matrix (S n) (S n) K} (h : g * stdJ K n * gᵀ = stdJ K n) (x : S n) :
    ∑ m, g x m • (g * colJ K (J := J) m) = colJ K x := by
  ext i u
  rw [sum_smul_entry]
  simp only [mul_colJ_entry]
  simp only [colJ, Matrix.of_apply]
  rw [← cov_entry h i x]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- `∑ m, g x m • (J_mᵀ * gᵀ) = J_xᵀ` when `g J gᵀ = J`. -/
theorem rowJ_transport {g : Matrix (S n) (S n) K} (h : g * stdJ K n * gᵀ = stdJ K n) (x : S n) :
    ∑ m, g x m • (rowJ K (I := I) m * gᵀ) = rowJ K x := by
  ext u j
  rw [sum_smul_entry]
  simp only [rowJ_mul_entry]
  simp only [rowJ, Matrix.of_apply]
  rw [← cov_entry h j x]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm (g x m)]
  congr 1
  exact Finset.sum_congr rfl fun j' _ => mul_comm _ _

theorem sum_one_smul {I : Type} [Fintype I] [DecidableEq I] {I' J' : Type} (a : I)
    (C : Matrix I' J' K) : ∑ j, (1 : Matrix I I K) a j • C = C := by
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]

end Vectors

/-! ### The blocks of `H` as matrices -/

section Blocks

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)
  (A : S n × S n × S n → K) (k : Fin th)

local notation "Hg" => Hgadget (K := K) n strH e0 e1 e2

theorem Hmat_dat_dat :
    Hg A k Blk.dat Blk.dat = if h : strH k = 0 then slice A (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_dat_dat]; by_cases h : strH k = 0 <;> simp [h, slice]
theorem Hmat_dat_cop : Hg A k Blk.dat Blk.cop = 0 := rfl
theorem Hmat_dat_mid :
    Hg A k Blk.dat Blk.mid = if strH k = 3 then (1 : Matrix (S n) (S n) K) else 0 := by
  ext i j; rw [Hgadget_dat_mid]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all
theorem Hmat_dat_anch :
    Hg A k Blk.dat Blk.anch = if h : strH k = 1 then colJ K (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_dat_anch]; by_cases h : strH k = 1 <;> simp [h, colJ]
theorem Hmat_cop_dat :
    Hg A k Blk.cop Blk.dat = if strH k = 3 then stdJ K n else 0 := by
  ext i j; rw [Hgadget_cop_dat]; by_cases h : strH k = 3 <;> simp [h]
theorem Hmat_cop_cop : Hg A k Blk.cop Blk.cop = 0 := rfl
theorem Hmat_cop_mid : Hg A k Blk.cop Blk.mid = 0 := rfl
theorem Hmat_cop_anch :
    Hg A k Blk.cop Blk.anch = if h : strH k = 2 then colE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_cop_anch]; by_cases h : strH k = 2 <;> simp [h, colE]
theorem Hmat_mid_dat : Hg A k Blk.mid Blk.dat = 0 := rfl
theorem Hmat_mid_cop :
    Hg A k Blk.mid Blk.cop = if strH k = 3 then (1 : Matrix (S n) (S n) K) else 0 := by
  ext i j; rw [Hgadget_mid_cop]; by_cases h : strH k = 3 <;> simp only [h, if_true, if_false,
    Matrix.one_apply, Matrix.zero_apply] <;> split_ifs <;> simp_all
theorem Hmat_mid_mid : Hg A k Blk.mid Blk.mid = 0 := rfl
theorem Hmat_mid_anch :
    Hg A k Blk.mid Blk.anch = if h : strH k = 0 then colE K (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_mid_anch]; by_cases h : strH k = 0 <;> simp [h, colE]
theorem Hmat_anch_dat :
    Hg A k Blk.anch Blk.dat = if h : strH k = 2 then rowE K (e2.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_anch_dat]; by_cases h : strH k = 2 <;> simp [h, rowE]
theorem Hmat_anch_cop :
    Hg A k Blk.anch Blk.cop = if h : strH k = 0 then rowJ K (e0.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_anch_cop]; by_cases h : strH k = 0 <;> simp [h, rowJ]
theorem Hmat_anch_mid :
    Hg A k Blk.anch Blk.mid = if h : strH k = 1 then rowE K (e1.symm ⟨k, h⟩) else 0 := by
  ext i j; rw [Hgadget_anch_mid]; by_cases h : strH k = 1 <;> simp [h, rowE]
theorem Hmat_anch_anch :
    Hg A k Blk.anch Blk.anch = if strH k = 3 then (1 : Matrix Unit Unit K) else 0 := by
  ext i j; rw [Hgadget_anch_anch]; by_cases h : strH k = 3 <;> simp [h, Matrix.one_apply]

end Blocks

/-! ### One block, one stratum -/

section Steps

variable {n th : ℕ} (strH : Fin th → Fin 4)

/-- A stratum-`g₀` block, transported by `G` along `e`. -/
theorem block_step {I I' J J' : Type} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
    (Rst : ∀ g : Fin 4, Matrix (Fib strH g) (Fib strH g) K)
    (P : Matrix I I' K) (Q : Matrix J J' K) (N : Fin th → Matrix I' J' K) (g₀ : Fin 4)
    (hN : ∀ k', strH k' ≠ g₀ → N k' = 0) (e : S n ≃ Fib strH g₀) (G : Matrix (S n) (S n) K)
    (hG : Rst g₀ = Matrix.reindex e e G) (Nx : S n → Matrix I' J' K)
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

/-- A stratum-3 block with identity transport. -/
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

/-! ### The forward direction -/

section Main

variable {n th : ℕ} (strH : Fin th → Fin 4)
  (e0 : S n ≃ Fib strH 0) (e1 : S n ≃ Fib strH 1) (e2 : S n ≃ Fib strH 2)

/-- **Forward direction (parametrised packing).** -/
theorem blockEquiv_of_sp3ti (g₁ g₂ g₃ : Matrix (S n) (S n) K)
    (h₁ : IsSymplecticMat K g₁) (h₂ : IsSymplecticMat K g₂) (h₃ : IsSymplecticMat K g₃)
    (A B : S n × S n × S n → K) (hAB : act3D K g₁ g₂ g₃ A = B) :
    BlockEquiv strH (Hgadget (K := K) n strH e0 e1 e2 A) (Hgadget (K := K) n strH e0 e1 e2 B) := by
  have hu₁ := isUnit_det_of_symplectic h₁
  have hu₂ := isUnit_det_of_symplectic h₂
  have hu₃ := isUnit_det_of_symplectic h₃
  have hc₁ := (isSymplecticMat_iff_covariant g₁).mp h₁
  have hc₂ := (isSymplecticMat_iff_covariant g₂).mp h₂
  have hc₃ := (isSymplecticMat_iff_covariant g₃).mp h₃
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
  -- dat, dat : data block, stratum 0, transport g₃
  · simp only [Hmat_dat_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₁ g₂
      (fun k' => if h : strH k' = 0 then slice A (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => slice A m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      exact act3D_slice g₁ g₂ g₃ A _
    · rw [dif_neg h, dif_neg h]
  -- dat, cop : zero
  · simp [Hmat_dat_cop]
  -- dat, mid : identity link, stratum 3
  · simp only [Hmat_dat_mid, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ g₁ (invT g₁)
      (fun k' => if strH k' = 3 then (1 : Matrix (S n) (S n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, mul_invT_transpose hu₁]
    · rw [if_neg h, if_neg h]
  -- dat, anch : form link, stratum 1, transport g₁
  · simp only [Hmat_dat_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₁ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 1 then colJ K (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => colJ K m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colJ_transport hc₁ _).symm
    · rw [dif_neg h, dif_neg h]
  -- cop, dat : form block, stratum 3
  · simp only [Hmat_cop_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ g₂ g₂ (fun k' => if strH k' = 3 then stdJ K n else 0) (stdJ K n)
      (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]
      exact hc₂.symm
    · rw [if_neg h, if_neg h]
  -- cop, cop : zero
  · simp [Hmat_cop_cop]
  -- cop, mid : zero
  · simp [Hmat_cop_mid]
  -- cop, anch : identity link, stratum 2, transport g₂⁻ᵀ
  · simp only [Hmat_cop_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ g₂ (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 2 then colE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (invT g₂) hR2 (fun m => colE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]
  -- mid, dat : zero
  · simp [Hmat_mid_dat]
  -- mid, cop : identity link, stratum 3
  · simp only [Hmat_mid_cop, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ (invT g₃) g₃
      (fun k' => if strH k' = 3 then (1 : Matrix (S n) (S n) K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h, Matrix.mul_one, invT_mul_transpose hu₃]
    · rw [if_neg h, if_neg h]
  -- mid, mid : zero
  · simp [Hmat_mid_mid]
  -- mid, anch : identity link, stratum 0, transport g₃
  · simp only [Hmat_mid_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (invT g₃) (1 : Matrix Unit Unit K)
      (fun k' => if h : strH k' = 0 then colE K (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => colE K m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.transpose_one, Matrix.mul_one]
      exact (colE_transport hu₃ _).symm
    · rw [dif_neg h, dif_neg h]
  -- anch, dat : identity link, stratum 2, transport g₂⁻ᵀ
  · simp only [Hmat_anch_dat, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) g₂
      (fun k' => if h : strH k' = 2 then rowE K (e2.symm ⟨k', h⟩) else 0) 2
      (fun k' hk' => dif_neg hk') e2 (invT g₂) hR2 (fun m => rowE K m)
      (fun m => by rw [dif_pos (e2 m).2]; simp) k]
    by_cases h : strH k = 2
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowE_transport_inv hu₂ _).symm
    · rw [dif_neg h, dif_neg h]
  -- anch, cop : form link, stratum 0, transport g₃
  · simp only [Hmat_anch_cop, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) g₃
      (fun k' => if h : strH k' = 0 then rowJ K (e0.symm ⟨k', h⟩) else 0) 0
      (fun k' hk' => dif_neg hk') e0 g₃ hR0 (fun m => rowJ K m)
      (fun m => by rw [dif_pos (e0 m).2]; simp) k]
    by_cases h : strH k = 0
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowJ_transport hc₃ _).symm
    · rw [dif_neg h, dif_neg h]
  -- anch, mid : identity link, stratum 1, transport g₁
  · simp only [Hmat_anch_mid, Pfwd, Qfwd]
    rw [Rfwd, block_step strH _ (1 : Matrix Unit Unit K) (invT g₁)
      (fun k' => if h : strH k' = 1 then rowE K (e1.symm ⟨k', h⟩) else 0) 1
      (fun k' hk' => dif_neg hk') e1 g₁ hR1 (fun m => rowE K m)
      (fun m => by rw [dif_pos (e1 m).2]; simp) k]
    by_cases h : strH k = 1
    · rw [dif_pos h, dif_pos h]
      simp only [Matrix.one_mul]
      exact (rowE_transport hu₁ _).symm
    · rw [dif_neg h, dif_neg h]
  -- anch, anch : the scalar anchor, stratum 3
  · simp only [Hmat_anch_anch, Pfwd, Qfwd]
    rw [Rfwd, block_step3 strH _ (1 : Matrix Unit Unit K) (1 : Matrix Unit Unit K)
      (fun k' => if strH k' = 3 then (1 : Matrix Unit Unit K) else 0) 1 (fun _ => rfl) hR3 k]
    by_cases h : strH k = 3
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]

/-- **Forward direction for the concrete packing.** -/
theorem sp3ti_rel_imp_blockEquiv_H (n : ℕ) (A B : S n × S n × S n → K)
    (h : (Sp3TI K).Rel n A B) : BlockEquiv (strHn n) (H n A) (H n B) := by
  obtain ⟨P, Q, R, hP, hQ, hR, hAB⟩ := h
  exact blockEquiv_of_sp3ti (strHn n) (e0n n) (e1n n) (e2n n) P Q R hP hQ hR A B hAB

end Main

end Mathproof.Meta.FGSEncodingForwardMain20260902

end Part_U30


section Part_U31


/-!
# The Levi principle: `TI ≤_p TI_G` for every group family containing the hyperbolic lifts

## Purpose

Snowball from `TI = TI_Sp`. The padding half `GL3TI ≤_p Sp3TI` used symplecticity in ONE place
only — to know that the hyperbolic lift `diag(P, P⁻ᵀ)` of an invertible `P` lies in the group —
and its reverse half (mode-support reflection) used nothing but invertibility. So the same
projection works for ANY family of matrix predicates `Grp n` on the doubled index `S n` with

* `Grp n g → IsUnit g.det`, and
* `IsUnit P.det → Grp n (hypLift P)`.

This module states that principle (`gl3ti_iff_tig_pad`, `leviProjection`) and instantiates it for
the isometry groups of the hyperbolic `ε`-forms `Φ_ε = [[0, I], [ε I, 0]]` for every unit `ε`:
`ε = −1` is `Sp` (recovering `padProjection`), `ε = 1` is the split orthogonal group `O(H)` of the
hyperbolic symmetric form, over every field (in characteristic 2 the two coincide).

The reverse half here is proved in coordinates through the cubic zero extension: the padding
`Fin n ↪ Fin n ⊕ Fin n` is, after `finSumFinEquiv`, the corner inclusion `Fin n ↪ Fin (n+n)`,
so `cubeExt_equiv_iff` applies (`reindex3_padArr`, `gl3ti_of_padded`).

## DAG chain walked

`finSumFinEquiv(_symm_apply_castAdd/natAdd)`, `Fin.addCases`, `Matrix.fromBlocks_multiply`,
`Matrix.fromBlocks_transpose`, `Matrix.nonsing_inv_mul`, `Matrix.det_mul`, `Matrix.det_transpose`;
tree: `PaddingProjection.padArr/padSrc`, `CubicZeroExtension.cubeExt_equiv_iff`,
`FGSPackaging.exists_act_reindex3 / exists_det_iff_isUnit / gl3ti_rel_iff`.
-/

namespace Mathproof.Meta.TIGroupLevi20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.PaddingProjection20260902
open Mathproof.Meta.FGSFlatArrays20260902 (act)
open Mathproof.Meta.FGSFlatReindex20260902 (reindex3)
open Mathproof.Meta.FGSPackaging20260902
open Mathproof.Meta.CubicZeroExtension20260902 (cubeExt cubeExt_equiv_iff)

universe u

variable {K : Type u} [Field K]

/-! ### Tensor isomorphism restricted to a group family -/

/-- Cubic arrays on the doubled index, under three independent matrices satisfying `Grp n`. -/
def TIG (Grp : ∀ n, Matrix (S n) (S n) K → Prop) : CoordProblem K where
  Idx := fun n => S n × S n × S n
  fin := fun _ => inferInstance
  Rel := fun n A B => ∃ g₁ g₂ g₃ : Matrix (S n) (S n) K,
    Grp n g₁ ∧ Grp n g₂ ∧ Grp n g₃ ∧ act3D K g₁ g₂ g₃ A = B

/-- `Sp3TI` is the instance `Grp := IsSymplecticMat`. -/
theorem sp3ti_eq_TIG : Sp3TI K = TIG (fun n g => IsSymplecticMat K g) := rfl

/-! ### The hyperbolic lift -/

/-- `diag(P, P⁻ᵀ)`. -/
noncomputable def hypLift {n : ℕ} (P : Matrix (Fin n) (Fin n) K) : Matrix (S n) (S n) K :=
  Matrix.fromBlocks P 0 0 P⁻¹ᵀ

theorem padArr_inr₁ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (a : Fin n) (x y : S n) :
    padArr A (Sum.inr a, x, y) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

theorem padArr_inr₂ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (x : S n) (a : Fin n) (y : S n) :
    padArr A (x, Sum.inr a, y) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

theorem padArr_inr₃ {n : ℕ} (A : Fin n × Fin n × Fin n → K) (x y : S n) (a : Fin n) :
    padArr A (x, y, Sum.inr a) = 0 :=
  padArr_eq_zero A _ (by rintro i j k h; simp at h)

/-- The lifts act on the padding as the originals act on the array. -/
theorem act3D_hypLift_padArr {n : ℕ} (P Q R : Matrix (Fin n) (Fin n) K)
    (A : Fin n × Fin n × Fin n → K) :
    act3D K (hypLift P) (hypLift Q) (hypLift R) (padArr A) = padArr (act3 K P Q R A) := by
  funext y
  obtain ⟨i, j, k⟩ := y
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp [act3D, act3, hypLift, Fintype.sum_sum_type, padArr_inr₁, padArr_inr₂, padArr_inr₃]

/-! ### The hyperbolic `ε`-forms and their isometries -/

/-- `Φ_ε = [[0, I], [ε I, 0]]`. -/
def hypForm (n : ℕ) (ε : K) : Matrix (S n) (S n) K := Matrix.fromBlocks 0 1 (ε • 1) 0

/-- Isometries of `Φ_ε`. -/
def IsIsometry (n : ℕ) (ε : K) (g : Matrix (S n) (S n) K) : Prop :=
  gᵀ * hypForm n ε * g = hypForm n ε

theorem stdJ_eq_hypForm (n : ℕ) : stdJ K n = hypForm n (-1) := by
  simp [stdJ, hypForm]

theorem isSymplecticMat_iff_isIsometry {n : ℕ} (g : Matrix (S n) (S n) K) :
    IsSymplecticMat K g ↔ IsIsometry n (-1) g := by
  simp only [IsSymplecticMat, IsIsometry, stdJ_eq_hypForm]

/-- `Φ_ε * [[0, ε⁻¹ I], [I, 0]] = 1`, so `Φ_ε` is invertible when `ε` is a unit. -/
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

/-- An isometry of an invertible form has a unit determinant. -/
theorem isUnit_det_of_isometry {n : ℕ} {Φ g : Matrix (S n) (S n) K} (hΦ : IsUnit Φ.det)
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

/-- **The hyperbolic lift is an isometry of every `Φ_ε`.** -/
theorem hypLift_isIsometry {n : ℕ} (ε : K) (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) :
    IsIsometry n ε (hypLift P) := by
  unfold IsIsometry hypForm hypLift
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_transpose]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul P hP, Matrix.transpose_one]

/-! ### The reverse half in coordinates, through the cubic zero extension -/

/-- Reindexing the padding along `finSumFinEquiv` is the corner zero-extension to `Fin (n+n)`. -/
theorem reindex3_padArr {n : ℕ} (A : Fin n × Fin n × Fin n → K) :
    reindex3 (finSumFinEquiv (m := n) (n := n)) finSumFinEquiv finSumFinEquiv (padArr A) =
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

theorem act3D_eq_act {n : ℕ} (g₁ g₂ g₃ : Matrix (S n) (S n) K) (A : S n × S n × S n → K) :
    act3D K g₁ g₂ g₃ A = act g₁ g₂ g₃ A := by
  funext ⟨i, j, k⟩
  rfl

/-- **Reflection**: any invertible triple carrying `padArr A` to `padArr B` yields `GL3TI A B`. -/
theorem gl3ti_of_padded {n : ℕ} (g₁ g₂ g₃ : Matrix (S n) (S n) K) (h₁ : IsUnit g₁.det)
    (h₂ : IsUnit g₂.det) (h₃ : IsUnit g₃.det) (A B : Fin n × Fin n × Fin n → K)
    (h : act3D K g₁ g₂ g₃ (padArr A) = padArr B) : (GL3TI K).Rel n A B := by
  have hflat : ∃ P₁ P₂ P₃ : Matrix (S n) (S n) K,
      IsUnit P₁.det ∧ IsUnit P₂.det ∧ IsUnit P₃.det ∧ act P₁ P₂ P₃ (padArr A) = padArr B :=
    ⟨g₁, g₂, g₃, h₁, h₂, h₃, by rw [← act3D_eq_act]; exact h⟩
  rw [exists_act_reindex3 (finSumFinEquiv (m := n) (n := n)) finSumFinEquiv finSumFinEquiv,
    reindex3_padArr, reindex3_padArr, exists_det_iff_isUnit] at hflat
  have hle : n ≤ n + n := Nat.le_add_right n n
  exact (gl3ti_rel_iff A B).mpr ((cubeExt_equiv_iff (K := K) hle hle hle A B).mpr hflat)

/-! ### The Levi principle -/

/-- **`GL3TI` on `A, B` is `TI_G` on their paddings**, for any `Grp` closed under hyperbolic lifts
and contained in the invertible matrices. -/
theorem gl3ti_iff_tig_pad (Grp : ∀ n, Matrix (S n) (S n) K → Prop)
    (hunit : ∀ n (g : Matrix (S n) (S n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det → Grp n (hypLift P))
    {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (TIG Grp).Rel n (padArr A) (padArr B) := by
  constructor
  · intro hAB
    obtain ⟨P, Q, R, hP, hQ, hR, hact⟩ := (gl3ti_rel_iff A B).mp hAB
    refine ⟨hypLift P, hypLift Q, hypLift R, hlift n P ((Matrix.isUnit_iff_isUnit_det P).mp hP),
      hlift n Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ), hlift n R ((Matrix.isUnit_iff_isUnit_det R).mp hR), ?_⟩
    rw [act3D_hypLift_padArr, act3_eq_act, hact]
  · rintro ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
    exact gl3ti_of_padded g₁ g₂ g₃ (hunit n g₁ h₁) (hunit n g₂ h₂) (hunit n g₃ h₃) A B h

/-- **The Levi projection** `GL3TI ⟶ TI_G`. -/
def leviProjection (Grp : ∀ n, Matrix (S n) (S n) K → Prop)
    (hunit : ∀ n (g : Matrix (S n) (S n) K), Grp n g → IsUnit g.det)
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

/-! ### Instances: every hyperbolic `ε`-form -/

/-- Tensor isomorphism under the isometry group of `Φ_ε`. -/
def TIIso (ε : K) : CoordProblem K := TIG (fun n g => IsIsometry n ε g)

/-- **`TI ≤_p TI_{O(Φ_ε)}` for every unit `ε`.** -/
def leviProjectionIso (ε : K) (hε : ε ≠ 0) : Projection (GL3TI K) (TIIso ε) :=
  leviProjection (fun n g => IsIsometry n ε g)
    (fun n g h => isUnit_det_of_isometry (isUnit_det_hypForm n ε hε) h)
    (fun n P hP => hypLift_isIsometry ε P hP)

theorem ti_reduces_tiIso (ε : K) (hε : ε ≠ 0) :
    (projectionSystem K).reduces (GL3TI K) (TIIso ε) :=
  ⟨leviProjectionIso ε hε⟩

theorem ti_class_le_tiIso_class (ε : K) (hε : ε ≠ 0) :
    (projectionSystem K).problemClass (GL3TI K) ⊆ (projectionSystem K).problemClass (TIIso ε) :=
  (projectionSystem K).problemClass_mono (ti_reduces_tiIso ε hε)

/-- The symplectic case is `ε = −1` — the old `padProjection`, re-derived. -/
def leviProjectionSp : Projection (GL3TI K) (Sp3TI K) :=
  leviProjection (fun n g => IsSymplecticMat K g)
    (fun _ _ h => Mathproof.Meta.FGSEncodingForwardMain20260902.isUnit_det_of_symplectic h)
    (fun n P hP => (isSymplecticMat_iff_isIsometry _).mpr (hypLift_isIsometry (-1) P hP))

/-- The split orthogonal case `ε = 1`: `TI ≤_p TI_{O(H)}` over every field. -/
def leviProjectionOH : Projection (GL3TI K) (TIIso (1 : K)) :=
  leviProjectionIso 1 one_ne_zero

end Mathproof.Meta.TIGroupLevi20260902

#print axioms Mathproof.Meta.TIGroupLevi20260902.gl3ti_iff_tig_pad
#print axioms Mathproof.Meta.TIGroupLevi20260902.leviProjectionIso
#print axioms Mathproof.Meta.TIGroupLevi20260902.leviProjectionOH
#print axioms Mathproof.Meta.TIGroupLevi20260902.ti_class_le_tiIso_class

end Part_U31


section Part_U32


/-!
# The Levi principle with arbitrary lower block, and unitary groups

## Purpose

`TIGroupLevi20260902` used the lift `diag(P, P⁻ᵀ)`, but its forward computation
`act3D_hypLift_padArr` only ever met the top-left block `P` (the padding lives on the `inl`
coordinates), so ANY block-diagonal lift `blockLift P X = diag(P, X)` works. Hence

> `TI ≤_p TI_G` for every family `Grp ⊆ GL(S n)` such that every invertible `P` has SOME `X` with
> `diag(P, X) ∈ Grp n`.

Instance: the unitary groups of the hyperbolic `ε`-forms with respect to a field involution
`σ : K →+* K`, `σ ∘ σ = id` — the lift is `diag(P, σ(P⁻ᵀ))`. This covers CGQTZ's third family
(`U`) forward over any field with an involution (`ℂ` with conjugation, `F_{q²}` with Frobenius),
with `σ = id` recovering the isometry groups.

## DAG chain walked

`Matrix.map_mul`, `Matrix.map_one`, `Matrix.map_zero`, `Matrix.transpose_map`, `Matrix.map_map`,
`Matrix.fromBlocks_map`, `RingHom.map_det`, `RingHom.mapMatrix_apply`; tree:
`TIGroupLevi20260902.gl3ti_of_padded / padArr_inr₁₂₃ / hypForm / isUnit_det_hypForm`.
-/

namespace Mathproof.Meta.TIGroupLeviGen20260902

open Matrix
open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.PaddingProjection20260902
open Mathproof.Meta.FGSPackaging20260902 (gl3ti_rel_iff act3_eq_act)
open Mathproof.Meta.TIGroupLevi20260902

universe u

variable {K : Type u} [Field K]

/-! ### Block lifts -/

/-- `diag(P, X)`. -/
def blockLift {n : ℕ} (P X : Matrix (Fin n) (Fin n) K) : Matrix (S n) (S n) K :=
  Matrix.fromBlocks P 0 0 X

theorem act3D_blockLift_padArr {n : ℕ} (P Q R X Y Z : Matrix (Fin n) (Fin n) K)
    (A : Fin n × Fin n × Fin n → K) :
    act3D K (blockLift P X) (blockLift Q Y) (blockLift R Z) (padArr A) =
      padArr (act3 K P Q R A) := by
  funext y
  obtain ⟨i, j, k⟩ := y
  rcases i with i | i <;> rcases j with j | j <;> rcases k with k | k <;>
    simp [act3D, act3, blockLift, Fintype.sum_sum_type, padArr_inr₁, padArr_inr₂, padArr_inr₃]

/-- **The Levi principle, general form.** -/
theorem gl3ti_iff_tig_pad_gen (Grp : ∀ n, Matrix (S n) (S n) K → Prop)
    (hunit : ∀ n (g : Matrix (S n) (S n) K), Grp n g → IsUnit g.det)
    (hlift : ∀ n (P : Matrix (Fin n) (Fin n) K), IsUnit P.det →
      ∃ X : Matrix (Fin n) (Fin n) K, Grp n (blockLift P X))
    {n : ℕ} (A B : Fin n × Fin n × Fin n → K) :
    (GL3TI K).Rel n A B ↔ (TIG Grp).Rel n (padArr A) (padArr B) := by
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

/-- **The Levi projection, general form.** -/
def leviProjectionGen (Grp : ∀ n, Matrix (S n) (S n) K → Prop)
    (hunit : ∀ n (g : Matrix (S n) (S n) K), Grp n g → IsUnit g.det)
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

/-! ### Unitary groups for a field involution -/

section Unitary

variable (σ : K →+* K)

/-- `g* Φ_ε g = Φ_ε` with `g* := (σ g)ᵀ`. -/
def IsUnitary (n : ℕ) (ε : K) (g : Matrix (S n) (S n) K) : Prop :=
  (g.map σ)ᵀ * hypForm n ε * g = hypForm n ε

/-- `diag(P, σ(P⁻ᵀ))`. -/
noncomputable def uLift {n : ℕ} (P : Matrix (Fin n) (Fin n) K) : Matrix (S n) (S n) K :=
  blockLift P ((P⁻¹ᵀ).map σ)

theorem det_map_eq {n : ℕ} (g : Matrix (S n) (S n) K) : (g.map σ).det = σ g.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

/-- A unitary matrix has a unit determinant. -/
theorem isUnit_det_of_unitary {n : ℕ} (ε : K) (hε : ε ≠ 0) {g : Matrix (S n) (S n) K}
    (h : IsUnitary σ n ε g) : IsUnit g.det := by
  have hΦ : (hypForm n ε).det ≠ 0 := (isUnit_det_hypForm n ε hε).ne_zero
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_eq] at hd
  have h2 : (σ g.det * g.det) * (hypForm n ε).det = 1 * (hypForm n ε).det := by
    rw [one_mul]
    calc (σ g.det * g.det) * (hypForm n ε).det = σ g.det * (hypForm n ε).det * g.det := by ring
      _ = (hypForm n ε).det := hd
  have h3 : σ g.det * g.det = 1 := mul_right_cancel₀ hΦ h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h3
  exact zero_ne_one h3

/-- **The unitary lift is unitary** when `σ` is an involution. -/
theorem uLift_isUnitary (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (ε : K) (P : Matrix (Fin n) (Fin n) K)
    (hP : IsUnit P.det) : IsUnitary σ n ε (uLift σ P) := by
  have hY : ((P⁻¹ᵀ).map σ).map σ = P⁻¹ᵀ := by
    rw [Matrix.map_map]
    have : (⇑σ ∘ ⇑σ) = id := funext hσ
    rw [this, Matrix.map_id]
  have h1 : (P.map σ)ᵀ * (P⁻¹ᵀ).map σ = 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul P hP, Matrix.transpose_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  unfold IsUnitary uLift blockLift hypForm
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ), hY, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_transpose]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  rw [h1, Matrix.nonsing_inv_mul P hP]

/-- Tensor isomorphism under the unitary group of `Φ_ε` for the involution `σ`. -/
def TIUnitary (ε : K) : CoordProblem K := TIG (fun n g => IsUnitary σ n ε g)

/-- **`TI ≤_p TI_{U(Φ_ε, σ)}`** for every involution `σ` and unit `ε`. -/
noncomputable def leviProjectionUnitary (hσ : ∀ x, σ (σ x) = x) (ε : K) (hε : ε ≠ 0) :
    Projection (GL3TI K) (TIUnitary σ ε) :=
  leviProjectionGen (fun n g => IsUnitary σ n ε g)
    (fun _ _ h => isUnit_det_of_unitary σ ε hε h)
    (fun _ P hP => ⟨(P⁻¹ᵀ).map σ, uLift_isUnitary σ hσ ε P hP⟩)

theorem ti_class_le_tiUnitary_class (hσ : ∀ x, σ (σ x) = x) (ε : K) (hε : ε ≠ 0) :
    (projectionSystem K).problemClass (GL3TI K) ⊆
      (projectionSystem K).problemClass (TIUnitary σ ε) :=
  (projectionSystem K).problemClass_mono ⟨leviProjectionUnitary σ hσ ε hε⟩

/-- With `σ = id` the unitary group is the isometry group. -/
theorem isUnitary_id_iff {n : ℕ} (ε : K) (g : Matrix (S n) (S n) K) :
    IsUnitary (RingHom.id K) n ε g ↔ IsIsometry n ε g := by
  simp [IsUnitary, IsIsometry]

end Unitary

end Mathproof.Meta.TIGroupLeviGen20260902

#print axioms Mathproof.Meta.TIGroupLeviGen20260902.leviProjectionGen
#print axioms Mathproof.Meta.TIGroupLeviGen20260902.leviProjectionUnitary
#print axioms Mathproof.Meta.TIGroupLeviGen20260902.ti_class_le_tiUnitary_class

end Part_U32


section Part_U33


/-!
# Counting symmetric matrices: `|Sym_n(K)| = |K|^{n(n+1)/2}`

Symmetric `n × n` matrices are exactly functions on unordered pairs `Sym2 (Fin n)` (`Sym2.lift`),
and `|Sym2 (Fin n)| = C(n+1, 2) = n(n+1)/2` (`Sym2.card`).  This is the finite-field factor
`q^{3n(n+1)/2}` of the transporter/stabilizer count in `TISpTransporterFibers`.
-/

namespace Mathproof.LibraryBridges.Claude.SymMatCard


variable {n : ℕ} {K : Type*}

/-- Symmetric matrices are functions on unordered pairs. -/
def symmEquivSym2 : {U : Matrix (Fin n) (Fin n) K // U.IsSymm} ≃ (Sym2 (Fin n) → K) :=
  (Equiv.subtypeEquivRight (fun U => by
      rw [Matrix.IsSymm.ext_iff]
      exact ⟨fun h i j => h j i, fun h i j => h j i⟩)).trans Sym2.lift

theorem natCard_symm [Finite K] :
    Nat.card {U : Matrix (Fin n) (Fin n) K // U.IsSymm} = Nat.card K ^ ((n + 1).choose 2) := by
  rw [Nat.card_congr symmEquivSym2, Nat.card_fun, Nat.card_eq_fintype_card (α := Sym2 (Fin n)),
    Sym2.card, Fintype.card_fin]

theorem natCard_symm_eq_div [Finite K] :
    Nat.card {U : Matrix (Fin n) (Fin n) K // U.IsSymm} = Nat.card K ^ (n * (n + 1) / 2) := by
  rw [natCard_symm, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

end Mathproof.LibraryBridges.Claude.SymMatCard

#print axioms Mathproof.LibraryBridges.Claude.SymMatCard.natCard_symm
#print axioms Mathproof.LibraryBridges.Claude.SymMatCard.natCard_symm_eq_div

end Part_U33


section Part_U34


/-!
# TI = TI_Sp fallout: symplectic transporters between padded concise tensors

Let `ι = padArr` be the hyperbolic zero-padding `K^n ⊗³ → (K^n ⊕ K^n)^{⊗3}` of the checked
projection `TI ≤ TI_Sp`, `G = GL_n(K)^3`, `H = Sp_{2n}(K)^3`.  For **concise** `A` (each mode
flattening has full rank `n`), this module proves the transporter classification announced in
`TI_FALLOUT_FORMALIZATION_2026-09-04.md` ("Concise transporter fibers", listed there as missing
Lean work):

    Trans_H(ι A, ι B)  ≃  Sym_n(K)³ × Trans_G(A, B).

Ingredients, all proved here:

* `sympl_factor` — a symplectic matrix whose lower-left block vanishes factors uniquely as
  `[[1,U],[0,1]] · diag(a, a⁻ᵀ)` with `U` symmetric and `a` invertible (`unip U * hypLift a`);
* `act3D_padArr_apply` / `act3D_padArr_congr` — the action on a padding only reads the left
  column blocks `M x (inl i)`, so the unipotent factor acts trivially and the diagonal factor acts
  as the original `GL` action (`act3D_hypLift_padArr`);
* `toBlocks₂₁_eq_zero₁/₂/₃` — conciseness of `A` forces the lower-left block of every mode
  matrix of a transporter `ι A → ι B` to vanish (the primal support `K^n` is preserved);
* `transporterEquiv`, `natCard_spTrans` — the fiber equivalence and
  `|Trans_H| = |Sym_n(K)|³ · |Trans_G|`; with `A = B` this is the stabilizer statement
  `Stab_H(ι A) ≃ Sym_n(K)³ × Stab_G(A)` (as sets).

Not claimed: anything about `TI_SL = TI` or complexity separations; the relation-level statement
`TI(A,B) ↔ TI_Sp(ι A, ι B)` was already checked in `TIGroupLevi20260902.gl3ti_iff_tig_pad`.
-/

open scoped Matrix

open Matrix

namespace Mathproof.LibraryBridges.Claude.TISpTransporterFibers

open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.PaddingProjection20260902
open Mathproof.Meta.TIGroupLevi20260902

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ## The action on a padding reads only the left column blocks -/

theorem act3D_padArr_apply (P Q R : Matrix (S n) (S n) K) (A : Fin n × Fin n × Fin n → K)
    (x y z : S n) :
    act3D K P Q R (padArr A) (x, y, z) =
      ∑ i, ∑ j, ∑ k, P x (Sum.inl i) * Q y (Sum.inl j) * R z (Sum.inl k) * A (i, j, k) := by
  simp [act3D, Fintype.sum_sum_type, padArr_inr₁, padArr_inr₂, padArr_inr₃]

theorem act3D_padArr_congr {P P' Q Q' R R' : Matrix (S n) (S n) K}
    (A : Fin n × Fin n × Fin n → K)
    (hP : ∀ x i, P x (Sum.inl i) = P' x (Sum.inl i))
    (hQ : ∀ y j, Q y (Sum.inl j) = Q' y (Sum.inl j))
    (hR : ∀ z k, R z (Sum.inl k) = R' z (Sum.inl k)) :
    act3D K P Q R (padArr A) = act3D K P' Q' R' (padArr A) := by
  funext w
  obtain ⟨x, y, z⟩ := w
  rw [act3D_padArr_apply, act3D_padArr_apply]
  simp only [hP, hQ, hR]

theorem padArr_injective {A B : Fin n × Fin n × Fin n → K} (h : padArr A = padArr B) : A = B := by
  funext w
  obtain ⟨i, j, k⟩ := w
  exact congrFun h (Sum.inl i, Sum.inl j, Sum.inl k)

/-! ## Block matrices: unipotent part, hyperbolic lift, factorization -/

/-- The unipotent symplectic matrix `[[1, U], [0, 1]]`. -/
def unip (U : Matrix (Fin n) (Fin n) K) : Matrix (S n) (S n) K := fromBlocks 1 U 0 1

theorem unip_mul_hypLift (U a : Matrix (Fin n) (Fin n) K) :
    unip U * hypLift a = fromBlocks a (U * a⁻¹ᵀ) 0 a⁻¹ᵀ := by
  simp [unip, hypLift, fromBlocks_multiply]

theorem isSymplecticMat_mul {g h : Matrix (S n) (S n) K} (hg : IsSymplecticMat K g)
    (hh : IsSymplecticMat K h) : IsSymplecticMat K (g * h) := by
  unfold IsSymplecticMat at *
  calc (g * h)ᵀ * stdJ K n * (g * h) = hᵀ * (gᵀ * stdJ K n * g) * h := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = stdJ K n := by rw [hg, hh]

theorem isSymplecticMat_unip {U : Matrix (Fin n) (Fin n) K} (hU : U.IsSymm) :
    IsSymplecticMat K (unip U) := by
  unfold IsSymplecticMat unip stdJ
  rw [fromBlocks_transpose]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, transpose_zero,
    transpose_one]
  simp [hU.eq]

theorem isSymplecticMat_hypLift {a : Matrix (Fin n) (Fin n) K} (ha : IsUnit a.det) :
    IsSymplecticMat K (hypLift a) :=
  (isSymplecticMat_iff_isIsometry _).mpr (hypLift_isIsometry (-1) a ha)

/-- The block equations of a symplectic matrix with vanishing lower-left block. -/
theorem sympl_blocks {M : Matrix (S n) (S n) K} (hM : IsSymplecticMat K M)
    (hc : M.toBlocks₂₁ = 0) :
    M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 ∧
      M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = M.toBlocks₂₂ᵀ * M.toBlocks₁₂ := by
  have hMeq : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  unfold IsSymplecticMat stdJ at hM
  rw [hMeq, fromBlocks_transpose] at hM
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_zero, zero_add, add_zero,
    transpose_zero, fromBlocks_inj] at hM
  obtain ⟨-, h12, -, h22⟩ := hM
  refine ⟨by simpa using h12, ?_⟩
  have h22' : -(M.toBlocks₂₂ᵀ * M.toBlocks₁₂) + M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = 0 := by
    simpa using h22
  exact (neg_add_eq_zero.mp h22').symm

/-- **Unique factorization** `M = [[1,U],[0,1]] · diag(a, a⁻ᵀ)` with `a = M₁₁`, `U = M₁₂ M₁₁ᵀ`. -/
theorem sympl_factor {M : Matrix (S n) (S n) K} (hM : IsSymplecticMat K M)
    (hc : M.toBlocks₂₁ = 0) :
    IsUnit M.toBlocks₁₁.det ∧ (M.toBlocks₁₂ * M.toBlocks₁₁ᵀ).IsSymm ∧
      M = unip (M.toBlocks₁₂ * M.toBlocks₁₁ᵀ) * hypLift M.toBlocks₁₁ := by
  obtain ⟨h12, h22⟩ := sympl_blocks hM hc
  set a := M.toBlocks₁₁ with ha_def
  set b := M.toBlocks₁₂ with hb_def
  set d := M.toBlocks₂₂ with hd_def
  have hMeq : M = fromBlocks a b 0 d := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  have hdet : IsUnit a.det := by
    have := congrArg Matrix.det h12
    rw [det_mul, det_transpose, det_one] at this
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one this)
  have hd : d = a⁻¹ᵀ := by
    rw [transpose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv h12).symm
  have h22' : bᵀ * a⁻¹ᵀ = a⁻¹ * b := by
    rw [hd, transpose_transpose] at h22
    exact h22
  have hsymm : (b * aᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_transpose]
    calc a * bᵀ = a * bᵀ * (a⁻¹ᵀ * aᵀ) := by
          rw [← transpose_mul, Matrix.mul_nonsing_inv a hdet, transpose_one, Matrix.mul_one]
      _ = a * (bᵀ * a⁻¹ᵀ) * aᵀ := by simp only [Matrix.mul_assoc]
      _ = a * (a⁻¹ * b) * aᵀ := by rw [h22']
      _ = b * aᵀ := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a hdet, Matrix.one_mul]
  have hb : b = b * aᵀ * a⁻¹ᵀ := by
    rw [Matrix.mul_assoc, ← transpose_mul, Matrix.nonsing_inv_mul a hdet, transpose_one,
      Matrix.mul_one]
  refine ⟨hdet, hsymm, ?_⟩
  rw [unip_mul_hypLift, ← hb, hMeq, hd]

theorem toBlocks₁₁_unip_mul_hypLift (U a : Matrix (Fin n) (Fin n) K) :
    (unip U * hypLift a).toBlocks₁₁ = a := by
  rw [unip_mul_hypLift, toBlocks_fromBlocks₁₁]

theorem toBlocks₁₂_unip_mul_hypLift (U a : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det) :
    (unip U * hypLift a).toBlocks₁₂ * (unip U * hypLift a).toBlocks₁₁ᵀ = U := by
  rw [unip_mul_hypLift, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₁, Matrix.mul_assoc,
    ← transpose_mul, Matrix.mul_nonsing_inv a ha, transpose_one, Matrix.mul_one]

/-- **Composition law** of the factorized transporters: the stabilizer is a semidirect product
`Sym_n(K)³ ⋊ Stab_G(A)` with `a` acting on `U'` by congruence `U' ↦ a U' aᵀ`. -/
theorem unip_mul_hypLift_mul (U U' a a' : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det) :
    (unip U * hypLift a) * (unip U' * hypLift a') =
      unip (U + a * U' * aᵀ) * hypLift (a * a') := by
  rw [unip_mul_hypLift, unip_mul_hypLift, unip_mul_hypLift, fromBlocks_multiply]
  have hinv : (a * a')⁻¹ᵀ = a⁻¹ᵀ * a'⁻¹ᵀ := by
    rw [Matrix.mul_inv_rev, transpose_mul]
  have hcancel : aᵀ * a⁻¹ᵀ = 1 := by
    rw [← transpose_mul, Matrix.nonsing_inv_mul a ha, transpose_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hinv, Matrix.add_mul]
  have hcancel' : aᵀ * (a⁻¹ᵀ * a'⁻¹ᵀ) = a'⁻¹ᵀ := by
    rw [← Matrix.mul_assoc, hcancel, Matrix.one_mul]
  congr 1
  simp only [Matrix.mul_assoc, hcancel']
  exact add_comm _ _

theorem unip_mul_hypLift_apply_inl (U a : Matrix (Fin n) (Fin n) K) (x : S n) (i : Fin n) :
    (unip U * hypLift a) x (Sum.inl i) = hypLift a x (Sum.inl i) := by
  rw [unip_mul_hypLift]
  rcases x with x | x <;> simp [hypLift]

theorem apply_inl_eq_hypLift {M : Matrix (S n) (S n) K} (hc : M.toBlocks₂₁ = 0) (x : S n)
    (i : Fin n) : M x (Sum.inl i) = hypLift M.toBlocks₁₁ x (Sum.inl i) := by
  rcases x with x | x
  · simp [hypLift, toBlocks₁₁]
  · have h0 : M (Sum.inr x) (Sum.inl i) = 0 := by
      have := congrFun (congrFun hc x) i
      simpa [toBlocks₂₁] using this
    simp [hypLift, h0]

/-- With vanishing lower-left blocks, the doubled action on a padding is the padded `GL` action of
the upper-left blocks. -/
theorem act3D_padArr_of_toBlocks₂₁ {P Q R : Matrix (S n) (S n) K} (hP : P.toBlocks₂₁ = 0)
    (hQ : Q.toBlocks₂₁ = 0) (hR : R.toBlocks₂₁ = 0) (A : Fin n × Fin n × Fin n → K) :
    act3D K P Q R (padArr A) = padArr (act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A) := by
  rw [← act3D_hypLift_padArr]
  exact act3D_padArr_congr A (apply_inl_eq_hypLift hP) (apply_inl_eq_hypLift hQ)
    (apply_inl_eq_hypLift hR)

/-! ## Conciseness forces the lower-left blocks to vanish -/

/-- Mode-1 conciseness: the slices `A (i, ·, ·)` are linearly independent. -/
def Concise₁ (A : Fin n × Fin n × Fin n → K) : Prop :=
  ∀ c : Fin n → K, (∀ j k, ∑ i, c i * A (i, j, k) = 0) → c = 0

def Concise₂ (A : Fin n × Fin n × Fin n → K) : Prop :=
  ∀ c : Fin n → K, (∀ i k, ∑ j, c j * A (i, j, k) = 0) → c = 0

def Concise₃ (A : Fin n × Fin n × Fin n → K) : Prop :=
  ∀ c : Fin n → K, (∀ i j, ∑ k, c k * A (i, j, k) = 0) → c = 0

/-- Concise: all three mode flattenings have full rank `n`. -/
def Concise (A : Fin n × Fin n × Fin n → K) : Prop := Concise₁ A ∧ Concise₂ A ∧ Concise₃ A

theorem sum3_kji (f : Fin n → Fin n → Fin n → K) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k :=
  Finset.sum_comm.trans ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)

theorem sum3_kij (f : Fin n → Fin n → Fin n → K) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem sum3_jik (f : Fin n → Fin n → Fin n → K) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ i, ∑ k, f i j k :=
  Finset.sum_comm

theorem submatrix_inl_one :
    (1 : Matrix (S n) (S n) K).submatrix Sum.inl Sum.inl = (1 : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp [Matrix.one_apply]

/-- `X_l · D · Y_lᵀ = 0` with `X, Y` invertible forces `D = 0` (`X_l` = the `inl` columns). -/
theorem eq_zero_of_flank {X Y : Matrix (S n) (S n) K} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    {D : Matrix (Fin n) (Fin n) K}
    (h : X.submatrix id Sum.inl * D * (Y.submatrix id Sum.inl)ᵀ = 0) : D = 0 := by
  have hX1 : X⁻¹.submatrix Sum.inl id * X.submatrix id Sum.inl = 1 := by
    rw [← Matrix.submatrix_mul X⁻¹ X Sum.inl id Sum.inl Function.bijective_id,
      Matrix.nonsing_inv_mul X hX, submatrix_inl_one]
  have hY1 : (Y.submatrix id Sum.inl)ᵀ * (Y⁻¹.submatrix Sum.inl id)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.submatrix_mul Y⁻¹ Y Sum.inl id Sum.inl Function.bijective_id,
      Matrix.nonsing_inv_mul Y hY, submatrix_inl_one, transpose_one]
  calc D = (X⁻¹.submatrix Sum.inl id * X.submatrix id Sum.inl) * D *
        ((Y.submatrix id Sum.inl)ᵀ * (Y⁻¹.submatrix Sum.inl id)ᵀ) := by
        rw [hX1, hY1, Matrix.one_mul, Matrix.mul_one]
    _ = X⁻¹.submatrix Sum.inl id * (X.submatrix id Sum.inl * D * (Y.submatrix id Sum.inl)ᵀ) *
        (Y⁻¹.submatrix Sum.inl id)ᵀ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

theorem toBlocks₂₁_eq_zero₁ {A B : Fin n × Fin n × Fin n → K} (hA : Concise₁ A)
    {P Q R : Matrix (S n) (S n) K} (hQ : IsUnit Q.det) (hR : IsUnit R.det)
    (h : act3D K P Q R (padArr A) = padArr B) : P.toBlocks₂₁ = 0 := by
  ext r i
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply]
  have hzero : ∀ y z, ∑ i, ∑ j, ∑ k,
      P (Sum.inr r) (Sum.inl i) * Q y (Sum.inl j) * R z (Sum.inl k) * A (i, j, k) = 0 := by
    intro y z
    have := congrFun h (Sum.inr r, y, z)
    rw [act3D_padArr_apply, padArr_inr₁] at this
    exact this
  set D : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun j k => ∑ i, P (Sum.inr r) (Sum.inl i) * A (i, j, k) with hDdef
  have hmat : Q.submatrix id Sum.inl * D * (R.submatrix id Sum.inl)ᵀ = 0 := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.zero_apply, hDdef, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    have hz := hzero y z
    rw [sum3_kji] at hz
    refine Eq.trans ?_ hz
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i _ => ?_
    ring
  have hD : D = 0 := eq_zero_of_flank hQ hR hmat
  have hc : (fun i => P (Sum.inr r) (Sum.inl i)) = 0 := hA _ (fun j k => by
    have := congrFun (congrFun hD j) k
    simpa [hDdef] using this)
  exact congrFun hc i

theorem toBlocks₂₁_eq_zero₂ {A B : Fin n × Fin n × Fin n → K} (hA : Concise₂ A)
    {P Q R : Matrix (S n) (S n) K} (hP : IsUnit P.det) (hR : IsUnit R.det)
    (h : act3D K P Q R (padArr A) = padArr B) : Q.toBlocks₂₁ = 0 := by
  ext r j
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply]
  have hzero : ∀ x z, ∑ i, ∑ j, ∑ k,
      P x (Sum.inl i) * Q (Sum.inr r) (Sum.inl j) * R z (Sum.inl k) * A (i, j, k) = 0 := by
    intro x z
    have := congrFun h (x, Sum.inr r, z)
    rw [act3D_padArr_apply, padArr_inr₂] at this
    exact this
  set D : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i k => ∑ j, Q (Sum.inr r) (Sum.inl j) * A (i, j, k) with hDdef
  have hmat : P.submatrix id Sum.inl * D * (R.submatrix id Sum.inl)ᵀ = 0 := by
    ext x z
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.zero_apply, hDdef, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    have hz := hzero x z
    rw [sum3_kij] at hz
    refine Eq.trans ?_ hz
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  have hD : D = 0 := eq_zero_of_flank hP hR hmat
  have hc : (fun j => Q (Sum.inr r) (Sum.inl j)) = 0 := hA _ (fun i k => by
    have := congrFun (congrFun hD i) k
    simpa [hDdef] using this)
  exact congrFun hc j

theorem toBlocks₂₁_eq_zero₃ {A B : Fin n × Fin n × Fin n → K} (hA : Concise₃ A)
    {P Q R : Matrix (S n) (S n) K} (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : act3D K P Q R (padArr A) = padArr B) : R.toBlocks₂₁ = 0 := by
  ext r k
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply]
  have hzero : ∀ x y, ∑ i, ∑ j, ∑ k,
      P x (Sum.inl i) * Q y (Sum.inl j) * R (Sum.inr r) (Sum.inl k) * A (i, j, k) = 0 := by
    intro x y
    have := congrFun h (x, y, Sum.inr r)
    rw [act3D_padArr_apply, padArr_inr₃] at this
    exact this
  set D : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => ∑ k, R (Sum.inr r) (Sum.inl k) * A (i, j, k) with hDdef
  have hmat : P.submatrix id Sum.inl * D * (Q.submatrix id Sum.inl)ᵀ = 0 := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.zero_apply, hDdef, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    have hz := hzero x y
    rw [sum3_jik] at hz
    refine Eq.trans ?_ hz
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  have hD : D = 0 := eq_zero_of_flank hP hQ hmat
  have hc : (fun k => R (Sum.inr r) (Sum.inl k)) = 0 := hA _ (fun i j => by
    have := congrFun (congrFun hD i) j
    simpa [hDdef] using this)
  exact congrFun hc k

/-! ## The transporter classification -/

/-- **Every symplectic transporter `ι A → ι B` with `A` concise is unipotent × hyperbolic lift of a
`GL` transporter `A → B`, uniquely.** -/
theorem transporter_factor {A B : Fin n × Fin n × Fin n → K} (hA : Concise A)
    {P Q R : Matrix (S n) (S n) K} (hP : IsSymplecticMat K P) (hQ : IsSymplecticMat K Q)
    (hR : IsSymplecticMat K R) (h : act3D K P Q R (padArr A) = padArr B) :
    (IsUnit P.toBlocks₁₁.det ∧ IsUnit Q.toBlocks₁₁.det ∧ IsUnit R.toBlocks₁₁.det ∧
        act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A = B) ∧
      ((P.toBlocks₁₂ * P.toBlocks₁₁ᵀ).IsSymm ∧ (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ).IsSymm ∧
        (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ).IsSymm) ∧
      (P = unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁ ∧
        Q = unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁ ∧
        R = unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp (isUnit_of_isSymplecticMat K P hP)
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp (isUnit_of_isSymplecticMat K Q hQ)
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp (isUnit_of_isSymplecticMat K R hR)
  have hPc := toBlocks₂₁_eq_zero₁ hA.1 hQd hRd h
  have hQc := toBlocks₂₁_eq_zero₂ hA.2.1 hPd hRd h
  have hRc := toBlocks₂₁_eq_zero₃ hA.2.2 hPd hQd h
  obtain ⟨hPdet, hPsym, hPeq⟩ := sympl_factor hP hPc
  obtain ⟨hQdet, hQsym, hQeq⟩ := sympl_factor hQ hQc
  obtain ⟨hRdet, hRsym, hReq⟩ := sympl_factor hR hRc
  have hact : padArr (act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A) = padArr B := by
    rw [← act3D_padArr_of_toBlocks₂₁ hPc hQc hRc]; exact h
  exact ⟨⟨hPdet, hQdet, hRdet, padArr_injective hact⟩, ⟨hPsym, hQsym, hRsym⟩, ⟨hPeq, hQeq, hReq⟩⟩

/-- Conversely, symmetric `U_i` and a `GL` transporter `a` give a symplectic transporter. -/
theorem transporter_of_factor {A B : Fin n × Fin n × Fin n → K}
    {U₁ U₂ U₃ a₁ a₂ a₃ : Matrix (Fin n) (Fin n) K}
    (hU₁ : U₁.IsSymm) (hU₂ : U₂.IsSymm) (hU₃ : U₃.IsSymm)
    (ha₁ : IsUnit a₁.det) (ha₂ : IsUnit a₂.det) (ha₃ : IsUnit a₃.det)
    (h : act3 K a₁ a₂ a₃ A = B) :
    IsSymplecticMat K (unip U₁ * hypLift a₁) ∧ IsSymplecticMat K (unip U₂ * hypLift a₂) ∧
      IsSymplecticMat K (unip U₃ * hypLift a₃) ∧
      act3D K (unip U₁ * hypLift a₁) (unip U₂ * hypLift a₂) (unip U₃ * hypLift a₃) (padArr A) =
        padArr B := by
  refine ⟨isSymplecticMat_mul (isSymplecticMat_unip hU₁) (isSymplecticMat_hypLift ha₁),
    isSymplecticMat_mul (isSymplecticMat_unip hU₂) (isSymplecticMat_hypLift ha₂),
    isSymplecticMat_mul (isSymplecticMat_unip hU₃) (isSymplecticMat_hypLift ha₃), ?_⟩
  rw [act3D_padArr_congr A (unip_mul_hypLift_apply_inl U₁ a₁) (unip_mul_hypLift_apply_inl U₂ a₂)
    (unip_mul_hypLift_apply_inl U₃ a₃), act3D_hypLift_padArr, h]

/-- Symmetric `n × n` matrices. -/
def SymMat (n : ℕ) (K : Type u) [Field K] := {U : Matrix (Fin n) (Fin n) K // U.IsSymm}

/-- Symplectic transporters between the paddings. -/
def SpTrans (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (S n) (S n) K × Matrix (S n) (S n) K × Matrix (S n) (S n) K //
    IsSymplecticMat K g.1 ∧ IsSymplecticMat K g.2.1 ∧ IsSymplecticMat K g.2.2 ∧
      act3D K g.1 g.2.1 g.2.2 (padArr A) = padArr B}

/-- `GL` transporters. -/
def GLTrans (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K //
    IsUnit g.1.det ∧ IsUnit g.2.1.det ∧ IsUnit g.2.2.det ∧ act3 K g.1 g.2.1 g.2.2 A = B}

/-- **`Trans_H(ι A, ι B) ≃ Sym_n(K)³ × Trans_G(A, B)`** for concise `A`. -/
noncomputable def transporterEquiv {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    SpTrans A B ≃ (SymMat n K × SymMat n K × SymMat n K) × GLTrans A B where
  toFun g :=
    ((⟨g.1.1.toBlocks₁₂ * g.1.1.toBlocks₁₁ᵀ,
        (transporter_factor hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.1⟩,
      ⟨g.1.2.1.toBlocks₁₂ * g.1.2.1.toBlocks₁₁ᵀ,
        (transporter_factor hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.1⟩,
      ⟨g.1.2.2.toBlocks₁₂ * g.1.2.2.toBlocks₁₁ᵀ,
        (transporter_factor hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.2⟩),
     ⟨(g.1.1.toBlocks₁₁, g.1.2.1.toBlocks₁₁, g.1.2.2.toBlocks₁₁),
        (transporter_factor hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).1⟩)
  invFun x :=
    ⟨(unip x.1.1.1 * hypLift x.2.1.1, unip x.1.2.1.1 * hypLift x.2.1.2.1,
        unip x.1.2.2.1 * hypLift x.2.1.2.2),
      transporter_of_factor x.1.1.2 x.1.2.1.2 x.1.2.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2⟩
  left_inv g := by
    obtain ⟨⟨P, Q, R⟩, hP, hQ, hR, h⟩ := g
    obtain ⟨-, -, hPeq, hQeq, hReq⟩ := transporter_factor hA hP hQ hR h
    apply Subtype.ext
    show (unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁,
      unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁,
      unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) = (P, Q, R)
    rw [← hPeq, ← hQeq, ← hReq]
  right_inv x := by
    obtain ⟨⟨⟨U₁, hU₁⟩, ⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩⟩, ⟨⟨a₁, a₂, a₃⟩, ha₁, ha₂, ha₃, h⟩⟩ := x
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
      (Subtype.ext ?_)
    · exact toBlocks₁₂_unip_mul_hypLift U₁ a₁ ha₁
    · exact toBlocks₁₂_unip_mul_hypLift U₂ a₂ ha₂
    · exact toBlocks₁₂_unip_mul_hypLift U₃ a₃ ha₃
    · show (_, _, _) = (a₁, a₂, a₃)
      rw [toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift]

/-- **`|Trans_H(ι A, ι B)| = |Sym_n(K)|³ · |Trans_G(A, B)|`** (as `Nat.card`; over `F_q` the first
factor is `q^{3n(n+1)/2}`). -/
theorem natCard_spTrans {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (SpTrans A B) = Nat.card (SymMat n K) ^ 3 * Nat.card (GLTrans A B) := by
  rw [Nat.card_congr (transporterEquiv hA), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

/-- **Finite fields: `|Trans_H(ι A, ι B)| = q^{3·C(n+1,2)} · |Trans_G(A, B)|`**, i.e. the factor
`q^{3n(n+1)/2}` announced in the fallout note. -/
theorem natCard_spTrans_finite [Finite K] {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (SpTrans A B) = Nat.card K ^ (3 * (n + 1).choose 2) * Nat.card (GLTrans A B) := by
  rw [natCard_spTrans hA,
    show Nat.card (SymMat n K) = Nat.card K ^ ((n + 1).choose 2) from SymMatCard.natCard_symm,
    ← pow_mul]
  ring

/-- Relation-level corollary: for concise `A`, `TI_Sp(ι A, ι B) ↔ TI(A, B)`. -/
theorem sp3ti_rel_pad_iff {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    (Sp3TI K).Rel n (padArr A) (padArr B) ↔ (GL3TI K).Rel n A B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    obtain ⟨⟨hPd, hQd, hRd, hact⟩, -, -⟩ := transporter_factor hA hP hQ hR h
    exact ⟨P.toBlocks₁₁, Q.toBlocks₁₁, R.toBlocks₁₁, (Matrix.isUnit_iff_isUnit_det _).mpr hPd,
      (Matrix.isUnit_iff_isUnit_det _).mpr hQd, (Matrix.isUnit_iff_isUnit_det _).mpr hRd, hact⟩
  · rintro ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h⟩
    obtain ⟨h₁, h₂, h₃, hact⟩ := transporter_of_factor (A := A) (B := B)
      (Matrix.isSymm_zero) (Matrix.isSymm_zero) (Matrix.isSymm_zero)
      ((Matrix.isUnit_iff_isUnit_det a₁).mp ha₁) ((Matrix.isUnit_iff_isUnit_det a₂).mp ha₂)
      ((Matrix.isUnit_iff_isUnit_det a₃).mp ha₃) h
    exact ⟨_, _, _, h₁, h₂, h₃, hact⟩

end Mathproof.LibraryBridges.Claude.TISpTransporterFibers

#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.sympl_factor
#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.transporter_factor
#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.transporterEquiv
#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.natCard_spTrans
#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.natCard_spTrans_finite
#print axioms Mathproof.LibraryBridges.Claude.TISpTransporterFibers.sp3ti_rel_pad_iff

end Part_U34


section Part_U35


/-!
# Counting antisymmetric matrices: `|{U : Uᵀ = -U}| = |K|^{n(n-1)/2}` outside characteristic two

Companion of `SymMatCard`.  An antisymmetric matrix over a field of characteristic `≠ 2` has zero
diagonal and is freely determined by its strict upper triangle, so it is a function on the strictly
ordered pairs of `Fin n`, of which there are `C(n, 2)` (`Fintype.card_product_filter_lt`).

This is the split-orthogonal fiber factor `q^{3·C(n,2)}` of the padded-transporter count in
`TIIsoTransporterFibers` (the `ε = 1` member of the family, as `SymMatCard` is the `ε = -1` one).
In characteristic two the two conditions coincide (`skew_iff_isSymm_of_two_eq_zero`) and the count
is `SymMatCard`'s.
-/

namespace Mathproof.LibraryBridges.Claude.SkewMatCard
open Matrix


variable {n : ℕ} {K : Type*} [Field K]

/-- An antisymmetric matrix has zero diagonal when `2 ≠ 0`. -/
theorem diag_eq_zero (h2 : (2 : K) ≠ 0) {U : Matrix (Fin n) (Fin n) K} (hU : Uᵀ = -U)
    (i : Fin n) : U i i = 0 := by
  have h : U i i = -U i i := by
    have := congrFun (congrFun hU i) i
    simpa using this
  have hs : U i i + U i i = 0 := add_eq_zero_iff_eq_neg.mpr h
  rw [← two_mul] at hs
  exact (mul_eq_zero.mp hs).resolve_left h2

/-- In characteristic two, antisymmetry is symmetry. -/
theorem skew_iff_isSymm_of_two_eq_zero (h2 : (2 : K) = 0) {U : Matrix (Fin n) (Fin n) K} :
    Uᵀ = -U ↔ U.IsSymm := by
  have hneg : -U = U := by
    ext i j
    have h0 : U i j + U i j = 0 := by
      have h1 : (2 : K) * U i j = 0 := by rw [h2, zero_mul]
      rwa [two_mul] at h1
    simpa using neg_eq_of_add_eq_zero_left h0
  rw [Matrix.IsSymm, hneg]

/-- The antisymmetric matrix with prescribed strict-upper-triangle entries. -/
def skewOfFun (f : {p : Fin n × Fin n // p.1 < p.2} → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0

theorem skewOfFun_apply (f : {p : Fin n × Fin n // p.1 < p.2} → K) (i j : Fin n) :
    skewOfFun f i j =
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0 := rfl

theorem skewOfFun_apply_lt {f : {p : Fin n × Fin n // p.1 < p.2} → K} {i j : Fin n} (h : i < j) :
    skewOfFun f i j = f ⟨(i, j), h⟩ := by
  rw [skewOfFun_apply, dif_pos h]

theorem skewOfFun_skew (f : {p : Fin n × Fin n // p.1 < p.2} → K) :
    (skewOfFun f)ᵀ = -(skewOfFun f) := by
  ext i j
  rw [transpose_apply, Matrix.neg_apply, skewOfFun_apply, skewOfFun_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp only [dif_neg (asymm h), dif_pos h]
  · subst h
    simp only [dif_neg (lt_irrefl i), neg_zero]
  · simp only [dif_pos h, dif_neg (asymm h), neg_neg]

/-- The strict-upper-triangle entries of a matrix. -/
def skewToFun (U : {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U}) :
    {p : Fin n × Fin n // p.1 < p.2} → K := fun p => U.1 p.1.1 p.1.2

/-- **Antisymmetric matrices are free on the strict upper triangle** (characteristic `≠ 2`). -/
def skewEquivStrict (h2 : (2 : K) ≠ 0) :
    {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U} ≃ ({p : Fin n × Fin n // p.1 < p.2} → K) where
  toFun := skewToFun
  invFun f := ⟨skewOfFun f, skewOfFun_skew f⟩
  left_inv U := by
    obtain ⟨U, hU⟩ := U
    refine Subtype.ext ?_
    ext i j
    show skewOfFun (skewToFun ⟨U, hU⟩) i j = U i j
    rw [skewOfFun_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_pos h]
      rfl
    · subst h
      simp only [dif_neg (lt_irrefl i)]
      exact (diag_eq_zero h2 hU i).symm
    · rw [dif_neg (asymm h), dif_pos h]
      show -U j i = U i j
      have hji : U j i = -U i j := by
        have := congrFun (congrFun hU i) j
        simpa using this
      rw [hji, neg_neg]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    exact skewOfFun_apply_lt h

theorem card_strictPairs (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- **`|{U : Uᵀ = -U}| = |K|^{C(n,2)}`** outside characteristic two. -/
theorem natCard_skew [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U} = Nat.card K ^ (n.choose 2) := by
  rw [Nat.card_congr (skewEquivStrict h2), Nat.card_fun,
    Nat.card_eq_fintype_card (α := {p : Fin n × Fin n // p.1 < p.2}), card_strictPairs]

theorem natCard_skew_eq_div [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U} = Nat.card K ^ (n * (n - 1) / 2) := by
  rw [natCard_skew h2, Nat.choose_two_right]

end Mathproof.LibraryBridges.Claude.SkewMatCard

#print axioms Mathproof.LibraryBridges.Claude.SkewMatCard.diag_eq_zero
#print axioms Mathproof.LibraryBridges.Claude.SkewMatCard.skewEquivStrict
#print axioms Mathproof.LibraryBridges.Claude.SkewMatCard.natCard_skew
#print axioms Mathproof.LibraryBridges.Claude.SkewMatCard.skew_iff_isSymm_of_two_eq_zero

end Part_U35


section Part_U36


/-!
# The padded-transporter technique for **every** hyperbolic form `Φ_ε`, not just the symplectic one

`TISpTransporterFibers` computes the symplectic transporters between paddings of concise tensors,
`Trans_{Sp}(ι A, ι B) ≃ Sym_n(K)³ × Trans_{GL}(A, B)`.  Nothing in that argument is special to
`ε = -1`: the padding action, the conciseness step and the block algebra never see the form, and
the form enters only through the factorization of an isometry with vanishing lower-left block.
This module runs the whole technique over the family `hypForm n ε = [[0, 1], [ε, 0]]` of
`TIGroupLevi20260902`, for every `ε ≠ 0`.

Main results (all for concise `A`, every field, every `ε ≠ 0`):

* `iso_factor` — an isometry of `Φ_ε` with `M₂₁ = 0` factors uniquely as `[[1,U],[0,1]] · diag(a,a⁻ᵀ)`
  with `Uᵀ = -(ε • U)` (`EpsSymm ε U`);
* `isoTransporterEquiv` — `Trans_{O(Φ_ε)}(ι A, ι B) ≃ EpsMat ε³ × Trans_{GL}(A, B)`;
* `natCard_isoTrans` — the corresponding count, with `natCard_isoTrans_neg_one` recovering the
  symplectic `q^{3·C(n+1,2)}` and `natCard_isoTrans_one` giving the **split-orthogonal**
  `q^{3·C(n,2)}` outside characteristic two (`SkewMatCard`);
* `isoTrans_equiv_glTrans_of_sq_ne_one` — **rigidity**: when `ε² ≠ 1` the unipotent fiber collapses
  (`EpsSymm ε U → U = 0`), so the padded transporter is *exactly* the `GL` transporter.  So the
  three-way trichotomy `ε = -1` / `ε = 1` / `ε² ≠ 1` is visible in the fiber size, and the two
  classical groups are precisely the cases with a nontrivial fiber;
* `tiIso_rel_pad_iff` — the relation-level corollary for every `ε ≠ 0`;
* `det_eq_one_of_transporter` — every such transporter has determinant one, so the isometry
  transporters and the *special* isometry transporters of a padded concise tensor coincide.

Not claimed: anything about complexity classes (the class-level equalities `TI = TI_Sp = TI_{O(H)}`
are `TILandscape20260902`'s, by a different, gadget-based route), and nothing about `TI_SL` beyond
the determinant remark above.
-/

open scoped Matrix

open Matrix

namespace Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers

open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.PaddingProjection20260902
open Mathproof.Meta.TIGroupLevi20260902
open Mathproof.LibraryBridges.Claude.TISpTransporterFibers

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ## The `ε`-symmetry condition cut out by the unipotent radical -/

/-- The condition on the off-diagonal block of `[[1,U],[0,1]]` making it an isometry of `Φ_ε`:
`Uᵀ = -(ε • U)`.  For `ε = -1` this is symmetry, for `ε = 1` antisymmetry. -/
def EpsSymm (ε : K) (U : Matrix (Fin n) (Fin n) K) : Prop := Uᵀ = -(ε • U)

theorem epsSymm_zero (ε : K) : EpsSymm ε (0 : Matrix (Fin n) (Fin n) K) := by
  simp [EpsSymm]

theorem epsSymm_neg_one_iff {U : Matrix (Fin n) (Fin n) K} :
    EpsSymm (-1 : K) U ↔ U.IsSymm := by
  simp [EpsSymm, Matrix.IsSymm]

theorem epsSymm_one_iff {U : Matrix (Fin n) (Fin n) K} : EpsSymm (1 : K) U ↔ Uᵀ = -U := by
  simp [EpsSymm]

/-- **Rigidity of the fiber**: if `ε² ≠ 1` the only `ε`-symmetric matrix is `0`. -/
theorem eq_zero_of_epsSymm_of_sq_ne_one {ε : K} (hε : ε * ε ≠ 1)
    {U : Matrix (Fin n) (Fin n) K} (hU : EpsSymm ε U) : U = 0 := by
  have h : U = (ε * ε) • U := by
    calc U = Uᵀᵀ := (transpose_transpose U).symm
      _ = (-(ε • U))ᵀ := by rw [hU]
      _ = -(ε • Uᵀ) := by rw [transpose_neg, transpose_smul]
      _ = -(ε • -(ε • U)) := by rw [hU]
      _ = (ε * ε) • U := by rw [smul_neg, neg_neg, smul_smul]
  have h1 : (1 - ε * ε) • U = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  have h2 : (1 : K) - ε * ε ≠ 0 := sub_ne_zero.mpr fun hc => hε hc.symm
  exact (smul_eq_zero.mp h1).resolve_left h2

/-! ## The `ε`-isometry group: unipotent part, hyperbolic lift, factorization -/

theorem isIsometry_mul {ε : K} {g h : Matrix (S n) (S n) K} (hg : IsIsometry n ε g)
    (hh : IsIsometry n ε h) : IsIsometry n ε (g * h) := by
  unfold IsIsometry at *
  calc (g * h)ᵀ * hypForm n ε * (g * h) = hᵀ * (gᵀ * hypForm n ε * g) * h := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = hypForm n ε := by rw [hg, hh]

theorem isIsometry_unip {ε : K} {U : Matrix (Fin n) (Fin n) K} (hU : EpsSymm ε U) :
    IsIsometry n ε (unip U) := by
  unfold IsIsometry hypForm unip
  rw [fromBlocks_transpose]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_zero, zero_add, add_zero,
    transpose_zero, transpose_one]
  rw [hU]
  simp

theorem isIsometry_hypLift {ε : K} {a : Matrix (Fin n) (Fin n) K} (ha : IsUnit a.det) :
    IsIsometry n ε (hypLift a) := hypLift_isIsometry ε a ha

theorem isUnit_det_of_isIsometry {ε : K} (hε : ε ≠ 0) {g : Matrix (S n) (S n) K}
    (hg : IsIsometry n ε g) : IsUnit g.det :=
  isUnit_det_of_isometry (isUnit_det_hypForm n ε hε) hg

/-- The block equations of an `ε`-isometry with vanishing lower-left block. -/
theorem iso_blocks {ε : K} {M : Matrix (S n) (S n) K} (hM : IsIsometry n ε M)
    (hc : M.toBlocks₂₁ = 0) :
    M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 ∧
      ε • (M.toBlocks₂₂ᵀ * M.toBlocks₁₂) + M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = 0 := by
  have hMeq : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  unfold IsIsometry hypForm at hM
  rw [hMeq, fromBlocks_transpose] at hM
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_zero, zero_add, add_zero,
    transpose_zero, fromBlocks_inj] at hM
  obtain ⟨-, h12, -, h22⟩ := hM
  exact ⟨h12, h22⟩

/-- **Unique factorization** `M = [[1,U],[0,1]] · diag(a, a⁻ᵀ)` with `a = M₁₁` and
`U = M₁₂ M₁₁ᵀ` an `ε`-symmetric matrix. -/
theorem iso_factor {ε : K} {M : Matrix (S n) (S n) K} (hM : IsIsometry n ε M)
    (hc : M.toBlocks₂₁ = 0) :
    IsUnit M.toBlocks₁₁.det ∧ EpsSymm ε (M.toBlocks₁₂ * M.toBlocks₁₁ᵀ) ∧
      M = unip (M.toBlocks₁₂ * M.toBlocks₁₁ᵀ) * hypLift M.toBlocks₁₁ := by
  obtain ⟨h12, h22⟩ := iso_blocks hM hc
  set a := M.toBlocks₁₁ with ha_def
  set b := M.toBlocks₁₂ with hb_def
  set d := M.toBlocks₂₂ with hd_def
  have hMeq : M = fromBlocks a b 0 d := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  have hdet : IsUnit a.det := by
    have := congrArg Matrix.det h12
    rw [det_mul, det_transpose, det_one] at this
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one this)
  have hd : d = a⁻¹ᵀ := by
    rw [transpose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv h12).symm
  have h22' : bᵀ * a⁻¹ᵀ = -(ε • (a⁻¹ * b)) := by
    rw [hd, transpose_transpose] at h22
    calc bᵀ * a⁻¹ᵀ = -(ε • (a⁻¹ * b)) + (ε • (a⁻¹ * b) + bᵀ * a⁻¹ᵀ) := by abel
      _ = -(ε • (a⁻¹ * b)) := by rw [h22, add_zero]
  have hsymm : EpsSymm ε (b * aᵀ) := by
    unfold EpsSymm
    rw [transpose_mul, transpose_transpose]
    calc a * bᵀ = a * bᵀ * (a⁻¹ᵀ * aᵀ) := by
          rw [← transpose_mul, Matrix.mul_nonsing_inv a hdet, transpose_one, Matrix.mul_one]
      _ = a * (bᵀ * a⁻¹ᵀ) * aᵀ := by simp only [Matrix.mul_assoc]
      _ = a * (-(ε • (a⁻¹ * b))) * aᵀ := by rw [h22']
      _ = -(ε • (a * (a⁻¹ * b) * aᵀ)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = -(ε • (b * aᵀ)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a hdet, Matrix.one_mul]
  have hb : b = b * aᵀ * a⁻¹ᵀ := by
    rw [Matrix.mul_assoc, ← transpose_mul, Matrix.nonsing_inv_mul a hdet, transpose_one,
      Matrix.mul_one]
  refine ⟨hdet, hsymm, ?_⟩
  rw [unip_mul_hypLift, ← hb, hMeq, hd]

/-! ## The transporter classification for `Φ_ε` -/

/-- **Every `Φ_ε`-isometry transporter `ι A → ι B` with `A` concise is unipotent × hyperbolic lift
of a `GL` transporter `A → B`, uniquely.** -/
theorem transporter_factor_iso {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) {P Q R : Matrix (S n) (S n) K} (hP : IsIsometry n ε P)
    (hQ : IsIsometry n ε Q) (hR : IsIsometry n ε R)
    (h : act3D K P Q R (padArr A) = padArr B) :
    (IsUnit P.toBlocks₁₁.det ∧ IsUnit Q.toBlocks₁₁.det ∧ IsUnit R.toBlocks₁₁.det ∧
        act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A = B) ∧
      (EpsSymm ε (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) ∧ EpsSymm ε (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) ∧
        EpsSymm ε (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ)) ∧
      (P = unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁ ∧
        Q = unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁ ∧
        R = unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) := by
  have hPd : IsUnit P.det := isUnit_det_of_isIsometry hε hP
  have hQd : IsUnit Q.det := isUnit_det_of_isIsometry hε hQ
  have hRd : IsUnit R.det := isUnit_det_of_isIsometry hε hR
  have hPc := toBlocks₂₁_eq_zero₁ hA.1 hQd hRd h
  have hQc := toBlocks₂₁_eq_zero₂ hA.2.1 hPd hRd h
  have hRc := toBlocks₂₁_eq_zero₃ hA.2.2 hPd hQd h
  obtain ⟨hPdet, hPsym, hPeq⟩ := iso_factor hP hPc
  obtain ⟨hQdet, hQsym, hQeq⟩ := iso_factor hQ hQc
  obtain ⟨hRdet, hRsym, hReq⟩ := iso_factor hR hRc
  have hact : padArr (act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A) = padArr B := by
    rw [← act3D_padArr_of_toBlocks₂₁ hPc hQc hRc]; exact h
  exact ⟨⟨hPdet, hQdet, hRdet, padArr_injective hact⟩, ⟨hPsym, hQsym, hRsym⟩, ⟨hPeq, hQeq, hReq⟩⟩

/-- Conversely, `ε`-symmetric `U_i` and a `GL` transporter give a `Φ_ε`-isometry transporter. -/
theorem transporter_of_factor_iso {ε : K} {A B : Fin n × Fin n × Fin n → K}
    {U₁ U₂ U₃ a₁ a₂ a₃ : Matrix (Fin n) (Fin n) K}
    (hU₁ : EpsSymm ε U₁) (hU₂ : EpsSymm ε U₂) (hU₃ : EpsSymm ε U₃)
    (ha₁ : IsUnit a₁.det) (ha₂ : IsUnit a₂.det) (ha₃ : IsUnit a₃.det)
    (h : act3 K a₁ a₂ a₃ A = B) :
    IsIsometry n ε (unip U₁ * hypLift a₁) ∧ IsIsometry n ε (unip U₂ * hypLift a₂) ∧
      IsIsometry n ε (unip U₃ * hypLift a₃) ∧
      act3D K (unip U₁ * hypLift a₁) (unip U₂ * hypLift a₂) (unip U₃ * hypLift a₃) (padArr A) =
        padArr B := by
  refine ⟨isIsometry_mul (isIsometry_unip hU₁) (isIsometry_hypLift ha₁),
    isIsometry_mul (isIsometry_unip hU₂) (isIsometry_hypLift ha₂),
    isIsometry_mul (isIsometry_unip hU₃) (isIsometry_hypLift ha₃), ?_⟩
  rw [act3D_padArr_congr A (unip_mul_hypLift_apply_inl U₁ a₁) (unip_mul_hypLift_apply_inl U₂ a₂)
    (unip_mul_hypLift_apply_inl U₃ a₃), act3D_hypLift_padArr, h]

/-- `ε`-symmetric `n × n` matrices: the unipotent radical of the Siegel parabolic of `Φ_ε`. -/
def EpsMat (ε : K) (n : ℕ) := {U : Matrix (Fin n) (Fin n) K // EpsSymm ε U}

/-- `Φ_ε`-isometry transporters between the paddings. -/
def IsoTrans (ε : K) (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (S n) (S n) K × Matrix (S n) (S n) K × Matrix (S n) (S n) K //
    IsIsometry n ε g.1 ∧ IsIsometry n ε g.2.1 ∧ IsIsometry n ε g.2.2 ∧
      act3D K g.1 g.2.1 g.2.2 (padArr A) = padArr B}

/-- **`Trans_{O(Φ_ε)}(ι A, ι B) ≃ EpsMat ε³ × Trans_{GL}(A, B)`** for concise `A`, every `ε ≠ 0`. -/
noncomputable def isoTransporterEquiv {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) :
    IsoTrans ε A B ≃ (EpsMat ε n × EpsMat ε n × EpsMat ε n) × GLTrans A B where
  toFun g :=
    ((⟨g.1.1.toBlocks₁₂ * g.1.1.toBlocks₁₁ᵀ,
        (transporter_factor_iso hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.1⟩,
      ⟨g.1.2.1.toBlocks₁₂ * g.1.2.1.toBlocks₁₁ᵀ,
        (transporter_factor_iso hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.1⟩,
      ⟨g.1.2.2.toBlocks₁₂ * g.1.2.2.toBlocks₁₁ᵀ,
        (transporter_factor_iso hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.2⟩),
     ⟨(g.1.1.toBlocks₁₁, g.1.2.1.toBlocks₁₁, g.1.2.2.toBlocks₁₁),
        (transporter_factor_iso hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).1⟩)
  invFun x :=
    ⟨(unip x.1.1.1 * hypLift x.2.1.1, unip x.1.2.1.1 * hypLift x.2.1.2.1,
        unip x.1.2.2.1 * hypLift x.2.1.2.2),
      transporter_of_factor_iso x.1.1.2 x.1.2.1.2 x.1.2.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2⟩
  left_inv g := by
    obtain ⟨⟨P, Q, R⟩, hP, hQ, hR, h⟩ := g
    obtain ⟨-, -, hPeq, hQeq, hReq⟩ := transporter_factor_iso hε hA hP hQ hR h
    apply Subtype.ext
    show (unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁,
      unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁,
      unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) = (P, Q, R)
    rw [← hPeq, ← hQeq, ← hReq]
  right_inv x := by
    obtain ⟨⟨⟨U₁, hU₁⟩, ⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩⟩, ⟨⟨a₁, a₂, a₃⟩, ha₁, ha₂, ha₃, h⟩⟩ := x
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
      (Subtype.ext ?_)
    · exact toBlocks₁₂_unip_mul_hypLift U₁ a₁ ha₁
    · exact toBlocks₁₂_unip_mul_hypLift U₂ a₂ ha₂
    · exact toBlocks₁₂_unip_mul_hypLift U₃ a₃ ha₃
    · show (_, _, _) = (a₁, a₂, a₃)
      rw [toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift]

/-- **`|Trans_{O(Φ_ε)}(ι A, ι B)| = |EpsMat ε|³ · |Trans_{GL}(A, B)|`**. -/
theorem natCard_isoTrans {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) :
    Nat.card (IsoTrans ε A B) = Nat.card (EpsMat ε n) ^ 3 * Nat.card (GLTrans A B) := by
  rw [Nat.card_congr (isoTransporterEquiv hε hA), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

/-! ## The three regimes of the fiber -/

/-- At `ε = -1` the fiber is the symmetric matrices: the symplectic case. -/
def epsMatNegOneEquiv : EpsMat (-1 : K) n ≃ SymMat n K :=
  Equiv.subtypeEquivRight fun _ => epsSymm_neg_one_iff

/-- Symplectic instance: `|Trans_{Sp}| = q^{3·C(n+1,2)} · |Trans_{GL}|` (recovers
`TISpTransporterFibers.natCard_spTrans_finite` from the general theorem). -/
theorem natCard_isoTrans_neg_one [Finite K] {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (IsoTrans (-1 : K) A B) =
      Nat.card K ^ (3 * (n + 1).choose 2) * Nat.card (GLTrans A B) := by
  rw [natCard_isoTrans (by norm_num) hA, Nat.card_congr (epsMatNegOneEquiv (K := K) (n := n)),
    show Nat.card (SymMat n K) = Nat.card K ^ ((n + 1).choose 2) from SymMatCard.natCard_symm,
    ← pow_mul]
  ring

/-- At `ε = 1` the fiber is the antisymmetric matrices: the split-orthogonal case. -/
def epsMatOneEquiv : EpsMat (1 : K) n ≃ {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U} :=
  Equiv.subtypeEquivRight fun _ => epsSymm_one_iff

/-- **Split-orthogonal instance** (characteristic `≠ 2`): the padded transporters of the isometry
group of the hyperbolic *symmetric* form satisfy `|Trans| = q^{3·C(n,2)} · |Trans_{GL}|`.  This is
the `ε = 1` sibling of the symplectic `q^{3·C(n+1,2)}`, and it is a strictly smaller fiber. -/
theorem natCard_isoTrans_one [Finite K] (h2 : (2 : K) ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) :
    Nat.card (IsoTrans (1 : K) A B) = Nat.card K ^ (3 * n.choose 2) * Nat.card (GLTrans A B) := by
  rw [natCard_isoTrans one_ne_zero hA, Nat.card_congr (epsMatOneEquiv (K := K) (n := n)),
    show Nat.card {U : Matrix (Fin n) (Fin n) K // Uᵀ = -U} = Nat.card K ^ (n.choose 2) from
      SkewMatCard.natCard_skew h2, ← pow_mul]
  ring

/-- In characteristic two the split-orthogonal and symplectic fibers coincide (`1 = -1`), and the
count is the symmetric one. -/
theorem natCard_isoTrans_one_of_two_eq_zero [Finite K] (h2 : (2 : K) = 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (IsoTrans (1 : K) A B) =
      Nat.card K ^ (3 * (n + 1).choose 2) * Nat.card (GLTrans A B) := by
  have hfib : Nat.card (EpsMat (1 : K) n) = Nat.card K ^ ((n + 1).choose 2) := by
    rw [Nat.card_congr (epsMatOneEquiv (K := K) (n := n)),
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => SkewMatCard.skew_iff_isSymm_of_two_eq_zero h2)]
    exact SymMatCard.natCard_symm
  rw [natCard_isoTrans one_ne_zero hA, hfib, ← pow_mul]
  ring

/-- **Stabilizer reading** (`A = B`): `Stab_{O(Φ_ε)}(ι A) ≃ EpsMat ε³ × Stab_{GL}(A)`.  With the
composition law `TISpTransporterFibers.unip_mul_hypLift_mul` (which is form-free, hence valid for
every `ε`) this identification is a semidirect product, `GL` acting on the fiber by congruence
`U ↦ a U aᵀ`. -/
theorem natCard_isoStab {ε : K} (hε : ε ≠ 0) {A : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (IsoTrans ε A A) = Nat.card (EpsMat ε n) ^ 3 * Nat.card (GLTrans A A) :=
  natCard_isoTrans hε hA

/-- **Rigidity**: for `ε² ≠ 1` the unipotent fiber is trivial, so the padded transporters are
*exactly* the `GL` transporters.  Only `ε = ±1` — symplectic and split orthogonal — have a
nontrivial fiber. -/
noncomputable def isoTrans_equiv_glTrans_of_sq_ne_one {ε : K} (hε : ε ≠ 0) (hsq : ε * ε ≠ 1)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) : IsoTrans ε A B ≃ GLTrans A B :=
  (isoTransporterEquiv hε hA).trans
    { toFun := fun x => x.2
      invFun := fun g => ((⟨0, epsSymm_zero ε⟩, ⟨0, epsSymm_zero ε⟩, ⟨0, epsSymm_zero ε⟩), g)
      left_inv := fun x => by
        obtain ⟨⟨U₁, U₂, U₃⟩, g⟩ := x
        refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))) rfl
        · exact (eq_zero_of_epsSymm_of_sq_ne_one hsq U₁.2).symm ▸ rfl
        · exact (eq_zero_of_epsSymm_of_sq_ne_one hsq U₂.2).symm ▸ rfl
        · exact (eq_zero_of_epsSymm_of_sq_ne_one hsq U₃.2).symm ▸ rfl
      right_inv := fun _ => rfl }

theorem natCard_isoTrans_of_sq_ne_one {ε : K} (hε : ε ≠ 0) (hsq : ε * ε ≠ 1)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (IsoTrans ε A B) = Nat.card (GLTrans A B) :=
  Nat.card_congr (isoTrans_equiv_glTrans_of_sq_ne_one hε hsq hA)

/-! ## Relation level and determinants -/

/-- Relation-level corollary for every `ε ≠ 0`: for concise `A`, `TI_{O(Φ_ε)}(ι A, ι B) ↔ TI(A,B)`. -/
theorem tiIso_rel_pad_iff {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) :
    (TIIso ε).Rel n (padArr A) (padArr B) ↔ (GL3TI K).Rel n A B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    obtain ⟨⟨hPd, hQd, hRd, hact⟩, -, -⟩ := transporter_factor_iso hε hA hP hQ hR h
    exact ⟨P.toBlocks₁₁, Q.toBlocks₁₁, R.toBlocks₁₁, (Matrix.isUnit_iff_isUnit_det _).mpr hPd,
      (Matrix.isUnit_iff_isUnit_det _).mpr hQd, (Matrix.isUnit_iff_isUnit_det _).mpr hRd, hact⟩
  · rintro ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h⟩
    obtain ⟨h₁, h₂, h₃, hact⟩ := transporter_of_factor_iso (A := A) (B := B)
      (epsSymm_zero ε) (epsSymm_zero ε) (epsSymm_zero ε)
      ((Matrix.isUnit_iff_isUnit_det a₁).mp ha₁) ((Matrix.isUnit_iff_isUnit_det a₂).mp ha₂)
      ((Matrix.isUnit_iff_isUnit_det a₃).mp ha₃) h
    exact ⟨_, _, _, h₁, h₂, h₃, hact⟩

theorem det_unip (U : Matrix (Fin n) (Fin n) K) : (unip U).det = 1 := by
  rw [unip, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem det_hypLift {a : Matrix (Fin n) (Fin n) K} (ha : IsUnit a.det) : (hypLift a).det = 1 := by
  rw [hypLift, det_fromBlocks_zero₂₁, det_transpose, det_nonsing_inv, Ring.mul_inverse_cancel _ ha]

/-- **Every `Φ_ε`-isometry transporter between paddings of a concise tensor has determinant one**:
the isometry transporters and the *special* isometry transporters coincide. -/
theorem det_eq_one_of_transporter {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) {P Q R : Matrix (S n) (S n) K} (hP : IsIsometry n ε P)
    (hQ : IsIsometry n ε Q) (hR : IsIsometry n ε R)
    (h : act3D K P Q R (padArr A) = padArr B) :
    P.det = 1 ∧ Q.det = 1 ∧ R.det = 1 := by
  obtain ⟨⟨hPd, hQd, hRd, -⟩, -, hPeq, hQeq, hReq⟩ := transporter_factor_iso hε hA hP hQ hR h
  refine ⟨?_, ?_, ?_⟩
  · rw [hPeq, det_mul, det_unip, det_hypLift hPd, mul_one]
  · rw [hQeq, det_mul, det_unip, det_hypLift hQd, mul_one]
  · rw [hReq, det_mul, det_unip, det_hypLift hRd, mul_one]

/-! ## Maximal generality of the technique: a different form on each mode -/

/-- Transporters when mode `i` carries its own hyperbolic form `Φ_{εᵢ}`.  The three modes are
handled independently by the argument, so nothing forces the three forms to agree. -/
def MixedTrans (ε₁ ε₂ ε₃ : K) (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (S n) (S n) K × Matrix (S n) (S n) K × Matrix (S n) (S n) K //
    IsIsometry n ε₁ g.1 ∧ IsIsometry n ε₂ g.2.1 ∧ IsIsometry n ε₃ g.2.2 ∧
      act3D K g.1 g.2.1 g.2.2 (padArr A) = padArr B}

theorem mixedTrans_self (ε : K) (A B : Fin n × Fin n × Fin n → K) :
    MixedTrans ε ε ε A B = IsoTrans ε A B := rfl

theorem transporter_factor_mixed {ε₁ ε₂ ε₃ : K} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hε₃ : ε₃ ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) {P Q R : Matrix (S n) (S n) K}
    (hP : IsIsometry n ε₁ P) (hQ : IsIsometry n ε₂ Q) (hR : IsIsometry n ε₃ R)
    (h : act3D K P Q R (padArr A) = padArr B) :
    (IsUnit P.toBlocks₁₁.det ∧ IsUnit Q.toBlocks₁₁.det ∧ IsUnit R.toBlocks₁₁.det ∧
        act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A = B) ∧
      (EpsSymm ε₁ (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) ∧ EpsSymm ε₂ (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) ∧
        EpsSymm ε₃ (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ)) ∧
      (P = unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁ ∧
        Q = unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁ ∧
        R = unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) := by
  have hPd : IsUnit P.det := isUnit_det_of_isIsometry hε₁ hP
  have hQd : IsUnit Q.det := isUnit_det_of_isIsometry hε₂ hQ
  have hRd : IsUnit R.det := isUnit_det_of_isIsometry hε₃ hR
  have hPc := toBlocks₂₁_eq_zero₁ hA.1 hQd hRd h
  have hQc := toBlocks₂₁_eq_zero₂ hA.2.1 hPd hRd h
  have hRc := toBlocks₂₁_eq_zero₃ hA.2.2 hPd hQd h
  obtain ⟨hPdet, hPsym, hPeq⟩ := iso_factor hP hPc
  obtain ⟨hQdet, hQsym, hQeq⟩ := iso_factor hQ hQc
  obtain ⟨hRdet, hRsym, hReq⟩ := iso_factor hR hRc
  have hact : padArr (act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A) = padArr B := by
    rw [← act3D_padArr_of_toBlocks₂₁ hPc hQc hRc]; exact h
  exact ⟨⟨hPdet, hQdet, hRdet, padArr_injective hact⟩, ⟨hPsym, hQsym, hRsym⟩, ⟨hPeq, hQeq, hReq⟩⟩

theorem transporter_of_factor_mixed {ε₁ ε₂ ε₃ : K} {A B : Fin n × Fin n × Fin n → K}
    {U₁ U₂ U₃ a₁ a₂ a₃ : Matrix (Fin n) (Fin n) K}
    (hU₁ : EpsSymm ε₁ U₁) (hU₂ : EpsSymm ε₂ U₂) (hU₃ : EpsSymm ε₃ U₃)
    (ha₁ : IsUnit a₁.det) (ha₂ : IsUnit a₂.det) (ha₃ : IsUnit a₃.det)
    (h : act3 K a₁ a₂ a₃ A = B) :
    IsIsometry n ε₁ (unip U₁ * hypLift a₁) ∧ IsIsometry n ε₂ (unip U₂ * hypLift a₂) ∧
      IsIsometry n ε₃ (unip U₃ * hypLift a₃) ∧
      act3D K (unip U₁ * hypLift a₁) (unip U₂ * hypLift a₂) (unip U₃ * hypLift a₃) (padArr A) =
        padArr B := by
  refine ⟨isIsometry_mul (isIsometry_unip hU₁) (isIsometry_hypLift ha₁),
    isIsometry_mul (isIsometry_unip hU₂) (isIsometry_hypLift ha₂),
    isIsometry_mul (isIsometry_unip hU₃) (isIsometry_hypLift ha₃), ?_⟩
  rw [act3D_padArr_congr A (unip_mul_hypLift_apply_inl U₁ a₁) (unip_mul_hypLift_apply_inl U₂ a₂)
    (unip_mul_hypLift_apply_inl U₃ a₃), act3D_hypLift_padArr, h]

/-- **The technique in its maximal generality**: an arbitrary hyperbolic form on each mode still
gives `Trans(ι A, ι B) ≃ EpsMat ε₁ × EpsMat ε₂ × EpsMat ε₃ × Trans_{GL}(A, B)`. -/
noncomputable def mixedTransporterEquiv {ε₁ ε₂ ε₃ : K} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0)
    (hε₃ : ε₃ ≠ 0) {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    MixedTrans ε₁ ε₂ ε₃ A B ≃ (EpsMat ε₁ n × EpsMat ε₂ n × EpsMat ε₃ n) × GLTrans A B where
  toFun g :=
    ((⟨g.1.1.toBlocks₁₂ * g.1.1.toBlocks₁₁ᵀ,
        (transporter_factor_mixed hε₁ hε₂ hε₃ hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.1⟩,
      ⟨g.1.2.1.toBlocks₁₂ * g.1.2.1.toBlocks₁₁ᵀ,
        (transporter_factor_mixed hε₁ hε₂ hε₃ hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.1⟩,
      ⟨g.1.2.2.toBlocks₁₂ * g.1.2.2.toBlocks₁₁ᵀ,
        (transporter_factor_mixed hε₁ hε₂ hε₃ hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.2⟩),
     ⟨(g.1.1.toBlocks₁₁, g.1.2.1.toBlocks₁₁, g.1.2.2.toBlocks₁₁),
        (transporter_factor_mixed hε₁ hε₂ hε₃ hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).1⟩)
  invFun x :=
    ⟨(unip x.1.1.1 * hypLift x.2.1.1, unip x.1.2.1.1 * hypLift x.2.1.2.1,
        unip x.1.2.2.1 * hypLift x.2.1.2.2),
      transporter_of_factor_mixed x.1.1.2 x.1.2.1.2 x.1.2.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2⟩
  left_inv g := by
    obtain ⟨⟨P, Q, R⟩, hP, hQ, hR, h⟩ := g
    obtain ⟨-, -, hPeq, hQeq, hReq⟩ := transporter_factor_mixed hε₁ hε₂ hε₃ hA hP hQ hR h
    apply Subtype.ext
    show (unip (P.toBlocks₁₂ * P.toBlocks₁₁ᵀ) * hypLift P.toBlocks₁₁,
      unip (Q.toBlocks₁₂ * Q.toBlocks₁₁ᵀ) * hypLift Q.toBlocks₁₁,
      unip (R.toBlocks₁₂ * R.toBlocks₁₁ᵀ) * hypLift R.toBlocks₁₁) = (P, Q, R)
    rw [← hPeq, ← hQeq, ← hReq]
  right_inv x := by
    obtain ⟨⟨⟨U₁, hU₁⟩, ⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩⟩, ⟨⟨a₁, a₂, a₃⟩, ha₁, ha₂, ha₃, h⟩⟩ := x
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
      (Subtype.ext ?_)
    · exact toBlocks₁₂_unip_mul_hypLift U₁ a₁ ha₁
    · exact toBlocks₁₂_unip_mul_hypLift U₂ a₂ ha₂
    · exact toBlocks₁₂_unip_mul_hypLift U₃ a₃ ha₃
    · show (_, _, _) = (a₁, a₂, a₃)
      rw [toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift, toBlocks₁₁_unip_mul_hypLift]

theorem natCard_mixedTrans {ε₁ ε₂ ε₃ : K} (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hε₃ : ε₃ ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (MixedTrans ε₁ ε₂ ε₃ A B) =
      Nat.card (EpsMat ε₁ n) * Nat.card (EpsMat ε₂ n) * Nat.card (EpsMat ε₃ n) *
        Nat.card (GLTrans A B) := by
  rw [Nat.card_congr (mixedTransporterEquiv hε₁ hε₂ hε₃ hA), Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

/-- Concrete mixed count over a finite field of characteristic `≠ 2`: symplectic on the first mode
and split orthogonal on the other two gives the fiber `q^{C(n+1,2) + 2·C(n,2)}`. -/
theorem natCard_mixedTrans_sp_o_o [Finite K] (h2 : (2 : K) ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (MixedTrans (-1 : K) 1 1 A B) =
      Nat.card K ^ ((n + 1).choose 2 + 2 * n.choose 2) * Nat.card (GLTrans A B) := by
  have hskew : Nat.card (EpsMat (1 : K) n) = Nat.card K ^ (n.choose 2) := by
    rw [Nat.card_congr (epsMatOneEquiv (K := K) (n := n))]
    exact SkewMatCard.natCard_skew h2
  have hsym : Nat.card (EpsMat (-1 : K) n) = Nat.card K ^ ((n + 1).choose 2) := by
    rw [Nat.card_congr (epsMatNegOneEquiv (K := K) (n := n))]
    exact SymMatCard.natCard_symm
  rw [natCard_mixedTrans (by norm_num) one_ne_zero one_ne_zero hA, hsym, hskew, two_mul,
    pow_add, pow_add]
  ring

/-! ## The determinant-one refinement (`TI_SL` frontier) -/

/-- Isometry transporters that additionally have determinant one. -/
def SIsoTrans (ε : K) (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (S n) (S n) K × Matrix (S n) (S n) K × Matrix (S n) (S n) K //
    (IsIsometry n ε g.1 ∧ IsIsometry n ε g.2.1 ∧ IsIsometry n ε g.2.2 ∧
        act3D K g.1 g.2.1 g.2.2 (padArr A) = padArr B) ∧
      (g.1.det = 1 ∧ g.2.1.det = 1 ∧ g.2.2.det = 1)}

/-- **Imposing `det = 1` does not shrink the padded transporter set**: every isometry transporter
of a padded concise tensor is already special.  So at the level of these transporters the
`SO`-problem and the `O`-problem coincide. -/
def sIsoTransEquiv {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    SIsoTrans ε A B ≃ IsoTrans ε A B where
  toFun g := ⟨g.1, g.2.1⟩
  invFun g := ⟨g.1, g.2, det_eq_one_of_transporter hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem natCard_sIsoTrans {ε : K} (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K}
    (hA : Concise A) :
    Nat.card (SIsoTrans ε A B) = Nat.card (EpsMat ε n) ^ 3 * Nat.card (GLTrans A B) := by
  rw [Nat.card_congr (sIsoTransEquiv hε hA)]
  exact natCard_isoTrans hε hA

end Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers

#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.iso_factor
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.isoTransporterEquiv
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_isoTrans
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_isoTrans_neg_one
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_isoTrans_one
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_isoTrans_one_of_two_eq_zero
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.isoTrans_equiv_glTrans_of_sq_ne_one
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.tiIso_rel_pad_iff
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.det_eq_one_of_transporter
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.mixedTransporterEquiv
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_mixedTrans
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_mixedTrans_sp_o_o
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.sIsoTransEquiv
#print axioms Mathproof.LibraryBridges.Claude.TIIsoTransporterFibers.natCard_sIsoTrans

end Part_U36


section Part_U37


/-!
# The padded-transporter technique for the **unitary** groups `U(Φ_ε, σ)`

Third run of the technique of `TISpTransporterFibers` (symplectic) and `TIIsoTransporterFibers`
(every hyperbolic bilinear form).  Here the form is sesquilinear for a field involution `σ`:
`IsUnitary σ n ε g` is `(σ g)ᵀ Φ_ε g = Φ_ε` (`TIGroupLeviGen20260902`), the Levi lift is
`uLift σ P = diag(P, σ(P⁻ᵀ))`, and the unipotent radical is cut out by the **`ε`-hermitian**
condition `(σ U)ᵀ = -(ε • U)`.

Main results (concise `A`, every field, every involution `σ`, every `ε ≠ 0`):

* `unitary_factor` — a unitary matrix with `M₂₁ = 0` factors uniquely as `[[1,U],[0,1]] · uLift σ a`
  with `U = M₁₂ (σ M₁₁)ᵀ` `ε`-hermitian;
* `unitaryTransporterEquiv` / `natCard_uTrans` —
  `Trans_{U(Φ_ε,σ)}(ι A, ι B) ≃ HermMat σ ε³ × Trans_{GL}(A, B)` and its count;
* `eq_zero_of_epsHerm_of_norm_ne_one` — **the rigidity threshold is the norm**: the fiber collapses
  to `0` unless `σ(ε) · ε = 1`.  For `σ = id` this is the `ε² = 1` trichotomy of
  `TIIsoTransporterFibers`, so the two classical bilinear families are the `σ = id` case of one
  norm-one condition;
* `tiUnitary_rel_pad_iff` — the relation-level corollary;
* `epsHerm_id_iff` / `uTrans_eq_isoTrans_of_id` — with `σ = id` everything specialises back to the
  isometry statements, so this module strictly extends the previous two.

Not attempted here: the finite-field count of `ε`-hermitian matrices over `F_{q²}` with `σ` the
Frobenius (it is `q^{n²}`, but that needs the fixed-field cardinality `√|K|`, which is extra
structure); the counts proved here are `SymMatCard`/`SkewMatCard` through `σ = id`.
-/

open scoped Matrix

open Matrix

namespace Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers

open Mathproof.Meta.ProjectionReductions20260902
open Mathproof.Meta.PaddingProjection20260902
open Mathproof.Meta.TIGroupLevi20260902
open Mathproof.Meta.TIGroupLeviGen20260902
open Mathproof.LibraryBridges.Claude.TISpTransporterFibers

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ## Entrywise `σ` on matrices -/

theorem map_smul' (σ : K →+* K) (c : K) (U : Matrix (Fin n) (Fin n) K) :
    (c • U).map σ = σ c • U.map σ := by
  ext i j
  simp [Matrix.map_apply, smul_eq_mul, map_mul]

theorem map_neg' (σ : K →+* K) (U : Matrix (Fin n) (Fin n) K) : (-U).map σ = -(U.map σ) := by
  ext i j
  simp [Matrix.map_apply]

theorem map_map_self {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) (U : Matrix (Fin n) (Fin n) K) :
    (U.map σ).map σ = U := by
  rw [Matrix.map_map]
  have h : (⇑σ ∘ ⇑σ) = id := funext hσ
  rw [h, Matrix.map_id]

theorem det_map (σ : K →+* K) (a : Matrix (Fin n) (Fin n) K) : (a.map σ).det = σ a.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

/-! ## The `ε`-hermitian condition cut out by the unipotent radical -/

/-- The condition making `[[1,U],[0,1]]` unitary for `Φ_ε`: `(σ U)ᵀ = -(ε • U)`. -/
def EpsHerm (σ : K →+* K) (ε : K) (U : Matrix (Fin n) (Fin n) K) : Prop :=
  (U.map σ)ᵀ = -(ε • U)

theorem epsHerm_zero (σ : K →+* K) (ε : K) :
    EpsHerm σ ε (0 : Matrix (Fin n) (Fin n) K) := by
  simp [EpsHerm, Matrix.map_zero _ (map_zero σ)]

/-- With `σ = id` the `ε`-hermitian condition is the `ε`-symmetric one. -/
theorem epsHerm_id_iff {ε : K} {U : Matrix (Fin n) (Fin n) K} :
    EpsHerm (RingHom.id K) ε U ↔ TIIsoTransporterFibers.EpsSymm ε U := by
  simp [EpsHerm, TIIsoTransporterFibers.EpsSymm]

/-- **Rigidity, norm form**: unless `σ(ε) · ε = 1` the only `ε`-hermitian matrix is `0`.
For `σ = id` this is `ε² ≠ 1 → U = 0`. -/
theorem eq_zero_of_epsHerm_of_norm_ne_one {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K}
    (hN : σ ε * ε ≠ 1) {U : Matrix (Fin n) (Fin n) K} (hU : EpsHerm σ ε U) : U = 0 := by
  have h1 : U.map σ = -(ε • Uᵀ) := by
    have h := congrArg Matrix.transpose hU
    rwa [transpose_transpose, transpose_neg, transpose_smul] at h
  have h2 : U = (σ ε * ε) • U := by
    calc U = (U.map σ).map σ := (map_map_self hσ U).symm
      _ = (-(ε • Uᵀ)).map σ := by rw [h1]
      _ = -(σ ε • (Uᵀ.map σ)) := by rw [map_neg', map_smul']
      _ = -(σ ε • (U.map σ)ᵀ) := by rw [← Matrix.transpose_map]
      _ = -(σ ε • -(ε • U)) := by rw [hU]
      _ = (σ ε * ε) • U := by rw [smul_neg, neg_neg, smul_smul]
  have h3 : (1 - σ ε * ε) • U = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  have h4 : (1 : K) - σ ε * ε ≠ 0 := sub_ne_zero.mpr fun hc => hN hc.symm
  exact (smul_eq_zero.mp h3).resolve_left h4

/-! ## The unitary group: unipotent part, Levi lift, factorization -/

theorem isUnitary_mul {σ : K →+* K} {ε : K} {g h : Matrix (S n) (S n) K}
    (hg : IsUnitary σ n ε g) (hh : IsUnitary σ n ε h) : IsUnitary σ n ε (g * h) := by
  unfold IsUnitary at *
  calc ((g * h).map σ)ᵀ * hypForm n ε * (g * h)
      = (h.map σ)ᵀ * ((g.map σ)ᵀ * hypForm n ε * g) * h := by
        rw [Matrix.map_mul, transpose_mul]; simp only [Matrix.mul_assoc]
    _ = hypForm n ε := by rw [hg, hh]

theorem isUnitary_unip {σ : K →+* K} {ε : K} {U : Matrix (Fin n) (Fin n) K} (hU : EpsHerm σ ε U) :
    IsUnitary σ n ε (unip U) := by
  unfold IsUnitary hypForm unip
  rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ),
    Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_zero, zero_add, add_zero]
  rw [hU]
  simp

/-- `[[1,U],[0,1]] · diag(a, σ(a⁻ᵀ))`. -/
theorem unip_mul_uLift (σ : K →+* K) (U a : Matrix (Fin n) (Fin n) K) :
    unip U * uLift σ a = fromBlocks a (U * (a⁻¹ᵀ).map σ) 0 ((a⁻¹ᵀ).map σ) := by
  simp [unip, uLift, blockLift, fromBlocks_multiply]

theorem unip_mul_uLift_apply_inl (σ : K →+* K) (U a : Matrix (Fin n) (Fin n) K) (x : S n)
    (i : Fin n) : (unip U * uLift σ a) x (Sum.inl i) = uLift σ a x (Sum.inl i) := by
  rw [unip_mul_uLift]
  rcases x with x | x <;> simp [uLift, blockLift]

theorem toBlocks₁₁_unip_mul_uLift (σ : K →+* K) (U a : Matrix (Fin n) (Fin n) K) :
    (unip U * uLift σ a).toBlocks₁₁ = a := by
  rw [unip_mul_uLift, toBlocks_fromBlocks₁₁]

/-- The identity `(σ a)ᵀ · σ(a⁻ᵀ) = 1` of `uLift_isUnitary`, isolated. -/
theorem transpose_map_mul_inv (σ : K →+* K) {a : Matrix (Fin n) (Fin n) K} (ha : IsUnit a.det) :
    (a.map σ)ᵀ * (a⁻¹ᵀ).map σ = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul a ha, Matrix.transpose_one, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem toBlocks₁₂_unip_mul_uLift (σ : K →+* K) (U a : Matrix (Fin n) (Fin n) K)
    (ha : IsUnit a.det) :
    (unip U * uLift σ a).toBlocks₁₂ * ((unip U * uLift σ a).toBlocks₁₁.map σ)ᵀ = U := by
  rw [unip_mul_uLift, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₁, Matrix.mul_assoc,
    mul_eq_one_comm.mp (transpose_map_mul_inv σ ha), Matrix.mul_one]

/-- The block equations of a unitary matrix with vanishing lower-left block. -/
theorem unitary_blocks {σ : K →+* K} {ε : K} {M : Matrix (S n) (S n) K} (hM : IsUnitary σ n ε M)
    (hc : M.toBlocks₂₁ = 0) :
    (M.toBlocks₁₁.map σ)ᵀ * M.toBlocks₂₂ = 1 ∧
      ε • ((M.toBlocks₂₂.map σ)ᵀ * M.toBlocks₁₂) +
        (M.toBlocks₁₂.map σ)ᵀ * M.toBlocks₂₂ = 0 := by
  have hMeq : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  unfold IsUnitary hypForm at hM
  rw [hMeq, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero σ), Matrix.fromBlocks_transpose,
    Matrix.transpose_zero] at hM
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_zero, zero_add, add_zero,
    fromBlocks_inj] at hM
  obtain ⟨-, h12, -, h22⟩ := hM
  exact ⟨h12, h22⟩

/-- **Unique factorization** `M = [[1,U],[0,1]] · uLift σ a` with `a = M₁₁` and `U = M₁₂ (σ M₁₁)ᵀ`
`ε`-hermitian. -/
theorem unitary_factor {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K} {M : Matrix (S n) (S n) K}
    (hM : IsUnitary σ n ε M) (hc : M.toBlocks₂₁ = 0) :
    IsUnit M.toBlocks₁₁.det ∧ EpsHerm σ ε (M.toBlocks₁₂ * (M.toBlocks₁₁.map σ)ᵀ) ∧
      M = unip (M.toBlocks₁₂ * (M.toBlocks₁₁.map σ)ᵀ) * uLift σ M.toBlocks₁₁ := by
  obtain ⟨h12, h22⟩ := unitary_blocks hM hc
  set a := M.toBlocks₁₁ with ha_def
  set b := M.toBlocks₁₂ with hb_def
  set d := M.toBlocks₂₂ with hd_def
  have hMeq : M = fromBlocks a b 0 d := by
    rw [← hc]; exact (fromBlocks_toBlocks M).symm
  have hdet : IsUnit a.det := by
    have hd0 := congrArg Matrix.det h12
    rw [det_mul, det_transpose, det_map, det_one] at hd0
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero, zero_mul] at hd0
    exact zero_ne_one hd0
  have hc1 : IsUnit ((a.map σ)ᵀ).det := by
    rw [det_transpose, det_map]
    exact hdet.map σ
  have hd : d = (a⁻¹ᵀ).map σ :=
    (Matrix.inv_eq_right_inv h12).symm.trans (Matrix.inv_eq_right_inv (transpose_map_mul_inv σ hdet))
  have hdc : d * (a.map σ)ᵀ = 1 := by
    rw [hd]
    exact mul_eq_one_comm.mp (transpose_map_mul_inv σ hdet)
  have hdmap : (d.map σ)ᵀ = a⁻¹ := by
    rw [hd, map_map_self hσ, transpose_transpose]
  have h22' : (b.map σ)ᵀ * d = -(ε • (a⁻¹ * b)) := by
    rw [hdmap] at h22
    calc (b.map σ)ᵀ * d
        = -(ε • (a⁻¹ * b)) + (ε • (a⁻¹ * b) + (b.map σ)ᵀ * d) := by abel
      _ = -(ε • (a⁻¹ * b)) := by rw [h22, add_zero]
  have hherm : EpsHerm σ ε (b * (a.map σ)ᵀ) := by
    unfold EpsHerm
    have hmap : ((b * (a.map σ)ᵀ).map σ)ᵀ = a * (b.map σ)ᵀ := by
      rw [Matrix.map_mul, ← Matrix.transpose_map, map_map_self hσ, transpose_mul,
        transpose_transpose]
    rw [hmap]
    calc a * (b.map σ)ᵀ
        = a * ((b.map σ)ᵀ * (d * (a.map σ)ᵀ)) := by
          rw [hdc, Matrix.mul_one]
      _ = a * ((b.map σ)ᵀ * d) * (a.map σ)ᵀ := by simp only [Matrix.mul_assoc]
      _ = a * (-(ε • (a⁻¹ * b))) * (a.map σ)ᵀ := by rw [h22']
      _ = -(ε • (a * (a⁻¹ * b) * (a.map σ)ᵀ)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = -(ε • (b * (a.map σ)ᵀ)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a hdet, Matrix.one_mul]
  have hb : b = b * (a.map σ)ᵀ * ((a⁻¹ᵀ).map σ) := by
    rw [Matrix.mul_assoc, transpose_map_mul_inv σ hdet, Matrix.mul_one]
  refine ⟨hdet, hherm, ?_⟩
  rw [unip_mul_uLift, ← hb, hMeq, hd]

/-! ## The transporter classification for `U(Φ_ε, σ)` -/

theorem transporter_factor_unitary {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K} (hε : ε ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) {P Q R : Matrix (S n) (S n) K}
    (hP : IsUnitary σ n ε P) (hQ : IsUnitary σ n ε Q) (hR : IsUnitary σ n ε R)
    (h : act3D K P Q R (padArr A) = padArr B) :
    (IsUnit P.toBlocks₁₁.det ∧ IsUnit Q.toBlocks₁₁.det ∧ IsUnit R.toBlocks₁₁.det ∧
        act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A = B) ∧
      (EpsHerm σ ε (P.toBlocks₁₂ * (P.toBlocks₁₁.map σ)ᵀ) ∧
        EpsHerm σ ε (Q.toBlocks₁₂ * (Q.toBlocks₁₁.map σ)ᵀ) ∧
        EpsHerm σ ε (R.toBlocks₁₂ * (R.toBlocks₁₁.map σ)ᵀ)) ∧
      (P = unip (P.toBlocks₁₂ * (P.toBlocks₁₁.map σ)ᵀ) * uLift σ P.toBlocks₁₁ ∧
        Q = unip (Q.toBlocks₁₂ * (Q.toBlocks₁₁.map σ)ᵀ) * uLift σ Q.toBlocks₁₁ ∧
        R = unip (R.toBlocks₁₂ * (R.toBlocks₁₁.map σ)ᵀ) * uLift σ R.toBlocks₁₁) := by
  have hPd : IsUnit P.det := isUnit_det_of_unitary σ ε hε hP
  have hQd : IsUnit Q.det := isUnit_det_of_unitary σ ε hε hQ
  have hRd : IsUnit R.det := isUnit_det_of_unitary σ ε hε hR
  have hPc := toBlocks₂₁_eq_zero₁ hA.1 hQd hRd h
  have hQc := toBlocks₂₁_eq_zero₂ hA.2.1 hPd hRd h
  have hRc := toBlocks₂₁_eq_zero₃ hA.2.2 hPd hQd h
  obtain ⟨hPdet, hPh, hPeq⟩ := unitary_factor hσ hP hPc
  obtain ⟨hQdet, hQh, hQeq⟩ := unitary_factor hσ hQ hQc
  obtain ⟨hRdet, hRh, hReq⟩ := unitary_factor hσ hR hRc
  have hact : padArr (act3 K P.toBlocks₁₁ Q.toBlocks₁₁ R.toBlocks₁₁ A) = padArr B := by
    rw [← act3D_padArr_of_toBlocks₂₁ hPc hQc hRc]; exact h
  exact ⟨⟨hPdet, hQdet, hRdet, padArr_injective hact⟩, ⟨hPh, hQh, hRh⟩, ⟨hPeq, hQeq, hReq⟩⟩

theorem transporter_of_factor_unitary {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K}
    {A B : Fin n × Fin n × Fin n → K} {U₁ U₂ U₃ a₁ a₂ a₃ : Matrix (Fin n) (Fin n) K}
    (hU₁ : EpsHerm σ ε U₁) (hU₂ : EpsHerm σ ε U₂) (hU₃ : EpsHerm σ ε U₃)
    (ha₁ : IsUnit a₁.det) (ha₂ : IsUnit a₂.det) (ha₃ : IsUnit a₃.det)
    (h : act3 K a₁ a₂ a₃ A = B) :
    IsUnitary σ n ε (unip U₁ * uLift σ a₁) ∧ IsUnitary σ n ε (unip U₂ * uLift σ a₂) ∧
      IsUnitary σ n ε (unip U₃ * uLift σ a₃) ∧
      act3D K (unip U₁ * uLift σ a₁) (unip U₂ * uLift σ a₂) (unip U₃ * uLift σ a₃) (padArr A) =
        padArr B := by
  refine ⟨isUnitary_mul (isUnitary_unip hU₁) (uLift_isUnitary σ hσ ε a₁ ha₁),
    isUnitary_mul (isUnitary_unip hU₂) (uLift_isUnitary σ hσ ε a₂ ha₂),
    isUnitary_mul (isUnitary_unip hU₃) (uLift_isUnitary σ hσ ε a₃ ha₃), ?_⟩
  rw [act3D_padArr_congr A (unip_mul_uLift_apply_inl σ U₁ a₁) (unip_mul_uLift_apply_inl σ U₂ a₂)
    (unip_mul_uLift_apply_inl σ U₃ a₃)]
  unfold uLift
  rw [act3D_blockLift_padArr, h]

/-- `ε`-hermitian matrices: the unipotent radical of the Siegel parabolic of `U(Φ_ε, σ)`. -/
def HermMat (σ : K →+* K) (ε : K) (n : ℕ) := {U : Matrix (Fin n) (Fin n) K // EpsHerm σ ε U}

/-- Unitary transporters between the paddings. -/
def UTrans (σ : K →+* K) (ε : K) (A B : Fin n × Fin n × Fin n → K) :=
  {g : Matrix (S n) (S n) K × Matrix (S n) (S n) K × Matrix (S n) (S n) K //
    IsUnitary σ n ε g.1 ∧ IsUnitary σ n ε g.2.1 ∧ IsUnitary σ n ε g.2.2 ∧
      act3D K g.1 g.2.1 g.2.2 (padArr A) = padArr B}

/-- **`Trans_{U(Φ_ε,σ)}(ι A, ι B) ≃ HermMat σ ε³ × Trans_{GL}(A, B)`** for concise `A`. -/
noncomputable def unitaryTransporterEquiv {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K}
    (hε : ε ≠ 0) {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    UTrans σ ε A B ≃ (HermMat σ ε n × HermMat σ ε n × HermMat σ ε n) × GLTrans A B where
  toFun g :=
    ((⟨g.1.1.toBlocks₁₂ * (g.1.1.toBlocks₁₁.map σ)ᵀ,
        (transporter_factor_unitary hσ hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.1⟩,
      ⟨g.1.2.1.toBlocks₁₂ * (g.1.2.1.toBlocks₁₁.map σ)ᵀ,
        (transporter_factor_unitary hσ hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.1⟩,
      ⟨g.1.2.2.toBlocks₁₂ * (g.1.2.2.toBlocks₁₁.map σ)ᵀ,
        (transporter_factor_unitary hσ hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).2.1.2.2⟩),
     ⟨(g.1.1.toBlocks₁₁, g.1.2.1.toBlocks₁₁, g.1.2.2.toBlocks₁₁),
        (transporter_factor_unitary hσ hε hA g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2).1⟩)
  invFun x :=
    ⟨(unip x.1.1.1 * uLift σ x.2.1.1, unip x.1.2.1.1 * uLift σ x.2.1.2.1,
        unip x.1.2.2.1 * uLift σ x.2.1.2.2),
      transporter_of_factor_unitary hσ x.1.1.2 x.1.2.1.2 x.1.2.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2⟩
  left_inv g := by
    obtain ⟨⟨P, Q, R⟩, hP, hQ, hR, h⟩ := g
    obtain ⟨-, -, hPeq, hQeq, hReq⟩ := transporter_factor_unitary hσ hε hA hP hQ hR h
    apply Subtype.ext
    show (unip (P.toBlocks₁₂ * (P.toBlocks₁₁.map σ)ᵀ) * uLift σ P.toBlocks₁₁,
      unip (Q.toBlocks₁₂ * (Q.toBlocks₁₁.map σ)ᵀ) * uLift σ Q.toBlocks₁₁,
      unip (R.toBlocks₁₂ * (R.toBlocks₁₁.map σ)ᵀ) * uLift σ R.toBlocks₁₁) = (P, Q, R)
    rw [← hPeq, ← hQeq, ← hReq]
  right_inv x := by
    obtain ⟨⟨⟨U₁, hU₁⟩, ⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩⟩, ⟨⟨a₁, a₂, a₃⟩, ha₁, ha₂, ha₃, h⟩⟩ := x
    refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
      (Subtype.ext ?_)
    · exact toBlocks₁₂_unip_mul_uLift σ U₁ a₁ ha₁
    · exact toBlocks₁₂_unip_mul_uLift σ U₂ a₂ ha₂
    · exact toBlocks₁₂_unip_mul_uLift σ U₃ a₃ ha₃
    · show (_, _, _) = (a₁, a₂, a₃)
      rw [toBlocks₁₁_unip_mul_uLift, toBlocks₁₁_unip_mul_uLift, toBlocks₁₁_unip_mul_uLift]

theorem natCard_uTrans {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K} (hε : ε ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    Nat.card (UTrans σ ε A B) = Nat.card (HermMat σ ε n) ^ 3 * Nat.card (GLTrans A B) := by
  rw [Nat.card_congr (unitaryTransporterEquiv hσ hε hA), Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

/-- **Rigidity for the unitary family**: if the norm `σ(ε)·ε` is not `1`, the padded unitary
transporters are exactly the `GL` transporters. -/
noncomputable def uTrans_equiv_glTrans_of_norm_ne_one {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
    {ε : K} (hε : ε ≠ 0) (hN : σ ε * ε ≠ 1) {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    UTrans σ ε A B ≃ GLTrans A B :=
  (unitaryTransporterEquiv hσ hε hA).trans
    { toFun := fun x => x.2
      invFun := fun g =>
        ((⟨0, epsHerm_zero σ ε⟩, ⟨0, epsHerm_zero σ ε⟩, ⟨0, epsHerm_zero σ ε⟩), g)
      left_inv := fun x => by
        obtain ⟨⟨U₁, U₂, U₃⟩, g⟩ := x
        refine Prod.ext (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))) rfl
        · exact (eq_zero_of_epsHerm_of_norm_ne_one hσ hN U₁.2).symm ▸ rfl
        · exact (eq_zero_of_epsHerm_of_norm_ne_one hσ hN U₂.2).symm ▸ rfl
        · exact (eq_zero_of_epsHerm_of_norm_ne_one hσ hN U₃.2).symm ▸ rfl
      right_inv := fun _ => rfl }

/-- Relation-level corollary for the unitary family. -/
theorem tiUnitary_rel_pad_iff {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x) {ε : K} (hε : ε ≠ 0)
    {A B : Fin n × Fin n × Fin n → K} (hA : Concise A) :
    (TIUnitary σ ε).Rel n (padArr A) (padArr B) ↔ (GL3TI K).Rel n A B := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR, h⟩
    obtain ⟨⟨hPd, hQd, hRd, hact⟩, -, -⟩ := transporter_factor_unitary hσ hε hA hP hQ hR h
    exact ⟨P.toBlocks₁₁, Q.toBlocks₁₁, R.toBlocks₁₁, (Matrix.isUnit_iff_isUnit_det _).mpr hPd,
      (Matrix.isUnit_iff_isUnit_det _).mpr hQd, (Matrix.isUnit_iff_isUnit_det _).mpr hRd, hact⟩
  · rintro ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h⟩
    obtain ⟨h₁, h₂, h₃, hact⟩ := transporter_of_factor_unitary (A := A) (B := B) hσ
      (epsHerm_zero σ ε) (epsHerm_zero σ ε) (epsHerm_zero σ ε)
      ((Matrix.isUnit_iff_isUnit_det a₁).mp ha₁) ((Matrix.isUnit_iff_isUnit_det a₂).mp ha₂)
      ((Matrix.isUnit_iff_isUnit_det a₃).mp ha₃) h
    exact ⟨_, _, _, h₁, h₂, h₃, hact⟩

/-- With `σ = id` the unitary transporters are the isometry transporters of
`TIIsoTransporterFibers`: this module extends that one. -/
theorem uTrans_eq_isoTrans_of_id {ε : K} {A B : Fin n × Fin n × Fin n → K} :
    UTrans (RingHom.id K) ε A B = TIIsoTransporterFibers.IsoTrans ε A B := by
  unfold UTrans TIIsoTransporterFibers.IsoTrans
  simp only [isUnitary_id_iff]

end Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers

#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.eq_zero_of_epsHerm_of_norm_ne_one
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.unitary_factor
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.unitaryTransporterEquiv
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.natCard_uTrans
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.uTrans_equiv_glTrans_of_norm_ne_one
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.tiUnitary_rel_pad_iff
#print axioms Mathproof.LibraryBridges.Claude.TIUnitaryTransporterFibers.uTrans_eq_isoTrans_of_id

end Part_U37

