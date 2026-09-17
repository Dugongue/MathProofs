import Mathlib

/-! Tensor order reduction over arbitrary fields.

The construction preserves isomorphism exactly, with total output dimension
bounded by an absolute constant times n^ceil(d/3). The final theorems cover
arbitrary ordered shapes and give a polynomial bound in the dense input size.
-/

noncomputable section
namespace TensorOrderReduction

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 500000
set_option linter.unusedSectionVars false

/- Superincreasing rank weights. -/
section

open Finset

variable {m : ℕ}

/-- **Superincreasing with slack `σ`**: every weight exceeds the total of all strictly lighter
weights by more than `σ`. -/
def SuperIncr (ρ : Fin m → ℕ) (σ : ℕ) : Prop :=
  ∀ i : Fin m, (∑ j ∈ univ.filter (fun j => j < i), ρ j) + σ < ρ i

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

end

/- Coordinate rigidity. -/
section
variable {K : Type*} [Field K]

def shift {n : ℕ} (v : Fin n → K) (i : Fin n) : K :=
  if h : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0

-- Adapted from TISLRigidLabels.shift_single in the existing workspace proof.
theorem shift_single {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    shift (Pi.single i (1 : K)) = Pi.single ⟨i.val + 1, hi⟩ 1 := by
  ext j
  by_cases hp : 0 < j.val
  · simp only [shift, dif_pos hp]
    by_cases he : j.val = i.val + 1
    · have hj : j = ⟨i.val + 1, hi⟩ := Fin.ext he
      subst j
      simp
    · have hji : j ≠ ⟨i.val + 1, hi⟩ := by
        intro h; exact he (congrArg Fin.val h)
      have hpred : (⟨j.val - 1, by omega⟩ : Fin n) ≠ i := by
        intro h
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [Pi.single_eq_of_ne hpred, Pi.single_eq_of_ne hji]
  · have hji : j ≠ ⟨i.val + 1, hi⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    simp [shift, hp, Pi.single_eq_of_ne hji]

/-- The explicit first basis vector and shift have trivial common stabilizer. -/
theorem first_shift_rigid {n : ℕ} (hn : 0 < n)
    (H : (Fin n → K) →ₗ[K] (Fin n → K))
    (hfirst : H (Pi.single ⟨0,hn⟩ 1) = Pi.single ⟨0,hn⟩ 1)
    (hshift : ∀ x, H (shift x) = shift (H x)) :
    H = LinearMap.id := by
  have hb : ∀ k (hk : k < n), H (Pi.single ⟨k,hk⟩ 1) = Pi.single ⟨k,hk⟩ 1 := by
    intro k
    induction k with
    | zero => intro hk; exact hfirst
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      rw [← shift_single (⟨k,hk'⟩ : Fin n) hk, hshift, ih hk']
  apply LinearMap.ext
  intro x
  have hx : x = ∑ j : Fin n, x j • Pi.single j (1 : K) := by
    ext j
    simp [Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum,map_smul,hb]
  exact hx.symm

section Blocks
variable {I : Type*} [DecidableEq I] {V : I → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Commutation with the named coordinate projectors. -/
def PreservesBlocks (F : (∀ i, V i) →ₗ[K] (∀ i, V i)) : Prop :=
  ∀ i x, F (Pi.single i (x i)) = Pi.single i (F x i)

def coordinateMap (F : (∀ i, V i) →ₗ[K] (∀ i, V i)) (i : I) : V i →ₗ[K] V i :=
  (LinearMap.proj i).comp (F.comp (LinearMap.single K V i))

theorem coordinateMap_apply (F : (∀ i, V i) →ₗ[K] (∀ i, V i))
    (hF : PreservesBlocks F) (i : I) (x : ∀ i, V i) :
    coordinateMap F i (x i) = F x i := by
  have h := congrFun (hF i x) i
  simpa [coordinateMap] using h

theorem supported_image (F : (∀ i, V i) →ₗ[K] (∀ i, V i))
    (hF : PreservesBlocks F) (i : I) (v : V i) :
    F (Pi.single i v) = Pi.single i (coordinateMap F i v) := by
  simpa [coordinateMap] using hF i (Pi.single i v)

/-- Every recovered coordinate map is invertible; invertibility is not assumed. -/
theorem coordinateMap_bijective (F : (∀ i, V i) ≃ₗ[K] (∀ i, V i))
    (hF : PreservesBlocks F.toLinearMap) (i : I) :
    Function.Bijective (coordinateMap F.toLinearMap i) := by
  constructor
  · intro x y h
    have hs : F (Pi.single i x) = F (Pi.single i y) := by
      change F.toLinearMap (Pi.single i x) = F.toLinearMap (Pi.single i y)
      rw [supported_image F.toLinearMap hF, supported_image F.toLinearMap hF, h]
    have hs' := congrFun (F.injective hs) i
    simpa using hs'
  · intro y
    obtain ⟨x,hx⟩ := F.surjective (Pi.single i y)
    refine ⟨x i, ?_⟩
    rw [coordinateMap_apply F.toLinearMap hF]
    change F x i = y
    rw [hx]
    simp

noncomputable def coordinateEquiv (F : (∀ i, V i) ≃ₗ[K] (∀ i, V i))
    (hF : PreservesBlocks F.toLinearMap) (i : I) : V i ≃ₗ[K] V i :=
  LinearEquiv.ofBijective (coordinateMap F.toLinearMap i) (coordinateMap_bijective F hF i)

/-- Sufficient block-recovery theorem for arbitrary, unequal named spaces. -/
theorem reconstruct_blocks (F : (∀ i, V i) ≃ₗ[K] (∀ i, V i))
    (hF : PreservesBlocks F.toLinearMap) :
    LinearEquiv.piCongrRight (coordinateEquiv F hF) = F := by
  ext x i
  exact coordinateMap_apply F.toLinearMap hF i x

theorem piCongr_single (g : ∀ i, V i ≃ₗ[K] V i) (i : I) (x : V i) :
    LinearEquiv.piCongrRight g (Pi.single i x) = Pi.single i (g i x) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

theorem piCongr_preservesBlocks (g : ∀ i, V i ≃ₗ[K] V i) :
    PreservesBlocks (LinearEquiv.piCongrRight g).toLinearMap := by
  intro i x
  exact piCongr_single g i (x i)

/-- The projector equations characterize exactly products of independent GL actions. -/
theorem preservesBlocks_iff (F : (∀ i, V i) ≃ₗ[K] (∀ i, V i)) :
    PreservesBlocks F.toLinearMap ↔
      ∃ g : ∀ i, V i ≃ₗ[K] V i, LinearEquiv.piCongrRight g = F := by
  constructor
  · intro hF; exact ⟨coordinateEquiv F hF, reconstruct_blocks F hF⟩
  · rintro ⟨g,rfl⟩; exact piCongr_preservesBlocks g

section Occurrences
variable {A : Type*} [Fintype A] [DecidableEq A] (under : A → I)

/-- The explicit map summing each private occurrence into its original named space. -/
def copyMap : (∀ a, V (under a)) →ₗ[K] (∀ i, V i) :=
  LinearMap.lsum K (fun a => V (under a)) K (fun a => LinearMap.single K V (under a))

@[simp] theorem copyMap_single (a : A) (x : V (under a)) :
    copyMap (K := K) under (Pi.single a x) = Pi.single (under a) x := by
  unfold copyMap
  rw [LinearMap.lsum_piSingle]
  rfl

/-- Preservation of the occurrence-copy map forces exactly the required identifications. -/
theorem copyMap_transport_iff (g : ∀ i, V i ≃ₗ[K] V i)
    (h : ∀ a, V (under a) ≃ₗ[K] V (under a)) :
    (LinearEquiv.piCongrRight g).toLinearMap.comp (copyMap (K := K) under) =
      (copyMap (K := K) under).comp (LinearEquiv.piCongrRight h).toLinearMap ↔
    ∀ a, h a = g (under a) := by
  constructor
  · intro he a
    ext x
    have hv := LinearMap.congr_fun he (Pi.single a x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, copyMap_single,
      piCongr_single] at hv
    have hv' := congrFun hv (under a)
    simpa using hv'.symm
  · intro he
    apply LinearMap.pi_ext
    intro a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, copyMap_single,
      piCongr_single, he]

end Occurrences
end Blocks
end

/- Deleting one partition. -/
section
open Module
noncomputable local instance {K : Type*} : DecidableEq K := Classical.decEq K
variable {K : Type*} [Field K]
variable {I : Type*} {V : Type*} {U E : I → Type*}
  [AddCommGroup V] [Module K V]
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

abbrev ColSpace (V : Type*) (U E : I → Type*) := V × (∀ i, U i) × (∀ i, E i)
abbrev RowSpace (V : Type*) (U E : I → Type*) := (∀ i, U i) × (I → V) × (∀ i, E i)

/-- A linear combination of the data slices and the new identity gadgets. -/
def mixedSlice (X : V →ₗ[K] (∀ i, U i)) (q : I → K) :
    ColSpace V U E →ₗ[K] RowSpace V U E where
  toFun x := (X x.1 + fun i => q i • x.2.1 i,
    (fun i => q i • x.1), fun i => q i • x.2.2 i)
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' a x := by ext <;> simp [smul_add,smul_smul,mul_comm]

/-- Extend the supported coordinates by zero and multiply by their nonzero coefficients. -/
noncomputable def supportEmbed (q : I → K) :
    (∀ i : {i // q i ≠ 0}, U i.val) →ₗ[K] (∀ i, U i) := by
  classical
  exact {
    toFun := fun x i => if h : q i ≠ 0 then q i • x ⟨i,h⟩ else 0
    map_add' := by intros; ext i; split_ifs <;> simp_all [smul_add]
    map_smul' := by intros; ext i; split_ifs <;> simp_all [smul_smul,mul_comm]
  }

theorem supportEmbed_injective (q : I → K) :
    Function.Injective (supportEmbed (U := U) q) := by
  classical
  intro x y h
  ext i
  have hi := congrFun h i.val
  simp only [supportEmbed,LinearMap.coe_mk,AddHom.coe_mk,dif_pos i.property] at hi
  exact (smul_right_injective _ i.property) hi

/-- Recover the original column vector from any nonzero gadget coordinate. -/
theorem mixedSlice_kernel {q : I → K} (hq : ∃ i, q i ≠ 0)
    (X : V →ₗ[K] (∀ i, U i)) (x : ColSpace V U E) :
    mixedSlice X q x = 0 ↔
      x.1 = 0 ∧ (∀ i, q i • x.2.1 i = 0) ∧ (∀ i, q i • x.2.2 i = 0) := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := hq
    have hv : q i • x.1 = 0 := congrFun (congrArg (fun z => z.2.1) h) i
    have hv' : x.1 = 0 := (smul_eq_zero.mp hv).resolve_left hi
    refine ⟨hv', ?_, ?_⟩
    · intro j
      have hj := congrFun (congrArg Prod.fst h) j
      simpa [mixedSlice,hv'] using hj
    · intro j
      exact congrFun (congrArg (fun z => z.2.2) h) j
  · rintro ⟨hv,hu,he⟩
    ext <;> simp [mixedSlice,hv,hu,he]

/-- Parametrize the image of an actual mixed slice by precisely its surviving coordinates. -/
noncomputable def imageParam (X : V →ₗ[K] (∀ i, U i)) (q : I → K) :
    (V × (∀ i : {i // q i ≠ 0}, U i.val) × (∀ i : {i // q i ≠ 0}, E i.val))
      →ₗ[K] RowSpace V U E where
  toFun x := (X x.1 + supportEmbed q x.2.1,
    (fun i => q i • x.1), supportEmbed q x.2.2)
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' a x := by ext <;> simp [smul_smul,mul_comm]

theorem imageParam_injective (X : V →ₗ[K] (∀ i, U i)) {q : I → K}
    (hq : ∃ i, q i ≠ 0) : Function.Injective (imageParam (E := E) X q) := by
  intro x y h
  obtain ⟨i,hi⟩ := hq
  have hv : q i • x.1 = q i • y.1 := congrFun (congrArg (fun z => z.2.1) h) i
  have hv' : x.1 = y.1 := (smul_right_injective _ hi) hv
  apply Prod.ext hv'
  apply Prod.ext
  · apply supportEmbed_injective q
    have he := congrArg Prod.fst h
    change X x.1 + supportEmbed q x.2.1 = X y.1 + supportEmbed q y.2.1 at he
    rwa [hv',add_left_cancel_iff] at he
  · exact supportEmbed_injective q (congrArg (fun z => z.2.2) h)

theorem range_mixedSlice (X : V →ₗ[K] (∀ i, U i)) (q : I → K) :
    LinearMap.range (mixedSlice (E := E) X q) = LinearMap.range (imageParam X q) := by
  classical
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨(x.1,(fun i => x.2.1 i.val),fun i => x.2.2 i.val), ?_⟩
    ext <;> simp [imageParam,mixedSlice,supportEmbed] <;> split_ifs <;> simp_all
  · rintro ⟨x,rfl⟩
    let u : ∀ i, U i := fun i => if h : q i ≠ 0 then x.2.1 ⟨i,h⟩ else 0
    let e : ∀ i, E i := fun i => if h : q i ≠ 0 then x.2.2 ⟨i,h⟩ else 0
    refine ⟨(x.1,u,e), ?_⟩
    ext <;> simp [imageParam,mixedSlice,supportEmbed,u,e]

/-- The exact rank formula of the smaller linear-size gadget, with the data term eliminated. -/
theorem mixedSlice_rank [Fintype I] [FiniteDimensional K V]
    [∀ i, FiniteDimensional K (U i)] [∀ i, FiniteDimensional K (E i)]
    (X : V →ₗ[K] (∀ i, U i)) {q : I → K} (hq : ∃ i, q i ≠ 0) :
    finrank K (LinearMap.range (mixedSlice (E := E) X q)) =
      finrank K V + (∑ i : {i // q i ≠ 0}, finrank K (U i.val)) +
        ∑ i : {i // q i ≠ 0}, finrank K (E i.val) := by
  classical
  rw [range_mixedSlice]
  have he := LinearEquiv.finrank_eq
    (LinearEquiv.ofInjective (imageParam (E := E) X q) (imageParam_injective X hq))
  simpa [Module.finrank_prod,Module.finrank_pi_fintype,add_assoc] using he.symm

section Construction
variable [DecidableEq I]

/-- Row transformation extending the independent original block transformations. -/
def rowLift (P : ∀ i, U i ≃ₗ[K] U i) (Q : V ≃ₗ[K] V) :
    RowSpace V U E ≃ₗ[K] RowSpace V U E :=
  (LinearEquiv.piCongrRight P).prodCongr
    ((LinearEquiv.piCongrRight (fun _ : I => Q.symm)).prodCongr (LinearEquiv.refl K _))

/-- Column transformation for the same explicit gadget. -/
def colLift (P : ∀ i, U i ≃ₗ[K] U i) (Q : V ≃ₗ[K] V) :
    ColSpace V U E ≃ₗ[K] ColSpace V U E :=
  Q.prodCongr ((LinearEquiv.piCongrRight (fun i => (P i).symm)).prodCongr
    (LinearEquiv.refl K _))

/-- Exact covariance of the concrete slices, including preservation of every gadget. -/
theorem mixedSlice_covariance (P : ∀ i, U i ≃ₗ[K] U i) (Q : V ≃ₗ[K] V)
    (X : V →ₗ[K] (∀ i, U i)) (q : I → K) :
    (rowLift (E := E) P Q).toLinearMap.comp
      ((mixedSlice (E := E) X q).comp (colLift P Q).toLinearMap) =
    mixedSlice ((LinearEquiv.piCongrRight P).toLinearMap.comp (X.comp Q.toLinearMap)) q := by
  ext x <;> simp [rowLift,colLift,mixedSlice,map_add,map_smul]

theorem mixedSlice_add (X Y : V →ₗ[K] (∀ i, U i)) (q r : I → K) :
    mixedSlice (E := E) (X+Y) (q+r) =
      mixedSlice X q + mixedSlice Y r := by
  ext x <;> simp [mixedSlice,add_smul]

theorem mixedSlice_smul (a : K) (X : V →ₗ[K] (∀ i, U i)) (q : I → K) :
    mixedSlice (E := E) (a • X) (a • q) = a • mixedSlice X q := by
  ext x <;> simp [mixedSlice,smul_add,smul_smul]

/-- The side lengths are genuine dimensions of the constructor's coordinate spaces. -/
theorem construction_dimensions [Fintype I] [FiniteDimensional K V]
    [∀ i, FiniteDimensional K (U i)] [∀ i, FiniteDimensional K (E i)] :
    finrank K (RowSpace V U E) =
      (∑ i, finrank K (U i)) + Fintype.card I * finrank K V + (∑ i, finrank K (E i)) ∧
    finrank K (ColSpace V U E) =
      finrank K V + (∑ i, finrank K (U i)) + (∑ i, finrank K (E i)) := by
  simp [RowSpace,ColSpace,Module.finrank_prod,Module.finrank_pi_fintype,
    Finset.sum_const,add_assoc]

end Construction

section Normalize
/-- A shear is an actual invertible row change, with an explicit inverse. -/
def rowShear (Z : (I → V) →ₗ[K] (∀ i, U i)) :
    RowSpace V U E ≃ₗ[K] RowSpace V U E where
  toFun x := (x.1 - Z x.2.1, x.2)
  invFun x := (x.1 + Z x.2.1, x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ext <;> simp <;> abel
  map_smul' a x := by ext <;> simp [smul_sub]

end Normalize

section Ranks
variable [Fintype I] [FiniteDimensional K V]
    [∀ i, FiniteDimensional K (U i)] [∀ i, FiniteDimensional K (E i)]

noncomputable def support (q : I → K) : Finset I := Finset.univ.filter (fun i => q i ≠ 0)

theorem sum_support (q : I → K) (f : I → ℕ) :
    (∑ i : {i // q i ≠ 0}, f i.val) = ∑ i ∈ support q, f i := by
  simpa [support] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) f (p := fun i => q i ≠ 0))

theorem mixedSlice_rank_support (X : V →ₗ[K] (∀ i, U i)) {q : I → K}
    (hq : ∃ i, q i ≠ 0) :
    finrank K (LinearMap.range (mixedSlice (E := E) X q)) =
      finrank K V + (∑ i ∈ support q, finrank K (U i)) +
        ∑ i ∈ support q, finrank K (E i) := by
  rw [mixedSlice_rank X hq, sum_support q (fun i => finrank K (U i)),
    sum_support q (fun i => finrank K (E i))]

theorem support_single [DecidableEq I] (i : I) :
    support (Pi.single i (1 : K)) = {i} := by
  ext j
  by_cases h : j = i <;> simp_all [support,Pi.single_apply,eq_comm]

theorem gadget_rank [DecidableEq I] (i : I) :
    finrank K (LinearMap.range (mixedSlice (E := E)
      (0 : V →ₗ[K] (∀ i, U i)) (Pi.single i 1))) =
      finrank K V + finrank K (U i) + finrank K (E i) := by
  rw [mixedSlice_rank_support _ (q := Pi.single i 1) ⟨i,by simp⟩, support_single]
  simp

theorem supported_dim_le (q : I → K) :
    (∑ i ∈ support q, finrank K (U i)) ≤ ∑ i, finrank K (U i) :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem data_rank_bound (X : V →ₗ[K] (∀ i, U i)) :
    finrank K (LinearMap.range (mixedSlice (E := E) X 0)) ≤ ∑ i, finrank K (U i) := by
  let j : (∀ i, U i) →ₗ[K] RowSpace V U E := LinearMap.inl K _ _
  have hr : LinearMap.range (mixedSlice (E := E) X 0) ≤ LinearMap.range j := by
    rintro y ⟨x,rfl⟩
    exact ⟨X x.1, by ext <;> simp [j,mixedSlice]⟩
  have hle := Submodule.finrank_mono hr
  have hj := j.finrank_range_le
  simpa [Module.finrank_pi_fintype] using hle.trans hj

end Ranks

section Geometric
variable {N : ℕ} {U E : Fin N → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [FiniteDimensional K V]
  [∀ i, FiniteDimensional K (U i)] [∀ i, FiniteDimensional K (E i)]

/-- Actual geometric tag spaces used by the construction. -/
abbrev Tags (i : Fin N) :=
  Fin (2 ^ i.val * ((∑ j, finrank K (U j)) + 1)) → K

theorem tags_dimension (i : Fin N) :
    finrank K (Tags (K := K) (U := U) i) =
      2 ^ i.val * ((∑ j, finrank K (U j)) + 1) := by
  simp [Tags]

/-- Rank equality with one gadget forces exactly its coefficient support.
The rank equality concerns the explicit constructor, not an assumed rank oracle. -/
theorem gadget_rank_recovers_support
    (htag : ∀ i, finrank K (E i) = 2 ^ i.val * ((∑ j, finrank K (U j)) + 1))
    (X : V →ₗ[K] (∀ i, U i)) (q : Fin N → K) (i : Fin N)
    (h : finrank K (LinearMap.range (mixedSlice (E := E) X q)) =
      finrank K V + finrank K (U i) + finrank K (E i)) :
    support q = {i} := by
  have htotal : finrank K (U i) ≤ ∑ j, finrank K (U j) :=
    Finset.single_le_sum (f := fun j : Fin N => finrank K (U j))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpow : 1 ≤ 2 ^ i.val := Nat.one_le_pow _ _ (by omega)
  have htaglarge : (∑ j, finrank K (U j)) < finrank K (E i) := by
    rw [htag i]
    nlinarith
  have hq : ∃ j, q j ≠ 0 := by
    by_contra hn
    have hz : q = 0 := by ext j; simpa using not_exists.mp hn j
    subst q
    have hd := data_rank_bound (E := E) X
    omega
  rw [mixedSlice_rank_support X hq] at h
  simp only [htag] at h
  have hsmall := supported_dim_le (U := U) q
  apply subset_eq_of_sum_eq
    (superIncr_geometric ((∑ j, finrank K (U j)) + 1) (by omega))
    (s := ∑ j ∈ support q, finrank K (U j)) (s' := finrank K (U i))
  · omega
  · omega
  · simp only [Finset.sum_singleton]
    omega

/-- The preceding support theorem instantiated with the explicit finite-coordinate tags. -/
theorem concrete_gadget_rank_recovers_support
    (X : V →ₗ[K] (∀ i, U i)) (q : Fin N → K) (i : Fin N)
    (h : finrank K (LinearMap.range (mixedSlice
      (E := Tags (K := K) (U := U)) X q)) =
      finrank K V + finrank K (U i) +
        2 ^ i.val * ((∑ j, finrank K (U j)) + 1)) :
    support q = {i} := by
  apply gadget_rank_recovers_support (tags_dimension (K := K) (U := U)) X q i
  simpa only [tags_dimension] using h

end Geometric

section TransporterRecovery
variable [Fintype I] [DecidableEq I] [Nontrivial I]

def gadget (i : I) : ColSpace V U E →ₗ[K] RowSpace V U E :=
  mixedSlice 0 (Pi.single i 1)

theorem gadget_zero_iff (i : I) (x : ColSpace V U E) :
    gadget (K := K) i x = 0 ↔ x.1 = 0 ∧ x.2.1 i = 0 ∧ x.2.2 i = 0 := by
  rw [gadget,mixedSlice_kernel ⟨i, by simp⟩]
  constructor
  · rintro ⟨hv,hu,he⟩
    exact ⟨hv,by simpa using hu i,by simpa using he i⟩
  · rintro ⟨hv,hu,he⟩
    refine ⟨hv,?_,?_⟩
    · intro j
      by_cases h : j = i
      · subst j; simpa using hu
      · simp [Pi.single_eq_of_ne h]
    · intro j
      by_cases h : j = i
      · subst j; simpa using he
      · simp [Pi.single_eq_of_ne h]

def auxColumn (i : I) (u : U i) (e : E i) : ColSpace V U E :=
  (0, Pi.single i u, Pi.single i e)

theorem column_aux_invariant (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (hk : ∀ i x, gadget (K := K) i x = 0 → gadget (K := K) i (Q x) = 0)
    (u : ∀ i, U i) (e : ∀ i, E i) : (Q (0,u,e)).1 = 0 := by
  have hlocal : ∀ i v w, (Q (auxColumn (V := V) i v w)).1 = 0 := by
    intro i v w
    obtain ⟨j,hji⟩ := exists_ne i
    have hj : gadget (K := K) j (auxColumn (V := V) i v w) = 0 := by
      rw [gadget_zero_iff]
      simp [auxColumn,Pi.single_eq_of_ne hji]
    exact ((gadget_zero_iff j _).mp (hk j _ hj)).1
  have hsum : ((0,u,e) : ColSpace V U E) = ∑ i : I, auxColumn (V := V) i (u i) (e i) := by
    ext <;> simp [auxColumn,Prod.fst_sum,Prod.snd_sum]
  rw [hsum,map_sum]
  change (∑ i : I, Q (auxColumn (V := V) i (u i) (e i))).1 = 0
  simp [Prod.fst_sum,hlocal]

theorem column_first_coordinate (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (hk : ∀ i x, gadget (K := K) i x = 0 → gadget (K := K) i (Q x) = 0)
    (x : ColSpace V U E) :
    (Q x).1 = (Q (x.1,0,0)).1 := by
  have hx : x = (x.1,0,0) + (0,x.2.1,x.2.2) := by ext <;> simp
  conv_lhs => rw [hx,map_add]
  simpa using congrArg (fun v => (Q (x.1,0,0)).1 + v)
    (column_aux_invariant Q hk x.2.1 x.2.2)

theorem column_symm_kernel (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (hk : ∀ i x, gadget (K := K) i (Q x) = 0 ↔ gadget (K := K) i x = 0) :
    ∀ i x, gadget (K := K) i x = 0 → gadget (K := K) i (Q.symm x) = 0 := by
  intro i x hx
  apply (hk i (Q.symm x)).mp
  simpa using hx

/-- An invertible column transformation on the original space, recovered from gadget preservation. -/
def columnQuotient (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (hk : ∀ i x, gadget (K := K) i (Q x) = 0 ↔ gadget (K := K) i x = 0) : V ≃ₗ[K] V where
  toFun v := (Q (v,0,0)).1
  invFun v := (Q.symm (v,0,0)).1
  left_inv v := by
    change (Q.symm ((Q (v,0,0)).1,0,0)).1 = v
    rw [← column_first_coordinate Q.symm (column_symm_kernel Q hk) (Q (v,0,0))]
    simp
  right_inv v := by
    change (Q ((Q.symm (v,0,0)).1,0,0)).1 = v
    rw [← column_first_coordinate Q (fun i x => (hk i x).mpr) (Q.symm (v,0,0))]
    simp
  map_add' v w := by
    have h : ((v+w,0,0) : ColSpace V U E) = (v,0,0) + (w,0,0) := by simp
    rw [h,map_add]; rfl
  map_smul' a v := by
    have h : ((a • v,0,0) : ColSpace V U E) = a • (v,0,0) := by simp
    rw [h,map_smul]; rfl

def rowCoordinates : RowSpace V U E ≃ₗ[K] (∀ i, U i × V × E i) where
  toFun x i := (x.1 i,x.2.1 i,x.2.2 i)
  invFun x := (fun i => (x i).1, (fun i => (x i).2.1),fun i => (x i).2.2)
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

theorem gadget_rowCoordinates (i : I) (x : ColSpace V U E) :
    rowCoordinates (K := K) (gadget (K := K) i x) = Pi.single i (x.2.1 i,x.1,x.2.2 i) := by
  apply funext
  intro j
  by_cases h : j = i
  · subst j; simp [rowCoordinates,gadget,mixedSlice]
  · simp [rowCoordinates,gadget,mixedSlice,Pi.single_eq_of_ne h]

/-- Kernel preservation follows from the actual normalized gadget equations. -/
theorem gadget_kernel_preserved
    (P : RowSpace V U E ≃ₗ[K] RowSpace V U E)
    (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (a : I → K) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ i x, P (gadget (K := K) i (Q x)) = a i • gadget (K := K) i x) :
    ∀ i x, gadget (K := K) i (Q x) = 0 ↔ gadget (K := K) i x = 0 := by
  intro i x
  constructor
  · intro hx
    have he := hg i x
    rw [hx,map_zero] at he
    exact (smul_eq_zero.mp he.symm).resolve_left (ha i)
  · intro hx
    apply P.injective
    simpa [hx] using hg i x

/-- Preserving each coordinate summand implies commutation with its projector. -/
theorem blocks_of_single_support
    {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (F : (∀ i, W i) →ₗ[K] (∀ i, W i))
    (h : ∀ i v, F (Pi.single i v) = Pi.single i (F (Pi.single i v) i)) :
    PreservesBlocks F := by
  intro i x
  let e : (∀ i, W i) →ₗ[K] (∀ i, W i) :=
    (LinearMap.single K W i).comp (LinearMap.proj i)
  have he : F.comp e = e.comp F := by
    apply LinearMap.pi_ext
    intro j v
    by_cases hij : j = i
    · subst j
      simpa [e] using h i v
    · have hj := h j v
      simp only [LinearMap.comp_apply]
      change F (Pi.single i ((Pi.single j v) i)) =
        Pi.single i (F (Pi.single j v) i)
      rw [hj]
      simp [Pi.single_eq_of_ne (Ne.symm hij)]
  exact LinearMap.congr_fun he x

/-- The normalized gadget equations force independent invertible transformations
of the enlarged row blocks; no diagonal-block invertibility is assumed. -/
theorem recover_row_blocks
    (P : RowSpace V U E ≃ₗ[K] RowSpace V U E)
    (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (a : I → K)
    (hg : ∀ i x, P (gadget (K := K) i (Q x)) = a i • gadget (K := K) i x) :
    ∃ p : ∀ i, (U i × V × E i) ≃ₗ[K] (U i × V × E i),
      ∀ x i, rowCoordinates (K := K) (P x) i = p i (rowCoordinates (K := K) x i) := by
  let C := rowCoordinates (K := K) (V := V) (U := U) (E := E)
  let F := C.symm ≪≫ₗ P ≪≫ₗ C
  have hs : ∀ i v, F (Pi.single i v) = Pi.single i (F (Pi.single i v) i) := by
    intro i v
    let z : ColSpace V U E := (v.2.1,Pi.single i v.1,Pi.single i v.2.2)
    have hz : C (gadget (K := K) i z) = Pi.single i v := by
      simpa [C,z] using gadget_rowCoordinates (V := V) (U := U) (E := E) i z
    have he := congrArg C (hg i (Q.symm z))
    simp only [LinearEquiv.apply_symm_apply] at he
    have hf : F (Pi.single i v) = C (P (gadget (K := K) i z)) := by
      change C (P (C.symm (Pi.single i v))) = _
      rw [← hz,LinearEquiv.symm_apply_apply]
    rw [hf,he]
    rw [map_smul,gadget_rowCoordinates]
    apply funext
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hji]
  have hb := blocks_of_single_support F.toLinearMap hs
  refine ⟨coordinateEquiv F hb, ?_⟩
  intro x i
  have he := LinearEquiv.congr_fun (reconstruct_blocks F hb) (C x)
  have hi := congrFun he i
  simpa [F,C] using hi.symm

end TransporterRecovery

section Extension
variable {A B W : Type*} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]
  [FiniteDimensional K B]

/-- Equal kernels yield an actual invertible left transporter, even for nonconcise data. -/
theorem exists_left_equiv_of_ker_eq (f g : A →ₗ[K] B)
    (h : LinearMap.ker f = LinearMap.ker g) :
    ∃ P : B ≃ₗ[K] B, ∀ x, P (f x) = g x := by
  let e : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
    f.quotKerEquivRange.symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ h ≪≫ₗ g.quotKerEquivRange
  obtain ⟨P,hP⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨P, fun x => ?_⟩
  have he := hP ⟨f x, ⟨x,rfl⟩⟩
  change (g.quotKerEquivRange ((Submodule.quotEquivOfEq _ _ h)
    (f.quotKerEquivRange.symm ⟨f x, ⟨x,rfl⟩⟩)) : B) = P (f x) at he
  have hf : f.quotKerEquivRange.symm ⟨f x, ⟨x,rfl⟩⟩ =
      (Submodule.Quotient.mk x : A ⧸ LinearMap.ker f) := by
    apply f.quotKerEquivRange.injective
    simp only [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hf,Submodule.quotEquivOfEq_mk] at he
  exact he.symm

/-- Cancel any injective zero-padding without assuming that the original tensors are concise. -/
theorem cancel_injective_padding (f g : A →ₗ[K] B)
    (j : B →ₗ[K] W) (hj : Function.Injective j) (P : W ≃ₗ[K] W)
    (h : ∀ x, P (j (f x)) = j (g x)) :
    ∃ Q : B ≃ₗ[K] B, ∀ x, Q (f x) = g x := by
  apply exists_left_equiv_of_ker_eq
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply hj
    simpa [hx] using (h x).symm
  · intro hx
    apply hj
    apply P.injective
    simpa [hx] using h x

end Extension

section SimultaneousShear
variable [Fintype I] [DecidableEq I]

def shearMap (X : I → V →ₗ[K] (∀ i, U i)) (a : I → K) :
    (I → V) →ₗ[K] (∀ i, U i) :=
  ∑ i, (a i)⁻¹ • (X i).comp (LinearMap.proj i)

theorem shearMap_single (X : I → V →ₗ[K] (∀ i, U i))
    (a : I → K) (i : I) (v : V) :
    shearMap X a (Pi.single i v) = (a i)⁻¹ • X i v := by
  classical
  simp [shearMap,LinearMap.sum_apply,Pi.single_apply,apply_ite]

/-- A single invertible shear normalizes all gadget slices at once. -/
theorem simultaneous_normalization (X : I → V →ₗ[K] (∀ i, U i))
    (a : I → K) (ha : ∀ i, a i ≠ 0) (i : I) :
    (rowShear (E := E) (shearMap X a)).toLinearMap.comp
      (mixedSlice (X i) (Pi.single i (a i))) =
      mixedSlice 0 (Pi.single i (a i)) := by
  have hs : ∀ v : V, (fun j => (Pi.single i (a i) : I → K) j • v) = Pi.single i (a i • v) := by
    intro v
    ext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  ext x <;>
    simp [rowShear,mixedSlice,hs,shearMap_single,smul_smul,inv_mul_cancel₀ (ha i)]

theorem rowShear_symm_data (Z : (I → V) →ₗ[K] (∀ i, U i))
    (X : V →ₗ[K] (∀ i, U i)) :
    (rowShear (E := E) Z).symm.toLinearMap.comp (mixedSlice X 0) =
      mixedSlice X 0 := by
  ext x <;> simp [rowShear,mixedSlice,show (fun _ : I => (0 : V)) = 0 from rfl]

end SimultaneousShear

section RankTransport
variable {A B : Type*} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

theorem rank_transport (f : A →ₗ[K] B) (P : B ≃ₗ[K] B) (Q : A ≃ₗ[K] A) :
    finrank K (LinearMap.range (P.toLinearMap.comp (f.comp Q.toLinearMap))) =
      finrank K (LinearMap.range f) := by
  rw [LinearMap.range_comp,LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range Q)]
  exact P.finrank_map_eq _

end RankTransport

section ConcreteRankSeparation
variable {N : ℕ} {U : Fin N → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [FiniteDimensional K V] [∀ i, FiniteDimensional K (U i)]

/-- The original data subspace is exactly the low-rank subspace of the encoding. -/
theorem concrete_low_rank_iff (X : V →ₗ[K] (∀ i, U i)) (q : Fin N → K) :
    finrank K (LinearMap.range (mixedSlice
      (E := Tags (K := K) (U := U)) X q)) ≤ ∑ i, finrank K (U i) ↔ q = 0 := by
  constructor
  · intro hr
    by_contra hq
    obtain ⟨i,hi⟩ : ∃ i, q i ≠ 0 := by
      contrapose! hq
      exact funext hq
    rw [mixedSlice_rank_support X ⟨i,hi⟩] at hr
    have hm : i ∈ support q := by simp [support,hi]
    have hs := Finset.single_le_sum
      (f := fun j => finrank K (Tags (K := K) (U := U) j))
      (fun j _ => Nat.zero_le _) hm
    rw [tags_dimension] at hs
    have hp : 1 ≤ 2 ^ i.val := Nat.one_le_pow _ _ (by omega)
    have hmul := Nat.mul_le_mul_right ((∑ j, finrank K (U j)) + 1) hp
    simp only [one_mul] at hmul
    omega
  · rintro rfl
    exact data_rank_bound X

variable {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]

def frontSlice (X : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (z : A × (Fin N → K)) :
    ColSpace V U (Tags (K := K) (U := U)) →ₗ[K]
      RowSpace V U (Tags (K := K) (U := U)) :=
  mixedSlice (X z.1) z.2

theorem front_rank_preserved
    (X Y : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (R : (A × (Fin N → K)) ≃ₗ[K] (A × (Fin N → K)))
    (P : RowSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (Q : ColSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (h : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z) (z : A × (Fin N → K)) :
    finrank K (LinearMap.range (frontSlice X (R z))) =
      finrank K (LinearMap.range (frontSlice Y z)) := by
  rw [← h z,rank_transport]

theorem front_data_invariant
    (X Y : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (R : (A × (Fin N → K)) ≃ₗ[K] (A × (Fin N → K)))
    (P : RowSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (Q : ColSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (h : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z) (z : A) :
    (R (z,0)).2 = 0 := by
  apply (concrete_low_rank_iff (X (R (z,0)).1) (R (z,0)).2).mp
  change finrank K (LinearMap.range (frontSlice X (R (z,0)))) ≤ _
  rw [front_rank_preserved X Y R P Q h]
  exact data_rank_bound (Y z)

/-- The restriction of the frontal transporter to the original data is invertible. -/
theorem front_data_equiv
    (X Y : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (R : (A × (Fin N → K)) ≃ₗ[K] (A × (Fin N → K)))
    (P : RowSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (Q : ColSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (h : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z) :
    ∃ S : A ≃ₗ[K] A, ∀ z, R (z,0) = (S z,0) := by
  let f : A →ₗ[K] A := (LinearMap.fst K A (Fin N → K)).comp
    (R.toLinearMap.comp (LinearMap.inl K A (Fin N → K)))
  have hf : Function.Injective f := by
    intro z w hzw
    have he : R (z,0) = R (w,0) := by
      apply Prod.ext
      · exact hzw
      · rw [front_data_invariant X Y R P Q h,front_data_invariant X Y R P Q h]
    exact congrArg Prod.fst (R.injective he)
  refine ⟨LinearEquiv.ofBijective f ⟨hf,LinearMap.injective_iff_surjective.mp hf⟩,?_⟩
  intro z
  exact Prod.ext rfl (front_data_invariant X Y R P Q h z)

theorem front_gadget_support
    (X Y : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (R : (A × (Fin N → K)) ≃ₗ[K] (A × (Fin N → K)))
    (P : RowSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (Q : ColSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (h : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z) (i : Fin N) :
    support (R (0,Pi.single i 1)).2 = {i} := by
  apply concrete_gadget_rank_recovers_support
    (X (R (0,Pi.single i 1)).1) (R (0,Pi.single i 1)).2 i
  change finrank K (LinearMap.range (frontSlice X (R (0,Pi.single i 1)))) = _
  rw [front_rank_preserved X Y R P Q h]
  change finrank K (LinearMap.range (mixedSlice (E := Tags (K := K) (U := U)) (Y 0) (Pi.single i 1))) = _
  rw [map_zero,gadget_rank,tags_dimension]

end ConcreteRankSeparation

section UnnormalizedRecovery
variable [Fintype I] [DecidableEq I] [Nontrivial I]
  [∀ i, FiniteDimensional K (U i)]
  {T : Type*} [Fintype T]

theorem gadget_scale (i : I) (a : K) :
    mixedSlice (E := E) (0 : V →ₗ[K] (∀ i, U i)) (Pi.single i a) =
      a • gadget (K := K) (V := V) (U := U) (E := E) i := by
  change mixedSlice 0 (Pi.single i a) = a • mixedSlice 0 (Pi.single i 1)
  rw [← mixedSlice_smul,smul_zero]
  congr 1
  ext j
  by_cases h : j = i <;> simp_all []

end UnnormalizedRecovery

section SizeBound
variable {N : ℕ} {U : Fin N → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [FiniteDimensional K V] [∀ i, FiniteDimensional K (U i)]
  {T : Type*} [Fintype T]

theorem tag_sum_bound :
    (∑ i : Fin N, finrank K (Tags (K := K) (U := U) i)) ≤
      N * 2 ^ N * ((∑ i, finrank K (U i)) + 1) := by
  calc
    _ ≤ ∑ _ : Fin N, 2 ^ N * ((∑ i, finrank K (U i)) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [tags_dimension]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt))
    _ = _ := by simp [Nat.mul_assoc]

/-- The actual three output dimensions have linear total overhead for fixed N. -/
theorem one_axis_size :
    finrank K (RowSpace V U (Tags (K := K) (U := U))) +
      finrank K (ColSpace V U (Tags (K := K) (U := U))) +
      finrank K ((T → K) × (Fin N → K)) ≤
    (2 * N * 2 ^ N + 2 * N + 4) *
      ((∑ i, finrank K (U i)) + finrank K V + Fintype.card T + 1) := by
  obtain ⟨hr,hc⟩ := construction_dimensions
    (K := K) (V := V) (U := U) (E := Tags (K := K) (U := U))
  rw [hr,hc]
  simp only [Module.finrank_prod,Module.finrank_pi,
    Fintype.card_fin]
  let D := ∑ i, finrank K (U i)
  let L := D + finrank K V + Fintype.card T + 1
  have hD : D ≤ L := by dsimp [L]; omega
  have hD1 : D + 1 ≤ L := by dsimp [L]; omega
  have hV : finrank K V ≤ L := by dsimp [L]; omega
  have hT : Fintype.card T ≤ L := by dsimp [L]; omega
  have h1 : 1 ≤ L := by dsimp [L]; omega
  have htag := (tag_sum_bound (K := K) (U := U)).trans
    (Nat.mul_le_mul_left (N * 2 ^ N) hD1)
  simp only [tags_dimension] at htag
  have hVm := Nat.mul_le_mul_left N hV
  have hNm := Nat.mul_le_mul_left N h1
  change D + N * finrank K V + _ + (finrank K V + D + _) +
    (Fintype.card T + N) ≤ (2 * N * 2 ^ N + 2 * N + 4) * L
  nlinarith

end SizeBound

section ActualTensor
variable {N : ℕ} {U : Fin N → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ i, FiniteDimensional K (U i)]
  {A : Type*} [AddCommGroup A] [Module K A]

/-- The actual output three-tensor, in curried bilinear-map coordinates. -/
def paddingCompile (X : A →ₗ[K] (V →ₗ[K] (∀ i, U i))) :
    (A × (Fin N → K)) →ₗ[K]
      ColSpace V U (Tags (K := K) (U := U)) →ₗ[K]
      RowSpace V U (Tags (K := K) (U := U)) where
  toFun z := frontSlice X z
  map_add' z w := by
    change mixedSlice (X (z.1+w.1)) (z.2+w.2) = _
    rw [map_add,mixedSlice_add]
    rfl
  map_smul' a z := by
    change mixedSlice (X (a • z.1)) (a • z.2) = _
    rw [map_smul,mixedSlice_smul]
    rfl

end ActualTensor

end

/- Transport through auxiliary spaces. -/
section
variable {K J : Type*} [Field K] [DecidableEq J]
  {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  {B : Type*} [AddCommGroup B] [Module K B]

abbrev AuxIndex (j₀ j : J) := {u : Unit // j = j₀}
abbrev Enlarged (j₀ j : J) := V j × (AuxIndex j₀ j → B)

/-- The auxiliary space belongs to exactly one distinguished partition block. -/
def regroup (j₀ : J) :
    ((∀ j, V j) × B) ≃ₗ[K] (∀ j, Enlarged (V := V) (B := B) j₀ j) where
  toFun x j := (x.1 j,fun _ => x.2)
  invFun x := (fun j => (x j).1, (x j₀).2 ⟨(),rfl⟩)
  left_inv x := rfl
  right_inv x := by
    funext j
    apply Prod.ext
    · rfl
    · funext u
      rcases u with ⟨⟨⟩,h⟩
      subst j
      rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Block transformations and an auxiliary transformation extend independently. -/
def quotientExtend (j₀ : J) (g : ∀ j, V j ≃ₗ[K] V j) (b : B ≃ₗ[K] B) :
    ∀ j, Enlarged (V := V) (B := B) j₀ j ≃ₗ[K] Enlarged (V := V) (B := B) j₀ j :=
  fun j => (g j).prodCongr (LinearEquiv.piCongrRight (fun _ => b))

theorem extend_apply (j₀ : J) (g : ∀ j, V j ≃ₗ[K] V j) (b : B ≃ₗ[K] B)
    (x : (∀ j, V j) × B) :
    (LinearEquiv.piCongrRight (quotientExtend j₀ g b)) (regroup (K := K) j₀ x) =
      regroup (K := K) j₀ ((LinearEquiv.piCongrRight g) x.1,b x.2) := rfl

/-- An invertible quotient induced by enlarged block transformations splits into
actual invertible transformations of the original blocks, including the enlarged one. -/
theorem recover [∀ j, FiniteDimensional K (V j)] (j₀ : J)
    (G : ∀ j, Enlarged (V := V) (B := B) j₀ j ≃ₗ[K] Enlarged (V := V) (B := B) j₀ j)
    (q : (∀ j, V j) ≃ₗ[K] (∀ j, V j))
    (hq : ∀ v j, q v j = (G j (v j,0)).1) :
    ∃ g : ∀ j, V j ≃ₗ[K] V j, ∀ v, q v = (LinearEquiv.piCongrRight g) v := by
  let f : ∀ j, V j →ₗ[K] V j := fun j =>
    (LinearMap.fst K (V j) (AuxIndex j₀ j → B)).comp
      ((G j).toLinearMap.comp (LinearMap.inl K (V j) (AuxIndex j₀ j → B)))
  have hf : ∀ j, Function.Injective (f j) := by
    intro j u v huv
    have he : q (Pi.single j u) = q (Pi.single j v) := by
      funext k
      rw [hq,hq]
      by_cases h : k = j
      · subst k
        simpa [f] using huv
      · simp [Pi.single_eq_of_ne h]
    have he' := congrFun (q.injective he) j
    simpa using he'
  let g : ∀ j, V j ≃ₗ[K] V j := fun j =>
    LinearEquiv.ofBijective (f j) ⟨hf j,LinearMap.injective_iff_surjective.mp (hf j)⟩
  refine ⟨g,fun v => funext (fun j => ?_)⟩
  exact hq v j

/-- Passing to the original quotient preserves all original partition blocks. -/
theorem recover_quotient [∀ j, FiniteDimensional K (V j)] (j₀ : J)
    (G : ∀ j, Enlarged (V := V) (B := B) j₀ j ≃ₗ[K] Enlarged (V := V) (B := B) j₀ j)
    (Q : ((∀ j, V j) × B) ≃ₗ[K] ((∀ j, V j) × B))
    (hQ : ∀ x, regroup (K := K) j₀ (Q x) = (LinearEquiv.piCongrRight G) (regroup (K := K) j₀ x))
    (q : (∀ j, V j) ≃ₗ[K] (∀ j, V j))
    (hq : ∀ v, q v = (Q (v,0)).1) :
    ∃ g : ∀ j, V j ≃ₗ[K] V j, ∀ v, q v = (LinearEquiv.piCongrRight g) v := by
  apply recover j₀ G q
  intro v j
  have he := congrArg (fun w => (w j).1) (hQ (v,0))
  change (Q (v,0)).1 j = (G j (v j,0)).1 at he
  rw [hq]
  exact he

end

/- Cyclic rotation and duality. -/
section
open Module
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

abbrev Tensor := A →ₗ[K] B →ₗ[K] C

def rotate (X : Tensor (K := K) (A := A) (B := B) (C := C)) :
    B →ₗ[K] (Dual K C) →ₗ[K] Dual K A where
  toFun b :=
    { toFun := fun f =>
        { toFun := fun a => f (X a b)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

def undual [FiniteDimensional K A] (g : Dual K A ≃ₗ[K] Dual K A) : A ≃ₗ[K] A :=
  Module.evalEquiv K A ≪≫ₗ g.dualMap ≪≫ₗ (Module.evalEquiv K A).symm

@[simp] theorem dual_undual [FiniteDimensional K A] (g : Dual K A ≃ₗ[K] Dual K A) :
    (undual g).dualMap = g := by
  ext f a
  simp [undual,LinearEquiv.dualMap_apply]

theorem covariance_iff [FiniteDimensional K C]
    (X Y : Tensor (K := K) (A := A) (B := B) (C := C))
    (P : C ≃ₗ[K] C) (Q : B ≃ₗ[K] B) (R : A ≃ₗ[K] A) :
    (∀ a b, P (X (R a) (Q b)) = Y a b) ↔
    (∀ b f, R.dualMap (rotate X (Q b) (P.dualMap f)) = rotate Y b f) := by
  constructor
  · intro h b f
    ext a
    simpa [rotate] using congrArg f (h a b)
  · intro h a b
    apply (Module.evalEquiv K C).injective
    ext f
    simpa [rotate] using congrArg (fun g : Dual K A => g a) (h b f)

def Iso (X Y : Tensor (K := K) (A := A) (B := B) (C := C)) : Prop :=
  ∃ P : C ≃ₗ[K] C, ∃ Q : B ≃ₗ[K] B, ∃ R : A ≃ₗ[K] A,
    ∀ a b, P (X (R a) (Q b)) = Y a b

section PiDual
variable {I : Type*} [Fintype I] [DecidableEq I]
  {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]

/-- The dual of a finite product is the product of the component duals. -/
def piDual : (∀ i, Dual K (U i)) ≃ₗ[K] Dual K (∀ i, U i) where
  toFun f := ∑ i, (f i).comp (LinearMap.proj i)
  invFun f i := f.comp (LinearMap.single K U i)
  left_inv f := by
    funext i
    ext v
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.proj_apply,
      LinearMap.single_apply]
    change (∑ j, f j (Pi.single i v j)) = f i v
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  right_inv f := by
    ext v
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
      LinearMap.single_apply]
    rw [← map_sum]
    congr 1
    ext i
    simp
  map_add' f g := by ext v; simp [Finset.sum_add_distrib]
  map_smul' a f := by ext v; simp [Finset.smul_sum]

theorem piDual_covariance (g : ∀ i, U i ≃ₗ[K] U i) (f : ∀ i, Dual K (U i)) :
    piDual ((LinearEquiv.piCongrRight (fun i => (g i).dualMap)) f) =
      (LinearEquiv.piCongrRight g).dualMap (piDual f) := by
  ext v
  simp [piDual,LinearEquiv.dualMap_apply]

end PiDual

section Parts
variable {I J L : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  {U : I → Type*} {V : J → Type*} {W : L → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ k, AddCommGroup (W k)] [∀ k, Module K (W k)]

def bilinearPartsIso (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) : Prop :=
  ∃ P : ∀ i, U i ≃ₗ[K] U i, ∃ Q : ∀ j, V j ≃ₗ[K] V j,
    ∃ R : ∀ k, W k ≃ₗ[K] W k,
      ∀ a b, (LinearEquiv.piCongrRight P)
        (X ((LinearEquiv.piCongrRight R) a) ((LinearEquiv.piCongrRight Q) b)) = Y a b

def rotateParts (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    (∀ j, V j) →ₗ[K] (∀ i, Dual K (U i)) →ₗ[K] (∀ k, Dual K (W k)) where
  toFun b :=
    { toFun := fun f => (piDual (K := K) (U := W)).symm (rotate X b (piDual f))
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem piDual_rotateParts
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i))
    (b : ∀ j, V j) (f : ∀ i, Dual K (U i)) :
    piDual (rotateParts X b f) = rotate X b (piDual f) := by
  change piDual ((piDual (K := K) (U := W)).symm _) = _
  simp

theorem parts_covariance_iff [∀ i, FiniteDimensional K (U i)]
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i))
    (P : ∀ i, U i ≃ₗ[K] U i) (Q : ∀ j, V j ≃ₗ[K] V j)
    (R : ∀ k, W k ≃ₗ[K] W k) :
    (∀ a b, (LinearEquiv.piCongrRight P)
      (X ((LinearEquiv.piCongrRight R) a) ((LinearEquiv.piCongrRight Q) b)) = Y a b) ↔
    (∀ b f, (LinearEquiv.piCongrRight (fun k => (R k).dualMap))
      (rotateParts X ((LinearEquiv.piCongrRight Q) b)
        ((LinearEquiv.piCongrRight (fun i => (P i).dualMap)) f)) = rotateParts Y b f) := by
  constructor
  · intro h b f
    apply (piDual (K := K) (U := W)).injective
    have ht := (covariance_iff X Y (LinearEquiv.piCongrRight P)
      (LinearEquiv.piCongrRight Q) (LinearEquiv.piCongrRight R)).mp h b (piDual f)
    simpa only [piDual_covariance,piDual_rotateParts] using ht
  · intro h
    apply (covariance_iff X Y (LinearEquiv.piCongrRight P)
      (LinearEquiv.piCongrRight Q) (LinearEquiv.piCongrRight R)).mpr
    intro b f
    have ht := congrArg (piDual (K := K) (U := W))
      (h b ((piDual (K := K) (U := U)).symm f))
    simpa only [piDual_covariance,piDual_rotateParts,LinearEquiv.apply_symm_apply] using ht

theorem partsIso_rotate_iff [∀ i, FiniteDimensional K (U i)]
    [∀ k, FiniteDimensional K (W k)]
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    bilinearPartsIso X Y ↔ bilinearPartsIso (rotateParts X) (rotateParts Y) := by
  constructor
  · rintro ⟨P,Q,R,h⟩
    exact ⟨fun k => (R k).dualMap,fun i => (P i).dualMap,Q,
      (parts_covariance_iff X Y P Q R).mp h⟩
  · rintro ⟨R,P,Q,h⟩
    refine ⟨fun i => undual (P i),Q,fun k => undual (R k),
      (parts_covariance_iff X Y (fun i => undual (P i)) Q (fun k => undual (R k))).mpr ?_⟩
    simpa only [dual_undual] using h

theorem rotation_total_dimension [∀ i, FiniteDimensional K (U i)]
    [∀ j, FiniteDimensional K (V j)] [∀ k, FiniteDimensional K (W k)] :
    finrank K (∀ j, V j) + finrank K (∀ i, Dual K (U i)) + finrank K (∀ k, Dual K (W k)) =
      finrank K (∀ k, W k) + finrank K (∀ j, V j) + finrank K (∀ i, U i) := by
  simp only [Module.finrank_pi_fintype,Subspace.dual_finrank_eq]
  omega

end Parts

end

section
section ExactRecovery
variable {K I V : Type*} [Field K]
  {U E : I → Type*} [AddCommGroup V] [Module K V]
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [Fintype I] [DecidableEq I] [Nontrivial I]
  [∀ i, FiniteDimensional K (U i)] {T : Type*} [Fintype T]
theorem normalized_recovery_exact
    (X Y : T → V →ₗ[K] (∀ i, U i))
    (P : RowSpace V U E ≃ₗ[K] RowSpace V U E)
    (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (a : I → K) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ i x, P (gadget (K := K) i (Q x)) = a i • gadget (K := K) i x)
    (hd : ∀ t x, P (mixedSlice (X t) 0 (Q x)) = mixedSlice (Y t) 0 x) :
    ∃ g : ∀ i, U i ≃ₗ[K] U i, ∃ q : V ≃ₗ[K] V,
      (∀ v, q v = (Q (v,0,0)).1) ∧
      ∀ t v, (LinearEquiv.piCongrRight g) (X t (q v)) = Y t v := by
  classical
  let hk := gadget_kernel_preserved P Q a ha hg
  let q := columnQuotient Q hk
  obtain ⟨p,hp⟩ := recover_row_blocks P Q a hg
  have he : ∀ i t v, p i ((X t (q v)) i,0,0) = ((Y t v) i,0,0) := by
    intro i t v
    have h := congrArg (fun z : RowSpace V U E => rowCoordinates (K := K) z i)
      (hd t (v,0,0))
    rw [hp] at h
    simpa [mixedSlice,rowCoordinates,q,columnQuotient] using h
  have hi : ∀ i, ∃ g : U i ≃ₗ[K] U i,
      ∀ t v, g ((X t (q v)) i) = (Y t v) i := by
    intro i
    let f : (T → V) →ₗ[K] U i :=
      ∑ t, ((LinearMap.proj i).comp ((X t).comp q.toLinearMap)).comp
        (LinearMap.proj t)
    let g : (T → V) →ₗ[K] U i :=
      ∑ t, ((LinearMap.proj i).comp (Y t)).comp (LinearMap.proj t)
    let j : U i →ₗ[K] (U i × V × E i) :=
      { toFun := fun u => (u,0,0)
        map_add' := by intros; simp
        map_smul' := by intros; simp }
    have hj : Function.Injective j := fun u v h => congrArg Prod.fst h
    have hfg : ∀ z, p i (j (f z)) = j (g z) := by
      intro z
      simp only [f,g,LinearMap.sum_apply,map_sum,LinearMap.comp_apply,
        LinearMap.proj_apply,LinearEquiv.coe_coe]
      apply Finset.sum_congr rfl
      intro t ht
      exact he i t (z t)
    obtain ⟨gi,hgi⟩ := cancel_injective_padding f g j hj (p i) hfg
    refine ⟨gi,fun t v => ?_⟩
    have h := hgi (Pi.single t v)
    simpa [f,g,LinearMap.sum_apply,Pi.single_apply,apply_ite] using h
  choose g hg' using hi
  refine ⟨g,q,fun _ => rfl,fun t v => ?_⟩
  exact funext (fun i => hg' i t v)

theorem contaminated_recovery_exact
    (X Y : T → V →ₗ[K] (∀ i, U i))
    (B : I → V →ₗ[K] (∀ i, U i))
    (P : RowSpace V U E ≃ₗ[K] RowSpace V U E)
    (Q : ColSpace V U E ≃ₗ[K] ColSpace V U E)
    (a : I → K) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ i x, P (mixedSlice (B i) (Pi.single i (a i)) (Q x)) =
      gadget (K := K) i x)
    (hd : ∀ t x, P (mixedSlice (X t) 0 (Q x)) = mixedSlice (Y t) 0 x) :
    ∃ g : ∀ i, U i ≃ₗ[K] U i, ∃ q : V ≃ₗ[K] V,
      (∀ v, q v = (Q (v,0,0)).1) ∧
      ∀ t v, (LinearEquiv.piCongrRight g) (X t (q v)) = Y t v := by
  let H := rowShear (E := E) (shearMap B a)
  let P' := H.symm ≪≫ₗ P
  have hnorm : ∀ i x, P' (gadget (K := K) i (Q x)) =
      (a i)⁻¹ • gadget (K := K) i x := by
    intro i x
    have hs := LinearMap.congr_fun (simultaneous_normalization (E := E) B a ha i) (Q x)
    change H (mixedSlice (B i) (Pi.single i (a i)) (Q x)) =
      mixedSlice 0 (Pi.single i (a i)) (Q x) at hs
    rw [gadget_scale] at hs
    have hh : H.symm (a i • gadget (K := K) i (Q x)) =
        mixedSlice (B i) (Pi.single i (a i)) (Q x) :=
      (congrArg H.symm hs).symm.trans (by simp)
    have hn : a i • P' (gadget (K := K) i (Q x)) = gadget (K := K) i x := by
      change a i • P (H.symm (gadget (K := K) i (Q x))) = _
      rw [← map_smul,← map_smul,hh,hg]
    have hn' := congrArg (fun w => (a i)⁻¹ • w) hn
    simpa [smul_smul,inv_mul_cancel₀ (ha i)] using hn'
  have hdata : ∀ t x, P' (mixedSlice (X t) 0 (Q x)) = mixedSlice (Y t) 0 x := by
    intro t x
    have hs := LinearMap.congr_fun (rowShear_symm_data (E := E) (shearMap B a) (X t)) (Q x)
    change H.symm (mixedSlice (X t) 0 (Q x)) = mixedSlice (X t) 0 (Q x) at hs
    change P (H.symm (mixedSlice (X t) 0 (Q x))) = _
    rw [hs,hd]
  exact normalized_recovery_exact X Y P' Q (fun i => (a i)⁻¹)
    (fun i => inv_ne_zero (ha i)) hnorm hdata

end ExactRecovery
section GeneralFrontal
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {N : ℕ} [Nontrivial (Fin N)] {U : Fin N → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [FiniteDimensional K V] [∀ i, FiniteDimensional K (U i)]
  {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A]
theorem one_axis_reverse_exact
    (X Y : A →ₗ[K] (V →ₗ[K] (∀ i, U i)))
    (R : (A × (Fin N → K)) ≃ₗ[K] (A × (Fin N → K)))
    (P : RowSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (Q : ColSpace V U (Tags (K := K) (U := U)) ≃ₗ[K] _)
    (h : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z) :
    ∃ S : A ≃ₗ[K] A,
      ∃ g : ∀ i, U i ≃ₗ[K] U i, ∃ q : V ≃ₗ[K] V,
        (∀ z, R (z,0) = (S z,0)) ∧
        (∀ v, q v = (Q (v,0,0)).1) ∧
        ∀ z v, (LinearEquiv.piCongrRight g) (X (S z) (q v)) = Y z v := by
  classical
  let b := Module.finBasis K A
  obtain ⟨S,hS⟩ := front_data_equiv X Y R P Q h
  let a : Fin N → K := fun i => (R (0,Pi.single i 1)).2 i
  let B : Fin N → V →ₗ[K] (∀ i, U i) := fun i => X (R (0,Pi.single i 1)).1
  have hs := front_gadget_support X Y R P Q h
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    have hi : i ∈ support (R (0,Pi.single i 1)).2 := by rw [hs]; simp
    simpa [support,a] using hi
  have hq : ∀ i, (R (0,Pi.single i 1)).2 = Pi.single i (a i) := by
    intro i
    ext j
    by_cases hji : j = i
    · subst j; simp [a]
    · have hj : j ∉ support (R (0,Pi.single i 1)).2 := by rw [hs]; simpa
      have hz : (R (0,Pi.single i 1)).2 j = 0 := by simpa [support] using hj
      simp [hz,Pi.single_eq_of_ne hji]
  have hg : ∀ i x, P (mixedSlice (B i) (Pi.single i (a i)) (Q x)) =
      gadget (K := K) i x := by
    intro i x
    have hi := LinearMap.congr_fun (h (0,Pi.single i 1)) x
    change P (mixedSlice (X (R (0,Pi.single i 1)).1)
      (R (0,Pi.single i 1)).2 (Q x)) =
      mixedSlice (Y 0) (Pi.single i 1) x at hi
    rw [hq,map_zero] at hi
    exact hi
  have hd : ∀ t x, P (mixedSlice (X (S (b t))) 0 (Q x)) =
      mixedSlice (Y (b t)) 0 x := by
    intro t x
    have hi := LinearMap.congr_fun (h (b t,0)) x
    rw [hS] at hi
    exact hi
  obtain ⟨g,q,hQquot,hgq⟩ := contaminated_recovery_exact
    (fun t => X (S (b t))) (fun t => Y (b t))
    B P Q a ha hg hd
  refine ⟨S,g,q,hS,hQquot,fun z v => ?_⟩
  have hz : z = ∑ t, b.repr z t • b t := (b.sum_repr z).symm
  rw [hz]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  simp only [hgq]

end GeneralFrontal
end

/- Deleting all three partitions. -/
section
open Module
variable {K : Type*} [Field K] {N M L : ℕ}
  {U : Fin N → Type*} {V : Fin M → Type*} {W : Fin L → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
  [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ k, AddCommGroup (W k)] [∀ k, Module K (W k)]
  [∀ i, FiniteDimensional K (U i)]
  [∀ j, FiniteDimensional K (V j)]
  [∀ k, FiniteDimensional K (W k)]

abbrev ColAux := (∀ i, U i) × (∀ i, Tags (K := K) (U := U) i)
abbrev OutRows := RowSpace (∀ j, V j) U (Tags (K := K) (U := U))
abbrev ColParts (j₀ : Fin M) (j : Fin M) :=
  Enlarged (V := V) (B := ColAux (K := K) (U := U)) j₀ j
abbrev FrontParts (k₀ : Fin L) (k : Fin L) :=
  Enlarged (V := W) (B := Fin N → K) k₀ k
abbrev RowParts (_ : Fin 1) := OutRows (K := K) (U := U) (V := V)

instance (priority := 1100) colAux_finite :
    FiniteDimensional K (ColAux (K := K) (U := U)) := by
  dsimp [ColAux]
  infer_instance

instance (priority := 1100) outRows_finite :
    FiniteDimensional K (OutRows (K := K) (U := U) (V := V)) := by
  dsimp [OutRows,RowSpace]
  infer_instance

instance (priority := 1100) colParts_finite (j₀ : Fin M) (j : Fin M) :
    FiniteDimensional K (ColParts (K := K) (U := U) (V := V) j₀ j) := by
  dsimp [ColParts,Enlarged]
  infer_instance

instance (priority := 1100) frontParts_finite (k₀ : Fin L) (k : Fin L) :
    FiniteDimensional K (FrontParts (K := K) (N := N) (W := W) k₀ k) := by
  dsimp [FrontParts,Enlarged]
  infer_instance

instance (priority := 1100) rowParts_finite (r : Fin 1) :
    FiniteDimensional K (RowParts (K := K) (U := U) (V := V) r) :=
  outRows_finite

abbrev frontFrame (k₀ : Fin L) := regroup (K := K) (V := W) (B := Fin N → K) k₀
abbrev columnFrame (j₀ : Fin M) :=
  regroup (K := K) (V := V) (B := ColAux (K := K) (U := U)) j₀

/-- Delete the row partition, retaining the other two actual partitions. -/
def deleteRow (j₀ : Fin M) (k₀ : Fin L)
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    (∀ k, FrontParts (K := K) (N := N) (W := W) k₀ k) →ₗ[K]
      (∀ j, ColParts (K := K) (U := U) (V := V) j₀ j) →ₗ[K]
        (∀ i : Fin 1, RowParts (K := K) (U := U) (V := V) i) where
  toFun a :=
    { toFun := fun b _ => paddingCompile X
        ((frontFrame (K := K) (N := N) (W := W) k₀).symm a)
        ((columnFrame (K := K) (U := U) (V := V) j₀).symm b)
      map_add' := by intros; funext r; simp
      map_smul' := by intros; funext r; simp }
  map_add' := by
    intros
    apply LinearMap.ext
    intro b
    funext r
    simp
  map_smul' := by
    intros
    apply LinearMap.ext
    intro b
    funext r
    simp

theorem deleteRow_reverse [Nontrivial (Fin N)] (j₀ : Fin M) (k₀ : Fin L)
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i))
    (h : bilinearPartsIso (deleteRow j₀ k₀ X) (deleteRow j₀ k₀ Y)) : bilinearPartsIso X Y := by
  classical
  obtain ⟨GP,GQ,GR,ht⟩ := h
  let F := frontFrame (K := K) (N := N) (W := W) k₀
  let C := columnFrame (K := K) (U := U) (V := V) j₀
  let R := F ≪≫ₗ LinearEquiv.piCongrRight GR ≪≫ₗ F.symm
  let Q := C ≪≫ₗ LinearEquiv.piCongrRight GQ ≪≫ₗ C.symm
  let P := GP 0
  have he : ∀ z, P.toLinearMap.comp ((frontSlice X (R z)).comp Q.toLinearMap) =
      frontSlice Y z := by
    intro z
    apply LinearMap.ext
    intro x
    have hh := congrFun (ht (F z) (C x)) 0
    change P (paddingCompile X (F.symm ((LinearEquiv.piCongrRight GR) (F z)))
      (C.symm ((LinearEquiv.piCongrRight GQ) (C x)))) =
      paddingCompile Y (F.symm (F z)) (C.symm (C x)) at hh
    simpa [R,Q,paddingCompile] using hh
  obtain ⟨S,g,q,hS,hq,hdata⟩ := one_axis_reverse_exact X Y R P Q he
  have hRR : ∀ x, F (R x) = (LinearEquiv.piCongrRight GR) (F x) := by
    intro x
    simp [R]
  have hQQ : ∀ x, C (Q x) = (LinearEquiv.piCongrRight GQ) (C x) := by
    intro x
    simp [Q]
  obtain ⟨gV,hV⟩ := recover_quotient j₀ GQ Q hQQ q hq
  have hSq : ∀ z, S z = (R (z,0)).1 := fun z => (congrArg Prod.fst (hS z)).symm
  obtain ⟨gW,hW⟩ := recover_quotient k₀ GR R hRR S hSq
  refine ⟨g,gV,gW,fun z v => ?_⟩
  simpa only [hV,hW] using hdata z v

theorem deleteRow_forward (j₀ : Fin M) (k₀ : Fin L)
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i))
    (h : bilinearPartsIso X Y) : bilinearPartsIso (deleteRow j₀ k₀ X) (deleteRow j₀ k₀ Y) := by
  classical
  obtain ⟨g,gV,gW,h⟩ := h
  let S := LinearEquiv.piCongrRight gW
  let q := LinearEquiv.piCongrRight gV
  let Bq : ColAux (K := K) (U := U) ≃ₗ[K] ColAux (K := K) (U := U) :=
    (LinearEquiv.piCongrRight (fun i => (g i).symm)).prodCongr (LinearEquiv.refl K _)
  let GR := quotientExtend k₀ gW (LinearEquiv.refl K (Fin N → K))
  let GQ := quotientExtend j₀ gV Bq
  let P := rowLift (E := Tags (K := K) (U := U)) g q
  let F := frontFrame (K := K) (N := N) (W := W) k₀
  let C := columnFrame (K := K) (U := U) (V := V) j₀
  refine ⟨fun _ => P,GQ,GR,?_⟩
  intro a b
  funext r
  change P (paddingCompile X (F.symm ((LinearEquiv.piCongrRight GR) a))
    (C.symm ((LinearEquiv.piCongrRight GQ) b))) = paddingCompile Y (F.symm a) (C.symm b)
  have hF : F.symm ((LinearEquiv.piCongrRight GR) a) =
      (S (F.symm a).1,(F.symm a).2) := by
    have hh := congrArg F.symm
      (extend_apply k₀ gW (LinearEquiv.refl K (Fin N → K)) (F.symm a))
    change F.symm ((LinearEquiv.piCongrRight GR) (F (F.symm a))) =
      F.symm (F (S (F.symm a).1,(F.symm a).2)) at hh
    simpa only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply] using hh
  have hC : C.symm ((LinearEquiv.piCongrRight GQ) b) = colLift g q (C.symm b) := by
    have hh := congrArg C.symm (extend_apply j₀ gV Bq (C.symm b))
    change C.symm ((LinearEquiv.piCongrRight GQ) (C (C.symm b))) =
      C.symm (C (colLift g q (C.symm b))) at hh
    simpa only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply] using hh
  rw [hF,hC]
  let z := F.symm a
  let x := C.symm b
  have hx : (LinearEquiv.piCongrRight g).toLinearMap.comp
      ((X (S z.1)).comp q.toLinearMap) = Y z.1 := by
    apply LinearMap.ext
    intro v
    exact h z.1 v
  have he := mixedSlice_covariance (E := Tags (K := K) (U := U)) g q (X (S z.1)) z.2
  rw [hx] at he
  exact LinearMap.congr_fun he x

theorem deleteRow_iff [Nontrivial (Fin N)] (j₀ : Fin M) (k₀ : Fin L)
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    bilinearPartsIso X Y ↔ bilinearPartsIso (deleteRow j₀ k₀ X) (deleteRow j₀ k₀ Y) :=
  ⟨deleteRow_forward j₀ k₀ X Y,deleteRow_reverse j₀ k₀ X Y⟩

def stageFactor (n : ℕ) : ℕ := 2 * n * 2 ^ n + 2 * n + 4

/-- Linear overhead of the actual constructor with its two surviving partitions. -/
theorem deleteRow_size (j₀ : Fin M) (k₀ : Fin L) :
    finrank K (∀ k, FrontParts (K := K) (N := N) (W := W) k₀ k) +
      finrank K (∀ j, ColParts (K := K) (U := U) (V := V) j₀ j) +
      finrank K (∀ r : Fin 1, RowParts (K := K) (U := U) (V := V) r) ≤
    stageFactor N * (finrank K (∀ k, W k) + finrank K (∀ j, V j) +
      finrank K (∀ i, U i) + 1) := by
  have hF := (frontFrame (K := K) (N := N) (W := W) k₀).finrank_eq
  have hC := (columnFrame (K := K) (U := U) (V := V) j₀).finrank_eq
  have hR : finrank K (∀ r : Fin 1, RowParts (K := K) (U := U) (V := V) r) =
      finrank K (OutRows (K := K) (U := U) (V := V)) := by
    simp [RowParts,Module.finrank_pi_fintype]
  rw [← hF,← hC,hR]
  have hs := one_axis_size (K := K) (V := ∀ j, V j) (U := U)
    (T := Fin (finrank K (∀ k, W k)))
  have hs' : finrank K (OutRows (K := K) (U := U) (V := V)) +
      finrank K ((∀ j, V j) × ColAux (K := K) (U := U)) +
      finrank K ((∀ k, W k) × (Fin N → K)) ≤
      stageFactor N * ((∑ i, finrank K (U i)) + finrank K (∀ j, V j) +
        finrank K (∀ k, W k) + 1) := by
    simpa only [stageFactor,Module.finrank_prod,Module.finrank_pi,
      Fintype.card_fin,Module.finrank_self] using hs
  have hr : finrank K (∀ i, U i) = ∑ i, finrank K (U i) :=
    Module.finrank_pi_fintype K
  rw [hr]
  convert hs' using 1 <;> ring

/-- The concrete three-stage tensor: delete, rotate, delete, rotate, delete. -/
def finalTensor (j₀ : Fin M) (k₀ : Fin L)
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :=
  deleteRow (0 : Fin 1) (0 : Fin 1)
    (rotateParts (deleteRow (0 : Fin 1) j₀ (rotateParts (deleteRow j₀ k₀ X))))

theorem partsIso_final_iff [Nontrivial (Fin N)] [Nontrivial (Fin M)]
    [Nontrivial (Fin L)] (j₀ : Fin M) (k₀ : Fin L)
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    bilinearPartsIso X Y ↔ bilinearPartsIso (finalTensor j₀ k₀ X) (finalTensor j₀ k₀ Y) := by
  let X₁ := deleteRow j₀ k₀ X
  let Y₁ := deleteRow j₀ k₀ Y
  let X₂ := deleteRow (0 : Fin 1) j₀ (rotateParts X₁)
  let Y₂ := deleteRow (0 : Fin 1) j₀ (rotateParts Y₁)
  have h₁ := deleteRow_iff j₀ k₀ X Y
  have hr₁ := partsIso_rotate_iff X₁ Y₁
  have h₂ := deleteRow_iff (0 : Fin 1) j₀ (rotateParts X₁) (rotateParts Y₁)
  have hr₂ := partsIso_rotate_iff X₂ Y₂
  have h₃ := deleteRow_iff (0 : Fin 1) (0 : Fin 1) (rotateParts X₂) (rotateParts Y₂)
  exact h₁.trans (hr₁.trans (h₂.trans (hr₂.trans h₃)))

section SinglePart
variable {D : Fin 1 → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]

theorem singleton_blocks (F : (∀ i, D i) ≃ₗ[K] (∀ i, D i)) :
    ∃ g : ∀ i, D i ≃ₗ[K] D i, LinearEquiv.piCongrRight g = F := by
  apply (preservesBlocks_iff F).mp
  intro i x
  have hs : ∀ v : ∀ i, D i, Pi.single i (v i) = v := by
    intro v
    funext j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    simp
  rw [hs,hs]

variable {A B C : Fin 1 → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]

theorem singleton_parts_iff
    (X Y : (∀ i, A i) →ₗ[K] (∀ i, B i) →ₗ[K] (∀ i, C i)) :
    bilinearPartsIso X Y ↔ Iso X Y := by
  constructor
  · rintro ⟨P,Q,R,h⟩
    exact ⟨LinearEquiv.piCongrRight P,LinearEquiv.piCongrRight Q,
      LinearEquiv.piCongrRight R,h⟩
  · rintro ⟨P,Q,R,h⟩
    obtain ⟨gP,hP⟩ := singleton_blocks P
    obtain ⟨gQ,hQ⟩ := singleton_blocks Q
    obtain ⟨gR,hR⟩ := singleton_blocks R
    exact ⟨gP,gQ,gR,by simpa only [hP,hQ,hR] using h⟩

end SinglePart

/-- Complete deletion of all three partitions, into ordinary tensor isomorphism. -/
theorem partition_compiler_correct [Nontrivial (Fin N)] [Nontrivial (Fin M)]
    [Nontrivial (Fin L)] (j₀ : Fin M) (k₀ : Fin L)
    (X Y : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    bilinearPartsIso X Y ↔ Iso (finalTensor j₀ k₀ X) (finalTensor j₀ k₀ Y) :=
  (partsIso_final_iff j₀ k₀ X Y).trans (singleton_parts_iff _ _)

/-- Sum of the three actual side dimensions of a curried tensor. -/
def partitionTotalDim {A B C : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (_X : A →ₗ[K] B →ₗ[K] C) : ℕ :=
  finrank K A + finrank K B + finrank K C

theorem stage_total_size (j₀ : Fin M) (k₀ : Fin L)
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    partitionTotalDim (deleteRow j₀ k₀ X) ≤ stageFactor N * (partitionTotalDim X + 1) :=
  deleteRow_size (K := K) (U := U) (V := V) (W := W) j₀ k₀

theorem rotation_total_size
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    partitionTotalDim (rotateParts X) = partitionTotalDim X :=
  rotation_total_dimension (K := K) (U := U) (V := V) (W := W)

def compilerFactor (n m l : ℕ) : ℕ :=
  (stageFactor m + 1) * (stageFactor l + 1) * (stageFactor n + 1)

private theorem add_one_size {a b c : ℕ} (h : a ≤ c * (b+1)) :
    a+1 ≤ (c+1)*(b+1) := by nlinarith

/-- A linear bound for the actual final three-tensor, with a shape-independent
constant whenever the three numbers of partition blocks are fixed. -/
theorem partition_compiler_size (j₀ : Fin M) (k₀ : Fin L)
    (X : (∀ k, W k) →ₗ[K] (∀ j, V j) →ₗ[K] (∀ i, U i)) :
    partitionTotalDim (finalTensor j₀ k₀ X) ≤ compilerFactor N M L * (partitionTotalDim X + 1) := by
  let X₁ := deleteRow j₀ k₀ X
  let X₂ := deleteRow (0 : Fin 1) j₀ (rotateParts X₁)
  have h₁ := stage_total_size j₀ k₀ X
  have h₂ := stage_total_size (0 : Fin 1) j₀ (rotateParts X₁)
  have h₃ := stage_total_size (0 : Fin 1) (0 : Fin 1) (rotateParts X₂)
  rw [rotation_total_size] at h₂ h₃
  have h₁' : partitionTotalDim X₁ + 1 ≤ (stageFactor N + 1) * (partitionTotalDim X + 1) :=
    add_one_size h₁
  have h₂' : partitionTotalDim X₂ + 1 ≤ (stageFactor L + 1) * (partitionTotalDim X₁ + 1) :=
    add_one_size h₂
  have h₃' : partitionTotalDim (finalTensor j₀ k₀ X) + 1 ≤
      (stageFactor M + 1) * (partitionTotalDim X₂ + 1) := add_one_size h₃
  have h₁₂ := h₂'.trans (Nat.mul_le_mul_left (stageFactor L + 1) h₁')
  have h₁₂₃ := h₃'.trans (Nat.mul_le_mul_left (stageFactor M + 1) h₁₂)
  calc
    partitionTotalDim (finalTensor j₀ k₀ X) ≤ partitionTotalDim (finalTensor j₀ k₀ X) + 1 := by omega
    _ ≤ (stageFactor M + 1) * ((stageFactor L + 1) *
        ((stageFactor N + 1) * (partitionTotalDim X + 1))) := h₁₂₃
    _ = compilerFactor N M L * (partitionTotalDim X + 1) := by simp [compilerFactor]; ring

end

/- Synchronizing primal and dual actions. -/
section
open Module
universe u
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- False is a primal space; true is its dual. -/
abbrev View : Bool → Type u
  | false => V
  | true => Dual K V

instance viewAddCommGroup (b : Bool) : AddCommGroup (View (K := K) (V := V) b) :=
  match b with
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup (Dual K V))

instance viewModule (b : Bool) : Module K (View (K := K) (V := V) b) :=
  match b with
  | false => inferInstanceAs (Module K V)
  | true => inferInstanceAs (Module K (Dual K V))

instance viewFinite [FiniteDimensional K V] (b : Bool) :
    FiniteDimensional K (View (K := K) (V := V) b) :=
  match b with
  | false => inferInstanceAs (FiniteDimensional K V)
  | true => inferInstanceAs (FiniteDimensional K (Dual K V))

def viewAction (g : V ≃ₗ[K] V) (b : Bool) :
    View (K := K) (V := V) b ≃ₗ[K] View (K := K) (V := V) b :=
  match b with
  | false => g
  | true => g.symm.dualMap

def pairing (b : Bool) :
    View (K := K) (V := V) b →ₗ[K] View (K := K) (V := V) (!b) →ₗ[K] K :=
  match b with
  | false => Module.Dual.eval K V
  | true => LinearMap.id

theorem pairing_action (g : V ≃ₗ[K] V) (b : Bool)
    (x : View (K := K) (V := V) b) (y : View (K := K) (V := V) (!b)) :
    pairing b (viewAction g b x) (viewAction g (!b) y) = pairing b x y := by
  cases b
  · change Dual K V at y
    change y (g.symm (g x)) = y x
    simp
  · change x (g.symm (g y)) = x y
    simp

/-- An actual evaluation pairing determines the contragredient action. -/
theorem pairing_transport_iff (P : V ≃ₗ[K] V) (Q : Dual K V ≃ₗ[K] Dual K V) :
    (∀ v f, Q f (P v) = f v) ↔ Q = P.symm.dualMap := by
  constructor
  · intro h
    ext f v
    simpa using h (P.symm v) f
  · rintro rfl
    simp

theorem pairing_determines_first [FiniteDimensional K V] (g : V ≃ₗ[K] V)
    (b : Bool) (P : View (K := K) (V := V) b ≃ₗ[K] View (K := K) (V := V) b)
    (h : ∀ x y, pairing b (P x) (viewAction g (!b) y) = pairing b x y) :
    P = viewAction g b := by
  cases b
  · apply LinearEquiv.ext
    intro x
    apply (Module.evalEquiv K V).injective
    ext f
    have hh := h x (g.dualMap f)
    change f (P x) = f (g x)
    change f (g (g.symm (P x))) = f (g x) at hh
    simpa using hh
  · apply LinearEquiv.ext
    intro f
    apply LinearMap.ext
    intro x
    have hh := h f (g.symm x)
    change (P f) x = f (g.symm x)
    change (P f) (g (g.symm x)) = f (g.symm x) at hh
    simpa using hh

/-- Five explicit cross-axis pairings synchronize six hub transformations. -/
theorem hub_recovery [FiniteDimensional K V]
    (pU pV pW : V ≃ₗ[K] V)
    (nU nV nW : Dual K V ≃ₗ[K] Dual K V)
    (hUV : ∀ v f, nV f (pU v) = f v)
    (hUW : ∀ v f, nW f (pU v) = f v)
    (hVW : ∀ v f, nW f (pV v) = f v)
    (hWV : ∀ v f, nV f (pW v) = f v)
    (hVU : ∀ v f, nU f (pV v) = f v) :
    pV = pU ∧ pW = pU ∧ nU = pU.symm.dualMap ∧
      nV = pU.symm.dualMap ∧ nW = pU.symm.dualMap := by
  have hNV := (pairing_transport_iff pU nV).mp hUV
  have hNW := (pairing_transport_iff pU nW).mp hUW
  have hPV : pV = pU := by
    have hh := pairing_determines_first pU false pV (by
      intro v f
      change Dual K V at f
      change (pU.symm.dualMap f) (pV v) = f v
      rw [← hNW]
      exact hVW v f)
    exact hh
  have hPW : pW = pU := by
    have hh := pairing_determines_first pU false pW (by
      intro v f
      change Dual K V at f
      change (pU.symm.dualMap f) (pW v) = f v
      rw [← hNV]
      exact hWV v f)
    exact hh
  have hNU := (pairing_transport_iff pV nU).mp hVU
  exact ⟨hPV,hPW,by simpa [hPV] using hNU,hNV,hNW⟩

theorem scalar_apply (H : K ≃ₗ[K] K) (x : K) : H x = H 1 * x := by
  simpa [mul_comm] using H.map_smul x (1 : K)

theorem scalar_ne_zero (H : K ≃ₗ[K] K) : H 1 ≠ 0 := by
  intro h
  have he : H 1 = H 0 := by simpa using h
  exact one_ne_zero (H.injective he)

def normalizeEquiv (H : V ≃ₗ[K] V) (a : K) (ha : a ≠ 0) : V ≃ₗ[K] V :=
  H ≪≫ₗ LinearEquiv.smulOfNeZero K V a⁻¹ (inv_ne_zero ha)

@[simp] theorem normalizeEquiv_apply (H : V ≃ₗ[K] V) (a : K) (ha : a ≠ 0) (x : V) :
    normalizeEquiv H a ha x = a⁻¹ • H x := by
  simp [normalizeEquiv]

theorem normalize_scalar (H : K ≃ₗ[K] K) :
    normalizeEquiv H (H 1) (scalar_ne_zero H) = LinearEquiv.refl K K := by
  ext x
  rw [normalizeEquiv_apply,scalar_apply H x]
  simp [smul_eq_mul]

section Forms
variable {A B C : Type u}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
abbrev Triform := A →ₗ[K] B →ₗ[K] C →ₗ[K] K

theorem triform_smul (T : Triform (K := K) (A := A) (B := B) (C := C))
    (a b c : K) (x : A) (y : B) (z : C) :
    T (a • x) (b • y) (c • z) = (a*b*c) * T x y z := by
  simp [smul_eq_mul]
  ring

theorem normalized_transport
    (T S : Triform (K := K) (A := A) (B := B) (C := C))
    (P : A ≃ₗ[K] A) (Q : B ≃ₗ[K] B) (R : C ≃ₗ[K] C)
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a*b*c = 1)
    (h : ∀ x y z, T (P x) (Q y) (R z) = S x y z) :
    ∀ x y z, T (normalizeEquiv P a ha x) (normalizeEquiv Q b hb y)
      (normalizeEquiv R c hc z) = S x y z := by
  intro x y z
  simp only [normalizeEquiv_apply,triform_smul,h]
  have hi : a⁻¹*b⁻¹*c⁻¹ = 1 := by
    simpa [mul_comm,mul_left_comm,mul_assoc] using congrArg (fun t : K => t⁻¹) habc
  rw [hi,one_mul]

end Forms

theorem view_finrank [FiniteDimensional K V] (b : Bool) :
    finrank K (View (K := K) (V := V) b) = finrank K V := by
  cases b
  · rfl
  · exact Subspace.dual_finrank_eq

theorem normalize_scalar_eq (H : K ≃ₗ[K] K) (a : K) (ha : a ≠ 0)
    (h : H 1 = a) : normalizeEquiv H a ha = LinearEquiv.refl K K := by
  subst a
  exact normalize_scalar H

theorem common_unit {a b c m : K} (h : a*b*c = 1) (hm : m*b*c = 1) : m = a := by
  have hbc : b*c ≠ 0 := by
    intro hz
    rw [mul_assoc,hz,mul_zero] at h
    exact zero_ne_one h
  apply mul_right_cancel₀ hbc
  simpa [mul_assoc] using hm.trans h.symm

section Axes
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  [∀ c, FiniteDimensional K (Base c)]
  {P E : Type} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]

abbrev OrigSpace (spec : P → Fin r × Bool) (i : P) :=
  View (K := K) (V := Base (spec i).1) (spec i).2

/-- Original parts, positive hubs, negative hubs, scalar markers, scalar anchor. -/
abbrev Axis (spec : P → Fin r × Bool) (E : Type) :=
  (∀ i, OrigSpace (K := K) (Base := Base) spec i) ×
    (∀ c, Base c) × (∀ c, Dual K (Base c)) × (E → K) × K

abbrev aOrig {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E) := x.1
abbrev aPos {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E) := x.2.1
abbrev aNeg {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E) := x.2.2.1
abbrev aMark {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E) := x.2.2.2.1
abbrev aAnchor {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E) := x.2.2.2.2

def hub {spec : P → Fin r × Bool} (x : Axis (K := K) (Base := Base) spec E)
    (c : Fin r) (b : Bool) : View (K := K) (V := Base c) b :=
  match b with
  | false => aPos x c
  | true => aNeg x c

structure AxisMaps (spec : P → Fin r × Bool) (E : Type) where
  original : ∀ i, OrigSpace (K := K) (Base := Base) spec i ≃ₗ[K] OrigSpace (K := K) (Base := Base) spec i
  primal : ∀ c, Base c ≃ₗ[K] Base c
  dual : ∀ c, Dual K (Base c) ≃ₗ[K] Dual K (Base c)
  marker : ∀ e : E, K ≃ₗ[K] K
  anchor : K ≃ₗ[K] K

variable {spec : P → Fin r × Bool}

def axisAct (H : AxisMaps (K := K) (Base := Base) spec E) :
    Axis (K := K) (Base := Base) spec E ≃ₗ[K] Axis (K := K) (Base := Base) spec E :=
  (LinearEquiv.piCongrRight H.original).prodCongr
    ((LinearEquiv.piCongrRight H.primal).prodCongr
      ((LinearEquiv.piCongrRight H.dual).prodCongr
        ((LinearEquiv.piCongrRight H.marker).prodCongr H.anchor)))

@[simp] theorem act_primal (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : Axis (K := K) (Base := Base) spec E) (c : Fin r) :
    aPos (axisAct H x) c = H.primal c (aPos x c) := rfl
@[simp] theorem act_dual (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : Axis (K := K) (Base := Base) spec E) (c : Fin r) :
    aNeg (axisAct H x) c = H.dual c (aNeg x c) := rfl
@[simp] theorem act_marker (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : Axis (K := K) (Base := Base) spec E) (e : E) :
    aMark (axisAct H x) e = H.marker e (aMark x e) := rfl
@[simp] theorem act_anchor (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : Axis (K := K) (Base := Base) spec E) :
    aAnchor (axisAct H x) = H.anchor (aAnchor x) := rfl

def axisLiftBase (g : ∀ c, Base c ≃ₗ[K] Base c) :
    AxisMaps (K := K) (Base := Base) spec E where
  original i := viewAction (g (spec i).1) (spec i).2
  primal := g
  dual c := (g c).symm.dualMap
  marker _ := LinearEquiv.refl K K
  anchor := LinearEquiv.refl K K

def axisNormalize (H : AxisMaps (K := K) (Base := Base) spec E)
    (a : K) (ha : a ≠ 0) : AxisMaps (K := K) (Base := Base) spec E where
  original i := normalizeEquiv (H.original i) a ha
  primal c := normalizeEquiv (H.primal c) a ha
  dual c := normalizeEquiv (H.dual c) a ha
  marker e := normalizeEquiv (H.marker e) a ha
  anchor := normalizeEquiv H.anchor a ha

@[simp] theorem normalize_act (H : AxisMaps (K := K) (Base := Base) spec E)
    (a : K) (ha : a ≠ 0) :
    (axisAct (axisNormalize H a ha)) = normalizeEquiv (axisAct H) a ha := by
  ext x <;> rfl

theorem normalized_markers (H : AxisMaps (K := K) (Base := Base) spec E)
    (h : ∀ e, H.marker e 1 = H.anchor 1) :
    ∀ e, ((axisNormalize H) (H.anchor 1) (scalar_ne_zero H.anchor)).marker e = LinearEquiv.refl K K :=
  fun e => normalize_scalar_eq (H.marker e) (H.anchor 1) (scalar_ne_zero H.anchor) (h e)

theorem hub_act (H : AxisMaps (K := K) (Base := Base) spec E)
    (g : ∀ c, Base c ≃ₗ[K] Base c)
    (hp : ∀ c, H.primal c = g c) (hn : ∀ c, H.dual c = (g c).symm.dualMap)
    (x : Axis (K := K) (Base := Base) spec E) (c : Fin r) (b : Bool) :
    hub (axisAct H x) c b = viewAction (g c) b (hub x c b) := by
  cases b
  · change H.primal c (aPos x c) = g c (aPos x c)
    rw [hp]
  · change H.dual c (aNeg x c) = (g c).symm.dualMap (aNeg x c)
    rw [hn]

theorem axis_dimension (spec : P → Fin r × Bool) :
    finrank K (Axis (K := K) (Base := Base) spec E) =
      (∑ i, finrank K (Base (spec i).1)) + 2 * (∑ c, finrank K (Base c)) +
        Fintype.card E + 1 := by
  simp [Axis,OrigSpace,Module.finrank_prod,Module.finrank_pi_fintype,view_finrank]
  omega

end Axes

section FormConstructors
variable {A B C : Type u}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

def pairLast (p : A →ₗ[K] B →ₗ[K] K) (c : C →ₗ[K] K) :
    Triform (K := K) (A := A) (B := B) (C := C) where
  toFun a :=
    { toFun := fun b => (p a b) • c
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }
  map_add' := by intros; ext; simp [add_smul]
  map_smul' := by intros; ext; simp [smul_smul]

@[simp] theorem pairLast_apply (p : A →ₗ[K] B →ₗ[K] K) (c : C →ₗ[K] K)
    (a : A) (b : B) (z : C) : pairLast p c a b z = p a b * c z := rfl

def cycle (T : Triform (K := K) (A := A) (B := B) (C := C)) :
    Triform (K := K) (A := B) (B := C) (C := A) where
  toFun b :=
    { toFun := fun c =>
        { toFun := fun a => T a b c
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem cycle_apply (T : Triform (K := K) (A := A) (B := B) (C := C))
    (a : A) (b : B) (c : C) : cycle T b c a = T a b c := rfl

def scalarPair (a : A →ₗ[K] K) (b : B →ₗ[K] K) : A →ₗ[K] B →ₗ[K] K where
  toFun x := (a x) • b
  map_add' := by intros; simp [add_smul]
  map_smul' := by intros; simp [smul_smul]

@[simp] theorem scalarPair_apply (a : A →ₗ[K] K) (b : B →ₗ[K] K) (x : A) (y : B) :
    scalarPair a b x y = a x * b y := rfl

def pullPair {X Y : Type u} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (p : X →ₗ[K] Y →ₗ[K] K) (a : A →ₗ[K] X) (b : B →ₗ[K] Y) :
    A →ₗ[K] B →ₗ[K] K where
  toFun x := (p (a x)).comp b
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem pullPair_apply {X Y : Type u} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (p : X →ₗ[K] Y →ₗ[K] K) (a : A →ₗ[K] X) (b : B →ₗ[K] Y) (x : A) (y : B) :
    pullPair p a b x y = p (a x) (b y) := rfl

def pullForm {X Y Z : Type u} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
    (T : Triform (K := K) (A := X) (B := Y) (C := Z))
    (a : A →ₗ[K] X) (b : B →ₗ[K] Y) (c : C →ₗ[K] Z) :
    Triform (K := K) (A := A) (B := B) (C := C) where
  toFun x :=
    { toFun := fun y => (T (a x) (b y)).comp c
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem pullForm_apply {X Y Z : Type u} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
    (T : Triform (K := K) (A := X) (B := Y) (C := Z))
    (a : A →ₗ[K] X) (b : B →ₗ[K] Y) (c : C →ₗ[K] Z) (x : A) (y : B) (z : C) :
    pullForm T a b c x y z = T (a x) (b y) (c z) := rfl

end FormConstructors

section AxisProjections
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P E : Type} {spec : P → Fin r × Bool}

def originalProj : Axis (K := K) (Base := Base) spec E →ₗ[K]
    (∀ i, OrigSpace (K := K) (Base := Base) spec i) where
  toFun := aOrig
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def origProj (i : P) : Axis (K := K) (Base := Base) spec E →ₗ[K]
    OrigSpace (K := K) (Base := Base) spec i :=
  (LinearMap.proj i).comp originalProj
def posProj (c : Fin r) : Axis (K := K) (Base := Base) spec E →ₗ[K] Base c where
  toFun x := aPos x c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def negProj (c : Fin r) : Axis (K := K) (Base := Base) spec E →ₗ[K] Dual K (Base c) where
  toFun x := aNeg x c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def markProj (e : E) : Axis (K := K) (Base := Base) spec E →ₗ[K] K where
  toFun x := aMark x e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def anchorProj : Axis (K := K) (Base := Base) spec E →ₗ[K] K where
  toFun := aAnchor
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def hubProj (c : Fin r) (b : Bool) :
    Axis (K := K) (Base := Base) spec E →ₗ[K] View (K := K) (V := Base c) b :=
  match b with
  | false => posProj c
  | true => negProj c

@[simp] theorem hubProj_apply (c : Fin r) (b : Bool)
    (x : Axis (K := K) (Base := Base) spec E) : hubProj c b x = hub x c b := by cases b <;> rfl

end AxisProjections

section Construction
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  (sp : P → Fin r × Bool) (sq : Q → Fin r × Bool) (sr : R → Fin r × Bool)

abbrev UM := Fin r ⊕ (Fin r ⊕ Q)
abbrev VM := Fin r ⊕ R
abbrev WM := Fin r ⊕ (Fin r ⊕ P)
abbrev UA := Axis (K := K) (Base := Base) sp (UM (r := r) (Q := Q))
abbrev VA := Axis (K := K) (Base := Base) sq (VM (r := r) (R := R))
abbrev WA := Axis (K := K) (Base := Base) sr (WM (r := r) (P := P))
abbrev Input := Triform (K := K)
  (A := ∀ i, OrigSpace (K := K) (Base := Base) sp i)
  (B := ∀ i, OrigSpace (K := K) (Base := Base) sq i)
  (C := ∀ i, OrigSpace (K := K) (Base := Base) sr i)

/-- Explicit linked-to-partitioned tensor: payload, anchors, markers, five
hub pairings per base space, and one pairing for each original part. -/
def linkedCompile (T : Input (K := K) (Base := Base) sp sq sr) :
    Triform (K := K) (A := UA (K := K) (Base := Base) sp (Q := Q))
      (B := VA (K := K) (Base := Base) sq (R := R)) (C := WA (K := K) (Base := Base) sr (P := P)) :=
  pullForm T originalProj originalProj originalProj +
  pairLast (scalarPair anchorProj anchorProj) anchorProj +
  (∑ e, pairLast (scalarPair (markProj e) anchorProj) anchorProj) +
  (∑ e, pairLast (scalarPair anchorProj (markProj e)) anchorProj) +
  (∑ e, pairLast (scalarPair anchorProj anchorProj) (markProj e)) +
  (∑ c, pairLast (pullPair (pairing false) (posProj c) (negProj c))
    (markProj (Sum.inl c))) +
  (∑ c, cycle (pairLast (pullPair (pairing true) (negProj c) (posProj c))
    (markProj (Sum.inl c)))) +
  (∑ c, cycle (cycle (pairLast (pullPair (pairing false) (posProj c) (negProj c))
    (markProj (Sum.inl c))))) +
  (∑ c, cycle (cycle (pairLast (pullPair (pairing true) (negProj c) (posProj c))
    (markProj (Sum.inr (Sum.inl c)))))) +
  (∑ c, pairLast (pullPair (pairing true) (negProj c) (posProj c))
    (markProj (Sum.inr (Sum.inl c)))) +
  (∑ i, pairLast (pullPair (pairing (sp i).2) (origProj i)
    (hubProj (sp i).1 (!(sp i).2))) (markProj (Sum.inr (Sum.inr i)))) +
  (∑ j, cycle (cycle (pairLast (pullPair (pairing (sq j).2) (origProj j)
    (hubProj (sq j).1 (!(sq j).2))) (markProj (Sum.inr (Sum.inr j)))))) +
  (∑ k, cycle (pairLast (pullPair (pairing (sr k).2) (origProj k)
    (hubProj (sr k).1 (!(sr k).2))) (markProj (Sum.inr k))))

variable {sp sq sr}

theorem compile_apply (T : Input (K := K) (Base := Base) sp sq sr)
    (x : UA (K := K) (Base := Base) sp (Q := Q))
    (y : VA (K := K) (Base := Base) sq (R := R))
    (z : WA (K := K) (Base := Base) sr (P := P)) :
    linkedCompile sp sq sr T x y z =
    T (aOrig x) (aOrig y) (aOrig z) +
    aAnchor x * aAnchor y * aAnchor z +
    (∑ e, aMark x e * aAnchor y * aAnchor z) +
    (∑ e, aAnchor x * aMark y e * aAnchor z) +
    (∑ e, aAnchor x * aAnchor y * aMark z e) +
    (∑ c, aNeg y c (aPos x c) * aMark z (Sum.inl c)) +
    (∑ c, aNeg z c (aPos x c) * aMark y (Sum.inl c)) +
    (∑ c, aNeg z c (aPos y c) * aMark x (Sum.inl c)) +
    (∑ c, aNeg y c (aPos z c) * aMark x (Sum.inr (Sum.inl c))) +
    (∑ c, aNeg x c (aPos y c) * aMark z (Sum.inr (Sum.inl c))) +
    (∑ i, pairing (sp i).2 (aOrig x i) (hub y (sp i).1 (!(sp i).2)) *
      aMark z (Sum.inr (Sum.inr i))) +
    (∑ j, pairing (sq j).2 (aOrig y j) (hub z (sq j).1 (!(sq j).2)) *
      aMark x (Sum.inr (Sum.inr j))) +
    (∑ k, pairing (sr k).2 (aOrig z k) (hub x (sr k).1 (!(sr k).2)) *
      aMark y (Sum.inr k)) := by
  simp [linkedCompile, originalProj,origProj,posProj,negProj,markProj,anchorProj,
    LinearMap.sum_apply,pairing]
  rfl

end Construction

section Injections
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P E : Type} [DecidableEq P] [DecidableEq E] {spec : P → Fin r × Bool}

def onlyOrig (x : ∀ i, OrigSpace (K := K) (Base := Base) spec i) :
    Axis (K := K) (Base := Base) spec E := (x,0,0,0,0)
def onlyPos (c : Fin r) (x : Base c) :
    Axis (K := K) (Base := Base) spec E := (0,Pi.single c x,0,0,0)
def onlyNeg (c : Fin r) (x : Dual K (Base c)) :
    Axis (K := K) (Base := Base) spec E := (0,0,Pi.single c x,0,0)
def onlyMark (e : E) (x : K) :
    Axis (K := K) (Base := Base) spec E := (0,0,0,Pi.single e x,0)
def onlyAnchor (x : K) : Axis (K := K) (Base := Base) spec E := (0,0,0,0,x)

theorem map_single {I : Type} [DecidableEq I] {D : I → Type u}
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (H : ∀ i, D i ≃ₗ[K] D i) (i : I) (v : D i) :
    (fun j => H j (Pi.single i v j)) = Pi.single i (H i v) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

@[simp] theorem act_onlyOrig (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : ∀ i, OrigSpace (K := K) (Base := Base) spec i) :
    (axisAct H) (onlyOrig x) = onlyOrig (fun i => H.original i (x i)) := by
  simp [axisAct,onlyOrig]
  rfl
@[simp] theorem act_onlyPos (H : AxisMaps (K := K) (Base := Base) spec E)
    (c : Fin r) (x : Base c) :
    (axisAct H) (onlyPos c x) = onlyPos c (H.primal c x) := by
  simp [axisAct,onlyPos]
  funext j
  rw [LinearEquiv.piCongrRight_apply]
  exact congrFun (map_single H.primal c x) j
@[simp] theorem act_onlyNeg (H : AxisMaps (K := K) (Base := Base) spec E)
    (c : Fin r) (x : Dual K (Base c)) :
    (axisAct H) (onlyNeg c x) = onlyNeg c (H.dual c x) := by
  simp [axisAct,onlyNeg]
  funext j
  rw [LinearEquiv.piCongrRight_apply]
  exact congrFun (map_single H.dual c x) j
@[simp] theorem act_onlyMark (H : AxisMaps (K := K) (Base := Base) spec E)
    (e : E) (x : K) :
    (axisAct H) (onlyMark e x) = onlyMark e (H.marker e x) := by
  simp [axisAct,onlyMark]
  funext j
  rw [LinearEquiv.piCongrRight_apply]
  exact congrFun (map_single H.marker e x) j
@[simp] theorem act_onlyAnchor (H : AxisMaps (K := K) (Base := Base) spec E) (x : K) :
    (axisAct H) (onlyAnchor x) = onlyAnchor (H.anchor x) := by
  simp [axisAct,onlyAnchor]

@[simp] theorem hub_onlyOrig (x : ∀ i, OrigSpace (K := K) (Base := Base) spec i)
    (c : Fin r) (b : Bool) :
    hub (onlyOrig (E := E) x) c b = 0 := by cases b <;> rfl
@[simp] theorem hub_onlyMark (e : E) (x : K) (c : Fin r) (b : Bool) :
    hub (onlyMark (spec := spec) (Base := Base) e x) c b = 0 := by cases b <;> rfl
@[simp] theorem hub_onlyAnchor (x : K) (c : Fin r) (b : Bool) :
    hub (onlyAnchor (spec := spec) (Base := Base) (E := E) x) c b = 0 := by cases b <;> rfl

end Injections

section Extraction
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  {sp : P → Fin r × Bool} {sq : Q → Fin r × Bool} {sr : R → Fin r × Bool}
  (T : Input (K := K) (Base := Base) sp sq sr)

@[simp] theorem compile_anchor (a b c : K) :
    linkedCompile sp sq sr T (onlyAnchor a) (onlyAnchor b) (onlyAnchor c) = a*b*c := by
  simp only [compile_apply,hub_onlyAnchor]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyAnchor]

@[simp] theorem compile_umark (e : UM (r := r) (Q := Q)) (a b c : K) :
    linkedCompile sp sq sr T (onlyMark e a) (onlyAnchor b) (onlyAnchor c) = a*b*c := by
  simp only [compile_apply,hub_onlyAnchor,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyAnchor,onlyMark,Pi.single_apply]

@[simp] theorem compile_vmark (e : VM (r := r) (R := R)) (a b c : K) :
    linkedCompile sp sq sr T (onlyAnchor a) (onlyMark e b) (onlyAnchor c) = a*b*c := by
  simp only [compile_apply,hub_onlyAnchor,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyAnchor,onlyMark,Pi.single_apply]

@[simp] theorem compile_wmark (e : WM (r := r) (P := P)) (a b c : K) :
    linkedCompile sp sq sr T (onlyAnchor a) (onlyAnchor b) (onlyMark e c) = a*b*c := by
  simp only [compile_apply,hub_onlyAnchor,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyAnchor,onlyMark,Pi.single_apply]

@[simp] theorem compile_payload
    (x : ∀ i, OrigSpace (K := K) (Base := Base) sp i)
    (y : ∀ j, OrigSpace (K := K) (Base := Base) sq j)
    (z : ∀ k, OrigSpace (K := K) (Base := Base) sr k) :
    linkedCompile sp sq sr T (onlyOrig x) (onlyOrig y) (onlyOrig z) = T x y z := by
  simp only [compile_apply,hub_onlyOrig]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyOrig]

@[simp] theorem compile_uv (c : Fin r) (v : Base c) (f : Dual K (Base c)) (a : K) :
    linkedCompile sp sq sr T (onlyPos c v) (onlyNeg c f) (onlyMark (Sum.inl c) a) = f v * a := by
  simp only [compile_apply,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyPos,onlyNeg,onlyMark,Pi.single_apply]

@[simp] theorem compile_uw (c : Fin r) (v : Base c) (f : Dual K (Base c)) (a : K) :
    linkedCompile sp sq sr T (onlyPos c v) (onlyMark (Sum.inl c) a) (onlyNeg c f) = f v * a := by
  simp only [compile_apply,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyPos,onlyNeg,onlyMark,Pi.single_apply]

@[simp] theorem compile_vw (c : Fin r) (v : Base c) (f : Dual K (Base c)) (a : K) :
    linkedCompile sp sq sr T (onlyMark (Sum.inl c) a) (onlyPos c v) (onlyNeg c f) = f v * a := by
  simp only [compile_apply,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyPos,onlyNeg,onlyMark,Pi.single_apply]

@[simp] theorem compile_wv (c : Fin r) (v : Base c) (f : Dual K (Base c)) (a : K) :
    linkedCompile sp sq sr T (onlyMark (Sum.inr (Sum.inl c)) a) (onlyNeg c f) (onlyPos c v) = f v * a := by
  simp only [compile_apply,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyPos,onlyNeg,onlyMark,Pi.single_apply]

@[simp] theorem compile_vu (c : Fin r) (v : Base c) (f : Dual K (Base c)) (a : K) :
    linkedCompile sp sq sr T (onlyNeg c f) (onlyPos c v) (onlyMark (Sum.inr (Sum.inl c)) a) = f v * a := by
  simp only [compile_apply,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyPos,onlyNeg,onlyMark,Pi.single_apply]

end Extraction

section HubInjection
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P E : Type} [DecidableEq P] [DecidableEq E] {spec : P → Fin r × Bool}

def onlyHub (c : Fin r) (b : Bool) (v : View (K := K) (V := Base c) b) :
    Axis (K := K) (Base := Base) spec E :=
  match b with
  | false => onlyPos c v
  | true => onlyNeg c v

@[simp] theorem hub_onlyHub (c : Fin r) (b : Bool) (v : View (K := K) (V := Base c) b) :
    hub (onlyHub (spec := spec) (E := E) c b v) c b = v := by
  cases b <;> simp [aPos,aNeg,onlyHub,hub,onlyPos,onlyNeg]

end HubInjection

section OriginalExtraction
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  {sp : P → Fin r × Bool} {sq : Q → Fin r × Bool} {sr : R → Fin r × Bool}
  (T : Input (K := K) (Base := Base) sp sq sr)

@[simp] theorem compile_uoriginal
    (i : P) (x : ∀ i, OrigSpace (K := K) (Base := Base) sp i)
    (y : VA (K := K) (Base := Base) sq (R := R)) (a : K) :
    linkedCompile sp sq sr T (onlyOrig x) y (onlyMark (Sum.inr (Sum.inr i)) a) =
      pairing (sp i).2 (x i) (hub y (sp i).1 (!(sp i).2)) * a := by
  simp only [compile_apply,hub_onlyOrig,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyOrig,onlyMark,Pi.single_apply]

@[simp] theorem compile_voriginal
    (j : Q) (y : ∀ j, OrigSpace (K := K) (Base := Base) sq j)
    (z : WA (K := K) (Base := Base) sr (P := P)) (a : K) :
    linkedCompile sp sq sr T (onlyMark (Sum.inr (Sum.inr j)) a) (onlyOrig y) z =
      pairing (sq j).2 (y j) (hub z (sq j).1 (!(sq j).2)) * a := by
  simp only [compile_apply,hub_onlyOrig,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyOrig,onlyMark,Pi.single_apply]

@[simp] theorem compile_woriginal
    (k : R) (z : ∀ k, OrigSpace (K := K) (Base := Base) sr k)
    (x : UA (K := K) (Base := Base) sp (Q := Q)) (a : K) :
    linkedCompile sp sq sr T x (onlyMark (Sum.inr k) a) (onlyOrig z) =
      pairing (sr k).2 (z k) (hub x (sr k).1 (!(sr k).2)) * a := by
  simp only [compile_apply,hub_onlyOrig,hub_onlyMark]
  simp [aOrig,aPos,aNeg,aMark,aAnchor,onlyOrig,onlyMark,Pi.single_apply]

end OriginalExtraction

section Correctness
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  [∀ c, FiniteDimensional K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  {sp : P → Fin r × Bool} {sq : Q → Fin r × Bool} {sr : R → Fin r × Bool}

def LinkedIso (T S : Input (K := K) (Base := Base) sp sq sr) : Prop :=
  ∃ g : ∀ c, Base c ≃ₗ[K] Base c, ∀ x y z,
    T (fun i => viewAction (g (sp i).1) (sp i).2 (x i))
      (fun j => viewAction (g (sq j).1) (sq j).2 (y j))
      (fun k => viewAction (g (sr k).1) (sr k).2 (z k)) = S x y z

def CompiledIso (T S : Input (K := K) (Base := Base) sp sq sr) : Prop :=
  ∃ (HU : AxisMaps (K := K) (Base := Base) sp (UM (r := r) (Q := Q)))
    (HV : AxisMaps (K := K) (Base := Base) sq (VM (r := r) (R := R)))
    (HW : AxisMaps (K := K) (Base := Base) sr (WM (r := r) (P := P))),
    ∀ x y z, linkedCompile sp sq sr T (axisAct HU x) (axisAct HV y) (axisAct HW z) =
      linkedCompile sp sq sr S x y z

theorem act_origFamily {E : Type}
    (H : AxisMaps (K := K) (Base := Base) sp E)
    (x : Axis (K := K) (Base := Base) sp E) :
    aOrig (axisAct H x) = fun i => H.original i (aOrig x i) := rfl

theorem lift_hub {E : Type} (g : ∀ c, Base c ≃ₗ[K] Base c)
    (x : Axis (K := K) (Base := Base) sp E) (c : Fin r) (b : Bool) :
    hub ((axisAct (axisLiftBase g)) x) c b = viewAction (g c) b (hub x c b) := by
  cases b <;> rfl

theorem compiler_forward (T S : Input (K := K) (Base := Base) sp sq sr)
    (h : LinkedIso T S) : CompiledIso T S := by
  obtain ⟨g,h⟩ := h
  refine ⟨axisLiftBase g,axisLiftBase g,axisLiftBase g,?_⟩
  intro x y z
  rw [compile_apply,compile_apply]
  simp only [act_origFamily,act_anchor,act_marker,act_primal,act_dual,lift_hub]
  dsimp only [axisLiftBase,LinearEquiv.refl_apply]
  simp only [pairing_action,LinearEquiv.dualMap_apply,LinearEquiv.symm_apply_apply,h]

theorem normalized_reverse (T S : Input (K := K) (Base := Base) sp sq sr)
    (HU : AxisMaps (K := K) (Base := Base) sp (UM (r := r) (Q := Q)))
    (HV : AxisMaps (K := K) (Base := Base) sq (VM (r := r) (R := R)))
    (HW : AxisMaps (K := K) (Base := Base) sr (WM (r := r) (P := P)))
    (hU : ∀ e, HU.marker e = LinearEquiv.refl K K)
    (hV : ∀ e, HV.marker e = LinearEquiv.refl K K)
    (hW : ∀ e, HW.marker e = LinearEquiv.refl K K)
    (h : ∀ x y z, linkedCompile sp sq sr T (axisAct HU x) (axisAct HV y) (axisAct HW z) =
      linkedCompile sp sq sr S x y z) : LinkedIso T S := by
  have hhUV : ∀ c v f, HV.dual c f (HU.primal c v) = f v := by
    intro c v f
    simpa only [act_onlyPos,act_onlyNeg,act_onlyMark,hW,LinearEquiv.refl_apply,
      compile_uv,mul_one] using h (onlyPos c v) (onlyNeg c f) (onlyMark (Sum.inl c) 1)
  have hhUW : ∀ c v f, HW.dual c f (HU.primal c v) = f v := by
    intro c v f
    simpa only [act_onlyPos,act_onlyNeg,act_onlyMark,hV,LinearEquiv.refl_apply,
      compile_uw,mul_one] using h (onlyPos c v) (onlyMark (Sum.inl c) 1) (onlyNeg c f)
  have hhVW : ∀ c v f, HW.dual c f (HV.primal c v) = f v := by
    intro c v f
    simpa only [act_onlyPos,act_onlyNeg,act_onlyMark,hU,LinearEquiv.refl_apply,
      compile_vw,mul_one] using h (onlyMark (Sum.inl c) 1) (onlyPos c v) (onlyNeg c f)
  have hhWV : ∀ c v f, HV.dual c f (HW.primal c v) = f v := by
    intro c v f
    simpa only [act_onlyPos,act_onlyNeg,act_onlyMark,hU,LinearEquiv.refl_apply,
      compile_wv,mul_one] using h (onlyMark (Sum.inr (Sum.inl c)) 1) (onlyNeg c f) (onlyPos c v)
  have hhVU : ∀ c v f, HU.dual c f (HV.primal c v) = f v := by
    intro c v f
    simpa only [act_onlyPos,act_onlyNeg,act_onlyMark,hW,LinearEquiv.refl_apply,
      compile_vu,mul_one] using h (onlyNeg c f) (onlyPos c v) (onlyMark (Sum.inr (Sum.inl c)) 1)
  let g := HU.primal
  have hs := fun c => hub_recovery (HU.primal c) (HV.primal c) (HW.primal c)
    (HU.dual c) (HV.dual c) (HW.dual c) (hhUV c) (hhUW c) (hhVW c) (hhWV c) (hhVU c)
  have hpU : ∀ c, HU.primal c = g c := fun _ => rfl
  have hpV : ∀ c, HV.primal c = g c := fun c => (hs c).1
  have hpW : ∀ c, HW.primal c = g c := fun c => (hs c).2.1
  have hnU : ∀ c, HU.dual c = (g c).symm.dualMap := fun c => (hs c).2.2.1
  have hnV : ∀ c, HV.dual c = (g c).symm.dualMap := fun c => (hs c).2.2.2.1
  have hnW : ∀ c, HW.dual c = (g c).symm.dualMap := fun c => (hs c).2.2.2.2
  have hoU : ∀ i, HU.original i = viewAction (g (sp i).1) (sp i).2 := by
    intro i
    apply pairing_determines_first
    intro v f
    have hh := h (onlyOrig (Pi.single i v)) (onlyHub (sp i).1 (!(sp i).2) f)
      (onlyMark (Sum.inr (Sum.inr i)) 1)
    simpa only [act_onlyOrig,act_onlyMark,hW,LinearEquiv.refl_apply,compile_uoriginal,
      Pi.single_eq_same,hub_act HV g hpV hnV,hub_onlyHub,mul_one] using hh
  have hoV : ∀ j, HV.original j = viewAction (g (sq j).1) (sq j).2 := by
    intro j
    apply pairing_determines_first
    intro v f
    have hh := h (onlyMark (Sum.inr (Sum.inr j)) 1) (onlyOrig (Pi.single j v))
      (onlyHub (sq j).1 (!(sq j).2) f)
    simpa only [act_onlyOrig,act_onlyMark,hU,LinearEquiv.refl_apply,compile_voriginal,
      Pi.single_eq_same,hub_act HW g hpW hnW,hub_onlyHub,mul_one] using hh
  have hoW : ∀ k, HW.original k = viewAction (g (sr k).1) (sr k).2 := by
    intro k
    apply pairing_determines_first
    intro v f
    have hh := h (onlyHub (sr k).1 (!(sr k).2) f) (onlyMark (Sum.inr k) 1)
      (onlyOrig (Pi.single k v))
    simpa only [act_onlyOrig,act_onlyMark,hV,LinearEquiv.refl_apply,compile_woriginal,
      Pi.single_eq_same,hub_act HU g hpU hnU,hub_onlyHub,mul_one] using hh
  refine ⟨g,?_⟩
  intro x y z
  simpa only [act_onlyOrig,compile_payload,hoU,hoV,hoW] using
    h (onlyOrig x) (onlyOrig y) (onlyOrig z)

theorem compiler_reverse (T S : Input (K := K) (Base := Base) sp sq sr)
    (h : CompiledIso T S) : LinkedIso T S := by
  obtain ⟨HU,HV,HW,h⟩ := h
  let a := HU.anchor 1
  let b := HV.anchor 1
  let c := HW.anchor 1
  have ha : a ≠ 0 := scalar_ne_zero HU.anchor
  have hb : b ≠ 0 := scalar_ne_zero HV.anchor
  have hc : c ≠ 0 := scalar_ne_zero HW.anchor
  have habc : a*b*c = 1 := by
    simpa only [act_onlyAnchor,compile_anchor,one_mul] using
      h (onlyAnchor 1) (onlyAnchor 1) (onlyAnchor 1)
  have hmU : ∀ e, HU.marker e 1 = a := by
    intro e
    apply common_unit habc
    simpa only [act_onlyAnchor,act_onlyMark,compile_umark,one_mul] using
      h (onlyMark e 1) (onlyAnchor 1) (onlyAnchor 1)
  have hmV : ∀ e, HV.marker e 1 = b := by
    intro e
    apply common_unit (a := b) (b := a) (c := c) (by simpa [mul_comm] using habc)
    have hh := h (onlyAnchor 1) (onlyMark e 1) (onlyAnchor 1)
    simpa [a,b,c,mul_comm] using hh
  have hmW : ∀ e, HW.marker e 1 = c := by
    intro e
    apply common_unit (a := c) (b := a) (c := b) (by
      simpa [mul_comm,mul_left_comm,mul_assoc] using habc)
    have hh := h (onlyAnchor 1) (onlyAnchor 1) (onlyMark e 1)
    simpa [a,b,c,mul_comm,mul_left_comm,mul_assoc] using hh
  apply normalized_reverse T S (axisNormalize HU a ha) (axisNormalize HV b hb) (axisNormalize HW c hc)
    (normalized_markers HU hmU) (normalized_markers HV hmV) (normalized_markers HW hmW)
  have hn := normalized_transport (linkedCompile sp sq sr T) (linkedCompile sp sq sr S)
    (axisAct HU) (axisAct HV) (axisAct HW) a b c ha hb hc habc h
  simpa only [normalize_act] using hn

/-- The explicit tensor admits blockwise isomorphism exactly when the original
tensor admits the linked primal/contragredient action. -/
theorem linked_compiler_correct (T S : Input (K := K) (Base := Base) sp sq sr) :
    LinkedIso T S ↔ CompiledIso T S :=
  ⟨compiler_forward T S,compiler_reverse T S⟩

theorem linked_compiler_dimension :
    finrank K (UA (K := K) (Base := Base) sp (Q := Q)) +
    finrank K (VA (K := K) (Base := Base) sq (R := R)) +
    finrank K (WA (K := K) (Base := Base) sr (P := P)) =
    (∑ i, finrank K (Base (sp i).1)) +
    (∑ j, finrank K (Base (sq j).1)) +
    (∑ k, finrank K (Base (sr k).1)) +
    6 * (∑ c, finrank K (Base c)) +
    Fintype.card P + Fintype.card Q + Fintype.card R + 5*r + 3 := by
  simp only [UA,VA,WA,axis_dimension]
  simp only [UM,VM,WM,Fintype.card_sum,Fintype.card_fin]
  omega

end Correctness

section PartCoordinates
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  {P E : Type} (spec : P → Fin r × Bool)

abbrev OutPart := P ⊕ (Fin r ⊕ (Fin r ⊕ (E ⊕ Unit)))

abbrev OutSpace : OutPart (r := r) (P := P) (E := E) → Type u
  | Sum.inl i => OrigSpace (K := K) (Base := Base) spec i
  | Sum.inr (Sum.inl c) => Base c
  | Sum.inr (Sum.inr (Sum.inl c)) => Dual K (Base c)
  | Sum.inr (Sum.inr (Sum.inr _)) => K

instance outAdd (i : OutPart (r := r) (P := P) (E := E)) :
    AddCommGroup (OutSpace (K := K) (Base := Base) spec i) :=
  match i with
  | Sum.inl _ => inferInstance
  | Sum.inr (Sum.inl _) => inferInstance
  | Sum.inr (Sum.inr (Sum.inl _)) => inferInstance
  | Sum.inr (Sum.inr (Sum.inr _)) => inferInstance

instance outModule (i : OutPart (r := r) (P := P) (E := E)) :
    Module K (OutSpace (K := K) (Base := Base) spec i) :=
  match i with
  | Sum.inl _ => inferInstance
  | Sum.inr (Sum.inl _) => inferInstance
  | Sum.inr (Sum.inr (Sum.inl _)) => inferInstance
  | Sum.inr (Sum.inr (Sum.inr _)) => inferInstance

instance outFinite [∀ c, FiniteDimensional K (Base c)]
    (i : OutPart (r := r) (P := P) (E := E)) :
    FiniteDimensional K (OutSpace (K := K) (Base := Base) spec i) :=
  match i with
  | Sum.inl _ => inferInstance
  | Sum.inr (Sum.inl _) => inferInstance
  | Sum.inr (Sum.inr (Sum.inl _)) => inferInstance
  | Sum.inr (Sum.inr (Sum.inr _)) => inferInstance

/-- An explicit identification with a product of independently transformable parts. -/
def splitParts :
    (∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i) ≃ₗ[K]
      Axis (K := K) (Base := Base) spec E where
  toFun x := (fun i => x (Sum.inl i),fun c => x (Sum.inr (Sum.inl c)),
    fun c => x (Sum.inr (Sum.inr (Sum.inl c))),
    fun e => x (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))),
    x (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
  invFun x i := match i with
    | Sum.inl i => aOrig x i
    | Sum.inr (Sum.inl c) => aPos x c
    | Sum.inr (Sum.inr (Sum.inl c)) => aNeg x c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl e))) => aMark x e
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => aAnchor x
  left_inv x := by
    funext i
    rcases i with i | c | c | e | u
    all_goals rfl
  right_inv x := by rcases x with ⟨x,p,n,m,a⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def axisAsParts (H : AxisMaps (K := K) (Base := Base) spec E) :
    ∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i ≃ₗ[K]
      OutSpace (K := K) (Base := Base) spec (E := E) i :=
  fun i => match i with
    | Sum.inl i => H.original i
    | Sum.inr (Sum.inl c) => H.primal c
    | Sum.inr (Sum.inr (Sum.inl c)) => H.dual c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl e))) => H.marker e
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => H.anchor

def mapsOfParts
    (G : ∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i ≃ₗ[K]
      OutSpace (K := K) (Base := Base) spec (E := E) i) :
    AxisMaps (K := K) (Base := Base) spec E where
  original i := G (Sum.inl i)
  primal c := G (Sum.inr (Sum.inl c))
  dual c := G (Sum.inr (Sum.inr (Sum.inl c)))
  marker e := G (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))
  anchor := G (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))

theorem split_asParts (H : AxisMaps (K := K) (Base := Base) spec E)
    (x : ∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i) :
    splitParts (K := K) spec (LinearEquiv.piCongrRight (axisAsParts spec H) x) =
      (axisAct H) (splitParts (K := K) spec x) := rfl

theorem split_mapsOfParts
    (G : ∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i ≃ₗ[K]
      OutSpace (K := K) (Base := Base) spec (E := E) i)
    (x : ∀ i, OutSpace (K := K) (Base := Base) spec (E := E) i) :
    splitParts (K := K) spec (LinearEquiv.piCongrRight G x) =
      (axisAct (mapsOfParts spec G)) (splitParts (K := K) spec x) := rfl

end PartCoordinates

section PartitionedCorrectness
variable {r : ℕ} {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  [∀ c, FiniteDimensional K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  {sp : P → Fin r × Bool} {sq : Q → Fin r × Bool} {sr : R → Fin r × Bool}

def partitioned (T : Input (K := K) (Base := Base) sp sq sr) :
    (∀ i, OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q)) i) →ₗ[K]
    (∀ j, OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R)) j) →ₗ[K]
    (∀ k, OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P)) k) →ₗ[K] K :=
  pullForm (linkedCompile sp sq sr T) (splitParts (K := K) sp).toLinearMap
    (splitParts (K := K) sq).toLinearMap (splitParts (K := K) sr).toLinearMap

def TriformPartsIso {I J L : Type} {A : I → Type u} {B : J → Type u} {C : L → Type u}
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module K (B j)]
    [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)]
    (T S : (∀ i,A i) →ₗ[K] (∀ j,B j) →ₗ[K] (∀ k,C k) →ₗ[K] K) : Prop :=
  ∃ (gA : ∀ i,A i ≃ₗ[K] A i) (gB : ∀ j,B j ≃ₗ[K] B j)
    (gC : ∀ k,C k ≃ₗ[K] C k),
    ∀ x y z, T (LinearEquiv.piCongrRight gA x)
      (LinearEquiv.piCongrRight gB y) (LinearEquiv.piCongrRight gC z) = S x y z

theorem compiled_iff_parts (T S : Input (K := K) (Base := Base) sp sq sr) :
    CompiledIso T S ↔ TriformPartsIso (partitioned T) (partitioned S) := by
  constructor
  · rintro ⟨HU,HV,HW,h⟩
    refine ⟨axisAsParts sp HU,axisAsParts sq HV,axisAsParts sr HW,?_⟩
    intro x y z
    simpa only [partitioned,pullForm_apply,LinearEquiv.coe_coe,split_asParts] using
      h (splitParts (K := K) sp x) (splitParts (K := K) sq y) (splitParts (K := K) sr z)
  · rintro ⟨gU,gV,gW,h⟩
    refine ⟨mapsOfParts sp gU,mapsOfParts sq gV,mapsOfParts sr gW,?_⟩
    intro x y z
    have hh := h ((splitParts (K := K) sp).symm x) ((splitParts (K := K) sq).symm y)
      ((splitParts (K := K) sr).symm z)
    simpa only [partitioned,pullForm_apply,LinearEquiv.coe_coe,split_mapsOfParts,
      LinearEquiv.apply_symm_apply] using hh

theorem linked_iff_partitioned (T S : Input (K := K) (Base := Base) sp sq sr) :
    LinkedIso T S ↔ TriformPartsIso (partitioned T) (partitioned S) :=
  (linked_compiler_correct T S).trans (compiled_iff_parts T S)

theorem output_counts :
    Fintype.card (OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q))) =
      Fintype.card P + Fintype.card Q + 4*r + 1 ∧
    Fintype.card (OutPart (r := r) (P := Q) (E := VM (r := r) (R := R))) =
      Fintype.card Q + Fintype.card R + 3*r + 1 ∧
    Fintype.card (OutPart (r := r) (P := R) (E := WM (r := r) (P := P))) =
      Fintype.card R + Fintype.card P + 4*r + 1 := by
  simp only [OutPart,UM,VM,WM,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  omega

end PartitionedCorrectness

end

/- Reindexing trilinear forms. -/
section
open Module
universe u
variable {K : Type u} [Field K]
variable {I J L I' J' L' : Type}
variable {A : I → Type u} {B : J → Type u} {C : L → Type u}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module K (B j)]
  [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)]

abbrev indexedForm := (∀ i,A i) →ₗ[K] (∀ j,B j) →ₗ[K] (∀ k,C k) →ₗ[K] K

def indexedPartsIso (T S : indexedForm (K := K) (A := A) (B := B) (C := C)) : Prop :=
  ∃ (gA : ∀ i,A i ≃ₗ[K] A i) (gB : ∀ j,B j ≃ₗ[K] B j)
    (gC : ∀ k,C k ≃ₗ[K] C k),
    ∀ x y z, T (LinearEquiv.piCongrRight gA x)
      (LinearEquiv.piCongrRight gB y) (LinearEquiv.piCongrRight gC z) = S x y z

def space (e : I ≃ I') : (∀ i,A i) ≃ₗ[K] (∀ j,A (e.symm j)) :=
  LinearEquiv.piCongrLeft' K A e

def maps (e : I ≃ I') :
    (∀ i,A i ≃ₗ[K] A i) ≃ (∀ j,A (e.symm j) ≃ₗ[K] A (e.symm j)) :=
  Equiv.piCongrLeft' (fun i => A i ≃ₗ[K] A i) e

theorem space_action (e : I ≃ I') (g : ∀ i,A i ≃ₗ[K] A i) (x : ∀ i,A i) :
    space (K := K) e (LinearEquiv.piCongrRight g x) =
      LinearEquiv.piCongrRight (maps e g) (space (K := K) e x) := by
  ext j
  rfl

theorem symm_space_action (e : I ≃ I') (g : ∀ i,A i ≃ₗ[K] A i)
    (x : ∀ j,A (e.symm j)) :
    (space (K := K) e).symm (LinearEquiv.piCongrRight (maps e g) x) =
      LinearEquiv.piCongrRight g ((space (K := K) e).symm x) := by
  apply (space (K := K) e).injective
  rw [LinearEquiv.apply_symm_apply,space_action,LinearEquiv.apply_symm_apply]

def reindex (e : I ≃ I') (f : J ≃ J') (g : L ≃ L')
    (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    indexedForm (K := K) (A := fun i => A (e.symm i))
      (B := fun j => B (f.symm j)) (C := fun k => C (g.symm k)) where
  toFun x :=
    { toFun := fun y =>
        (T ((space (K := K) e).symm x) ((space (K := K) f).symm y)).comp
          (space (K := K) g).symm.toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem reindex_apply (e : I ≃ I') (f : J ≃ J') (g : L ≃ L')
    (T : indexedForm (K := K) (A := A) (B := B) (C := C)) (x y z) :
    reindex e f g T x y z = T ((space (K := K) e).symm x)
      ((space (K := K) f).symm y) ((space (K := K) g).symm z) := rfl

theorem partsIso_reindex_iff (e : I ≃ I') (f : J ≃ J') (g : L ≃ L')
    (T S : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    indexedPartsIso (reindex e f g T) (reindex e f g S) ↔ indexedPartsIso T S := by
  constructor
  · rintro ⟨a,b,c,h⟩
    let a' := (maps (K := K) (A := A) e).symm a
    let b' := (maps (K := K) (A := B) f).symm b
    let c' := (maps (K := K) (A := C) g).symm c
    refine ⟨a',b',c',?_⟩
    intro x y z
    have hh := h (space (K := K) e x) (space (K := K) f y) (space (K := K) g z)
    have ha : a = maps e a' := (Equiv.apply_symm_apply _ _).symm
    have hb : b = maps f b' := (Equiv.apply_symm_apply _ _).symm
    have hc : c = maps g c' := (Equiv.apply_symm_apply _ _).symm
    simpa only [reindex_apply,ha,hb,hc,symm_space_action,LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨a,b,c,h⟩
    refine ⟨maps e a,maps f b,maps g c,?_⟩
    intro x y z
    simpa only [reindex_apply,symm_space_action] using
      h ((space (K := K) e).symm x) ((space (K := K) f).symm y) ((space (K := K) g).symm z)

theorem reindex_dimension (e : I ≃ I') :
    finrank K (∀ j,A (e.symm j)) = finrank K (∀ i,A i) :=
  (space (K := K) (A := A) e).finrank_eq.symm

end

/- Trilinear and bilinear descriptions. -/
section
open Module
universe u
variable {K : Type u} [Field K]
variable {I J L : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  {A : I → Type u} {B : J → Type u} {C : L → Type u}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module K (B j)]
  [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)]

def asBilinear (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    (∀ i,A i) →ₗ[K] (∀ j,B j) →ₗ[K] (∀ k,Dual K (C k)) where
  toFun x :=
    { toFun := fun y => (piDual (K := K) (U := C)).symm (T x y)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem piDual_asBilinear
    (T : indexedForm (K := K) (A := A) (B := B) (C := C)) (x y) :
    piDual (asBilinear T x y) = T x y :=
  (piDual (K := K) (U := C)).apply_symm_apply _

theorem partsIso_asBilinear_iff [∀ k,FiniteDimensional K (C k)]
    (T S : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    indexedPartsIso T S ↔ bilinearPartsIso (asBilinear T) (asBilinear S) := by
  constructor
  · rintro ⟨a,b,c,h⟩
    refine ⟨fun k => (c k).dualMap,b,a,?_⟩
    intro x y
    apply (piDual (K := K) (U := C)).injective
    rw [piDual_covariance,piDual_asBilinear,piDual_asBilinear]
    apply LinearMap.ext
    intro z
    simpa only [LinearEquiv.dualMap_apply] using h x y z
  · rintro ⟨c,b,a,h⟩
    refine ⟨a,b,fun k => undual (c k),?_⟩
    intro x y z
    have hc : c = fun k => (undual (c k)).dualMap := by
      funext k
      exact (dual_undual (c k)).symm
    rw [hc] at h
    have hh := congrArg (fun f => piDual (K := K) (U := C) f z) (h x y)
    simpa only [piDual_covariance,piDual_asBilinear,LinearEquiv.dualMap_apply] using hh

theorem dual_side_dimension [∀ k,FiniteDimensional K (C k)] :
    finrank K (∀ k,Dual K (C k)) = finrank K (∀ k,C k) := by
  simp [Module.finrank_pi_fintype,Subspace.dual_finrank_eq]

end

/- Compiling partitioned forms. -/
section
open Module
universe u
variable {K : Type u} [Field K]
variable {I J L : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  [Nontrivial I] [Nontrivial J] [Nontrivial L]
  {A : I → Type u} {B : J → Type u} {C : L → Type u}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)] [∀ i,FiniteDimensional K (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module K (B j)] [∀ j,FiniteDimensional K (B j)]
  [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)] [∀ k,FiniteDimensional K (C k)]

instance finCardNontrivial {X : Type} [Fintype X] [Nontrivial X] :
    Nontrivial (Fin (Fintype.card X)) :=
  Fin.nontrivial_iff_two_le.mpr Fintype.one_lt_card

abbrev indexed (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :=
  reindex (Fintype.equivFin I) (Fintype.equivFin J) (Fintype.equivFin L) T

def partitionOrdinary (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :=
  finalTensor (0 : Fin (Fintype.card J)) (0 : Fin (Fintype.card I))
    (asBilinear (indexed T))

def partitionOutputIso (T S : indexedForm (K := K) (A := A) (B := B) (C := C)) : Prop :=
  Iso (partitionOrdinary T) (partitionOrdinary S)

def partitionOutputDim (T : indexedForm (K := K) (A := A) (B := B) (C := C)) : ℕ :=
  partitionTotalDim (partitionOrdinary T)

theorem partitionOrdinary_correct (T S : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    indexedPartsIso T S ↔ partitionOutputIso T S := by
  exact (partsIso_reindex_iff _ _ _ T S).symm.trans
    ((partsIso_asBilinear_iff (indexed T) (indexed S)).trans
      (partition_compiler_correct
        (0 : Fin (Fintype.card J)) (0 : Fin (Fintype.card I)) _ _))

def inputDim (_T : indexedForm (K := K) (A := A) (B := B) (C := C)) :=
  finrank K (∀ i,A i) + finrank K (∀ j,B j) + finrank K (∀ k,C k)

theorem indexed_bilinear_dimension
    (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    partitionTotalDim (asBilinear (indexed T)) = inputDim T := by
  unfold partitionTotalDim inputDim
  rw [dual_side_dimension]
  rw [reindex_dimension,reindex_dimension,
    reindex_dimension]

theorem partitionOrdinary_size (T : indexedForm (K := K) (A := A) (B := B) (C := C)) :
    partitionOutputDim T ≤
      compilerFactor (Fintype.card L) (Fintype.card J) (Fintype.card I) *
        (inputDim T + 1) := by
  have h := partition_compiler_size
    (0 : Fin (Fintype.card J)) (0 : Fin (Fintype.card I))
    (asBilinear (indexed T))
  simpa only [partitionOutputDim,partitionOrdinary,indexed_bilinear_dimension] using h

end

/- Compiling linked forms. -/
section
open Module
universe u
variable {K : Type u} [Field K]
variable {r : ℕ} [NeZero r] {Base : Fin r → Type u}
  [∀ c, AddCommGroup (Base c)] [∀ c, Module K (Base c)]
  [∀ c, FiniteDimensional K (Base c)]
  {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]
  {sp : P → Fin r × Bool} {sq : Q → Fin r × Bool} {sr : R → Fin r × Bool}

instance outNontrivial {X E : Type} :
    Nontrivial (OutPart (r := r) (P := X) (E := E)) :=
  ⟨⟨Sum.inr (Sum.inl 0),Sum.inr (Sum.inr (Sum.inl 0)),by intro h; cases h⟩⟩

def linkedOrdinary (T : Input (K := K) (Base := Base) sp sq sr) :=
  partitionOrdinary (K := K)
    (I := OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q)))
    (J := OutPart (r := r) (P := Q) (E := VM (r := r) (R := R)))
    (L := OutPart (r := r) (P := R) (E := WM (r := r) (P := P)))
    (A := OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q)))
    (B := OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R)))
    (C := OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P))) (partitioned T)

def linkedOutputIso (T S : Input (K := K) (Base := Base) sp sq sr) : Prop :=
  partitionOutputIso (K := K) (I := OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q))) (J := OutPart (r := r) (P := Q) (E := VM (r := r) (R := R))) (L := OutPart (r := r) (P := R) (E := WM (r := r) (P := P))) (A := OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q))) (B := OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R))) (C := OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P))) (partitioned T) (partitioned S)

def linkedOutputDim (T : Input (K := K) (Base := Base) sp sq sr) : ℕ :=
  partitionOutputDim (K := K) (I := OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q))) (J := OutPart (r := r) (P := Q) (E := VM (r := r) (R := R))) (L := OutPart (r := r) (P := R) (E := WM (r := r) (P := P))) (A := OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q))) (B := OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R))) (C := OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P))) (partitioned T)

theorem linkedOrdinary_correct (T S : Input (K := K) (Base := Base) sp sq sr) :
    LinkedIso T S ↔ linkedOutputIso T S := by
  classical
  exact (linked_iff_partitioned T S).trans (partitionOrdinary_correct (K := K)
    (I := OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q)))
    (J := OutPart (r := r) (P := Q) (E := VM (r := r) (R := R)))
    (L := OutPart (r := r) (P := R) (E := WM (r := r) (P := P)))
    (A := OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q)))
    (B := OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R)))
    (C := OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P))) (partitioned T) (partitioned S))

def linkFactor (p q s r : ℕ) :=
  compilerFactor (s+p+4*r+1) (q+s+3*r+1) (p+q+4*r+1)

def linkedDim (_T : Input (K := K) (Base := Base) sp sq sr) :=
    (∑ i,finrank K (Base (sp i).1)) +
    (∑ j,finrank K (Base (sq j).1)) +
    (∑ k,finrank K (Base (sr k).1)) +
    6 * (∑ c,finrank K (Base c)) +
    Fintype.card P + Fintype.card Q + Fintype.card R + 5*r + 3

theorem partitioned_dimension (T : Input (K := K) (Base := Base) sp sq sr) :
    inputDim (partitioned T) = linkedDim T := by
  unfold inputDim linkedDim
  rw [(splitParts (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q))).finrank_eq,
    (splitParts (K := K) (Base := Base) sq (E := VM (r := r) (R := R))).finrank_eq,
    (splitParts (K := K) (Base := Base) sr (E := WM (r := r) (P := P))).finrank_eq]
  exact linked_compiler_dimension

theorem linkedOrdinary_size (T : Input (K := K) (Base := Base) sp sq sr) :
    linkedOutputDim T ≤
      linkFactor (Fintype.card P) (Fintype.card Q) (Fintype.card R) r * (linkedDim T + 1) := by
  classical
  have h := partitionOrdinary_size (K := K)
    (I := OutPart (r := r) (P := P) (E := UM (r := r) (Q := Q)))
    (J := OutPart (r := r) (P := Q) (E := VM (r := r) (R := R)))
    (L := OutPart (r := r) (P := R) (E := WM (r := r) (P := P)))
    (A := OutSpace (K := K) (Base := Base) sp (E := UM (r := r) (Q := Q)))
    (B := OutSpace (K := K) (Base := Base) sq (E := VM (r := r) (R := R)))
    (C := OutSpace (K := K) (Base := Base) sr (E := WM (r := r) (P := P))) (partitioned T)
  rw [partitioned_dimension] at h
  have hc := output_counts (r := r) (P := P) (Q := Q) (R := R)
  simpa only [linkedOutputDim,hc.1,hc.2.1,hc.2.2,linkFactor] using h

end

/- Packing a named-space system. -/
section
open Module
universe u
variable {K C R S : Type u} [Field K]
  [AddCommGroup C] [Module K C] [AddCommGroup R] [Module K R]
  [AddCommGroup S] [Module K S]

abbrev Bases : Fin 4 → Type u := ![K,C,R,S]

instance baseAdd (i : Fin 4) : AddCommGroup (Bases (K := K) (C := C) (R := R) (S := S) i) :=
  Fin.cases (inferInstanceAs (AddCommGroup K))
    (Fin.cases (inferInstanceAs (AddCommGroup C))
      (Fin.cases (inferInstanceAs (AddCommGroup R))
        (Fin.cases (inferInstanceAs (AddCommGroup S)) (fun i => Fin.elim0 i)))) i

instance baseModule (i : Fin 4) : Module K (Bases (K := K) (C := C) (R := R) (S := S) i) :=
  Fin.cases (inferInstanceAs (Module K K))
    (Fin.cases (inferInstanceAs (Module K C))
      (Fin.cases (inferInstanceAs (Module K R))
        (Fin.cases (inferInstanceAs (Module K S)) (fun i => Fin.elim0 i)))) i

instance baseFinite [FiniteDimensional K C] [FiniteDimensional K R] [FiniteDimensional K S]
    (i : Fin 4) : FiniteDimensional K (Bases (K := K) (C := C) (R := R) (S := S) i) :=
  Fin.cases (inferInstanceAs (FiniteDimensional K K))
    (Fin.cases (inferInstanceAs (FiniteDimensional K C))
      (Fin.cases (inferInstanceAs (FiniteDimensional K R))
        (Fin.cases (inferInstanceAs (FiniteDimensional K S)) (fun i => Fin.elim0 i)))) i

abbrev packedSp : Fin 5 → Fin 4 × Bool := ![(0,false),(1,false),(2,false),(3,false),(3,true)]
abbrev packedSq : Fin 4 → Fin 4 × Bool := ![(0,true),(1,true),(3,false),(3,true)]
abbrev packedSr : Fin 5 → Fin 4 × Bool := ![(0,true),(1,true),(2,true),(3,false),(3,true)]

abbrev PU := ∀ i,OrigSpace (K := K) (Base := Bases (K := K) (C := C) (R := R) (S := S)) packedSp i
abbrev PV := ∀ i,OrigSpace (K := K) (Base := Bases (K := K) (C := C) (R := R) (S := S)) packedSq i
abbrev PW := ∀ i,OrigSpace (K := K) (Base := Bases (K := K) (C := C) (R := R) (S := S)) packedSr i
abbrev PackForm := Input (K := K) (Base := Bases (K := K) (C := C) (R := R) (S := S)) packedSp packedSq packedSr

def u0 : PU (K := K) (C := C) (R := R) (S := S) →ₗ[K] K :=
  LinearMap.proj (0 : Fin 5)
def u1 : PU (K := K) (C := C) (R := R) (S := S) →ₗ[K] C :=
  LinearMap.proj (1 : Fin 5)
def u2 : PU (K := K) (C := C) (R := R) (S := S) →ₗ[K] R :=
  LinearMap.proj (2 : Fin 5)
def u3 : PU (K := K) (C := C) (R := R) (S := S) →ₗ[K] S :=
  LinearMap.proj (3 : Fin 5)
def v0 : PV (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K K :=
  LinearMap.proj (0 : Fin 4)
def v1 : PV (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K C :=
  LinearMap.proj (1 : Fin 4)
def v2 : PV (K := K) (C := C) (R := R) (S := S) →ₗ[K] S :=
  LinearMap.proj (2 : Fin 4)
def w0 : PW (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K K :=
  LinearMap.proj (0 : Fin 5)
def w1 : PW (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K C :=
  LinearMap.proj (1 : Fin 5)
def w2 : PW (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K R :=
  LinearMap.proj (2 : Fin 5)
def w3 : PW (K := K) (C := C) (R := R) (S := S) →ₗ[K] S :=
  LinearMap.proj (3 : Fin 5)
def w4 : PW (K := K) (C := C) (R := R) (S := S) →ₗ[K] Dual K S :=
  LinearMap.proj (4 : Fin 5)

def evaluateBilinear (L : S →ₗ[K] S →ₗ[K] C) : S →ₗ[K] S →ₗ[K] Dual K C →ₗ[K] K where
  toFun x :=
    { toFun := fun y => Module.Dual.eval K C (L x y)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem evaluateBilinear_apply (L : S →ₗ[K] S →ₗ[K] C) (x y : S) (f : Dual K C) :
    evaluateBilinear L x y f = f (L x y) := rfl

/-- The eight distinct blocks of the fixed-part system encoding. All maps
and label vectors are data, rather than hypothesized correctness properties. -/
def pack {I A : Type} [Fintype I] [Fintype A]
    (J : C →ₗ[K] C) (e : C) (rlab : I → C) (slab : A → C)
    (rp : I → R →ₗ[K] R) (ss : A → S →ₗ[K] S) (cp : S →ₗ[K] R)
    (F : S →ₗ[K] S →ₗ[K] S →ₗ[K] K) (L : S →ₗ[K] S →ₗ[K] C) :
    PackForm (K := K) (C := C) (R := R) (S := S) :=
  let mu : PackForm (K := K) (C := C) (R := R) (S := S) :=
    pairLast (pullPair (pairing false) u0 v0)
      ((Module.Dual.eval K K 1).comp w0)
  let shiftPart : PackForm (K := K) (C := C) (R := R) (S := S) :=
    pairLast (pullPair ((Module.Dual.eval K C).comp J) u1 v1)
      ((Module.Dual.eval K K 1).comp w0)
  let firstPart : PackForm (K := K) (C := C) (R := R) (S := S) :=
    pairLast (scalarPair u0
      ((Module.Dual.eval K C e).comp v1))
      ((Module.Dual.eval K K 1).comp w0)
  let rows : PackForm (K := K) (C := C) (R := R) (S := S) :=
    ∑ i, cycle (pairLast (pullPair (pairing true) w2
      ((rp i).comp u2))
      ((Module.Dual.eval K C (rlab i)).comp v1))
  let copies : PackForm (K := K) (C := C) (R := R) (S := S) :=
    ∑ a, cycle (pairLast (pullPair (pairing true) w4
      ((ss a).comp u3))
      ((Module.Dual.eval K C (slab a)).comp v1))
  let links : PackForm (K := K) (C := C) (R := R) (S := S) :=
    cycle (pairLast (pullPair (pairing true) w2
      (cp.comp u3)) ((Module.Dual.eval K K 1).comp v0))
  let dataPart : PackForm (K := K) (C := C) (R := R) (S := S) :=
    pullForm F u3 v2 w3
  let duality : PackForm (K := K) (C := C) (R := R) (S := S) :=
    pullForm (evaluateBilinear L) u3 v2 w1
  mu + shiftPart + firstPart + rows + copies + links + dataPart + duality

theorem pack_apply {I A : Type} [Fintype I] [Fintype A]
    (J : C →ₗ[K] C) (e : C) (rlab : I → C) (slab : A → C)
    (rp : I → R →ₗ[K] R) (ss : A → S →ₗ[K] S) (cp : S →ₗ[K] R)
    (F : S →ₗ[K] S →ₗ[K] S →ₗ[K] K) (L : S →ₗ[K] S →ₗ[K] C)
    (x : PU (K := K) (C := C) (R := R) (S := S))
    (y : PV (K := K) (C := C) (R := R) (S := S))
    (z : PW (K := K) (C := C) (R := R) (S := S)) :
    pack J e rlab slab rp ss cp F L x y z =
      (v0 y) ((u0 x)) * (w0 z) 1 +
      (v1 y) (J ((u1 x))) * (w0 z) 1 +
      (u0 x) * (v1 y) e * (w0 z) 1 +
      (∑ i,(w2 z) (rp i ((u2 x))) * (v1 y) (rlab i)) +
      (∑ a,(w4 z) (ss a ((u3 x))) * (v1 y) (slab a)) +
      (w2 z) (cp ((u3 x))) * (v0 y) 1 +
      F ((u3 x)) ((v2 y)) ((w3 z)) +
      (w1 z) (L ((u3 x)) ((v2 y))) := by
  simp only [pack,pairLast_apply,cycle_apply,pullPair_apply,pullForm_apply,scalarPair_apply,evaluateBilinear_apply,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply]
  rfl

end

section
open Module
universe u
variable {K : Type u} [Field K]
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  (under : A → I)

abbrev Named := ∀ i,V i
abbrev Occurs := ∀ a,V (under a)
abbrev Labels := Fin (Fintype.card (I ⊕ A) + 1) → K

def labelIndex (x : I ⊕ A) : Fin (Fintype.card (I ⊕ A) + 1) :=
  (Fintype.equivFin (I ⊕ A) x).castSucc

theorem labelIndex_injective : Function.Injective (labelIndex (I := I) (A := A)) :=
  (Fin.castSucc_injective _).comp (Fintype.equivFin (I ⊕ A)).injective

def label (x : I ⊕ A) : Labels (K := K) (I := I) (A := A) :=
  Pi.single (labelIndex x) 1

def coord (x : I ⊕ A) : Labels (K := K) (I := I) (A := A) →ₗ[K] K :=
  LinearMap.proj (labelIndex x)

@[simp] theorem coord_label (x y : I ⊕ A) :
    coord (K := K) x (label y) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst y; simp [coord,label]
  · have h' : labelIndex x ≠ labelIndex y := fun he => h (labelIndex_injective he)
    simp [coord,label,Pi.single_eq_of_ne h',h]

theorem named_sum_test (f : I → K) (i : I) :
    (∑ j,f j * coord (K := K) (Sum.inl i : I ⊕ A) (label (Sum.inl j))) = f i := by
  simp [coord_label]

theorem occurrence_sum_test (f : A → K) (a : A) :
    (∑ b,f b * coord (K := K) (Sum.inr a : I ⊕ A) (label (Sum.inr b))) = f a := by
  simp [coord_label]

def shiftMap : Labels (K := K) (I := I) (A := A) →ₗ[K] Labels (K := K) (I := I) (A := A) where
  toFun := shift
  map_add' x y := by
    ext i
    change shift (x+y) i = shift x i + shift y i
    simp only [shift]
    split_ifs <;> simp
  map_smul' a x := by
    ext i
    change shift (a • x) i = a • shift x i
    simp only [shift]
    split_ifs <;> simp

def first : Labels (K := K) (I := I) (A := A) := Pi.single 0 1

theorem frame_rigid
    (g : Labels (K := K) (I := I) (A := A) ≃ₗ[K] Labels (K := K) (I := I) (A := A))
    (he : g (first (K := K)) = first)
    (hj : ∀ x,g (shiftMap x) = shiftMap (g x)) : g = LinearEquiv.refl K _ := by
  apply LinearEquiv.toLinearMap_injective
  exact first_shift_rigid (Nat.succ_pos _) g.toLinearMap he hj

def namedProjector (i : I) : Named (V := V) →ₗ[K] Named (V := V) :=
  (LinearMap.single K V i).comp (LinearMap.proj i)

def occurrenceProjector (a : A) : Occurs (V := V) under →ₗ[K] Occurs (V := V) under :=
  (LinearMap.single K (fun a => V (under a)) a).comp (LinearMap.proj a)

abbrev EncodedForm := PackForm (K := K) (C := Labels (K := K) (I := I) (A := A))
  (R := Named (V := V)) (S := Occurs (V := V) under)

def encode
    (F : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] K)
    (L : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Labels (K := K) (I := I) (A := A)) :
    EncodedForm (K := K) (V := V) under :=
  pack shiftMap first (fun i => label (Sum.inl i)) (fun a => label (Sum.inr a))
    namedProjector (occurrenceProjector under) (copyMap under) F L

end

section
open Module
universe u
variable {K C R S : Type u} [Field K]
  [AddCommGroup C] [Module K C] [AddCommGroup R] [Module K R]
  [AddCommGroup S] [Module K S]
variable {I A : Type} [Fintype I] [Fintype A]
  (J : C →ₗ[K] C) (e : C) (rlab : I → C) (slab : A → C)
  (rp : I → R →ₗ[K] R) (ss : A → S →ₗ[K] S) (cp : S →ₗ[K] R)
  (F : S →ₗ[K] S →ₗ[K] S →ₗ[K] K) (L : S →ₗ[K] S →ₗ[K] C)

@[simp] theorem pack_mu (a : K) (f g : Dual K K) :
    pack J e rlab slab rp ss cp F L (Pi.single (0 : Fin 5) a)
      (Pi.single (0 : Fin 4) f) (Pi.single (0 : Fin 5) g) = f a * g 1 := by
  rw [pack_apply]
  change (f : Dual K K) (a : K) * (g : Dual K K) 1 +
    (0 : Dual K C) (J (0 : C)) * (g : Dual K K) 1 +
    (a : K) * (0 : Dual K C) e * (g : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (0 : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (0 : S)) * (0 : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (0 : S)) * (f : Dual K K) 1 +
    F (0 : S) (0 : S) (0 : S) + (0 : Dual K C) (L (0 : S) (0 : S)) = f a * g 1
  simp

@[simp] theorem pack_shift (x : C) (f : Dual K C) (g : Dual K K) :
    pack J e rlab slab rp ss cp F L (Pi.single (1 : Fin 5) x)
      (Pi.single (1 : Fin 4) f) (Pi.single (0 : Fin 5) g) = f (J x) * g 1 := by
  rw [pack_apply]
  change (0 : Dual K K) (0 : K) * (g : Dual K K) 1 +
    (f : Dual K C) (J (x : C)) * (g : Dual K K) 1 +
    (0 : K) * (f : Dual K C) e * (g : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (f : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (0 : S)) * (f : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (0 : S)) * (0 : Dual K K) 1 +
    F (0 : S) (0 : S) (0 : S) + (0 : Dual K C) (L (0 : S) (0 : S)) = f (J x) * g 1
  simp

@[simp] theorem pack_first (a : K) (f : Dual K C) (g : Dual K K) :
    pack J e rlab slab rp ss cp F L (Pi.single (0 : Fin 5) a)
      (Pi.single (1 : Fin 4) f) (Pi.single (0 : Fin 5) g) = a * f e * g 1 := by
  rw [pack_apply]
  change (0 : Dual K K) (a : K) * (g : Dual K K) 1 +
    (f : Dual K C) (J (0 : C)) * (g : Dual K K) 1 +
    (a : K) * (f : Dual K C) e * (g : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (f : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (0 : S)) * (f : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (0 : S)) * (0 : Dual K K) 1 +
    F (0 : S) (0 : S) (0 : S) + (0 : Dual K C) (L (0 : S) (0 : S)) = a * f e * g 1
  simp

@[simp] theorem pack_rows (x : R) (f : Dual K C) (g : Dual K R) :
    pack J e rlab slab rp ss cp F L (Pi.single (2 : Fin 5) x)
      (Pi.single (1 : Fin 4) f) (Pi.single (2 : Fin 5) g) = ∑ i,g (rp i x) * f (rlab i) := by
  rw [pack_apply]
  change (0 : Dual K K) (0 : K) * (0 : Dual K K) 1 +
    (f : Dual K C) (J (0 : C)) * (0 : Dual K K) 1 +
    (0 : K) * (f : Dual K C) e * (0 : Dual K K) 1 +
    (∑ i,(g : Dual K R) (rp i (x : R)) * (f : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (0 : S)) * (f : Dual K C) (slab a)) +
    (g : Dual K R) (cp (0 : S)) * (0 : Dual K K) 1 +
    F (0 : S) (0 : S) (0 : S) + (0 : Dual K C) (L (0 : S) (0 : S)) = ∑ i,g (rp i x) * f (rlab i)
  simp

@[simp] theorem pack_occurrences (x : S) (f : Dual K C) (g : Dual K S) :
    pack J e rlab slab rp ss cp F L (Pi.single (3 : Fin 5) x)
      (Pi.single (1 : Fin 4) f) (Pi.single (4 : Fin 5) g) = ∑ a,g (ss a x) * f (slab a) := by
  rw [pack_apply]
  change (0 : Dual K K) (0 : K) * (0 : Dual K K) 1 +
    (f : Dual K C) (J (0 : C)) * (0 : Dual K K) 1 +
    (0 : K) * (f : Dual K C) e * (0 : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (f : Dual K C) (rlab i)) +
    (∑ a,(g : Dual K S) (ss a (x : S)) * (f : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (x : S)) * (0 : Dual K K) 1 +
    F (x : S) (0 : S) (0 : S) + (0 : Dual K C) (L (x : S) (0 : S)) = ∑ a,g (ss a x) * f (slab a)
  simp

@[simp] theorem pack_copy (x : S) (f : Dual K K) (g : Dual K R) :
    pack J e rlab slab rp ss cp F L (Pi.single (3 : Fin 5) x)
      (Pi.single (0 : Fin 4) f) (Pi.single (2 : Fin 5) g) = g (cp x) * f 1 := by
  rw [pack_apply]
  change (f : Dual K K) (0 : K) * (0 : Dual K K) 1 +
    (0 : Dual K C) (J (0 : C)) * (0 : Dual K K) 1 +
    (0 : K) * (0 : Dual K C) e * (0 : Dual K K) 1 +
    (∑ i,(g : Dual K R) (rp i (0 : R)) * (0 : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (x : S)) * (0 : Dual K C) (slab a)) +
    (g : Dual K R) (cp (x : S)) * (f : Dual K K) 1 +
    F (x : S) (0 : S) (0 : S) + (0 : Dual K C) (L (x : S) (0 : S)) = g (cp x) * f 1
  simp

@[simp] theorem pack_data (x y z : S) :
    pack J e rlab slab rp ss cp F L (Pi.single (3 : Fin 5) x)
      (Pi.single (2 : Fin 4) y) (Pi.single (3 : Fin 5) z) = F x y z := by
  rw [pack_apply]
  change (0 : Dual K K) (0 : K) * (0 : Dual K K) 1 +
    (0 : Dual K C) (J (0 : C)) * (0 : Dual K K) 1 +
    (0 : K) * (0 : Dual K C) e * (0 : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (0 : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (x : S)) * (0 : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (x : S)) * (0 : Dual K K) 1 +
    F (x : S) (y : S) (z : S) + (0 : Dual K C) (L (x : S) (y : S)) = F x y z
  simp

@[simp] theorem pack_duality (x y : S) (f : Dual K C) :
    pack J e rlab slab rp ss cp F L (Pi.single (3 : Fin 5) x)
      (Pi.single (2 : Fin 4) y) (Pi.single (1 : Fin 5) f) = f (L x y) := by
  rw [pack_apply]
  change (0 : Dual K K) (0 : K) * (0 : Dual K K) 1 +
    (0 : Dual K C) (J (0 : C)) * (0 : Dual K K) 1 +
    (0 : K) * (0 : Dual K C) e * (0 : Dual K K) 1 +
    (∑ i,(0 : Dual K R) (rp i (0 : R)) * (0 : Dual K C) (rlab i)) +
    (∑ a,(0 : Dual K S) (ss a (x : S)) * (0 : Dual K C) (slab a)) +
    (0 : Dual K R) (cp (x : S)) * (0 : Dual K K) 1 +
    F (x : S) (y : S) (0 : S) + (f : Dual K C) (L (x : S) (y : S)) = f (L x y)
  simp

abbrev Transform := ∀ i,Bases (K := K) (C := C) (R := R) (S := S) i ≃ₗ[K]
  Bases (K := K) (C := C) (R := R) (S := S) i

def uAction (g : Transform (K := K) (C := C) (R := R) (S := S)) :
    PU (K := K) (C := C) (R := R) (S := S) ≃ₗ[K] PU (K := K) (C := C) (R := R) (S := S) :=
  LinearEquiv.piCongrRight (fun i => viewAction (g (packedSp i).1) (packedSp i).2)

def vAction (g : Transform (K := K) (C := C) (R := R) (S := S)) :
    PV (K := K) (C := C) (R := R) (S := S) ≃ₗ[K] PV (K := K) (C := C) (R := R) (S := S) :=
  LinearEquiv.piCongrRight (fun i => viewAction (g (packedSq i).1) (packedSq i).2)

def wAction (g : Transform (K := K) (C := C) (R := R) (S := S)) :
    PW (K := K) (C := C) (R := R) (S := S) ≃ₗ[K] PW (K := K) (C := C) (R := R) (S := S) :=
  LinearEquiv.piCongrRight (fun i => viewAction (g (packedSr i).1) (packedSr i).2)

theorem uAction_single (g : Transform (K := K) (C := C) (R := R) (S := S))
    (i : Fin 5) (x) :
    uAction g (Pi.single i x) = Pi.single i (viewAction (g (packedSp i).1) (packedSp i).2 x) :=
  piCongr_single _ _ _

theorem vAction_single (g : Transform (K := K) (C := C) (R := R) (S := S))
    (i : Fin 4) (x) :
    vAction g (Pi.single i x) = Pi.single i (viewAction (g (packedSq i).1) (packedSq i).2 x) :=
  piCongr_single _ _ _

theorem wAction_single (g : Transform (K := K) (C := C) (R := R) (S := S))
    (i : Fin 5) (x) :
    wAction g (Pi.single i x) = Pi.single i (viewAction (g (packedSr i).1) (packedSr i).2 x) :=
  piCongr_single _ _ _

end

section
set_option backward.isDefEq.respectTransparency false
open Module
universe u
variable {K C R S : Type u} [Field K]
  [AddCommGroup C] [Module K C] [AddCommGroup R] [Module K R]
  [AddCommGroup S] [Module K S]
variable {I A : Type} [Fintype I] [Fintype A]
  (J : C →ₗ[K] C) (e : C) (rlab : I → C) (slab : A → C)
  (rp : I → R →ₗ[K] R) (ss : A → S →ₗ[K] S) (cp : S →ₗ[K] R)
  (F F' : S →ₗ[K] S →ₗ[K] S →ₗ[K] K) (L L' : S →ₗ[K] S →ₗ[K] C)
  (g : Transform (K := K) (C := C) (R := R) (S := S))
  (h : ∀ x y z,pack J e rlab slab rp ss cp F L (uAction g x) (vAction g y) (wAction g z) =
    pack J e rlab slab rp ss cp F' L' x y z)

include h in
theorem scalar_rigid : g 0 = LinearEquiv.refl K K := by
  let G : K ≃ₗ[K] K := g 0
  have hh := h (Pi.single (0 : Fin 5) (1 : K))
    (Pi.single (0 : Fin 4) (LinearMap.id : Dual K K))
    (Pi.single (0 : Fin 5) (LinearMap.id : Dual K K))
  have hi : G.symm 1 = 1 := by
    simpa [G,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      LinearEquiv.dualMap_apply] using hh
  have h1 : G 1 = 1 := by
    have ht := congrArg G hi
    exact ht.symm.trans (G.apply_symm_apply _)
  change G = LinearEquiv.refl K K
  apply LinearEquiv.ext
  intro x
  rw [scalar_apply G x,h1,one_mul]
  rfl

theorem dual_separates [FiniteDimensional K C] (x y : C)
    (h : ∀ f : Dual K C,f x = f y) : x = y := by
  apply (Module.evalEquiv K C).injective
  apply LinearMap.ext
  exact h

include h in
theorem first_recovery [FiniteDimensional K C] (hs : g 0 = LinearEquiv.refl K K) :
    g 1 e = e := by
  have hi : (g 1).symm e = e := by
    apply dual_separates (K := K) (C := C)
    intro f
    have hh := h (Pi.single (0 : Fin 5) (1 : K)) (Pi.single (1 : Fin 4) f)
      (Pi.single (0 : Fin 5) (LinearMap.id : Dual K K))
    simpa [uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hs,LinearEquiv.dualMap_apply] using hh
  have ht := congrArg (g 1) hi
  exact ht.symm.trans ((g 1).apply_symm_apply _)

include h in
theorem shift_recovery [FiniteDimensional K C] (hs : g 0 = LinearEquiv.refl K K) :
    ∀ x,g 1 (J x) = J (g 1 x) := by
  intro x
  have hi : (g 1).symm (J (g 1 x)) = J x := by
    apply dual_separates (K := K) (C := C)
    intro f
    have hh := h (Pi.single (1 : Fin 5) x) (Pi.single (1 : Fin 4) f)
      (Pi.single (0 : Fin 5) (LinearMap.id : Dual K K))
    simpa [uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hs,LinearEquiv.dualMap_apply] using hh
  have ht := congrArg (g 1) hi
  exact ht.symm.trans ((g 1).apply_symm_apply _)

end

section
open Module
universe u
variable {K C R S : Type u} [Field K]
  [AddCommGroup C] [Module K C] [AddCommGroup R] [Module K R]
  [AddCommGroup S] [Module K S]

def baseActions (a : K ≃ₗ[K] K) (c : C ≃ₗ[K] C)
    (r : R ≃ₗ[K] R) (s : S ≃ₗ[K] S) : Transform (K := K) (C := C) (R := R) (S := S) :=
  Fin.cases a (Fin.cases c (Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))))

@[simp] theorem baseActions_zero (a : K ≃ₗ[K] K) (c : C ≃ₗ[K] C) (r : R ≃ₗ[K] R) (s : S ≃ₗ[K] S) :
    baseActions a c r s 0 = a := rfl
@[simp] theorem baseActions_one (a : K ≃ₗ[K] K) (c : C ≃ₗ[K] C) (r : R ≃ₗ[K] R) (s : S ≃ₗ[K] S) :
    baseActions a c r s 1 = c := rfl
@[simp] theorem baseActions_two (a : K ≃ₗ[K] K) (c : C ≃ₗ[K] C) (r : R ≃ₗ[K] R) (s : S ≃ₗ[K] S) :
    baseActions a c r s 2 = r := rfl
@[simp] theorem baseActions_three (a : K ≃ₗ[K] K) (c : C ≃ₗ[K] C) (r : R ≃ₗ[K] R) (s : S ≃ₗ[K] S) :
    baseActions a c r s 3 = s := rfl

@[simp] theorem u0_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PU (K := K) (C := C) (R := R) (S := S)) :
    u0 (K := K) (C := C) (R := R) (S := S) (uAction g x) = g 0 (u0 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem u1_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PU (K := K) (C := C) (R := R) (S := S)) :
    u1 (K := K) (C := C) (R := R) (S := S) (uAction g x) = g 1 (u1 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem u2_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PU (K := K) (C := C) (R := R) (S := S)) :
    u2 (K := K) (C := C) (R := R) (S := S) (uAction g x) = g 2 (u2 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem u3_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PU (K := K) (C := C) (R := R) (S := S)) :
    u3 (K := K) (C := C) (R := R) (S := S) (uAction g x) = g 3 (u3 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem v0_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PV (K := K) (C := C) (R := R) (S := S)) :
    v0 (K := K) (C := C) (R := R) (S := S) (vAction g x) = (g 0).symm.dualMap (v0 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem v1_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PV (K := K) (C := C) (R := R) (S := S)) :
    v1 (K := K) (C := C) (R := R) (S := S) (vAction g x) = (g 1).symm.dualMap (v1 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem v2_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PV (K := K) (C := C) (R := R) (S := S)) :
    v2 (K := K) (C := C) (R := R) (S := S) (vAction g x) = g 3 (v2 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem w0_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PW (K := K) (C := C) (R := R) (S := S)) :
    w0 (K := K) (C := C) (R := R) (S := S) (wAction g x) = (g 0).symm.dualMap (w0 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem w1_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PW (K := K) (C := C) (R := R) (S := S)) :
    w1 (K := K) (C := C) (R := R) (S := S) (wAction g x) = (g 1).symm.dualMap (w1 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem w2_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PW (K := K) (C := C) (R := R) (S := S)) :
    w2 (K := K) (C := C) (R := R) (S := S) (wAction g x) = (g 2).symm.dualMap (w2 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem w3_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PW (K := K) (C := C) (R := R) (S := S)) :
    w3 (K := K) (C := C) (R := R) (S := S) (wAction g x) = g 3 (w3 (K := K) (C := C) (R := R) (S := S) x) := rfl
@[simp] theorem w4_action (g : Transform (K := K) (C := C) (R := R) (S := S))
    (x : PW (K := K) (C := C) (R := R) (S := S)) :
    w4 (K := K) (C := C) (R := R) (S := S) (wAction g x) = (g 3).symm.dualMap (w4 (K := K) (C := C) (R := R) (S := S) x) := rfl

end

section
open Module
universe u
variable {K : Type u} [Field K]
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  (under : A → I)

def namedG (g : ∀ i,V i ≃ₗ[K] V i) : Named (V := V) ≃ₗ[K] Named (V := V) :=
  LinearEquiv.piCongrRight g

def occurrenceG (g : ∀ i,V i ≃ₗ[K] V i) :
    Occurs (V := V) under ≃ₗ[K] Occurs (V := V) under :=
  LinearEquiv.piCongrRight (fun a => g (under a))

theorem named_conjugate (g : ∀ i,V i ≃ₗ[K] V i) (i : I) (x : Named (V := V)) :
    (namedG (K := K) g).symm (namedProjector (K := K) i (namedG (K := K) g x)) = namedProjector (K := K) i x := by
  apply (namedG (K := K) g).injective
  rw [LinearEquiv.apply_symm_apply]
  change Pi.single i ((LinearEquiv.piCongrRight g) x i) =
    (LinearEquiv.piCongrRight g) (Pi.single i (x i))
  rw [piCongr_single]
  rfl

theorem occurrence_conjugate (g : ∀ i,V i ≃ₗ[K] V i) (a : A) (x : Occurs (V := V) under) :
    (occurrenceG (K := K) under g).symm (occurrenceProjector (K := K) under a (occurrenceG (K := K) under g x)) =
      occurrenceProjector (K := K) under a x :=
  named_conjugate (fun a => g (under a)) a x

theorem copy_conjugate (g : ∀ i,V i ≃ₗ[K] V i) (x : Occurs (V := V) under) :
    (namedG (K := K) g).symm (copyMap (K := K) under (occurrenceG (K := K) under g x)) =
      copyMap (K := K) under x := by
  have he := (copyMap_transport_iff (K := K) under g (fun a => g (under a))).mpr (fun _ => rfl)
  have hx := LinearMap.congr_fun he x
  apply (namedG (K := K) g).injective
  rw [LinearEquiv.apply_symm_apply]
  exact hx.symm

def OccurrenceSystemIso
    (F F' : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] K)
    (L L' : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Labels (K := K) (I := I) (A := A)) : Prop :=
  ∃ g : ∀ i,V i ≃ₗ[K] V i,
    (∀ x y z,F (occurrenceG (K := K) under g x) (occurrenceG (K := K) under g y) (occurrenceG (K := K) under g z) = F' x y z) ∧
    (∀ x y,L (occurrenceG (K := K) under g x) (occurrenceG (K := K) under g y) = L' x y)

end

section
open Module
universe u
variable {K : Type u} [Field K]
variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,FiniteDimensional K (V i)] (under : A → I)
set_option backward.isDefEq.respectTransparency false

abbrev EncodedTransform := Transform (K := K) (C := Labels (K := K) (I := I) (A := A))
  (R := Named (V := V)) (S := Occurs (V := V) under)

variable
  (F F' : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] K)
  (L L' : Occurs (V := V) under →ₗ[K] Occurs (V := V) under →ₗ[K] Labels (K := K) (I := I) (A := A))

def Equations (g : EncodedTransform (K := K) (V := V) under) : Prop :=
  ∀ x y z,encode under F L (uAction g x) (vAction g y) (wAction g z) =
    encode under F' L' x y z

theorem encode_forward (h : OccurrenceSystemIso under F F' L L') :
    LinkedIso (encode under F L) (encode under F' L') := by
  obtain ⟨g,hF,hL⟩ := h
  let G := baseActions (LinearEquiv.refl K K)
    (LinearEquiv.refl K (Labels (K := K) (I := I) (A := A)))
    (namedG (K := K) g) (occurrenceG (K := K) under g)
  refine ⟨G,?_⟩
  intro x y z
  change encode under F L (uAction G x) (vAction G y) (wAction G z) = encode under F' L' x y z
  simp only [encode,pack_apply,u0_action,u1_action,u2_action,u3_action,
    v0_action,v1_action,v2_action,w0_action,w1_action,w2_action,w3_action,w4_action]
  simp [G,LinearEquiv.dualMap_apply,named_conjugate,occurrence_conjugate,
    copy_conjugate,hF,hL]

variable (g : EncodedTransform (K := K) (V := V) under)
  (h : Equations under F F' L L' g)

include h in
theorem encoded_frame :
    g 0 = LinearEquiv.refl K K ∧
    g 1 = LinearEquiv.refl K (Labels (K := K) (I := I) (A := A)) := by
  have hs := scalar_rigid (K := K) (C := Labels (K := K) (I := I) (A := A)) (R := Named (V := V)) (S := Occurs (V := V) under) (I := I) (A := A) (shiftMap (K := K) (I := I) (A := A)) (first (K := K) (I := I) (A := A)) (fun i => label (K := K) (I := I) (A := A) (Sum.inl i))
    (fun a => label (K := K) (I := I) (A := A) (Sum.inr a)) (namedProjector (K := K) (V := V)) (occurrenceProjector (K := K) (V := V) under)
    (copyMap (K := K) (V := V) under) F F' L L' g h
  refine ⟨hs,frame_rigid (K := K) (I := I) (A := A) (g 1) ?_ ?_⟩
  · exact first_recovery (K := K) (C := Labels (K := K) (I := I) (A := A)) (R := Named (V := V)) (S := Occurs (V := V) under) (I := I) (A := A) (shiftMap (K := K) (I := I) (A := A)) (first (K := K) (I := I) (A := A)) (fun i => label (K := K) (I := I) (A := A) (Sum.inl i))
      (fun a => label (K := K) (I := I) (A := A) (Sum.inr a)) (namedProjector (K := K) (V := V)) (occurrenceProjector (K := K) (V := V) under)
      (copyMap (K := K) (V := V) under) F F' L L' g h hs
  · exact shift_recovery (K := K) (C := Labels (K := K) (I := I) (A := A)) (R := Named (V := V)) (S := Occurs (V := V) under) (I := I) (A := A) (shiftMap (K := K) (I := I) (A := A)) (first (K := K) (I := I) (A := A)) (fun i => label (K := K) (I := I) (A := A) (Sum.inl i))
      (fun a => label (K := K) (I := I) (A := A) (Sum.inr a)) (namedProjector (K := K) (V := V)) (occurrenceProjector (K := K) (V := V) under)
      (copyMap (K := K) (V := V) under) F F' L L' g h hs

include h in
theorem encoded_named_blocks (hc : g 1 = LinearEquiv.refl K (Labels (K := K) (I := I) (A := A))) :
    PreservesBlocks (g 2).toLinearMap := by
  intro i x
  have he : (g 2).symm (namedProjector (K := K) i (g 2 x)) = namedProjector (K := K) i x := by
    apply dual_separates (K := K) (C := Named (V := V))
    intro f
    have hh := h (Pi.single (2 : Fin 5) x)
      (Pi.single (1 : Fin 4) (coord (K := K) (Sum.inl i : I ⊕ A)))
      (Pi.single (2 : Fin 5) f)
    simpa [encode,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hc,LinearEquiv.dualMap_apply,named_sum_test] using hh
  change g 2 (namedProjector (K := K) i x) = namedProjector (K := K) i (g 2 x)
  exact (congrArg (g 2) he).symm.trans ((g 2).apply_symm_apply _)

include h in
theorem encoded_occurrence_blocks (hc : g 1 = LinearEquiv.refl K (Labels (K := K) (I := I) (A := A))) :
    PreservesBlocks (g 3).toLinearMap := by
  intro a x
  have he : (g 3).symm (occurrenceProjector (K := K) under a (g 3 x)) = occurrenceProjector (K := K) under a x := by
    apply dual_separates (K := K) (C := Occurs (V := V) under)
    intro f
    have hh := h (Pi.single (3 : Fin 5) x)
      (Pi.single (1 : Fin 4) (coord (K := K) (Sum.inr a : I ⊕ A)))
      (Pi.single (4 : Fin 5) f)
    simpa [encode,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hc,LinearEquiv.dualMap_apply,occurrence_sum_test] using hh
  change g 3 (occurrenceProjector (K := K) under a x) = occurrenceProjector (K := K) under a (g 3 x)
  exact (congrArg (g 3) he).symm.trans ((g 3).apply_symm_apply _)

include h in
theorem encoded_copy (hs : g 0 = LinearEquiv.refl K K) :
    (g 2).toLinearMap.comp (copyMap (K := K) (V := V) under) =
      (copyMap (K := K) (V := V) under).comp (g 3).toLinearMap := by
  apply LinearMap.ext
  intro x
  have he : (g 2).symm (copyMap (K := K) under (g 3 x)) = copyMap (K := K) under x := by
    apply dual_separates (K := K) (C := Named (V := V))
    intro f
    have hh := h (Pi.single (3 : Fin 5) x)
      (Pi.single (0 : Fin 4) (LinearMap.id : Dual K K))
      (Pi.single (2 : Fin 5) f)
    simpa [encode,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hs,LinearEquiv.dualMap_apply] using hh
  exact (congrArg (g 2) he).symm.trans ((g 2).apply_symm_apply _)

omit h in
theorem encode_reverse (hh : LinkedIso (encode under F L) (encode under F' L')) :
    OccurrenceSystemIso under F F' L L' := by
  obtain ⟨g,h⟩ := hh
  have hE : Equations under F F' L L' g := h
  obtain ⟨hs,hc⟩ := encoded_frame under F F' L L' g hE
  obtain ⟨gn,hn⟩ := (preservesBlocks_iff (g 2)).mp
    (encoded_named_blocks under F F' L L' g hE hc)
  obtain ⟨go,ho⟩ := (preservesBlocks_iff (g 3)).mp
    (encoded_occurrence_blocks under F F' L L' g hE hc)
  have hcopy := encoded_copy under F F' L L' g hE hs
  rw [← hn,← ho] at hcopy
  have heach := (copyMap_transport_iff under gn go).mp hcopy
  have hO : occurrenceG (K := K) under gn = g 3 := by
    have hgo : go = fun a => gn (under a) := funext heach
    rw [hgo] at ho
    exact ho
  refine ⟨gn,?_,?_⟩
  · intro x y z
    have ht := hE (Pi.single (3 : Fin 5) x) (Pi.single (2 : Fin 4) y) (Pi.single (3 : Fin 5) z)
    simpa [encode,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,← hO] using ht
  · intro x y
    apply dual_separates (K := K) (C := Labels (K := K) (I := I) (A := A))
    intro f
    have ht := hE (Pi.single (3 : Fin 5) x) (Pi.single (2 : Fin 4) y) (Pi.single (1 : Fin 5) f)
    simpa [encode,uAction_single,vAction_single,wAction_single,packedSp,packedSq,packedSr,viewAction,
      hc,← hO,LinearEquiv.dualMap_apply] using ht

omit h in
theorem encoding_correct :
    OccurrenceSystemIso under F F' L L' ↔ LinkedIso (encode under F L) (encode under F' L') :=
  ⟨encode_forward under F F' L L',encode_reverse under F F' L L'⟩

end

/- Private occurrence blocks. -/
section

variable {K C : Type*} [Field K] [Fintype C] [DecidableEq C]
variable {U V W : C → Type*}
variable [∀ c, AddCommGroup (U c)] [∀ c, Module K (U c)]
variable [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- Sum of trilinear components on private coordinate blocks. -/
def packForms (T : ∀ c, U c →ₗ[K] V c →ₗ[K] W c →ₗ[K] K)
    (x : ∀ c, U c) (y : ∀ c, V c) (z : ∀ c, W c) : K :=
  ∑ c, T c (x c) (y c) (z c)
/-- The packed function is an actual curried trilinear form. Astra construction. -/
def packedForm (T : ∀ c, U c →ₗ[K] V c →ₗ[K] W c →ₗ[K] K) :
    (∀ c, U c) →ₗ[K] (∀ c, V c) →ₗ[K] (∀ c, W c) →ₗ[K] K where
  toFun x := {
    toFun := fun y => {
      toFun := fun z => packForms T x y z
      map_add' := by intros; simp [packForms, map_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [packForms, Finset.mul_sum] }
    map_add' := by intros; ext z; simp [packForms, map_add, Finset.sum_add_distrib]
    map_smul' := by intros; ext z; simp [packForms, Finset.mul_sum] }
  map_add' := by intros; ext y z; simp [packForms, map_add, Finset.sum_add_distrib]
  map_smul' := by intros; ext y z; simp [packForms, Finset.mul_sum]

/-- Astra assembly: blockwise linear maps preserve single-block support. -/
theorem blockAction_single (g : ∀ c, U c ≃ₗ[K] U c)
    (c : C) (x : U c) :
    (fun b => g b (Pi.single c x b)) = Pi.single c (g c x) := by
  funext b
  by_cases hb : b = c
  · subst b; simp
  · simp [Pi.single_eq_of_ne hb]

/-- Astra fallback proof; local model attempts are retained separately. -/
theorem packed_component_recovery (T : ∀ c, U c →ₗ[K] V c →ₗ[K] W c →ₗ[K] K)
    (c : C) (x : U c) (y : V c) (z : W c) :
    packForms T (Pi.single c x) (Pi.single c y) (Pi.single c z) = T c x y z := by
  unfold packForms
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hc
    simp at hc

theorem packed_transport_iff
    (T S : ∀ c, U c →ₗ[K] V c →ₗ[K] W c →ₗ[K] K)
    (g : ∀ c, U c ≃ₗ[K] U c) (h : ∀ c, V c ≃ₗ[K] V c)
    (k : ∀ c, W c ≃ₗ[K] W c) :
    (∀ x y z, packForms T (fun c => g c (x c))
      (fun c => h c (y c)) (fun c => k c (z c)) = packForms S x y z) ↔
    (∀ c x y z, T c (g c x) (h c y) (k c z) = S c x y z) := by
  constructor
  · intro H c x y z
    have q := H (Pi.single c x) (Pi.single c y) (Pi.single c z)
    simpa only [blockAction_single, packed_component_recovery] using q
  · intro H x y z
    exact Finset.sum_congr rfl (fun c _ => H c (x c) (y c) (z c))

end

/- Primal and dual payloads. -/
section
open Module
universe u
variable {K : Type u} [Field K]
  {I C : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  (sp sq sr : C → I × Bool)

abbrev Name := I × Bool
abbrev NamedSpace (p : Name (I := I)) := View (K := K) (V := V p.1) p.2
abbrev Occ := C ⊕ (C ⊕ (C ⊕ (I ⊕ I)))
def under : Occ (I := I) (C := C) → Name (I := I)
  | Sum.inl c => sp c
  | Sum.inr (Sum.inl c) => sq c
  | Sum.inr (Sum.inr (Sum.inl c)) => sr c
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => (i,false)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) => (i,true)
abbrev payloadSpace := ∀ o,NamedSpace (K := K) (V := V) (under sp sq sr o)
abbrev Components := ∀ c,NamedSpace (K := K) (V := V) (sp c) →ₗ[K]
  NamedSpace (K := K) (V := V) (sq c) →ₗ[K] NamedSpace (K := K) (V := V) (sr c) →ₗ[K] K

def p0 : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (∀ c,NamedSpace (K := K) (V := V) (sp c)) where
  toFun x c := x (Sum.inl c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def p1 : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (∀ c,NamedSpace (K := K) (V := V) (sq c)) where
  toFun x c := x (Sum.inr (Sum.inl c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def p2 : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (∀ c,NamedSpace (K := K) (V := V) (sr c)) where
  toFun x c := x (Sum.inr (Sum.inr (Sum.inl c)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lift0 (x : ∀ c,NamedSpace (K := K) (V := V) (sp c)) : payloadSpace (K := K) (V := V) sp sq sr :=
  fun o => match o with | Sum.inl c => x c | Sum.inr _ => 0
def lift1 (x : ∀ c,NamedSpace (K := K) (V := V) (sq c)) : payloadSpace (K := K) (V := V) sp sq sr :=
  fun o => match o with
    | Sum.inl _ => 0 | Sum.inr (Sum.inl c) => x c | Sum.inr (Sum.inr _) => 0
def lift2 (x : ∀ c,NamedSpace (K := K) (V := V) (sr c)) : payloadSpace (K := K) (V := V) sp sq sr :=
  fun o => match o with
    | Sum.inl _ => 0 | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl c)) => x c | Sum.inr (Sum.inr (Sum.inr _)) => 0

@[simp] theorem p0_lift0 (x : ∀ c,NamedSpace (K := K) (V := V) (sp c)) :
    p0 sp sq sr (lift0 sp sq sr x) = x := rfl
@[simp] theorem p1_lift1 (x : ∀ c,NamedSpace (K := K) (V := V) (sq c)) :
    p1 sp sq sr (lift1 sp sq sr x) = x := rfl
@[simp] theorem p2_lift2 (x : ∀ c,NamedSpace (K := K) (V := V) (sr c)) :
    p2 sp sq sr (lift2 sp sq sr x) = x := rfl

def action (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p) :
    payloadSpace (K := K) (V := V) sp sq sr ≃ₗ[K] payloadSpace (K := K) (V := V) sp sq sr :=
  LinearEquiv.piCongrRight (fun o => g (under sp sq sr o))

@[simp] theorem p0_action (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p)
    (x : payloadSpace (K := K) (V := V) sp sq sr) :
    p0 sp sq sr (action sp sq sr g x) = fun c => g (sp c) (p0 sp sq sr x c) := rfl
@[simp] theorem p1_action (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p)
    (x : payloadSpace (K := K) (V := V) sp sq sr) :
    p1 sp sq sr (action sp sq sr g x) = fun c => g (sq c) (p1 sp sq sr x c) := rfl
@[simp] theorem p2_action (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p)
    (x : payloadSpace (K := K) (V := V) sp sq sr) :
    p2 sp sq sr (action sp sq sr g x) = fun c => g (sr c) (p2 sp sq sr x c) := rfl

def payload (T : Components (K := K) (V := V) sp sq sr) :
    payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] payloadSpace (K := K) (V := V) sp sq sr →ₗ[K]
      payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] K :=
  pullForm (packedForm T) (p0 sp sq sr) (p1 sp sq sr) (p2 sp sq sr)

@[simp] theorem payload_apply (T : Components (K := K) (V := V) sp sq sr) (x y z) :
    payload sp sq sr T x y z =
      packForms T (p0 sp sq sr x) (p1 sp sq sr y) (p2 sp sq sr z) := rfl

theorem payload_transport_iff (T T' : Components (K := K) (V := V) sp sq sr)
    (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p) :
    (∀ x y z,payload sp sq sr T (action sp sq sr g x) (action sp sq sr g y)
      (action sp sq sr g z) = payload sp sq sr T' x y z) ↔
    (∀ c x y z,T c (g (sp c) x) (g (sq c) y) (g (sr c) z) = T' c x y z) := by
  constructor
  · intro h
    apply (packed_transport_iff T T' (fun c => g (sp c))
      (fun c => g (sq c)) (fun c => g (sr c))).mp
    intro x y z
    simpa only [payload_apply,p0_action,p1_action,p2_action,p0_lift0,p1_lift1,p2_lift2] using
      h (lift0 sp sq sr x) (lift1 sp sq sr y) (lift2 sp sq sr z)
  · intro h x y z
    exact (packed_transport_iff T T' (fun c => g (sp c))
      (fun c => g (sq c)) (fun c => g (sr c))).mpr h
      (p0 sp sq sr x) (p1 sp sq sr y) (p2 sp sq sr z)

def positiveProj : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (∀ i,V i) where
  toFun x i := x (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def negativeProj : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (∀ i,Dual K (V i)) where
  toFun x i := x (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftPositive (x : ∀ i,V i) : payloadSpace (K := K) (V := V) sp sq sr :=
  fun o => match o with
    | Sum.inl _ => 0 | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => x i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0
def liftNegative (x : ∀ i,Dual K (V i)) : payloadSpace (K := K) (V := V) sp sq sr :=
  fun o => match o with
    | Sum.inl _ => 0 | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) => x i

@[simp] theorem positive_lift (x : ∀ i,V i) :
    positiveProj (K := K) sp sq sr (liftPositive (K := K) sp sq sr x) = x := rfl
@[simp] theorem negative_lift (x : ∀ i,Dual K (V i)) :
    negativeProj sp sq sr (liftNegative sp sq sr x) = x := rfl

@[simp] theorem positive_action
    (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p)
    (x : payloadSpace (K := K) (V := V) sp sq sr) (i : I) :
    positiveProj (K := K) sp sq sr (action sp sq sr g x) i = g (i,false) (positiveProj (K := K) sp sq sr x i) := rfl
@[simp] theorem negative_action
    (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p)
    (x : payloadSpace (K := K) (V := V) sp sq sr) (i : I) :
    negativeProj sp sq sr (action sp sq sr g x) i = g (i,true) (negativeProj sp sq sr x i) := rfl

def pairVector : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] (I → K) where
  toFun x :=
    { toFun := fun y i => negativeProj sp sq sr x i (positiveProj (K := K) sp sq sr y i)
      map_add' := by intros; funext i; simp
      map_smul' := by intros; funext i; simp }
  map_add' := by intros; apply LinearMap.ext; intro y; funext i; simp
  map_smul' := by intros; apply LinearMap.ext; intro y; funext i; simp

@[simp] theorem pairVector_apply (x y : payloadSpace (K := K) (V := V) sp sq sr) (i : I) :
    pairVector sp sq sr x y i = negativeProj sp sq sr x i (positiveProj (K := K) sp sq sr y i) := rfl

theorem pairVector_transport_iff
    (g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p) :
    (∀ x y,pairVector sp sq sr (action sp sq sr g x) (action sp sq sr g y) = pairVector sp sq sr x y) ↔
      (∀ i,g (i,true) = (g (i,false)).symm.dualMap) := by
  constructor
  · intro h i
    apply (pairing_transport_iff (g (i,false)) (g (i,true))).mp
    intro v f
    have hh := congrFun (h (liftNegative sp sq sr (Pi.single i f))
      (liftPositive (K := K) sp sq sr (Pi.single i v))) i
    simpa only [pairVector_apply,negative_action,positive_action,negative_lift,
      positive_lift,Pi.single_eq_same] using hh
  · intro h x y
    funext i
    simp only [pairVector_apply,negative_action,positive_action,h]
    change negativeProj sp sq sr x i ((g (i,false)).symm
      (g (i,false) (positiveProj (K := K) sp sq sr y i))) =
        negativeProj sp sq sr x i (positiveProj (K := K) sp sq sr y i)
    exact congrArg (negativeProj sp sq sr x i) ((g (i,false)).symm_apply_apply _)

def MixedIso (T T' : Components (K := K) (V := V) sp sq sr) : Prop :=
  ∃ g : ∀ i,V i ≃ₗ[K] V i, ∀ c x y z,
    T c (viewAction (g (sp c).1) (sp c).2 x)
      (viewAction (g (sq c).1) (sq c).2 y)
      (viewAction (g (sr c).1) (sr c).2 z) = T' c x y z

def ExpandedIso (T T' : Components (K := K) (V := V) sp sq sr) : Prop :=
  ∃ g : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p,
    (∀ x y z,payload sp sq sr T (action sp sq sr g x) (action sp sq sr g y)
      (action sp sq sr g z) = payload sp sq sr T' x y z) ∧
    (∀ x y,pairVector sp sq sr (action sp sq sr g x) (action sp sq sr g y) = pairVector sp sq sr x y)

theorem mixed_iff_expanded (T T' : Components (K := K) (V := V) sp sq sr) :
    MixedIso sp sq sr T T' ↔ ExpandedIso sp sq sr T T' := by
  constructor
  · rintro ⟨g,h⟩
    let G : ∀ p,NamedSpace (K := K) (V := V) p ≃ₗ[K] NamedSpace (K := K) (V := V) p :=
      fun p => viewAction (g p.1) p.2
    refine ⟨G,(payload_transport_iff sp sq sr T T' G).mpr h,?_⟩
    apply (pairVector_transport_iff sp sq sr G).mpr
    intro i
    rfl
  · rintro ⟨G,hT,hP⟩
    have hp := (pairVector_transport_iff sp sq sr G).mp hP
    have ht := (payload_transport_iff sp sq sr T T' G).mp hT
    let g : ∀ i,V i ≃ₗ[K] V i := fun i => G (i,false)
    have he : ∀ p,G p = viewAction (g p.1) p.2 := by
      rintro ⟨i,b⟩
      cases b
      · rfl
      · exact hp i
    refine ⟨g,?_⟩
    intro c x y z
    simpa only [he] using ht c x y z

end

/- Compiling mixed systems. -/
section
open Module
universe u
variable {K : Type u} [Field K]
  {I C : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,FiniteDimensional K (V i)]
  (sp sq sr : C → I × Bool)

abbrev LabelSpace := Labels (K := K) (I := Name (I := I)) (A := Occ (I := I) (C := C))

def pairLabels : (I → K) →ₗ[K] LabelSpace (K := K) (I := I) (C := C) where
  toFun x := ∑ i,x i • label (K := K) (Sum.inl (i,false) :
    Name (I := I) ⊕ Occ (I := I) (C := C))
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum,smul_smul]

@[simp] theorem test_pairLabels (x : I → K) (i : I) :
    coord (K := K) (Sum.inl (i,false) : Name (I := I) ⊕ Occ (I := I) (C := C))
      (pairLabels (K := K) (C := C) x) = x i := by
  simp [pairLabels,coord_label]

theorem pairLabels_injective : Function.Injective (pairLabels (K := K) (I := I) (C := C)) := by
  intro x y h
  funext i
  have hh := congrArg (coord (K := K)
    (Sum.inl (i,false) : Name (I := I) ⊕ Occ (I := I) (C := C))) h
  simpa only [test_pairLabels] using hh

def coupling : payloadSpace (K := K) (V := V) sp sq sr →ₗ[K] payloadSpace (K := K) (V := V) sp sq sr →ₗ[K]
    LabelSpace (K := K) (I := I) (C := C) where
  toFun x := (pairLabels (K := K) (C := C)).comp (pairVector sp sq sr x)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

theorem expanded_iff_occurrence (T T' : Components (K := K) (V := V) sp sq sr) :
    ExpandedIso sp sq sr T T' ↔
      OccurrenceSystemIso (under sp sq sr)
        (payload sp sq sr T) (payload sp sq sr T') (coupling sp sq sr) (coupling sp sq sr) := by
  constructor
  · rintro ⟨g,hT,hP⟩
    refine ⟨g,hT,?_⟩
    intro x y
    exact congrArg (pairLabels (K := K) (C := C)) (hP x y)
  · rintro ⟨g,hT,hP⟩
    refine ⟨g,hT,?_⟩
    intro x y
    exact pairLabels_injective (hP x y)

def linked (T : Components (K := K) (V := V) sp sq sr) :=
  encode (under sp sq sr) (payload sp sq sr T) (coupling sp sq sr)

/-- Complete mixed-variance system packing into the explicit 14-part,
four-base linked tensor. -/
theorem mixed_iff_linked (T T' : Components (K := K) (V := V) sp sq sr) :
    MixedIso sp sq sr T T' ↔ LinkedIso (linked sp sq sr T) (linked sp sq sr T') :=
  (mixed_iff_expanded sp sq sr T T').trans
    ((expanded_iff_occurrence sp sq sr T T').trans
      (encoding_correct (under sp sq sr)
        (payload sp sq sr T) (payload sp sq sr T') (coupling sp sq sr) (coupling sp sq sr)))

def baseDim := ∑ i,finrank K (V i)
def incidenceDim :=
  (∑ c,finrank K (V (sp c).1)) + (∑ c,finrank K (V (sq c).1)) + (∑ c,finrank K (V (sr c).1))

theorem mixedNamed_dimension :
    finrank K (∀ p,NamedSpace (K := K) (V := V) p) = 2 * baseDim (K := K) (V := V) := by
  simp [Module.finrank_pi_fintype,Fintype.sum_prod_type,NamedSpace,view_finrank,baseDim,
    Finset.mul_sum,two_mul]

theorem mixedOccurrence_dimension :
    finrank K (payloadSpace (K := K) (V := V) sp sq sr) =
      incidenceDim (K := K) (V := V) sp sq sr + 2 * baseDim (K := K) (V := V) := by
  change finrank K (∀ o : Occ (I := I) (C := C),NamedSpace (K := K) (V := V) (under sp sq sr o)) = _
  rw [Module.finrank_pi_fintype]
  simp only [Fintype.sum_sum_type]
  change (∑ c,finrank K (NamedSpace (K := K) (V := V) (sp c))) +
    ((∑ c,finrank K (NamedSpace (K := K) (V := V) (sq c))) +
    ((∑ c,finrank K (NamedSpace (K := K) (V := V) (sr c))) +
    ((∑ i,finrank K (NamedSpace (K := K) (V := V) (i,false))) +
    (∑ i,finrank K (NamedSpace (K := K) (V := V) (i,true)))))) = _
  have hv (p : I × Bool) : finrank K (NamedSpace (K := K) (V := V) p) = finrank K (V p.1) := view_finrank _
  simp_rw [hv]
  unfold incidenceDim baseDim
  omega

theorem labels_dimension :
    finrank K (LabelSpace (K := K) (I := I) (C := C)) = 4*Fintype.card I + 3*Fintype.card C + 1 := by
  simp [LabelSpace,Labels,Name,Occ]
  omega

end

section
open Module
universe u
variable {K C R S : Type u} [Field K]
  [AddCommGroup C] [Module K C] [AddCommGroup R] [Module K R]
  [AddCommGroup S] [Module K S]
  [FiniteDimensional K C] [FiniteDimensional K R] [FiniteDimensional K S]
theorem packed_linked_dimension (T : PackForm (K := K) (C := C) (R := R) (S := S)) :
    linkedDim T =
      9 * finrank K C + 8 * finrank K R + 12 * finrank K S + 46 := by
  have hb (i : Fin 4) : finrank K (Bases (K := K) (C := C) (R := R) (S := S) i) =
      ![1,finrank K C,finrank K R,finrank K S] i := by
    fin_cases i
    · change finrank K K = 1
      exact Module.finrank_self K
    · rfl
    · rfl
    · rfl
  unfold linkedDim
  simp_rw [hb]
  simp [packedSp,packedSq,packedSr,Fin.sum_univ_succ]
  omega
end

section
open Module
universe u
variable {K : Type u} [Field K]
  {I C : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
  {V : I → Type u} [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,FiniteDimensional K (V i)]
  (sp sq sr : C → I × Bool)

def mixedOrdinary (T : Components (K := K) (V := V) sp sq sr) :=
  linkedOrdinary (linked sp sq sr T)
def mixedOutputIso (T U : Components (K := K) (V := V) sp sq sr) : Prop :=
  linkedOutputIso (linked sp sq sr T) (linked sp sq sr U)
def mixedOutputDim (T : Components (K := K) (V := V) sp sq sr) : ℕ :=
  linkedOutputDim (linked sp sq sr T)

theorem mixed_iff_ordinary (T U : Components (K := K) (V := V) sp sq sr) :
    MixedIso sp sq sr T U ↔ mixedOutputIso sp sq sr T U :=
  (mixed_iff_linked sp sq sr T U).trans
    (linkedOrdinary_correct (linked sp sq sr T) (linked sp sq sr U))

theorem linked_dimension (T : Components (K := K) (V := V) sp sq sr) :
    linkedDim (linked sp sq sr T) =
      9*(4*Fintype.card I + 3*Fintype.card C + 1) +
      40*baseDim (K := K) (V := V) + 12*incidenceDim (K := K) (V := V) sp sq sr + 46 := by
  rw [packed_linked_dimension]
  rw [labels_dimension,mixedNamed_dimension,mixedOccurrence_dimension]
  omega

theorem mixedOrdinary_size (T : Components (K := K) (V := V) sp sq sr) :
    mixedOutputDim sp sq sr T ≤ linkFactor 5 4 5 4 *
      (9*(4*Fintype.card I + 3*Fintype.card C + 1) +
      40*baseDim (K := K) (V := V) + 12*incidenceDim (K := K) (V := V) sp sq sr + 47) := by
  have h := linkedOrdinary_size (linked sp sq sr T)
  rw [linked_dimension] at h
  simpa only [mixedOutputDim,Fintype.card_fin,Nat.add_assoc] using h

end

/- Product trees and dimension bounds. -/
section
open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

inductive Tree where
  | leaf (dimension : ℕ)
  | node (left right : Tree)
  deriving DecidableEq

def Idx : Tree → Type
  | Tree.leaf n => Fin n
  | Tree.node l r => Idx l × Idx r

instance idxFintype : (t : Tree) → Fintype (Idx t)
  | Tree.leaf n => inferInstanceAs (Fintype (Fin n))
  | Tree.node l r => @instFintypeProd _ _ (idxFintype l) (idxFintype r)

instance idxDecidableEq : (t : Tree) → DecidableEq (Idx t)
  | Tree.leaf n => inferInstanceAs (DecidableEq (Fin n))
  | Tree.node l r => @instDecidableEqProd _ _ (idxDecidableEq l) (idxDecidableEq r)

variable {K : Type*} [Field K]

/-- Coordinates of the canonical bilinear tensor product. -/
def pure {I J : Type*} (x : I → K) (y : J → K) : I × J → K :=
  fun ij => x ij.1 * y ij.2

theorem kron_pure {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I K) (B : Matrix J J K) (x : I → K) (y : J → K) :
    (A ⊗ₖ B).mulVec (pure x y) = pure (A.mulVec x) (B.mulVec y) := by
  ext ⟨i,j⟩
  simp only [mulVec, dotProduct, pure, kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem pure_single {I J : Type*} [DecidableEq I] [DecidableEq J] (i : I) (j : J) :
    pure (Pi.single i (1 : K)) (Pi.single j 1) = Pi.single (i,j) 1 := by
  ext ⟨a,b⟩
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp_all [pure, Prod.mk.injEq, eq_comm]

/-- Preserving the actual bilinear product is equivalent to a Kronecker matrix. -/
theorem preserves_product_iff {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I K) (B : Matrix J J K) (P : Matrix (I × J) (I × J) K) :
    (∀ x y, P.mulVec (pure x y) = pure (A.mulVec x) (B.mulVec y)) ↔
      P = A ⊗ₖ B := by
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    rintro ⟨i,j⟩
    rw [← pure_single i j, h, kron_pure]
  · rintro rfl
    exact kron_pure A B

abbrev TreeGL (t : Tree) := (Matrix (Idx t) (Idx t) K)ˣ

/-- Independently chosen invertible matrices at the original leaves. -/
def Leaves (K : Type*) [Field K] : Tree → Type _
  | Tree.leaf n => (Matrix (Fin n) (Fin n) K)ˣ
  | Tree.node l r => Leaves K l × Leaves K r

/-- Independent invertible matrices at every named space, including internal nodes. -/
def Changes (K : Type*) [Field K] : Tree → Type _
  | Tree.leaf n => (Matrix (Fin n) (Fin n) K)ˣ
  | Tree.node l r => Changes K l × Changes K r × TreeGL (K := K) (Tree.node l r)

def root : {t : Tree} → Changes K t → TreeGL (K := K) t
  | Tree.leaf _, h => h
  | Tree.node _ _, h => h.2.2

def leafRoot : {t : Tree} → Leaves K t → TreeGL (K := K) t
  | Tree.leaf _, g => g
  | Tree.node _ _, g => GeneralLinearGroup.kronecker (leafRoot g.1) (leafRoot g.2)

def restrict : {t : Tree} → Changes K t → Leaves K t
  | Tree.leaf _, h => h
  | Tree.node _ _, h => (restrict h.1, restrict h.2.1)

def treeExtend : {t : Tree} → Leaves K t → Changes K t
  | Tree.leaf _, g => g
  | Tree.node _ _, g => (treeExtend g.1, treeExtend g.2, leafRoot g)

/-- These are the equations of the fixed canonical bilinear tensors at all nodes. -/
def Coherent : {t : Tree} → Changes K t → Prop
  | Tree.leaf _, _ => True
  | Tree.node _ _, h =>
      Coherent h.1 ∧ Coherent h.2.1 ∧
      ∀ x y, h.2.2.val.mulVec (pure x y) =
        pure ((root h.1).val.mulVec x) ((root h.2.1).val.mulVec y)

@[simp] theorem root_extend {t : Tree} (g : Leaves K t) :
    root (treeExtend g) = leafRoot g := by
  cases t <;> rfl

theorem extend_coherent {t : Tree} (g : Leaves K t) : Coherent (treeExtend g) := by
  induction t with
  | leaf n => trivial
  | node l r hl hr =>
    refine ⟨hl g.1, hr g.2, ?_⟩
    change ∀ x y, ((leafRoot g.1).val ⊗ₖ (leafRoot g.2).val).mulVec (pure x y) =
      pure ((root (treeExtend g.1)).val.mulVec x) ((root (treeExtend g.2)).val.mulVec y)
    rw [root_extend, root_extend]
    exact kron_pure _ _

/-- All internal transformations are forced, with no scalar ambiguity. -/
theorem root_recovery {t : Tree} (h : Changes K t) (hc : Coherent h) :
    root h = leafRoot (restrict h) := by
  induction t with
  | leaf n => rfl
  | node l r hl hr =>
    obtain ⟨hcl,hcr,hp⟩ := hc
    apply Units.ext
    change h.2.2.val = (leafRoot (restrict h.1)).val ⊗ₖ
      (leafRoot (restrict h.2.1)).val
    rw [← hl h.1 hcl, ← hr h.2.1 hcr]
    exact (preserves_product_iff _ _ _).mp hp

/-- The ordinary three-factor coordinate action on the three root spaces. -/
def rootAction {a b c : Tree} (A : TreeGL (K := K) a) (B : TreeGL (K := K) b)
    (C : TreeGL (K := K) c) (T : Idx a × (Idx b × Idx c) → K) :
    Idx a × (Idx b × Idx c) → K :=
  (A.val ⊗ₖ (B.val ⊗ₖ C.val)).mulVec T

/-- Tensor isomorphism with one independent change of basis at each original leaf. -/
def LeafIso (a b c : Tree) (T U : Idx a × (Idx b × Idx c) → K) : Prop :=
  ∃ ga : Leaves K a, ∃ gb : Leaves K b, ∃ gc : Leaves K c,
    rootAction (leafRoot ga) (leafRoot gb) (leafRoot gc) T = U

/-- Isomorphism of the root tensor together with every fixed canonical product tensor. -/
def SystemIso (a b c : Tree) (T U : Idx a × (Idx b × Idx c) → K) : Prop :=
  ∃ ha : Changes K a, ∃ hb : Changes K b, ∃ hc : Changes K c,
    Coherent ha ∧ Coherent hb ∧ Coherent hc ∧
    rootAction (root ha) (root hb) (root hc) T = U

/-- Unconditional forward and reverse reduction for arbitrary shapes and arbitrary tensors. -/
theorem leafIso_iff_systemIso (a b c : Tree)
    (T U : Idx a × (Idx b × Idx c) → K) :
    LeafIso a b c T U ↔ SystemIso a b c T U := by
  constructor
  · rintro ⟨ga,gb,gc,h⟩
    exact ⟨treeExtend ga, treeExtend gb, treeExtend gc, extend_coherent ga, extend_coherent gb,
      extend_coherent gc, by simpa only [root_extend] using h⟩
  · rintro ⟨ha,hb,hc,hca,hcb,hcc,h⟩
    exact ⟨restrict ha, restrict hb, restrict hc,
      by simpa only [root_recovery ha hca, root_recovery hb hcb, root_recovery hc hcc] using h⟩

def dim : Tree → ℕ
  | Tree.leaf n => n
  | Tree.node l r => dim l * dim r

def leafCount : Tree → ℕ
  | Tree.leaf _ => 1
  | Tree.node l r => leafCount l + leafCount r

def spaceCount : Tree → ℕ
  | Tree.leaf _ => 1
  | Tree.node l r => spaceCount l + spaceCount r + 1

def treeTotalDim : Tree → ℕ
  | Tree.leaf n => n
  | Tree.node l r => treeTotalDim l + treeTotalDim r + dim (Tree.node l r)

def productOccurrenceDim : Tree → ℕ
  | Tree.leaf _ => 0
  | Tree.node l r => productOccurrenceDim l + productOccurrenceDim r +
      dim l + dim r + dim (Tree.node l r)

theorem card_idx (t : Tree) : Fintype.card (Idx t) = dim t := by
  induction t with
  | leaf n => exact Fintype.card_fin n
  | node l r hl hr =>
    change Fintype.card (Idx l × Idx r) = dim l * dim r
    rw [Fintype.card_prod, hl, hr]

theorem leafCount_pos (t : Tree) : 0 < leafCount t := by
  induction t <;> simp_all [leafCount]

theorem spaceCount_eq (t : Tree) : spaceCount t + 1 = 2 * leafCount t := by
  induction t <;> simp_all [spaceCount, leafCount]
  omega

/-- Every original space occurs once and every internal space occurs twice. -/
theorem occurrence_bound (t : Tree) :
    productOccurrenceDim t + dim t ≤ 2 * treeTotalDim t := by
  induction t with
  | leaf n => simp only [productOccurrenceDim, dim, treeTotalDim]; omega
  | node l r hl hr =>
    simp only [productOccurrenceDim, treeTotalDim]
    omega

/-- Prefix tree, with an explicit first dimension so the group is nonempty. -/
def prefixTree (first : ℕ) : List ℕ → Tree
  | [] => Tree.leaf first
  | n :: ns => Tree.node (prefixTree first ns) (Tree.leaf n)

theorem prefix_leaves (first : ℕ) (ns : List ℕ) :
    leafCount (prefixTree first ns) = ns.length + 1 := by
  induction ns <;> simp_all [prefixTree, leafCount]

theorem prefix_dim_bound {n first : ℕ} (hf : first ≤ n) (ns : List ℕ)
    (hs : ∀ m ∈ ns, m ≤ n) :
    dim (prefixTree first ns) ≤ n ^ (ns.length + 1) := by
  induction ns with
  | nil => simpa [prefixTree,dim] using hf
  | cons m ms ih =>
    have hm := hs m (by simp)
    have hms : ∀ a ∈ ms, a ≤ n := fun a ha => hs a (by simp [ha])
    simpa [prefixTree, dim, pow_succ] using Nat.mul_le_mul (ih hms) hm

/-- Linear in the largest group dimension, with constant independent of its length. -/
theorem prefix_total_bound {n first : ℕ} (hn : 2 ≤ n) (hf : first ≤ n)
    (ns : List ℕ) (hs : ∀ m ∈ ns, m ≤ n) :
    treeTotalDim (prefixTree first ns) ≤ 3 * n ^ (ns.length + 1) := by
  induction ns with
  | nil => simp only [prefixTree,treeTotalDim,List.length_nil,zero_add,pow_one]; omega
  | cons m ms ih =>
    have hm := hs m (by simp)
    have hms : ∀ a ∈ ms, a ≤ n := fun a ha => hs a (by simp [ha])
    have hprev := ih hms
    have hdim := prefix_dim_bound hf ms hms
    have hp : n ≤ n ^ (ms.length + 1) := Nat.le_self_pow (by omega) n
    have hmul : dim (prefixTree first ms) * m ≤ n ^ (ms.length + 1) * n :=
      Nat.mul_le_mul hdim hm
    have hscale : 2 * n ^ (ms.length + 1) ≤ n ^ (ms.length + 1) * n := by
      nlinarith
    change treeTotalDim (prefixTree first ms) + m + dim (prefixTree first ms) * m ≤
      3 * n ^ ((ms.length + 1) + 1)
    rw [pow_succ]
    nlinarith

def systemDim (a b c : Tree) : ℕ := treeTotalDim a + treeTotalDim b + treeTotalDim c

def systemOccurrenceDim (a b c : Tree) : ℕ :=
  (productOccurrenceDim a + dim a) + (productOccurrenceDim b + dim b) +
    (productOccurrenceDim c + dim c)

def systemSpaces (a b c : Tree) : ℕ := spaceCount a + spaceCount b + spaceCount c

def systemComponents (a b c : Tree) : ℕ := leafCount a + leafCount b + leafCount c - 2

theorem system_occurrence_bound (a b c : Tree) :
    systemOccurrenceDim a b c ≤ 2 * systemDim a b c := by
  have ha := occurrence_bound a
  have hb := occurrence_bound b
  have hc := occurrence_bound c
  unfold systemOccurrenceDim systemDim
  omega

theorem exact_counts (a b c : Tree) :
    let d := leafCount a + leafCount b + leafCount c
    systemSpaces a b c = 2*d-3 ∧ systemComponents a b c = d-2 := by
  have ha := spaceCount_eq a
  have hb := spaceCount_eq b
  have hc := spaceCount_eq c
  have ha' := leafCount_pos a
  have hb' := leafCount_pos b
  have hc' := leafCount_pos c
  dsimp [systemSpaces,systemComponents]
  omega

theorem prefix_bound_at {n k first : ℕ} (hn : 2 ≤ n) (hf : first ≤ n)
    (ns : List ℕ) (hs : ∀ m ∈ ns, m ≤ n) (hk : ns.length + 1 ≤ k) :
    treeTotalDim (prefixTree first ns) ≤ 3 * n ^ k :=
  (prefix_total_bound hn hf ns hs).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) hk))

/-- Positivity of the original factor dimensions. -/
def Positive : Tree → Prop
  | Tree.leaf n => 1 ≤ n
  | Tree.node l r => Positive l ∧ Positive r

theorem positive_dim {t : Tree} (h : Positive t) : 1 ≤ dim t := by
  induction t with
  | leaf n => exact h
  | node l r hl hr => exact Nat.mul_pos (hl h.1) (hr h.2)

/-- Polynomial size in the actual dense coordinate count, without a uniform-shape assumption. -/
theorem totalDim_le_spaces_mul_dim {t : Tree} (h : Positive t) :
    treeTotalDim t ≤ spaceCount t * dim t := by
  induction t with
  | leaf n => simp [treeTotalDim, spaceCount, dim]
  | node l r hl hr =>
    have hdl := positive_dim h.1
    have hdr := positive_dim h.2
    have hl' := hl h.1
    have hr' := hr h.2
    have h₁ : dim l ≤ dim l * dim r := Nat.le_mul_of_pos_right _ hdr
    have h₂ : dim r ≤ dim l * dim r := Nat.le_mul_of_pos_left _ hdl
    have h₃ := Nat.mul_le_mul_left (spaceCount l) h₁
    have h₄ := Nat.mul_le_mul_left (spaceCount r) h₂
    simp only [treeTotalDim,spaceCount,dim]
    nlinarith

theorem actual_input_size_bound (a b c : Tree) (ha : Positive a)
    (hb : Positive b) (hc : Positive c) :
    systemDim a b c ≤ systemSpaces a b c * (dim a * dim b * dim c) := by
  have h₁ := totalDim_le_spaces_mul_dim ha
  have h₂ := totalDim_le_spaces_mul_dim hb
  have h₃ := totalDim_le_spaces_mul_dim hc
  have hpa := positive_dim ha
  have hpb := positive_dim hb
  have hpc := positive_dim hc
  have hab : 1 ≤ dim a * dim b := Nat.mul_pos hpa hpb
  have hac : 1 ≤ dim a * dim c := Nat.mul_pos hpa hpc
  have hbc : 1 ≤ dim b * dim c := Nat.mul_pos hpb hpc
  have hA : dim a ≤ dim a * dim b * dim c := by
    simpa [mul_assoc] using Nat.le_mul_of_pos_right (dim a) hbc
  have hB : dim b ≤ dim a * dim b * dim c := by
    simpa [mul_assoc,mul_left_comm,mul_comm] using Nat.le_mul_of_pos_right (dim b) hac
  have hC : dim c ≤ dim a * dim b * dim c := Nat.le_mul_of_pos_left _ hab
  have hA' := Nat.mul_le_mul_left (spaceCount a) hA
  have hB' := Nat.mul_le_mul_left (spaceCount b) hB
  have hC' := Nat.mul_le_mul_left (spaceCount c) hC
  unfold systemDim systemSpaces
  nlinarith

end

/- Flattening product-tree systems. -/
section
open Module
universe u
variable {K : Type u} [Field K]

def Nodes : Tree → Type
  | Tree.leaf _ => Unit
  | Tree.node l r => Nodes l ⊕ (Nodes r ⊕ Unit)
def nodeAt : (t : Tree) → Nodes t → Tree
  | Tree.leaf n,_ => Tree.leaf n
  | Tree.node l _,Sum.inl i => nodeAt l i
  | Tree.node _ r,Sum.inr (Sum.inl i) => nodeAt r i
  | Tree.node l r,Sum.inr (Sum.inr _) => Tree.node l r
instance nodesFintype : (t : Tree) → Fintype (Nodes t)
  | Tree.leaf _ => inferInstanceAs (Fintype Unit)
  | Tree.node l r => @instFintypeSum _ _ (nodesFintype l)
      (@instFintypeSum _ _ (nodesFintype r) inferInstance)
instance nodesDecidableEq : (t : Tree) → DecidableEq (Nodes t)
  | Tree.leaf _ => inferInstanceAs (DecidableEq Unit)
  | Tree.node l r => @instDecidableEqSum _ _ (nodesDecidableEq l)
      (@instDecidableEqSum _ _ (nodesDecidableEq r) inferInstance)
def top : (t : Tree) → Nodes t
  | Tree.leaf _ => ()
  | Tree.node _ _ => Sum.inr (Sum.inr ())
@[simp] theorem nodeAt_top (t : Tree) : nodeAt t (top t) = t := by cases t <;> rfl
abbrev nodeSpace (t : Tree) (i : Nodes t) := Idx (nodeAt t i) → K

def Inner : Tree → Type
  | Tree.leaf _ => Empty
  | Tree.node l r => Inner l ⊕ (Inner r ⊕ Unit)
instance innerFintype : (t : Tree) → Fintype (Inner t)
  | Tree.leaf _ => inferInstanceAs (Fintype Empty)
  | Tree.node l r => @instFintypeSum _ _ (innerFintype l)
      (@instFintypeSum _ _ (innerFintype r) inferInstance)
instance innerDecidableEq : (t : Tree) → DecidableEq (Inner t)
  | Tree.leaf _ => inferInstanceAs (DecidableEq Empty)
  | Tree.node l r => @instDecidableEqSum _ _ (innerDecidableEq l)
      (@instDecidableEqSum _ _ (innerDecidableEq r) inferInstance)

def leftName : (t : Tree) → Inner t → Nodes t
  | Tree.leaf _,e => nomatch e
  | Tree.node l _,Sum.inl i => Sum.inl (leftName l i)
  | Tree.node _ r,Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (leftName r i))
  | Tree.node l _,Sum.inr (Sum.inr _) => Sum.inl (top l)
def rightName : (t : Tree) → Inner t → Nodes t
  | Tree.leaf _,e => nomatch e
  | Tree.node l _,Sum.inl i => Sum.inl (rightName l i)
  | Tree.node _ r,Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (rightName r i))
  | Tree.node _ r,Sum.inr (Sum.inr _) => Sum.inr (Sum.inl (top r))
def parentName : (t : Tree) → Inner t → Nodes t
  | Tree.leaf _,e => nomatch e
  | Tree.node l _,Sum.inl i => Sum.inl (parentName l i)
  | Tree.node _ r,Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (parentName r i))
  | Tree.node _ _,Sum.inr (Sum.inr _) => Sum.inr (Sum.inr ())

def coordinateProduct {A B : Type} : (A → K) →ₗ[K] (B → K) →ₗ[K] (A × B → K) where
  toFun x :=
    { toFun := fun y ab => x ab.1 * y ab.2
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }
  map_add' := by intros; ext; simp [add_mul]
  map_smul' := by intros; ext; simp [mul_assoc]

end
section
open Module
universe u
variable {K : Type u} [Field K]

def topSpace (t : Tree) : nodeSpace (K := K) t (top t) ≃ₗ[K] (Idx t → K) := by
  cases t <;> exact LinearEquiv.refl K _

def flatten : {t : Tree} → Changes K t → ∀ i : Nodes t,TreeGL (K := K) (nodeAt t i)
  | Tree.leaf _,g,_ => g
  | Tree.node _ _,g,Sum.inl i => flatten g.1 i
  | Tree.node _ _,g,Sum.inr (Sum.inl i) => flatten g.2.1 i
  | Tree.node _ _,g,Sum.inr (Sum.inr _) => g.2.2

def unflatten : (t : Tree) → (∀ i : Nodes t,TreeGL (K := K) (nodeAt t i)) → Changes K t
  | Tree.leaf _,g => g ()
  | Tree.node l r,g => (unflatten l (fun i => g (Sum.inl i)),
      unflatten r (fun i => g (Sum.inr (Sum.inl i))),g (Sum.inr (Sum.inr ())))

theorem unflatten_flatten {t : Tree} (g : Changes K t) : unflatten t (flatten g) = g := by
  induction t with
  | leaf n => rfl
  | node l r hl hr => exact Prod.ext (hl g.1) (Prod.ext (hr g.2.1) rfl)

theorem flatten_unflatten (t : Tree) (g : ∀ i : Nodes t,TreeGL (K := K) (nodeAt t i)) :
    flatten (unflatten t g) = g := by
  induction t with
  | leaf n => funext i; cases i; rfl
  | node l r hl hr =>
    funext i
    rcases i with i | (i | i)
    · exact congrFun (hl (fun i => g (Sum.inl i))) i
    · exact congrFun (hr (fun i => g (Sum.inr (Sum.inl i)))) i
    · cases i; rfl

def changesEquiv (t : Tree) : Changes K t ≃ (∀ i : Nodes t,TreeGL (K := K) (nodeAt t i)) where
  toFun := flatten
  invFun := unflatten t
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten t

def matrixEquiv {A : Type} [Fintype A] [DecidableEq A] :
    (Matrix A A K)ˣ ≃* ((A → K) ≃ₗ[K] (A → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (A → K))

@[simp] theorem matrixEquiv_apply {A : Type} [Fintype A] [DecidableEq A]
    (g : (Matrix A A K)ˣ) (x : A → K) : matrixEquiv g x = g.val.mulVec x := rfl

def linearChangesEquiv (t : Tree) :
    Changes K t ≃ (∀ i : Nodes t,nodeSpace (K := K) t i ≃ₗ[K] nodeSpace (K := K) t i) :=
  (changesEquiv t).trans (Equiv.piCongrRight (fun _ => matrixEquiv.toEquiv))

@[simp] theorem top_flatten {t : Tree} (g : Changes K t) (x : nodeSpace (K := K) t (top t)) :
    topSpace t (matrixEquiv (flatten g (top t)) x) = matrixEquiv (root g) (topSpace t x) := by
  cases t <;> rfl

end
section
set_option backward.isDefEq.respectTransparency false
open Module
universe u
variable {K : Type u} [Field K]

def rootProduct (l r : Tree) : nodeSpace (K := K) l (top l) →ₗ[K]
    nodeSpace (K := K) r (top r) →ₗ[K] (Idx (Tree.node l r) → K) where
  toFun x := (coordinateProduct (topSpace l x)).comp (topSpace r).toLinearMap
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change coordinateProduct (topSpace l (x+y)) (topSpace r z) =
      coordinateProduct (topSpace l x) (topSpace r z) + coordinateProduct (topSpace l y) (topSpace r z)
    rw [map_add,map_add,LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    change coordinateProduct (topSpace l (a • x)) (topSpace r z) =
      a • coordinateProduct (topSpace l x) (topSpace r z)
    rw [map_smul,map_smul,LinearMap.smul_apply]

def product : (t : Tree) → (i : Inner t) →
    nodeSpace (K := K) t (leftName t i) →ₗ[K]
      nodeSpace (K := K) t (rightName t i) →ₗ[K] nodeSpace (K := K) t (parentName t i)
  | Tree.leaf _,e => nomatch e
  | Tree.node l _,Sum.inl i => product l i
  | Tree.node _ r,Sum.inr (Sum.inl i) => product r i
  | Tree.node l r,Sum.inr (Sum.inr _) => rootProduct l r

def Preserves (t : Tree) (g : ∀ i : Nodes t,nodeSpace (K := K) t i ≃ₗ[K] nodeSpace (K := K) t i) : Prop :=
  ∀ i x y,g (parentName t i) (product t i x y) =
    product t i (g (leftName t i) x) (g (rightName t i) y)

theorem preserves_iff_coherent {t : Tree} (g : Changes K t) :
    Preserves t (linearChangesEquiv t g) ↔ Coherent g := by
  induction t with
  | leaf n => simp [Preserves,Inner,Coherent]
  | node l r hl hr =>
    change (∀ i x y,matrixEquiv (flatten g (parentName (Tree.node l r) i))
      (product (Tree.node l r) i x y) = product (Tree.node l r) i
      (matrixEquiv (flatten g (leftName (Tree.node l r) i)) x)
      (matrixEquiv (flatten g (rightName (Tree.node l r) i)) y)) ↔ _
    constructor
    · intro h
      refine ⟨(hl g.1).mp (fun i x y => h (Sum.inl i) x y),
        (hr g.2.1).mp (fun i x y => h (Sum.inr (Sum.inl i)) x y),?_⟩
      intro x y
      have hh := h (Sum.inr (Sum.inr ())) ((topSpace l).symm x) ((topSpace r).symm y)
      change matrixEquiv g.2.2 (pure (topSpace l ((topSpace l).symm x))
        (topSpace r ((topSpace r).symm y))) =
        pure (topSpace l (matrixEquiv (flatten g.1 (top l)) ((topSpace l).symm x)))
          (topSpace r (matrixEquiv (flatten g.2.1 (top r)) ((topSpace r).symm y))) at hh
      rw [top_flatten (t := l) g.1,top_flatten (t := r) g.2.1] at hh
      simpa only [LinearEquiv.apply_symm_apply,matrixEquiv_apply] using hh
    · rintro ⟨hcl,hcr,hp⟩ i x y
      rcases i with i | (i | i)
      · exact ((hl g.1).mpr hcl) i x y
      · exact ((hr g.2.1).mpr hcr) i x y
      · cases i
        change matrixEquiv g.2.2 (pure (topSpace l x) (topSpace r y)) =
          pure (topSpace l (matrixEquiv (flatten g.1 (top l)) x))
            (topSpace r (matrixEquiv (flatten g.2.1 (top r)) y))
        rw [top_flatten (t := l) g.1,top_flatten (t := r) g.2.1]
        exact hp (topSpace l x) (topSpace r y)

end
section
open Module
universe u
variable {K : Type u} [Field K]
variable {A B W : Type u} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]

def formOfProduct (P : A →ₗ[K] B →ₗ[K] W) : A →ₗ[K] B →ₗ[K] Dual K W →ₗ[K] K where
  toFun x := (Dual.eval K W).comp (P x)
  map_add' := by intros; apply LinearMap.ext; intro y; simp [LinearMap.comp_apply,LinearMap.add_apply]
  map_smul' := by intros; apply LinearMap.ext; intro y; simp [LinearMap.comp_apply,LinearMap.smul_apply]

theorem formOfProduct_preserves_iff [FiniteDimensional K W]
    (P : A →ₗ[K] B →ₗ[K] W) (a : A ≃ₗ[K] A) (b : B ≃ₗ[K] B) (w : W ≃ₗ[K] W) :
    (∀ x y f,formOfProduct P (a x) (b y) (w.symm.dualMap f) = formOfProduct P x y f) ↔
      ∀ x y,w (P x y) = P (a x) (b y) := by
  constructor
  · intro h x y
    have he : w.symm (P (a x) (b y)) = P x y := by
      apply (Module.evalEquiv K W).injective
      apply LinearMap.ext
      intro f
      exact h x y f
    have hh := congrArg w he
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  · intro h x y f
    change f (w.symm (P (a x) (b y))) = f (P x y)
    rw [← h x y,LinearEquiv.symm_apply_apply]

def component (t : Tree) (i : Inner t) := formOfProduct (product (K := K) t i)

theorem component_preserves_iff (t : Tree)
    (g : ∀ i : Nodes t,nodeSpace (K := K) t i ≃ₗ[K] nodeSpace (K := K) t i) :
    (∀ i x y f,component (K := K) t i (g (leftName t i) x) (g (rightName t i) y)
      ((g (parentName t i)).symm.dualMap f) = component (K := K) t i x y f) ↔ Preserves t g := by
  exact forall_congr' (fun i => formOfProduct_preserves_iff (product (K := K) t i) _ _ _)

@[simp] theorem nodes_card (t : Tree) : Fintype.card (Nodes t) = spaceCount t := by
  induction t with
  | leaf n => change Fintype.card Unit = 1; exact Fintype.card_unique
  | node l r hl hr =>
    change Fintype.card (Nodes l ⊕ (Nodes r ⊕ Unit)) = _
    simp only [Fintype.card_sum,Fintype.card_unique,hl,hr,spaceCount]
    omega
@[simp] theorem inner_card (t : Tree) : Fintype.card (Inner t) + 1 = leafCount t := by
  induction t with
  | leaf n => rfl
  | node l r hl hr =>
    change Fintype.card (Inner l ⊕ (Inner r ⊕ Unit)) + 1 = _
    simp only [Fintype.card_sum,Fintype.card_unique,leafCount]
    omega
@[simp] theorem node_dimension (t : Tree) :
    (∑ i : Nodes t,finrank K (nodeSpace (K := K) t i)) = treeTotalDim t := by
  simp only [nodeSpace,Module.finrank_pi,card_idx]
  induction t with
  | leaf n => change (∑ _ : Unit,n) = n; simp
  | node l r hl hr =>
    change (∑ i : Nodes l ⊕ (Nodes r ⊕ Unit),dim (nodeAt (Tree.node l r) i)) = _
    simp only [Fintype.sum_sum_type,nodeAt,Fintype.sum_unique,treeTotalDim]
    omega
end

/- The root tensor form. -/
section
open Matrix
open scoped Kronecker
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
universe u
variable {K : Type u} [Field K] {I J L : Type}
  [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
abbrev rootForm := (I → K) →ₗ[K] (J → K) →ₗ[K] (L → K) →ₗ[K] K

def tensorForm (T : I × (J × L) → K) : rootForm (K := K) (I := I) (J := J) (L := L) where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => ∑ i,∑ j,∑ k,T (i,j,k)*x i*y j*z k
          map_add' := by intros; simp [mul_add,Finset.sum_add_distrib]
          map_smul' := by intros; simp [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; congr 1; ext k; ring }
      map_add' := by intros; apply LinearMap.ext; intro z; simp [add_mul,mul_add,Finset.sum_add_distrib]
      map_smul' := by intros; apply LinearMap.ext; intro z; simp [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; congr 1; ext k; ring }
  map_add' := by intros; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z; simp [add_mul,mul_add,Finset.sum_add_distrib]
  map_smul' := by intros; apply LinearMap.ext; intro y; apply LinearMap.ext; intro z; simp [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; congr 1; ext k; ring

@[simp] theorem tensorForm_apply (T : I × (J × L) → K) (x : I → K) (y : J → K) (z : L → K) :
    tensorForm T x y z = ∑ i,∑ j,∑ k,T (i,j,k)*x i*y j*z k := rfl

@[simp] theorem tensorForm_single (T : I × (J × L) → K) (i : I) (j : J) (k : L) :
    tensorForm T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) = T (i,j,k) := by
  simp [tensorForm_apply,Pi.single_apply,mul_ite]

theorem form_ext (T U : rootForm (K := K) (I := I) (J := J) (L := L))
    (h : ∀ i j k,T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) =
      U (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)) : T = U := by
  ext i j k
  exact h i j k

def transposeGL {A : Type} [Fintype A] [DecidableEq A] (g : (Matrix A A K)ˣ) : (Matrix A A K)ˣ where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul,g.inv_val,Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul,g.val_inv,Matrix.transpose_one]

@[simp] theorem transposeGL_twice {A : Type} [Fintype A] [DecidableEq A] (g : (Matrix A A K)ˣ) :
    transposeGL (transposeGL g) = g := by apply Units.ext; exact Matrix.transpose_transpose _

theorem transformed_single (T : I × (J × L) → K)
    (A : Matrix I I K) (B : Matrix J J K) (C : Matrix L L K) (i : I) (j : J) (k : L) :
    tensorForm T (A.mulVec (Pi.single i 1)) (B.mulVec (Pi.single j 1)) (C.mulVec (Pi.single k 1)) =
      (A.transpose ⊗ₖ (B.transpose ⊗ₖ C.transpose)).mulVec T (i,j,k) := by
  simp only [tensorForm_apply,Matrix.mulVec_single,Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp only [MulOpposite.op_one,one_smul,Matrix.col,Matrix.transpose_apply]
  ring

def transport (T : rootForm (K := K) (I := I) (J := J) (L := L))
    (A : Matrix I I K) (B : Matrix J J K) (C : Matrix L L K) :
    rootForm (K := K) (I := I) (J := J) (L := L) where
  toFun x :=
    { toFun := fun y => (T (A.mulVecLin x) (B.mulVecLin y)).comp C.mulVecLin
      map_add' := by intros; ext; simp [Matrix.mulVec_add]
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp [Matrix.mulVec_add]
  map_smul' := by intros; ext; simp

theorem transport_iff (T U : I × (J × L) → K)
    (A : Matrix I I K) (B : Matrix J J K) (C : Matrix L L K) :
    (∀ x y z,tensorForm T (A.mulVec x) (B.mulVec y) (C.mulVec z) = tensorForm U x y z) ↔
      (A.transpose ⊗ₖ (B.transpose ⊗ₖ C.transpose)).mulVec T = U := by
  constructor
  · intro h
    funext ⟨i,j,k⟩
    have hh := h (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)
    simpa only [transformed_single,tensorForm_single] using hh
  · intro h
    have he : transport (tensorForm T) A B C = tensorForm U := by
      apply form_ext
      intro i j k
      change tensorForm T (A.mulVec (Pi.single i 1)) (B.mulVec (Pi.single j 1))
        (C.mulVec (Pi.single k 1)) = _
      rw [transformed_single,h,tensorForm_single]
    intro x y z
    exact congrArg (fun F : rootForm (K := K) (I := I) (J := J) (L := L) => F x y z) he
end
section
open Matrix
open scoped Kronecker
universe u
variable {K : Type u} [Field K]

def transposeChanges : {t : Tree} → Changes K t → Changes K t
  | Tree.leaf _,g => transposeGL g
  | Tree.node _ _,g => (transposeChanges g.1,transposeChanges g.2.1,transposeGL g.2.2)
@[simp] theorem root_transpose {t : Tree} (g : Changes K t) :
    root (transposeChanges g) = transposeGL (root g) := by cases t <;> rfl
@[simp] theorem transposeChanges_twice {t : Tree} (g : Changes K t) :
    transposeChanges (transposeChanges g) = g := by
  induction t with
  | leaf n => exact transposeGL_twice g
  | node l r hl hr => exact Prod.ext (hl g.1) (Prod.ext (hr g.2.1) (transposeGL_twice g.2.2))

theorem coherent_transpose {t : Tree} (g : Changes K t) (h : Coherent g) :
    Coherent (transposeChanges g) := by
  induction t with
  | leaf n => trivial
  | node l r hl hr =>
    refine ⟨hl g.1 h.1,hr g.2.1 h.2.1,?_⟩
    apply (preserves_product_iff _ _ _).mpr
    change g.2.2.val.transpose = (root (transposeChanges g.1)).val ⊗ₖ (root (transposeChanges g.2.1)).val
    rw [root_transpose,root_transpose]
    change g.2.2.val.transpose = (root g.1).val.transpose ⊗ₖ (root g.2.1).val.transpose
    rw [(preserves_product_iff _ _ _).mp h.2.2]
    rfl

/-- The all-positive root form has exactly the source tensor action after transposition. -/
theorem root_form_transport (a b c : Tree) (T U : Idx a × (Idx b × Idx c) → K)
    (ga : Changes K a) (gb : Changes K b) (gc : Changes K c) :
    (∀ x y z,tensorForm T (matrixEquiv (root ga) x) (matrixEquiv (root gb) y)
      (matrixEquiv (root gc) z) = tensorForm U x y z) ↔
      rootAction (root (transposeChanges ga)) (root (transposeChanges gb))
        (root (transposeChanges gc)) T = U := by
  simpa only [matrixEquiv_apply,root_transpose,rootAction,transposeGL] using
    transport_iff T U (root ga).val (root gb).val (root gc).val
end
/- Encoding product trees as a mixed system. -/
section
set_option backward.isDefEq.respectTransparency false
open Module
universe u
variable {K : Type u} [Field K]
variable (a b c : Tree)
abbrev Names := Nodes a ⊕ (Nodes b ⊕ Nodes c)
abbrev Comps := Inner a ⊕ (Inner b ⊕ (Inner c ⊕ Unit))
def treeAt : Names a b c → Tree
  | Sum.inl i => nodeAt a i
  | Sum.inr (Sum.inl i) => nodeAt b i
  | Sum.inr (Sum.inr i) => nodeAt c i
abbrev V (i : Names a b c) := Idx (treeAt a b c i) → K

def treeSp : Comps a b c → Names a b c × Bool
  | Sum.inl i => (Sum.inl (leftName a i),false)
  | Sum.inr (Sum.inl i) => (Sum.inr (Sum.inl (leftName b i)),false)
  | Sum.inr (Sum.inr (Sum.inl i)) => (Sum.inr (Sum.inr (leftName c i)),false)
  | Sum.inr (Sum.inr (Sum.inr _)) => (Sum.inl (top a),false)
def treeSq : Comps a b c → Names a b c × Bool
  | Sum.inl i => (Sum.inl (rightName a i),false)
  | Sum.inr (Sum.inl i) => (Sum.inr (Sum.inl (rightName b i)),false)
  | Sum.inr (Sum.inr (Sum.inl i)) => (Sum.inr (Sum.inr (rightName c i)),false)
  | Sum.inr (Sum.inr (Sum.inr _)) => (Sum.inr (Sum.inl (top b)),false)
def treeSr : Comps a b c → Names a b c × Bool
  | Sum.inl i => (Sum.inl (parentName a i),true)
  | Sum.inr (Sum.inl i) => (Sum.inr (Sum.inl (parentName b i)),true)
  | Sum.inr (Sum.inr (Sum.inl i)) => (Sum.inr (Sum.inr (parentName c i)),true)
  | Sum.inr (Sum.inr (Sum.inr _)) => (Sum.inr (Sum.inr (top c)),false)

def rootComponent (T : Idx a × (Idx b × Idx c) → K) :=
  pullForm (tensorForm T) (topSpace a).toLinearMap (topSpace b).toLinearMap (topSpace c).toLinearMap

def system (T : Idx a × (Idx b × Idx c) → K) :
    Components (K := K) (V := V (K := K) a b c) (treeSp a b c) (treeSq a b c) (treeSr a b c)
  | Sum.inl i => component a i
  | Sum.inr (Sum.inl i) => component b i
  | Sum.inr (Sum.inr (Sum.inl i)) => component c i
  | Sum.inr (Sum.inr (Sum.inr _)) => rootComponent a b c T

def join (ga : Changes K a) (gb : Changes K b) (gc : Changes K c) :
    ∀ i,V (K := K) a b c i ≃ₗ[K] V (K := K) a b c i
  | Sum.inl i => linearChangesEquiv a ga i
  | Sum.inr (Sum.inl i) => linearChangesEquiv b gb i
  | Sum.inr (Sum.inr i) => linearChangesEquiv c gc i

theorem join_surjective (G : ∀ i,V (K := K) a b c i ≃ₗ[K] V (K := K) a b c i) :
    ∃ ga gb gc,join a b c ga gb gc = G := by
  refine ⟨(linearChangesEquiv a).symm (fun i => G (Sum.inl i)),
    (linearChangesEquiv b).symm (fun i => G (Sum.inr (Sum.inl i))),
    (linearChangesEquiv c).symm (fun i => G (Sum.inr (Sum.inr i))),?_⟩
  funext i
  rcases i with i | (i | i)
  · exact congrFun ((linearChangesEquiv a).apply_symm_apply _) i
  · exact congrFun ((linearChangesEquiv b).apply_symm_apply _) i
  · exact congrFun ((linearChangesEquiv c).apply_symm_apply _) i

def Transports (T U : Idx a × (Idx b × Idx c) → K)
    (G : ∀ i,V (K := K) a b c i ≃ₗ[K] V (K := K) a b c i) : Prop :=
  ∀ i x y z,system a b c T i (viewAction (G (treeSp a b c i).1) (treeSp a b c i).2 x)
    (viewAction (G (treeSq a b c i).1) (treeSq a b c i).2 y)
    (viewAction (G (treeSr a b c i).1) (treeSr a b c i).2 z) = system a b c U i x y z

theorem transports_join_iff (T U : Idx a × (Idx b × Idx c) → K)
    (ga : Changes K a) (gb : Changes K b) (gc : Changes K c) :
    Transports a b c T U (join a b c ga gb gc) ↔
      Coherent ga ∧ Coherent gb ∧ Coherent gc ∧
        rootAction (root (transposeChanges ga)) (root (transposeChanges gb))
          (root (transposeChanges gc)) T = U := by
  constructor
  · intro h
    refine ⟨(preserves_iff_coherent ga).mp ((component_preserves_iff a _).mp
      (fun i x y z => h (Sum.inl i) x y z)),
      (preserves_iff_coherent gb).mp ((component_preserves_iff b _).mp
      (fun i x y z => h (Sum.inr (Sum.inl i)) x y z)),
      (preserves_iff_coherent gc).mp ((component_preserves_iff c _).mp
      (fun i x y z => h (Sum.inr (Sum.inr (Sum.inl i))) x y z)),?_⟩
    apply (root_form_transport a b c T U ga gb gc).mp
    intro x y z
    have hh := h (Sum.inr (Sum.inr (Sum.inr ())))
      ((topSpace a).symm x) ((topSpace b).symm y) ((topSpace c).symm z)
    change tensorForm T (topSpace a (matrixEquiv (flatten ga (top a)) ((topSpace a).symm x)))
      (topSpace b (matrixEquiv (flatten gb (top b)) ((topSpace b).symm y)))
      (topSpace c (matrixEquiv (flatten gc (top c)) ((topSpace c).symm z))) =
      tensorForm U (topSpace a ((topSpace a).symm x)) (topSpace b ((topSpace b).symm y))
        (topSpace c ((topSpace c).symm z)) at hh
    rw [top_flatten (t := a) ga,top_flatten (t := b) gb,top_flatten (t := c) gc] at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh
  · rintro ⟨ha,hb,hc,ht⟩ i x y z
    rcases i with i | (i | (i | i))
    · exact ((component_preserves_iff a _).mpr ((preserves_iff_coherent ga).mpr ha)) i x y z
    · exact ((component_preserves_iff b _).mpr ((preserves_iff_coherent gb).mpr hb)) i x y z
    · exact ((component_preserves_iff c _).mpr ((preserves_iff_coherent gc).mpr hc)) i x y z
    · cases i
      change tensorForm T (topSpace a (matrixEquiv (flatten ga (top a)) x))
        (topSpace b (matrixEquiv (flatten gb (top b)) y))
        (topSpace c (matrixEquiv (flatten gc (top c)) z)) =
        tensorForm U (topSpace a x) (topSpace b y) (topSpace c z)
      rw [top_flatten (t := a) ga,top_flatten (t := b) gb,top_flatten (t := c) gc]
      exact (root_form_transport a b c T U ga gb gc).mpr ht (topSpace a x) (topSpace b y) (topSpace c z)

theorem leafIso_iff_mixed (T U : Idx a × (Idx b × Idx c) → K) :
    LeafIso a b c T U ↔ MixedIso (treeSp a b c) (treeSq a b c) (treeSr a b c)
      (system a b c T) (system a b c U) := by
  rw [leafIso_iff_systemIso]
  constructor
  · rintro ⟨ga,gb,gc,ha,hb,hc,ht⟩
    refine ⟨join a b c (transposeChanges ga) (transposeChanges gb) (transposeChanges gc),?_⟩
    apply (transports_join_iff a b c T U _ _ _).mpr
    exact ⟨coherent_transpose ga ha,coherent_transpose gb hb,coherent_transpose gc hc,
      by simpa only [transposeChanges_twice] using ht⟩
  · rintro ⟨G,hG⟩
    obtain ⟨ga,gb,gc,rfl⟩ := join_surjective a b c G
    obtain ⟨ha,hb,hc,ht⟩ := (transports_join_iff a b c T U ga gb gc).mp hG
    exact ⟨transposeChanges ga,transposeChanges gb,transposeChanges gc,
      coherent_transpose ga ha,coherent_transpose gb hb,coherent_transpose gc hc,ht⟩
end
section

def productWeight (t : Tree) (i : Inner t) : ℕ :=
  dim (nodeAt t (leftName t i)) + dim (nodeAt t (rightName t i)) + dim (nodeAt t (parentName t i))
theorem product_incidence_dimension (t : Tree) :
    (∑ i : Inner t,productWeight t i) = productOccurrenceDim t := by
  induction t with
  | leaf n =>
    change (∑ i : Empty,productWeight (Tree.leaf n) i) = 0
    exact Finset.sum_eq_zero (fun i _ => nomatch i)
  | node l r hl hr =>
    change (∑ i : Inner l ⊕ (Inner r ⊕ Unit),_) = _
    simp only [Fintype.sum_sum_type,productWeight,leftName,rightName,parentName,nodeAt,
      Fintype.sum_unique,nodeAt_top,productOccurrenceDim]
    simp only [productWeight] at hl hr
    omega
end

section
open Module
universe u
variable {K : Type u} [Field K]
variable (a b c : Tree)

theorem names_count : Fintype.card (Names a b c) = systemSpaces a b c := by
  simp only [Names,Fintype.card_sum,nodes_card,systemSpaces]
  omega

theorem components_count : Fintype.card (Comps a b c) = systemComponents a b c := by
  have ha := inner_card a
  have hb := inner_card b
  have hc := inner_card c
  simp only [Comps,Fintype.card_sum,Fintype.card_unique,systemComponents]
  omega

theorem treeNamed_dimension :
    (∑ i,finrank K (V (K := K) a b c i)) = systemDim a b c := by
  have ha := node_dimension (K := K) a
  have hb := node_dimension (K := K) b
  have hc := node_dimension (K := K) c
  change (∑ i : Nodes a ⊕ (Nodes b ⊕ Nodes c),finrank K (V (K := K) a b c i)) = _
  simp only [Fintype.sum_sum_type]
  change (∑ i,finrank K (nodeSpace (K := K) a i)) +
    ((∑ i,finrank K (nodeSpace (K := K) b i)) + (∑ i,finrank K (nodeSpace (K := K) c i))) = _
  rw [ha,hb,hc]
  unfold systemDim
  omega

theorem treeOccurrence_dimension :
    (∑ i,finrank K (V (K := K) a b c (treeSp a b c i).1)) +
    (∑ i,finrank K (V (K := K) a b c (treeSq a b c i).1)) +
    (∑ i,finrank K (V (K := K) a b c (treeSr a b c i).1)) = systemOccurrenceDim a b c := by
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  simp only [V,Module.finrank_pi,card_idx]
  change (∑ i : Inner a ⊕ (Inner b ⊕ (Inner c ⊕ Unit)),_) = _
  simp only [Fintype.sum_sum_type,treeSp,treeSq,treeSr,treeAt,Fintype.sum_unique,nodeAt_top]
  change (∑ i,productWeight a i) + ((∑ i,productWeight b i) + ((∑ i,productWeight c i) + (dim a + dim b + dim c))) = _
  rw [product_incidence_dimension,product_incidence_dimension,product_incidence_dimension]
  unfold systemOccurrenceDim
  omega
end
/- Ordinary tensor reduction. -/
section
set_option backward.isDefEq.respectTransparency false
open Module
universe u
variable {K : Type u} [Field K]
variable (a b c : Tree)

def ordinary (T : Idx a × (Idx b × Idx c) → K) :=
  mixedOrdinary (treeSp a b c) (treeSq a b c) (treeSr a b c) (system a b c T)
def OutputIso (T U : Idx a × (Idx b × Idx c) → K) : Prop :=
  mixedOutputIso (treeSp a b c) (treeSq a b c) (treeSr a b c) (system a b c T) (system a b c U)
def outputDim (T : Idx a × (Idx b × Idx c) → K) : ℕ :=
  mixedOutputDim (treeSp a b c) (treeSq a b c) (treeSr a b c) (system a b c T)

theorem ordinary_correct (T U : Idx a × (Idx b × Idx c) → K) :
    LeafIso a b c T U ↔ OutputIso a b c T U :=
  (leafIso_iff_mixed a b c T U).trans
    (mixed_iff_ordinary (treeSp a b c) (treeSq a b c) (treeSr a b c) (system a b c T) (system a b c U))

theorem ordinary_size (T : Idx a × (Idx b × Idx c) → K) :
    outputDim a b c T ≤ linkFactor 5 4 5 4 *
      (9*(4*systemSpaces a b c + 3*systemComponents a b c + 1) +
      40*systemDim a b c + 12*systemOccurrenceDim a b c + 47) := by
  have h := mixedOrdinary_size (treeSp a b c) (treeSq a b c) (treeSr a b c) (system a b c T)
  have hD : baseDim (K := K) (V := V (K := K) a b c) = systemDim a b c :=
    treeNamed_dimension a b c
  have hO : incidenceDim (K := K) (V := V (K := K) a b c)
      (treeSp a b c) (treeSq a b c) (treeSr a b c) = systemOccurrenceDim a b c := treeOccurrence_dimension a b c
  rw [names_count,components_count,hD,hO] at h
  exact h

def absoluteConstant : ℕ := 1200 * linkFactor 5 4 5 4

theorem balanced_bound {n d f₁ f₂ f₃ : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ d)
    (l₁ l₂ l₃ : List ℕ)
    (hf₁ : f₁ ≤ n) (hf₂ : f₂ ≤ n) (hf₃ : f₃ ≤ n)
    (hs₁ : ∀ m ∈ l₁,m ≤ n) (hs₂ : ∀ m ∈ l₂,m ≤ n) (hs₃ : ∀ m ∈ l₃,m ≤ n)
    (hlen₁ : l₁.length+1 = d/3) (hlen₂ : l₂.length+1 = (d+1)/3)
    (hlen₃ : l₃.length+1 = (d+2)/3)
    (T : Idx (prefixTree f₁ l₁) × (Idx (prefixTree f₂ l₂) × Idx (prefixTree f₃ l₃)) → K) :
    outputDim (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) T ≤
      absoluteConstant * n^((d+2)/3) := by
  have h₁ := prefix_bound_at hn hf₁ l₁ hs₁ (by omega : l₁.length+1 ≤ (d+2)/3)
  have h₂ := prefix_bound_at hn hf₂ l₂ hs₂ (by omega : l₂.length+1 ≤ (d+2)/3)
  have h₃ := prefix_bound_at hn hf₃ l₃ hs₃ (by omega : l₃.length+1 ≤ (d+2)/3)
  have hD : systemDim (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) ≤
      9*n^((d+2)/3) := by unfold systemDim; omega
  have hO := system_occurrence_bound (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃)
  have hc := exact_counts (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃)
  dsimp only at hc
  rw [prefix_leaves, prefix_leaves, prefix_leaves, hlen₁, hlen₂, hlen₃] at hc
  have hk : (d+2)/3 ≤ n^((d+2)/3) := (Nat.lt_pow_self (by omega : 1 < n)).le
  have hp : 1 ≤ n^((d+2)/3) := Nat.one_le_pow _ _ (by omega)
  have hdN : d ≤ 3*n^((d+2)/3) := by omega
  have hb : 9*(4*systemSpaces (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) +
      3*systemComponents (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) + 1) +
      40*systemDim (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) +
      12*systemOccurrenceDim (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) + 47 ≤
      1200*n^((d+2)/3) := by omega
  calc
    _ ≤ linkFactor 5 4 5 4 * _ := ordinary_size _ _ _ T
    _ ≤ linkFactor 5 4 5 4 * (1200*n^((d+2)/3)) := Nat.mul_le_mul_left _ hb
    _ = _ := by unfold absoluteConstant; ac_rfl

/-- Actual unconstrained three-tensor compilation: exact isomorphism equivalence
and an absolute-constant balanced dimension bound, over every field. -/
theorem balanced_ordinary_reduction {n d f₁ f₂ f₃ : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ d)
    (l₁ l₂ l₃ : List ℕ)
    (hf₁ : f₁ ≤ n) (hf₂ : f₂ ≤ n) (hf₃ : f₃ ≤ n)
    (hs₁ : ∀ m ∈ l₁,m ≤ n) (hs₂ : ∀ m ∈ l₂,m ≤ n) (hs₃ : ∀ m ∈ l₃,m ≤ n)
    (hlen₁ : l₁.length+1 = d/3) (hlen₂ : l₂.length+1 = (d+1)/3)
    (hlen₃ : l₃.length+1 = (d+2)/3)
    (T U : Idx (prefixTree f₁ l₁) × (Idx (prefixTree f₂ l₂) × Idx (prefixTree f₃ l₃)) → K) :
    (LeafIso (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) T U ↔
      OutputIso (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) T U) ∧
    outputDim (prefixTree f₁ l₁) (prefixTree f₂ l₂) (prefixTree f₃ l₃) T ≤
      absoluteConstant*n^((d+2)/3) :=
  ⟨ordinary_correct _ _ _ T U,
    balanced_bound hn hd l₁ l₂ l₃ hf₁ hf₂ hf₃ hs₁ hs₂ hs₃ hlen₁ hlen₂ hlen₃ T⟩
end
section

theorem size_arithmetic (d P m c D O : ℕ)
    (hm : m ≤ 2*d) (hc : c ≤ d) (hD : D ≤ m*P) (hO : O ≤ 2*D) :
    9*(4*m+3*c+1)+40*D+12*O+47 ≤ 300*((d+1)*(P+1)) := by
  have hDP : D ≤ 2*d*P := hD.trans (Nat.mul_le_mul_right P hm)
  nlinarith

end
section
universe u
variable {K : Type u} [Field K]

/-- A bound polynomial in the actual dense input size and number of factors.
This is a size theorem, not a machine-running-time assertion. -/
theorem actual_dense_polynomial_size (a b c : Tree)
    (ha : Positive a) (hb : Positive b) (hc : Positive c)
    (T : Idx a × (Idx b × Idx c) → K) :
    outputDim a b c T ≤
      (300 * linkFactor 5 4 5 4) *
        ((leafCount a + leafCount b + leafCount c + 1) * (dim a * dim b * dim c + 1)) := by
  have hD := actual_input_size_bound a b c ha hb hc
  have hO := system_occurrence_bound a b c
  have hn := exact_counts a b c
  dsimp only at hn
  have hm : systemSpaces a b c ≤ 2*(leafCount a + leafCount b + leafCount c) := by omega
  have hmC : systemComponents a b c ≤ leafCount a + leafCount b + leafCount c := by omega
  have hbound : 9*(4*systemSpaces a b c + 3*systemComponents a b c + 1) +
      40*systemDim a b c + 12*systemOccurrenceDim a b c + 47 ≤
      300*((leafCount a + leafCount b + leafCount c + 1)*(dim a*dim b*dim c+1)) :=
    size_arithmetic _ _ _ _ _ _ hm hmC hD hO
  calc
    _ ≤ linkFactor 5 4 5 4 * _ := ordinary_size a b c T
    _ ≤ linkFactor 5 4 5 4 *
      (300*((leafCount a + leafCount b + leafCount c + 1)*(dim a*dim b*dim c+1))) := Nat.mul_le_mul_left _ hbound
    _ = _ := by ac_rfl
end
section

def leafDimensions : Tree → List ℕ
  | Tree.leaf n => [n]
  | Tree.node l r => leafDimensions l ++ leafDimensions r

@[simp] theorem prefix_leafDimensions (f : ℕ) (ns : List ℕ) :
    leafDimensions (prefixTree f ns) = f :: ns.reverse := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [prefixTree,leafDimensions,ih]

theorem split_three_balanced (L : List ℕ) :
    ∃ A B C : List ℕ,L = A ++ (B ++ C) ∧
      A.length = L.length/3 ∧ B.length = (L.length+1)/3 ∧ C.length = (L.length+2)/3 := by
  let A := L.take (L.length/3)
  let R := L.drop (L.length/3)
  let B := R.take ((L.length+1)/3)
  let C := R.drop ((L.length+1)/3)
  refine ⟨A,B,C,?_,?_,?_,?_⟩
  · dsimp [A,B,C,R]
    rw [List.take_append_drop,List.take_append_drop]
  · simp only [A,List.length_take]; omega
  · simp only [B,R,List.length_take,List.length_drop]; omega
  · simp only [C,R,List.length_drop]; omega

theorem nonempty_prefix_list (L : List ℕ) (h : 0 < L.length) :
    ∃ (f : ℕ) (ns : List ℕ),L = f :: ns.reverse := by
  cases L with
  | nil => simp at h
  | cons f ns => exact ⟨f,ns.reverse,by simp⟩

/-- Every dimension list of order at least three has a balanced prefix-tree
presentation, preserving the order of its original factors. -/
theorem balanced_shape_lists (L : List ℕ) (h : 3 ≤ L.length) :
    ∃ (f₁ : ℕ) (l₁ : List ℕ) (f₂ : ℕ) (l₂ : List ℕ) (f₃ : ℕ) (l₃ : List ℕ),
      L = (f₁ :: l₁.reverse) ++ ((f₂ :: l₂.reverse) ++ (f₃ :: l₃.reverse)) ∧
      l₁.length+1 = L.length/3 ∧ l₂.length+1 = (L.length+1)/3 ∧
      l₃.length+1 = (L.length+2)/3 := by
  obtain ⟨A,B,C,hL,hA,hB,hC⟩ := split_three_balanced L
  obtain ⟨f₁,l₁,rfl⟩ := nonempty_prefix_list A (by omega)
  obtain ⟨f₂,l₂,rfl⟩ := nonempty_prefix_list B (by omega)
  obtain ⟨f₃,l₃,rfl⟩ := nonempty_prefix_list C (by omega)
  refine ⟨f₁,l₁,f₂,l₂,f₃,l₃,hL,?_,?_,?_⟩
  · simpa only [List.length_cons,List.length_reverse] using hA
  · simpa only [List.length_cons,List.length_reverse] using hB
  · simpa only [List.length_cons,List.length_reverse] using hC

end
section
universe u
variable {K : Type u} [Field K]

/-- Arbitrary ordered dimension lists, with the balanced grouping constructed
inside the theorem. Coordinates are nested products of exactly these factors. -/
theorem arbitrary_shape_ordinary_reduction {n : ℕ} (hn : 2 ≤ n)
    (L : List ℕ) (hd : 3 ≤ L.length) (hbound : ∀ m ∈ L,m ≤ n) :
    ∃ a b c : Tree,
      leafDimensions a ++ (leafDimensions b ++ leafDimensions c) = L ∧
      ∀ T U : Idx a × (Idx b × Idx c) → K,
        (LeafIso a b c T U ↔ OutputIso a b c T U) ∧
        outputDim a b c T ≤ absoluteConstant*n^((L.length+2)/3) := by
  obtain ⟨f₁,l₁,f₂,l₂,f₃,l₃,hL,h₁,h₂,h₃⟩ := balanced_shape_lists L hd
  rw [hL] at hbound
  simp only [List.forall_mem_append, List.forall_mem_cons, List.mem_reverse] at hbound
  rcases hbound with ⟨⟨hf₁, hs₁⟩, ⟨hf₂, hs₂⟩, hf₃, hs₃⟩
  refine ⟨prefixTree f₁ l₁, prefixTree f₂ l₂, prefixTree f₃ l₃, ?_, ?_⟩
  · simpa only [prefix_leafDimensions] using hL.symm
  · intro T U
    exact balanced_ordinary_reduction hn hd l₁ l₂ l₃
      hf₁ hf₂ hf₃ hs₁ hs₂ hs₃ h₁ h₂ h₃ T U

end

end TensorOrderReduction

#print axioms TensorOrderReduction.ordinary_correct
#print axioms TensorOrderReduction.balanced_ordinary_reduction
#print axioms TensorOrderReduction.actual_dense_polynomial_size
#print axioms TensorOrderReduction.arbitrary_shape_ordinary_reduction
