import Mathproof.MinimumGenerationResidual
import Mathproof.MinimumGenerationRadical
import Mathproof.MinimumGenerationTowerReplay
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Choose

namespace Mathproof.MinimumGenerationResidual

open Subgroup
open scoped commutatorElement

set_option linter.style.haveILetI false

variable {G : Type*} [Group G]

/-- Automorphisms permute the kernels of epimorphisms to perfect simple groups. -/
instance semisimpleResidual_characteristic : (semisimpleResidual G).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro e x hx
  change e x ∈ semisimpleResidual G
  apply (mem_semisimpleResidual_iff _).mpr
  intro K
  let f := (QuotientGroup.mk' K.1).comp e.toMonoidHom
  have hs : Function.Surjective f := (QuotientGroup.mk'_surjective K.1).comp e.surjective
  have hk := semisimpleResidual_le_ker_of_surj_perfect_simple f hs hx
  exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hk)

theorem isPerfect_minimalNormal [Finite G] (hR : solvableRadical G = ⊥)
    {N : Subgroup G} (hN : IsMinimalNormal N) : Group.IsPerfect N := by
  letI : N.Normal := hN.1.1
  let D := commutator N
  letI : D.Characteristic := by change (commutator N).Characteristic; rw [commutator_def]; infer_instance
  letI : (D.map N.subtype).Normal :=
    Mathproof.MinimumGeneration.normal_map_subtype_of_characteristic N D
  have hne : D.map N.subtype ≠ ⊥ := by
    intro hz
    have hD := (Subgroup.map_eq_bot_iff_of_injective D N.subtype_injective).mp hz
    letI : IsMulCommutative N := (commutator_eq_bot_iff N).mp hD
    letI : Group.IsSolvable N := Group.isSolvable_of_comm mul_comm'
    exact hN.1.2 (le_bot_iff.mp ((le_solvableRadical (H := N)).trans hR.le))
  have hle : D.map N.subtype ≤ N := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have he := le_antisymm hle (hN.2 ⟨inferInstance, hne⟩ hle)
  apply Group.isPerfect_def.mpr
  change D = ⊤
  apply (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
  rw [he, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isPerfectSimpleProduct_minimalNormal [Finite G] (hR : solvableRadical G = ⊥)
    {N : Subgroup G} (hN : IsMinimalNormal N) : IsPerfectSimpleProduct N := by
  letI : N.Normal := hN.1.1
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.1.2
  letI : Group.IsPerfect N := isPerfect_minimalNormal hR hN
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun K : Subgroup N => K.Normal ∧ K ≠ ⊤) (a := ⊥) ⟨inferInstance, bot_ne_top⟩
  letI : M.Normal := hM.1.1
  let K : PerfectSimpleKernel N := ⟨M, hM, inferInstance, inferInstance⟩
  let R := semisimpleResidual N
  letI : (R.map N.subtype).Normal :=
    Mathproof.MinimumGeneration.normal_map_subtype_of_characteristic N R
  have hle : R.map N.subtype ≤ N := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hne : R.map N.subtype ≠ N := by
    intro he
    have hRt : R = ⊤ := (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
      (he.trans (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]))
    have hRM : R ≤ M := fun x hx => (mem_semisimpleResidual_iff x).mp hx K
    exact hM.1.2 (le_antisymm le_top (hRt ▸ hRM))
  have hb : R.map N.subtype = ⊥ := by
    by_contra hnb
    exact hne (le_antisymm hle (hN.2 ⟨inferInstance, hnb⟩ hle))
  have hRb : R = ⊥ := (Subgroup.map_eq_bot_iff_of_injective R N.subtype_injective).mp hb
  have h := (quotient_isPerfectSimpleProduct_iff (G := N) ⊥).mpr hRb.le
  exact isPerfectSimpleProduct_of_surjective QuotientGroup.quotientBot.toMonoidHom
    QuotientGroup.quotientBot.surjective h


section SocleProduct

universe u

theorem pi_isPerfectSimpleProduct {J : Type u} [Finite J] (F : J → Type u)
    [∀ j, Group (F j)] (hf : ∀ j, IsPerfectSimpleProduct (F j)) :
    IsPerfectSimpleProduct ((j : J) → F j) := by
  classical
  unfold IsPerfectSimpleProduct at hf
  choose I hI T hT hAll using hf
  letI : ∀ j, Finite (I j) := hI
  letI : ∀ j i, Group (T j i) := hT
  let e (j : J) : F j ≃* ((i : I j) → T j i) := (hAll j).2.2.some
  let E : ((j : J) → F j) ≃* ((p : Sigma I) → T p.1 p.2) :=
    { toFun := fun x p => e p.1 (x p.1) p.2
      invFun := fun y j => (e j).symm (fun i => y ⟨j, i⟩)
      left_inv := by intro x; funext j; exact (e j).symm_apply_apply (x j)
      right_inv := by intro y; funext p; exact congrFun ((e p.1).apply_symm_apply _) p.2
      map_mul' := by intro x y; funext p; exact congrFun ((e p.1).map_mul _ _) p.2 }
  exact ⟨Sigma I, inferInstance, fun p => T p.1 p.2, inferInstance,
    fun p => (hAll p.1).1 p.2, fun p => (hAll p.1).2.1 p.2, ⟨E⟩⟩

theorem isPerfectSimpleProduct_socle {G : Type u} [Group G] [Finite G]
    (hR : solvableRadical G = ⊥) : IsPerfectSimpleProduct (socle G) := by
  classical
  let J := {N : Subgroup G // IsMinimalNormal N}
  letI : Fintype J := Fintype.ofFinite _
  let N : J → Subgroup G := fun j => j.1
  have hc : Pairwise fun i j : J => ∀ x y : G, x ∈ N i → y ∈ N j → Commute x y := by
    intro i j hij x y hx hy
    letI : (N i).Normal := i.2.1.1
    letI : (N j).Normal := j.2.1.1
    have hd : Disjoint (N i) (N j) := by
      rw [disjoint_iff_inf_le]
      by_contra h
      have hnb : N i ⊓ N j ≠ ⊥ := fun he => h he.le
      have hNi : N i ≤ N i ⊓ N j := i.2.2 ⟨inferInstance, hnb⟩ inf_le_left
      have hNj : N j ≤ N i ⊓ N j := j.2.2 ⟨inferInstance, hnb⟩ inf_le_right
      exact hij (Subtype.ext (le_antisymm (hNi.trans inf_le_right) (hNj.trans inf_le_left)))
    exact Subgroup.commute_of_normal_of_disjoint (N i) (N j)
      inferInstance inferInstance hd x y hx hy
  let p := Subgroup.noncommPiCoprod (H := N) hc
  have hp : p.range = socle G := by
    rw [Subgroup.noncommPiCoprod_range, socle, sSup_eq_iSup']
    rfl
  let f := (MulEquiv.subgroupCongr hp).toMonoidHom.comp p.rangeRestrict
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr hp).surjective.comp
    p.rangeRestrict_surjective
  apply isPerfectSimpleProduct_of_surjective f hf
  apply pi_isPerfectSimpleProduct (fun j : J => N j)
  intro j
  exact isPerfectSimpleProduct_minimalNormal hR j.2

end SocleProduct


section ProductComplements

universe u

private theorem pi_normal_centralizer {I : Type u} [Finite I] [DecidableEq I]
    (S : I → Type u) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    [∀ i, Group.IsPerfect (S i)] (M : Subgroup ((i : I) → S i)) [M.Normal] :
    M ⊓ centralizer (M : Set _) = ⊥ ∧ M ⊔ centralizer (M : Set _) = ⊤ := by
  classical
  let A (i : I) := M.comap (MonoidHom.mulSingle S i)
  have hCoords : ∀ x : ((i : I) → S i), x ∈ M ↔ ∀ i, x i ∈ A i := by
    intro x
    conv_lhs => rw [normal_subgroup_pi_eq_pi S M]
    simp [Subgroup.mem_pi, A]
  have hSimple (i : I) : A i = ⊥ ∨ A i = ⊤ := by
    letI : (A i).Normal := inferInstanceAs ((M.comap (MonoidHom.mulSingle S i)).Normal)
    exact (inferInstance : (A i).Normal).eq_bot_or_eq_top
  constructor
  · apply le_bot_iff.mp
    intro x hx
    rw [mem_bot]
    funext i
    change x i = 1
    rcases hSimple i with h0 | h1
    · simpa only [h0, mem_bot] using (hCoords x).mp hx.1 i
    · have hc : x i ∈ center (S i) := by
        rw [Subgroup.mem_center_iff]
        intro a
        have ha : (Pi.mulSingle i a : (j : I) → S j) ∈ M := by
          change a ∈ A i
          rw [h1]
          exact Subgroup.mem_top _
        have he := (Subgroup.mem_centralizer_iff.mp hx.2) _ ha
        simpa using congrFun he i
      simpa only [center_eq_bot_of_simple_perfect, mem_bot] using hc
  · apply top_unique
    intro x _
    let a : (i : I) → S i := fun i => if A i = ⊤ then x i else 1
    let b : (i : I) → S i := fun i => if A i = ⊤ then 1 else x i
    have ha : a ∈ M := (hCoords a).mpr fun i => by
      by_cases hi : A i = ⊤
      · simp [a, hi]
      · simp [a, hi]
    have hb : b ∈ centralizer (M : Set _) := by
      rw [mem_centralizer_iff]
      intro y hy
      funext i
      change y i * b i = b i * y i
      by_cases hi : A i = ⊤
      · simp [b, hi]
      · have h0 : A i = ⊥ := (hSimple i).resolve_right hi
        have he : y i = 1 := by simpa only [h0, mem_bot] using (hCoords y).mp hy i
        simp [he]
    have hmul : a * b = x := by
      funext i
      change a i * b i = x i
      by_cases hi : A i = ⊤ <;> simp [a, b, hi]
    let C : Subgroup ((i : I) → S i) := centralizer (M : Set _)
    let B : Subgroup ((i : I) → S i) := M ⊔ C
    have hl : M ≤ B := le_sup_left
    have hr : C ≤ B := le_sup_right
    have ha' : a ∈ B := hl ha
    have hb' : b ∈ B := hr hb
    have hab : a * b ∈ B := B.mul_mem ha' hb'
    rw [hmul] at hab
    exact hab

/-- A normal subgroup in a product of perfect simple groups has its centralizer as a complement. -/
theorem normal_centralizer_complement_of_perfectSimpleProduct {G : Type u} [Group G]
    (hG : IsPerfectSimpleProduct G) (U : Subgroup G) [U.Normal] :
    U ⊓ centralizer (U : Set G) = ⊥ ∧ U ⊔ centralizer (U : Set G) = ⊤ := by
  classical
  obtain ⟨I, hI, S, hS, hSimple, hPerfect, ⟨e⟩⟩ := hG
  letI : Finite I := hI
  letI : ∀ i, Group (S i) := hS
  letI : ∀ i, IsSimpleGroup (S i) := hSimple
  letI : ∀ i, Group.IsPerfect (S i) := hPerfect
  let f := e.symm.toMonoidHom
  let M := U.comap f
  letI : M.Normal := inferInstanceAs ((U.comap f).Normal)
  have hC : centralizer (M : Set _) = (centralizer (U : Set G)).comap f := by
    ext x
    change x ∈ centralizer (M : Set _) ↔ e.symm x ∈ centralizer (U : Set G)
    simp only [mem_centralizer_iff]
    constructor
    · intro hx y hy
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hx (e y) (by change e.symm (e y) ∈ U; simpa)
    · intro hx y hy
      apply e.symm.injective
      simp only [map_mul]
      exact hx (e.symm y) hy
  obtain ⟨hd, hs⟩ := pi_normal_centralizer S M
  rw [hC] at hd hs
  change U.comap f ⊓ _ = ⊥ at hd
  change U.comap f ⊔ _ = ⊤ at hs
  rw [← comap_inf] at hd
  rw [Subgroup.comap_sup_eq f U (centralizer (U : Set G)) e.symm.surjective] at hs
  constructor
  · apply (Subgroup.comap_injective (f := f) e.symm.surjective)
    rw [hd, MonoidHom.comap_bot]
    exact ((MonoidHom.ker_eq_bot_iff f).mpr e.symm.injective).symm
  · apply (Subgroup.comap_injective (f := f) e.symm.surjective)
    rw [hs, Subgroup.comap_top]

/-- Every semisimple normal subgroup of a radical-free finite group lies in the socle. -/
theorem le_socle_of_perfectSimpleProduct {G : Type u} [Group G] [Finite G]
    (hR : solvableRadical G = ⊥) (N : Subgroup G) [N.Normal]
    (hN : IsPerfectSimpleProduct N) : N ≤ socle G := by
  let S := socle G
  let U := S.subgroupOf N
  let C := N ⊓ centralizer ((S ⊓ N : Subgroup G) : Set G)
  letI : U.Normal := inferInstanceAs ((S.comap N.subtype).Normal)
  letI : C.Normal := inferInstanceAs ((N ⊓ centralizer ((S ⊓ N : Subgroup G) : Set G)).Normal)
  obtain ⟨hd, hs⟩ := normal_centralizer_complement_of_perfectSimpleProduct hN U
  have hCDisjoint : Disjoint C S := by
    rw [disjoint_iff_inf_le]
    intro x hx
    let z : N := ⟨x, hx.1.1⟩
    have hz : z ∈ U ⊓ centralizer (U : Set N) := by
      refine ⟨hx.2, ?_⟩
      change z ∈ centralizer (U : Set N)
      rw [mem_centralizer_iff]
      intro w hw
      exact Subtype.ext ((mem_centralizer_iff.mp hx.1.2) (w : G) ⟨hw, w.2⟩)
    rw [hd, mem_bot] at hz
    exact mem_bot.mpr (congrArg Subtype.val hz)
  have hCb : C = ⊥ := by
    apply le_bot_iff.mp
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_eq_bot_of_disjoint hCDisjoint)).trans
    exact (centralizer_socle_eq_bot hR).le
  have hUb : centralizer (U : Set N) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hmem : (z : G) ∈ C := by
      refine ⟨z.2, ?_⟩
      change (z : G) ∈ centralizer ((S ⊓ N : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val ((mem_centralizer_iff.mp hz) (⟨w, hw.2⟩ : N) hw.1)
    rw [hCb, mem_bot] at hmem
    exact mem_bot.mpr (Subtype.ext hmem)
  rw [hUb, sup_bot_eq] at hs
  exact subgroupOf_eq_top.mp hs

end ProductComplements


section SocleRecognition

universe u

theorem isPerfectSimpleProduct_of_normal_subgroup {G : Type u} [Group G]
    (hG : IsPerfectSimpleProduct G) (N : Subgroup G) [N.Normal] :
    IsPerfectSimpleProduct N := by
  let C := centralizer (N : Set G)
  letI : C.Normal := inferInstanceAs ((centralizer (N : Set G)).Normal)
  obtain ⟨hd, hs⟩ := normal_centralizer_complement_of_perfectSimpleProduct hG N
  let f := (QuotientGroup.mk' C).comp N.subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro y hy
    have hc : (y : G) ∈ C := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    have hm : (y : G) ∈ N ⊓ C := ⟨y.2, hc⟩
    rw [hd, mem_bot] at hm
    exact mem_bot.mpr (Subtype.ext hm)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hx : x ∈ N ⊔ C := by rw [hs]; exact mem_top _
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    change QuotientGroup.mk' C a = QuotientGroup.mk' C (a * b)
    have hq : QuotientGroup.mk' C b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    rw [map_mul, hq, mul_one]
  let e := MulEquiv.ofBijective f ⟨hi, hf⟩
  let r := e.symm.toMonoidHom.comp (QuotientGroup.mk' C)
  exact isPerfectSimpleProduct_of_surjective r
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective C)) hG

/-- In a finite radical-free group, the socle consists of the elements whose
ambient normal closure is a product of perfect simple groups. -/
theorem mem_socle_iff_perfectSimpleProduct_normalClosure {G : Type u} [Group G] [Finite G]
    (hR : solvableRadical G = ⊥) (x : G) :
    x ∈ socle G ↔ IsPerfectSimpleProduct (normalClosure ({x} : Set G)) := by
  let H := normalClosure ({x} : Set G)
  let S := socle G
  constructor
  · intro hx
    have hHS : H ≤ S := Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hx)
    let K := H.subgroupOf S
    letI : K.Normal := inferInstanceAs ((H.comap S.subtype).Normal)
    have hK := isPerfectSimpleProduct_of_normal_subgroup (isPerfectSimpleProduct_socle hR) K
    let f : K →* H :=
      { toFun := fun z => ⟨(z.1 : G), z.2⟩
        map_one' := rfl
        map_mul' := by intro a b; rfl }
    have hf : Function.Surjective f := by
      intro z
      exact ⟨⟨⟨z.1, hHS z.2⟩, z.2⟩, rfl⟩
    exact isPerfectSimpleProduct_of_surjective f hf hK
  · intro hx
    exact le_socle_of_perfectSimpleProduct hR H hx (subset_normalClosure (Set.mem_singleton x))

/-- A socle step queries precisely the semisimple residual of the source normal closure. -/
theorem quotient_mk_mem_socle_iff_semisimpleResidual_le {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hR : solvableRadical (G ⧸ K) = ⊥) (x : G) :
    QuotientGroup.mk' K x ∈ socle (G ⧸ K) ↔
      semisimpleResidual (normalClosure ({x} : Set G)) ≤ K.subgroupOf (normalClosure {x}) :=
  (mem_socle_iff_perfectSimpleProduct_normalClosure hR _).trans
    (quotient_mk_normalClosure_isPerfectSimpleProduct_iff K x)

/-- The same socle step can test membership on a generating list of the residual. -/
theorem quotient_mk_mem_socle_iff_forall_generator {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hR : solvableRadical (G ⧸ K) = ⊥) (x : G)
    {ι : Type*} (gen : ι → normalClosure ({x} : Set G))
    (hgen : closure (Set.range gen) = semisimpleResidual (normalClosure ({x} : Set G))) :
    QuotientGroup.mk' K x ∈ socle (G ⧸ K) ↔ ∀ i, (gen i : G) ∈ K := by
  rw [quotient_mk_mem_socle_iff_semisimpleResidual_le K hR, ← hgen, closure_le]
  exact Set.range_subset_iff

end SocleRecognition


section ReplayBridge

open Mathproof.MinimumGeneration.TowerReplay

/-- Source residual generators are represented in the original group, not in
a recursively materialized quotient table. -/
def sourceResidual (socleStep : Bool) (x : G) : Subgroup G :=
  let H := normalClosure ({x} : Set G)
  if socleStep then (semisimpleResidual H).map H.subtype
  else (solvableResidual H).map H.subtype

private theorem sourceResidual_le_iff {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (socleStep : Bool) (x : G)
    (hFree : socleStep = true → solvableRadical (G ⧸ K) = ⊥) :
    (if socleStep then QuotientGroup.mk' K x ∈ socle (G ⧸ K)
      else QuotientGroup.mk' K x ∈ solvableRadical (G ⧸ K)) ↔
    sourceResidual socleStep x ≤ K := by
  cases socleStep with
  | false =>
    simp only [Bool.false_eq_true, if_false, sourceResidual, map_le_iff_le_comap]
    exact quotient_mk_mem_solvableRadical_iff K x
  | true =>
    simp only [if_true, sourceResidual, map_le_iff_le_comap]
    exact quotient_mk_mem_socle_iff_semisimpleResidual_le K (hFree rfl) x

/-- Read one valid generator ordinal and encode its result as a source label.
An invalid label instead produces a fixed invalid label at ordinal zero. -/
def rawResidualChild (n : Nat) (gen : Nat → Fin n → List (Fin n)) : Child :=
  fun level x j =>
    if hx : x < n then ((gen level ⟨x, hx⟩)[j]?).map Fin.val
    else if j = 0 then some n else none

def rawResidualBase (n : Nat) [Group (Fin n)] (x : Nat) : Bool :=
  if hx : x < n then decide ((⟨x, hx⟩ : Fin n) = 1) else false

def rawKernelMember (n : Nat) [Group (Fin n)] (K : Nat → Subgroup (Fin n))
    (l x : Nat) : Prop :=
  ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ K l

theorem rawResidualBase_correct (n : Nat) [Group (Fin n)]
    (K : Nat → Subgroup (Fin n)) (hZero : K 0 = ⊥) (x : Nat) :
    rawResidualBase n x = true ↔ rawKernelMember n K 0 x := by
  by_cases hx : x < n <;> simp [rawResidualBase, rawKernelMember, hx, hZero, mem_bot]

/-- Generator-list semantics instantiate the existing ordinal replay interface
for the alternating radical and socle layers. -/
theorem rawResidualChild_correct (n radix : Nat) [Group (Fin n)] (hRadix : 0 < radix)
    (K : Nat → Subgroup (Fin n)) [∀ l, (K l).Normal] (mode : Nat → Bool)
    (gen : Nat → Fin n → List (Fin n))
    (hLength : ∀ l x, (gen l x).length ≤ radix)
    (hGen : ∀ l x, closure {a | a ∈ gen (l + 1) x} = sourceResidual (mode (l + 1)) x)
    (hLayer : ∀ l (x : Fin n), x ∈ K (l + 1) ↔
      if mode (l + 1) then QuotientGroup.mk' (K l) x ∈ socle (Fin n ⧸ K l)
      else QuotientGroup.mk' (K l) x ∈ solvableRadical (Fin n ⧸ K l))
    (hFree : ∀ l, mode (l + 1) = true → solvableRadical (Fin n ⧸ K l) = ⊥)
    (l x : Nat) :
    rawKernelMember n K (l + 1) x ↔
      ∀ j < radix, ∀ y, rawResidualChild n gen (l + 1) x j = some y →
        rawKernelMember n K l y := by
  by_cases hx : x < n
  · let a : Fin n := ⟨x, hx⟩
    have hR : a ∈ K (l + 1) ↔ ∀ b ∈ gen (l + 1) a, b ∈ K l := by
      rw [hLayer, sourceResidual_le_iff _ _ _ (hFree l), ← hGen, closure_le]
      rfl
    have hx' : rawKernelMember n K (l + 1) x ↔ a ∈ K (l + 1) :=
      ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    rw [hx', hR]
    constructor
    · intro h j _ y hj
      simp only [rawResidualChild, dif_pos hx, Option.map_eq_some_iff] at hj
      obtain ⟨b, hb, rfl⟩ := hj
      exact ⟨b.isLt, h b (List.mem_iff_getElem?.mpr ⟨j, hb⟩)⟩
    · intro h b hb
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
      have hlt := (List.getElem?_eq_some_iff.mp hj).1
      have hout := h j (lt_of_lt_of_le hlt (hLength _ _)) b.val
        (by simp [rawResidualChild, hx, a, hj])
      exact hout.2
  · constructor
    · intro hh
      exact (hx hh.1).elim
    · intro h
      have hout := h 0 hRadix n (by simp [rawResidualChild, hx])
      exact (Nat.lt_irrefl n hout.1).elim

/-- The executable replay controller decides membership in an actual radical–socle
tower when its source-level residual generator lists are supplied with certificates. -/
theorem replay_halts_with_kernel_membership (n radix : Nat) [Group (Fin n)] (hRadix : 0 < radix)
    (K : Nat → Subgroup (Fin n)) [∀ l, (K l).Normal] (hZero : K 0 = ⊥)
    (mode : Nat → Bool) (gen : Nat → Fin n → List (Fin n))
    (hLength : ∀ l x, (gen l x).length ≤ radix)
    (hGen : ∀ l x, closure {a | a ∈ gen (l + 1) x} = sourceResidual (mode (l + 1)) x)
    (hLayer : ∀ l (x : Fin n), x ∈ K (l + 1) ↔
      if mode (l + 1) then QuotientGroup.mk' (K l) x ∈ socle (Fin n ⧸ K l)
      else QuotientGroup.mk' (K l) x ∈ solvableRadical (Fin n ⧸ K l))
    (hFree : ∀ l, mode (l + 1) = true → solvableRadical (Fin n ⧸ K l) = ⊥)
    (l x : Nat) :
    ∃ answer, ControlRuns (rawResidualChild n gen) (rawResidualBase n) radix l x
        (.scan (radix ^ l) 0) (.halt answer) ∧
      controlStep (rawResidualChild n gen) (rawResidualBase n) radix l x (.halt answer) = none ∧
      (answer = true ↔ rawKernelMember n K l x) :=
  control_decides_membership (rawResidualChild n gen) (rawResidualBase n) hRadix
    (rawKernelMember n K) (rawResidualBase_correct n K hZero)
    (rawResidualChild_correct n radix hRadix K mode gen hLength hGen hLayer hFree) l x

end ReplayBridge

end Mathproof.MinimumGenerationResidual
