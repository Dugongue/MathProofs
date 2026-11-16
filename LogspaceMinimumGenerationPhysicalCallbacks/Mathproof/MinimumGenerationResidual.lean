import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# Residual tests for the alternating radical and socle tower

The results below concern the group-theoretic tests performed on the original
table, independently of implementation or workspace bounds.
-/

namespace Mathproof.MinimumGenerationResidual

open Subgroup

set_option linter.style.haveILetI false

variable {G : Type*} [Group G]

local instance [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The solvable residual is the intersection of the derived series. -/
def solvableResidual (G : Type*) [Group G] : Subgroup G :=
  ⨅ n : ℕ, derivedSeries G n

theorem solvableResidual_le_derivedSeries (n : ℕ) :
    solvableResidual G ≤ derivedSeries G n :=
  iInf_le _ n

instance solvableResidual_normal : (solvableResidual G).Normal :=
  Subgroup.normal_iInf_normal fun n => derivedSeries_normal G n

theorem perfect_le_derivedSeries (H : Subgroup G) [Group.IsPerfect H] (n : ℕ) :
    H ≤ derivedSeries G n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
      rw [derivedSeries_succ, ← H.commutator_eq_self]
      exact Subgroup.commutator_mono ih ih

theorem perfect_le_solvableResidual (H : Subgroup G) [Group.IsPerfect H] :
    H ≤ solvableResidual G :=
  le_iInf (perfect_le_derivedSeries H)

theorem solvableResidual_eq_derivedSeries [Finite G] :
    ∃ n : ℕ, solvableResidual G = derivedSeries G n := by
  obtain ⟨H, hH⟩ := WellFoundedLT.exists_minimal
    (inferInstance : WellFoundedLT (Subgroup G))
    {H : Subgroup G | ∃ n, derivedSeries G n = H}
    ⟨⊤, 0, rfl⟩
  obtain ⟨n, rfl⟩ := hH.1
  refine ⟨n, le_antisymm (solvableResidual_le_derivedSeries n) ?_⟩
  apply le_iInf
  intro m
  obtain h | h := le_total n m
  · exact (hH.eq_of_le ⟨m, rfl⟩ (derivedSeries_antitone G h)).ge
  · exact derivedSeries_antitone G h

instance solvableResidual_isPerfect [Finite G] : Group.IsPerfect (solvableResidual G) := by
  obtain ⟨n, hn⟩ := solvableResidual_eq_derivedSeries (G := G)
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · exact Subgroup.commutator_le_self _
  · simpa only [hn, ← derivedSeries_succ] using
      (solvableResidual_le_derivedSeries (G := G) (n + 1) :
        solvableResidual G ≤ derivedSeries G (n + 1))

/-- The residual is the smallest kernel yielding a solvable quotient. -/
theorem isSolvable_quotient_iff [Finite G] (K : Subgroup G) [K.Normal] :
    Group.IsSolvable (G ⧸ K) ↔ solvableResidual G ≤ K := by
  constructor
  · rintro ⟨⟨n, hn⟩⟩
    have hn' : (derivedSeries G n).map (QuotientGroup.mk' K) = ⊥ :=
      (map_derivedSeries_eq (QuotientGroup.mk'_surjective K) n).trans hn
    exact (solvableResidual_le_derivedSeries n).trans
      (by simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff (derivedSeries G n)).mp hn')
  · intro h
    obtain ⟨n, hn⟩ := solvableResidual_eq_derivedSeries (G := G)
    refine ⟨⟨n, ?_⟩⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective K), ← hn,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h

/-- The solvable radical, defined as the join of all solvable normal subgroups. -/
def solvableRadical (G : Type*) [Group G] : Subgroup G :=
  sSup {H : Subgroup G | H.Normal ∧ Group.IsSolvable H}

instance solvableRadical_normal : (solvableRadical G).Normal :=
  Subgroup.sSup_normal _ fun _ h => h.1

theorem le_solvableRadical {H : Subgroup G} [H.Normal] [Group.IsSolvable H] :
    H ≤ solvableRadical G :=
  le_sSup ⟨inferInstance, inferInstance⟩

/-- The supremum of two solvable normal subgroups is solvable.
Adapted to the active Mathlib interface from CFSG.GroupTheory.ABGLocalTools.Constraint. -/
theorem isSolvable_sup_normal (H K : Subgroup G) [H.Normal] [K.Normal]
    [Group.IsSolvable H] [Group.IsSolvable K] : Group.IsSolvable (H ⊔ K : Subgroup G) := by
  let L : Subgroup G := H ⊔ K
  let M : Subgroup L := H.subgroupOf L
  letI : M.Normal := Subgroup.normal_subgroupOf
  letI : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ L)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : K →* L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : K ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := H) (t := K)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (inferInstance : H.Normal).conj_mem' a ha b
  letI : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact (Group.isSolvable_iff_subgroup_quotient M).mpr ⟨inferInstance, inferInstance⟩

instance solvableRadical_isSolvable [Finite G] : Group.IsSolvable (solvableRadical G) := by
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun H : Subgroup G => H.Normal ∧ Group.IsSolvable H) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  have hle : ∀ H : Subgroup G, H.Normal ∧ Group.IsSolvable H → H ≤ M := by
    rintro H ⟨hH, hHs⟩
    letI : M.Normal := hM.1.1
    letI : Group.IsSolvable M := hM.1.2
    have h := hM.eq_of_le ⟨inferInstance, isSolvable_sup_normal M H⟩ le_sup_left
    rw [h]
    exact le_sup_right
  have heq : solvableRadical G = M := le_antisymm (sSup_le hle) (le_sSup hM.1)
  rw [heq]
  exact hM.1.2

/-- Principal normal closures commute with any surjective group homomorphism. -/
theorem map_principalNormalClosure {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (x : G) :
    (normalClosure {x}).map f = normalClosure {f x} := by
  rw [Subgroup.map_normalClosure _ _ hf, Set.image_singleton]

theorem mem_solvableRadical_iff_normalClosure [Finite G] (x : G) :
    x ∈ solvableRadical G ↔ Group.IsSolvable (normalClosure ({x} : Set G)) := by
  constructor
  · intro hx
    have hle : normalClosure {x} ≤ solvableRadical G :=
      normalClosure_le_normal (Set.singleton_subset_iff.mpr hx)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  · intro h
    letI : Group.IsSolvable (normalClosure ({x} : Set G)) := h
    exact le_solvableRadical (subset_normalClosure (Set.mem_singleton x))

/-- Source-group test for a radical layer of a quotient. -/
theorem quotient_mk_mem_solvableRadical_iff [Finite G] (K : Subgroup G) [K.Normal]
    (x : G) :
    QuotientGroup.mk' K x ∈ solvableRadical (G ⧸ K) ↔
      solvableResidual (normalClosure ({x} : Set G)) ≤ K.subgroupOf (normalClosure {x}) := by
  let H := normalClosure ({x} : Set G)
  let f := (QuotientGroup.mk' K).comp H.subtype
  have hker : f.ker = K.subgroupOf H := by
    ext y
    change QuotientGroup.mk' K (y : G) = 1 ↔ (y : G) ∈ K
    exact QuotientGroup.eq_one_iff _
  have hrange : f.range = normalClosure {QuotientGroup.mk' K x} := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_principalNormalClosure _ (QuotientGroup.mk'_surjective K) x
  rw [mem_solvableRadical_iff_normalClosure, ← hrange, ← hker, ← isSolvable_quotient_iff]
  have e := QuotientGroup.quotientKerEquivRange f
  constructor
  · intro h
    letI := h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro h
    letI := h
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective


/-- Quotienting by the solvable radical leaves trivial solvable radical. -/
theorem solvableRadical_quotient_solvableRadical_eq_bot [Finite G] :
    solvableRadical (G ⧸ solvableRadical G) = ⊥ := by
  let R := solvableRadical G
  let Q := solvableRadical (G ⧸ R)
  let f := QuotientGroup.mk' R
  let E := Q.comap f
  have hRE : R ≤ E := by
    intro x hx
    change f x ∈ Q
    have hfx : f x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hfx]
    exact Q.one_mem
  let g : E →* Q := (f.comp E.subtype).codRestrict Q fun x => x.2
  let j : R →* E := Subgroup.inclusion hRE
  have hker : g.ker ≤ j.range := by
    intro x hx
    have h : f (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, (QuotientGroup.eq_one_iff (x : G)).mp h⟩, Subtype.ext rfl⟩
  letI : Group.IsSolvable E := Group.isSolvable_of_ker_le_range j g hker
  letI : E.Normal := inferInstanceAs ((Q.comap f).Normal)
  have hER : E ≤ R := le_solvableRadical
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr (hER hy))

/-- A maximal proper normal subgroup, ordered by inclusion. -/
def IsMaximalNormal (M : Subgroup G) : Prop :=
  Maximal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊤) M

theorem isSimple_quotient_of_maximalNormal (M : Subgroup G) [M.Normal]
    (hM : IsMaximalNormal M) : IsSimpleGroup (G ⧸ M) := by
  let q := QuotientGroup.mk' M
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective M
  haveI : Nontrivial (G ⧸ M) := by
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM.1.2)
    exact ⟨⟨q x, 1, fun h => hx.2 ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  refine ⟨fun H hH => ?_⟩
  by_cases ht : H = ⊤
  · exact Or.inr ht
  · left
    have hn : (H.comap q).Normal := hH.comap q
    have hp : H.comap q ≠ ⊤ := by
      intro he
      apply ht
      rw [← map_comap_eq_self_of_surjective hq H, he, map_top_of_surjective q hq]
    have hm : M ≤ H.comap q := by
      intro x hx
      change q x ∈ H
      have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hqx]
      exact H.one_mem
    rw [← map_comap_eq_self_of_surjective hq H, ← hM.eq_of_le ⟨hn, hp⟩ hm]
    exact (Subgroup.map_eq_bot_iff M).mpr (by simp [q])

private theorem map_maximalNormal_eq_top_of_ne (M K : Subgroup G) [K.Normal]
    (hM : IsMaximalNormal M) (hK : IsMaximalNormal K) (hne : M ≠ K) :
    M.map (QuotientGroup.mk' K) = ⊤ := by
  letI : M.Normal := hM.1.1
  letI : IsSimpleGroup (G ⧸ K) := isSimple_quotient_of_maximalNormal K hK
  have hnorm : (M.map (QuotientGroup.mk' K)).Normal :=
    (inferInstance : M.Normal).map _ (QuotientGroup.mk'_surjective K)
  refine hnorm.eq_bot_or_eq_top.resolve_left ?_
  intro hb
  exact hne (hM.eq_of_le hK.1
    (by simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff M).mp hb))

private theorem finset_inf_normal (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, M.Normal) : (S.inf id).Normal := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (inferInstance : (⊤ : Subgroup G).Normal)
  | insert M S hMS ih =>
      letI : M.Normal := hS M (Finset.mem_insert_self M S)
      have hSn : ∀ N ∈ S, N.Normal := fun N hN => hS N (Finset.mem_insert_of_mem hN)
      letI : (S.inf id).Normal := ih hSn
      simpa only [Finset.inf_insert, id_eq] using
        (inferInstance : (M ⊓ S.inf id).Normal)

/-- For a perfect simple quotient with kernel K, the intersection of any
finite collection of other maximal normal kernels still surjects onto it. -/
private theorem map_inf_maximalNormal_eq_top (K : Subgroup G) [K.Normal]
    [Group.IsPerfect (G ⧸ K)] (hK : IsMaximalNormal K) (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, IsMaximalNormal M) (hKS : K ∉ S) :
    (S.inf id).map (QuotientGroup.mk' K) = ⊤ := by
  classical
  let q := QuotientGroup.mk' K
  induction S using Finset.induction_on with
  | empty => simpa using map_top_of_surjective q (QuotientGroup.mk'_surjective K)
  | insert M S hMS ih =>
    have hM := hS M (Finset.mem_insert_self M S)
    have hS' : ∀ N ∈ S, IsMaximalNormal N := fun N hN => hS N (Finset.mem_insert_of_mem hN)
    have hne : M ≠ K := fun h => hKS (h ▸ Finset.mem_insert_self M S)
    have hKS' : K ∉ S := fun h => hKS (Finset.mem_insert_of_mem h)
    letI : M.Normal := hM.1.1
    letI : (S.inf id).Normal := finset_inf_normal S fun N hN => (hS' N hN).1.1
    have hmap : M.map q = ⊤ := map_maximalNormal_eq_top_of_ne M K hM hK hne
    apply top_unique
    rw [Finset.inf_insert, id_eq]
    have hc := Subgroup.map_mono (Subgroup.commutator_le_inf M (S.inf id))
      (f := q)
    rw [Subgroup.map_commutator, hmap, ih hS' hKS',
      ← commutator_def, Group.IsPerfect.commutator_eq_top] at hc
    exact hc

/-- A finite perfect group has a single normal generator.
The proof uses commutators to implement finite Chinese remaindering. -/
theorem exists_normalClosure_singleton_eq_top_of_perfect [Finite G] [Group.IsPerfect G] :
    ∃ x : G, normalClosure ({x} : Set G) = ⊤ := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  let S : Finset (Subgroup G) := Finset.univ.filter IsMaximalNormal
  have hS : ∀ M ∈ S, IsMaximalNormal M := fun M h => (Finset.mem_filter.mp h).2
  have hAvoid (T : Finset (Subgroup G)) (hT : ∀ M ∈ T, IsMaximalNormal M) :
      ∃ x : G, ∀ M ∈ T, x ∉ M := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert M T hMT ih =>
      have hM := hT M (Finset.mem_insert_self M T)
      have hT' : ∀ N ∈ T, IsMaximalNormal N := fun N hN => hT N (Finset.mem_insert_of_mem hN)
      obtain ⟨x, hx⟩ := ih hT'
      by_cases hxM : x ∈ M
      · letI : M.Normal := hM.1.1
        have hmap := map_inf_maximalNormal_eq_top M hM T hT' hMT
        letI : IsSimpleGroup (G ⧸ M) := isSimple_quotient_of_maximalNormal M hM
        obtain ⟨a, ha⟩ := exists_ne (1 : G ⧸ M)
        have ham : a ∈ (T.inf id).map (QuotientGroup.mk' M) := hmap ▸ mem_top a
        obtain ⟨y, hy, hyq⟩ := ham
        have hyM : y ∉ M := fun h => ha (hyq.symm.trans ((QuotientGroup.eq_one_iff y).mpr h))
        refine ⟨x * y, fun N hn => ?_⟩
        rcases Finset.mem_insert.mp hn with rfl | hn
        · intro hc
          exact hyM ((mul_mem_cancel_left hxM).mp hc)
        · have hyn : y ∈ N := (Finset.inf_le (f := id) hn : T.inf id ≤ N) hy
          intro hc
          exact hx N hn ((mul_mem_cancel_right hyn).mp hc)
      · exact ⟨x, fun N hn => (Finset.mem_insert.mp hn).elim (fun he => he ▸ hxM) (hx N)⟩
  obtain ⟨x, hx⟩ := hAvoid S hS
  refine ⟨x, ?_⟩
  by_contra hn
  obtain ⟨M, hle, hM⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup G => M.Normal ∧ M ≠ ⊤)
    (a := normalClosure ({x} : Set G)) ⟨inferInstance, hn⟩
  exact hx M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩)
    (hle (subset_normalClosure (Set.mem_singleton x)))

/-- A perfect principal normal closure attains the solvable residual. -/
theorem exists_normalClosure_singleton_eq_solvableResidual [Finite G] :
    ∃ x : G, normalClosure ({x} : Set G) = solvableResidual G := by
  let R := solvableResidual G
  obtain ⟨x, hx⟩ := exists_normalClosure_singleton_eq_top_of_perfect (G := R)
  refine ⟨x, le_antisymm (normalClosure_le_normal (Set.singleton_subset_iff.mpr x.2)) ?_⟩
  have h := map_normalClosure_le ({x} : Set R) R.subtype
  rw [hx, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_singleton] at h
  exact h


/-- Minimal nontrivial normal subgroups of the ambient group. -/
def IsMinimalNormal (K : Subgroup G) : Prop :=
  Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) K

def socle (G : Type*) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | IsMinimalNormal K}

instance socle_normal : (socle G).Normal :=
  Subgroup.sSup_normal _ fun _ h => h.1.1

/-- In a finite group with trivial solvable radical, the socle is
self-centralizing in the sense that its centralizer is trivial. -/
theorem centralizer_socle_eq_bot [Finite G] (hR : solvableRadical G = ⊥) :
    centralizer (socle G : Set G) = ⊥ := by
  let S := socle G
  let C := centralizer (S : Set G)
  let I := C ⊓ S
  letI : C.Normal := inferInstanceAs ((centralizer (S : Set G)).Normal)
  letI : I.Normal := inferInstanceAs ((C ⊓ S).Normal)
  letI : Group.IsSolvable I := Group.isSolvable_of_comm fun a b => by
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp a.2.1) _ b.2.2).symm
  have hI : I = ⊥ := le_bot_iff.mp (le_solvableRadical.trans hR.le)
  by_contra hC
  obtain ⟨M, hMC, hM⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) C ⟨inferInstance, hC⟩
  have hMS : M ≤ S := le_sSup hM
  exact hM.1.2 (le_bot_iff.mp ((le_inf hMC hMS).trans hI.le))


theorem conjNormal_ker_eq_centralizer (H : Subgroup G) [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = centralizer (H : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg x hx
    have he : g * x * g⁻¹ = x := by
      simpa [MulAut.conjNormal_apply] using congrArg
        (fun u : MulAut H => ((u ⟨x, hx⟩ : H) : G)) hg
    simpa [mul_assoc] using (congrArg (fun z : G => z * g) he).symm
  · intro hg
    ext x
    rw [MulAut.conjNormal_apply, ← hg (x : G) x.2]
    simp [mul_assoc]

theorem conjNormal_socle_injective [Finite G] (hR : solvableRadical G = ⊥) :
    Function.Injective (MulAut.conjNormal (H := socle G)) :=
  (MonoidHom.ker_eq_bot_iff _).mp
    ((conjNormal_ker_eq_centralizer (socle G)).trans (centralizer_socle_eq_bot hR))


/-- Maximizing cardinality over all perfect principal normal closures recovers
exactly the solvable residual. -/
theorem max_perfect_normalClosure_eq_solvableResidual [Finite G] (x : G)
    (hx : Group.IsPerfect (normalClosure ({x} : Set G)))
    (hmax : ∀ y : G, Group.IsPerfect (normalClosure ({y} : Set G)) →
      Nat.card (normalClosure ({y} : Set G)) ≤ Nat.card (normalClosure ({x} : Set G))) :
    normalClosure ({x} : Set G) = solvableResidual G := by
  letI := hx
  obtain ⟨y, hy⟩ := exists_normalClosure_singleton_eq_solvableResidual (G := G)
  apply Subgroup.eq_of_le_of_card_ge (perfect_le_solvableResidual _)
  rw [← hy]
  apply hmax
  rw [hy]
  infer_instance

/-- A source generator list implements the radical membership criterion
without retaining a subgroup table. -/
theorem quotient_mk_mem_solvableRadical_iff_forall_generator [Finite G]
    (K : Subgroup G) [K.Normal] (x : G) {ι : Type*}
    (u : ι → normalClosure ({x} : Set G))
    (hu : closure (Set.range u) = solvableResidual (normalClosure ({x} : Set G))) :
    QuotientGroup.mk' K x ∈ solvableRadical (G ⧸ K) ↔ ∀ i, (u i : G) ∈ K := by
  rw [quotient_mk_mem_solvableRadical_iff, ← hu, closure_le]
  exact Set.range_subset_iff

/-- Conjugation on a radical-free group's socle gives the basic cardinal bound. -/
theorem card_le_card_mulAut_socle [Finite G] (hR : solvableRadical G = ⊥) :
    Nat.card G ≤ Nat.card (MulAut (socle G)) :=
  Nat.card_le_card_of_injective _ (conjNormal_socle_injective hR)

/-- The maximal normal kernels with perfect simple quotients. -/
def IsPerfectSimpleKernel (K : Subgroup G) : Prop :=
  IsMaximalNormal K ∧ ∃ h : K.Normal, letI := h; Group.IsPerfect (G ⧸ K)

abbrev PerfectSimpleKernel (G : Type*) [Group G] :=
  {K : Subgroup G // IsPerfectSimpleKernel K}

instance perfectSimpleKernel_normal (K : PerfectSimpleKernel G) : K.1.Normal :=
  K.2.1.1.1

instance perfectSimpleKernel_perfect (K : PerfectSimpleKernel G) :
    Group.IsPerfect (G ⧸ K.1) := by
  obtain ⟨_, hp⟩ := K.2.2
  exact hp

instance perfectSimpleKernel_simple (K : PerfectSimpleKernel G) :
    IsSimpleGroup (G ⧸ K.1) :=
  isSimple_quotient_of_maximalNormal K.1 K.2.1

/-- Finite Chinese remaindering among the perfect simple quotients. -/
theorem exists_simultaneous_mod_perfectSimpleKernels (F : Finset (Subgroup G))
    (hF : ∀ K ∈ F, IsPerfectSimpleKernel K) (targets : Subgroup G → G) :
    ∃ g : G, ∀ K ∈ F, (targets K)⁻¹ * g ∈ K := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert K F hkF ih =>
    have hk := hF K (Finset.mem_insert_self K F)
    obtain ⟨hkN, hkP⟩ := hk.2
    letI : K.Normal := hkN
    letI : Group.IsPerfect (G ⧸ K) := hkP
    have hF' : ∀ M ∈ F, IsPerfectSimpleKernel M :=
      fun M hm => hF M (Finset.mem_insert_of_mem hm)
    obtain ⟨x, hx⟩ := ih hF'
    let q := QuotientGroup.mk' K
    have htop := map_inf_maximalNormal_eq_top K hk.1 F
      (fun M hm => (hF' M hm).1) hkF
    have hmem : q (x⁻¹ * targets K) ∈ (F.inf id).map q :=
      htop ▸ mem_top _
    obtain ⟨y, hy, hq⟩ := hmem
    refine ⟨x * y, ?_⟩
    intro M hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · apply (QuotientGroup.eq_one_iff _).mp
      change q ((targets M)⁻¹ * (x * y)) = 1
      simp [map_mul, hq]
    · rw [← mul_assoc]
      exact M.mul_mem (hx M hm) ((Finset.inf_le (f := id) hm : F.inf id ≤ M) hy)

def semisimpleProjection (G : Type*) [Group G] :
    G →* ((K : PerfectSimpleKernel G) → G ⧸ K.1) :=
  MonoidHom.pi fun K => QuotientGroup.mk' K.1

/-- The semisimple residual is the intersection of the perfect simple quotient kernels. -/
def semisimpleResidual (G : Type*) [Group G] : Subgroup G :=
  (semisimpleProjection G).ker

instance semisimpleResidual_normal : (semisimpleResidual G).Normal :=
  inferInstanceAs ((semisimpleProjection G).ker.Normal)

theorem mem_semisimpleResidual_iff (x : G) :
    x ∈ semisimpleResidual G ↔ ∀ K : PerfectSimpleKernel G, x ∈ K.1 := by
  change semisimpleProjection G x = 1 ↔ _
  rw [funext_iff]
  exact forall_congr' fun K => QuotientGroup.eq_one_iff x

theorem semisimpleProjection_surjective [Finite G] :
    Function.Surjective (semisimpleProjection G) := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  intro a
  let targets (K : Subgroup G) : G :=
    if h : IsPerfectSimpleKernel K then
      letI : K.Normal := h.1.1.1
      Classical.choose (QuotientGroup.mk'_surjective K (a ⟨K, h⟩))
    else 1
  let F := (Finset.univ : Finset (Subgroup G)).filter IsPerfectSimpleKernel
  obtain ⟨g, hg⟩ := exists_simultaneous_mod_perfectSimpleKernels F
    (fun K h => (Finset.mem_filter.mp h).2) targets
  refine ⟨g, ?_⟩
  funext K
  have hk : K.1 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.2⟩
  have h := (QuotientGroup.eq_one_iff _).mpr (hg K.1 hk)
  change QuotientGroup.mk' K.1 ((targets K.1)⁻¹ * g) = 1 at h
  have hh : QuotientGroup.mk' K.1 (targets K.1) = a K := by
    simp only [targets, dif_pos K.2]
    exact Classical.choose_spec (QuotientGroup.mk'_surjective K.1 (a K))
  rw [map_mul, map_inv, hh, inv_mul_eq_one] at h
  exact h.symm

/-- The quotient by the semisimple residual is the product of all perfect simple quotients. -/
noncomputable def quotientSemisimpleResidualEquivPi [Finite G] :
    G ⧸ semisimpleResidual G ≃* ((K : PerfectSimpleKernel G) → G ⧸ K.1) :=
  QuotientGroup.quotientKerEquivOfSurjective (semisimpleProjection G)
    semisimpleProjection_surjective

theorem center_eq_bot_of_simple_perfect [IsSimpleGroup G] [Group.IsPerfect G] :
    center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h)).elim

section NormalSubgroupsOfProducts

open scoped commutatorElement

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable (S : ι → Type*) [∀ i, Group (S i)]
variable [∀ i, IsSimpleGroup (S i)] [∀ i, Group.IsPerfect (S i)]

/-- A normal subgroup of a finite product of perfect simple groups is a
product of coordinate subgroups, each of which is trivial or full. -/
theorem normal_subgroup_pi_eq_pi (M : Subgroup ((i : ι) → S i)) [M.Normal] :
    M = Subgroup.pi Set.univ (fun i => M.comap (MonoidHom.mulSingle S i)) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_pi]
    intro i _
    let A := M.comap (MonoidHom.mulSingle S i)
    letI : A.Normal := inferInstanceAs ((M.comap (MonoidHom.mulSingle S i)).Normal)
    change x i ∈ A
    rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.mem_bot]
      have hc : x i ∈ center (S i) := by
        rw [Subgroup.mem_center_iff]
        intro a
        have hm : ⁅(Pi.mulSingle i a : (j : ι) → S j), x⁆ ∈ M := by
          exact M.mul_mem ((inferInstance : M.Normal).conj_mem _ hx _) (M.inv_mem hx)
        have he : ⁅(Pi.mulSingle i a : (j : ι) → S j), x⁆ = Pi.mulSingle i ⁅a, x i⁆ := by
          funext j
          by_cases hij : j = i
          · subst j
            simp [commutatorElement_def]
          · simp [commutatorElement_def, Pi.mulSingle_eq_of_ne hij]
        rw [he] at hm
        have hb : ⁅a, x i⁆ ∈ A := hm
        rw [h, Subgroup.mem_bot, commutatorElement_def] at hb
        simpa [mul_assoc] using congrArg (fun q : S i => q * (x i * a)) hb
      rwa [center_eq_bot_of_simple_perfect, Subgroup.mem_bot] at hc
    · rw [h]
      exact Subgroup.mem_top _
  · apply Subgroup.pi_le_iff.mpr
    intro i
    rw [Subgroup.map_le_iff_le_comap]

end NormalSubgroupsOfProducts

theorem isMaximalNormal_ker_of_surj_simple {H : Type*} [Group H] [IsSimpleGroup H]
    (f : G →* H) (hf : Function.Surjective f) : IsMaximalNormal f.ker := by
  have hproper : f.ker ≠ ⊤ := by
    obtain ⟨y, hy⟩ := exists_ne (1 : H)
    obtain ⟨x, rfl⟩ := hf y
    intro h
    exact hy (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  refine ⟨⟨inferInstance, hproper⟩, ?_⟩
  rintro K ⟨hn, hp⟩ hle
  rcases (hn.map f hf).eq_bot_or_eq_top with hb | ht
  · exact (Subgroup.map_eq_bot_iff K).mp hb
  · exact False.elim (hp (by
      rw [← Subgroup.comap_map_eq_self hle, ht, Subgroup.comap_top]))

theorem semisimpleResidual_le_ker_of_surj_perfect_simple {H : Type*} [Group H]
    [IsSimpleGroup H] [Group.IsPerfect H] (f : G →* H) (hf : Function.Surjective f) :
    semisimpleResidual G ≤ f.ker := by
  have hmax := isMaximalNormal_ker_of_surj_simple f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hperf : Group.IsPerfect (G ⧸ f.ker) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  intro x hx
  exact (mem_semisimpleResidual_iff x).mp hx ⟨f.ker, hmax, inferInstance, hperf⟩

section PiQuotients

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable (S : ι → Type*) [∀ i, Group (S i)]
variable [∀ i, IsSimpleGroup (S i)] [∀ i, Group.IsPerfect (S i)]

def survivingCoordinate (M : Subgroup ((i : ι) → S i)) (i : ι) : Prop :=
  M.comap (MonoidHom.mulSingle S i) = ⊥

noncomputable def quotientPiEquivSurviving (M : Subgroup ((i : ι) → S i)) [M.Normal] :
    ((i : ι) → S i) ⧸ M ≃* ((i : {i : ι // survivingCoordinate S M i}) → S i.1) := by
  classical
  let J := {i : ι // survivingCoordinate S M i}
  let p : ((i : ι) → S i) →* ((i : J) → S i.1) :=
    MonoidHom.pi fun i => Pi.evalMonoidHom S i.1
  have hp : Function.Surjective p := by
    intro y
    refine ⟨fun i => if h : survivingCoordinate S M i then y ⟨i, h⟩ else 1, ?_⟩
    funext i
    rcases i with ⟨i, hi⟩
    change (if h : survivingCoordinate S M i then y ⟨i, h⟩ else 1) = y ⟨i, hi⟩
    rw [dif_pos hi]
  have hk : p.ker = M := by
    ext x
    rw [MonoidHom.mem_ker, funext_iff]
    change (∀ i : J, x i.1 = 1) ↔ x ∈ M
    have hN := normal_subgroup_pi_eq_pi S M
    conv_rhs => rw [hN]
    simp only [Subgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx i
      let A := M.comap (MonoidHom.mulSingle S i)
      letI : A.Normal := inferInstanceAs ((M.comap (MonoidHom.mulSingle S i)).Normal)
      change x i ∈ A
      rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
      · rw [h, Subgroup.mem_bot]
        exact hx ⟨i, h⟩
      · rw [h]
        exact Subgroup.mem_top _
    · intro hx i
      have hi : M.comap (MonoidHom.mulSingle S i.1) = ⊥ := i.2
      simpa only [hi, Subgroup.mem_bot] using hx i.1
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p hp)

end PiQuotients

section PerfectSimpleProducts

universe v

/-- Finite products of perfect simple groups, including the empty product. -/
def IsPerfectSimpleProduct (G : Type v) [Group G] : Prop :=
  ∃ (I : Type v) (_ : Finite I) (S : I → Type v) (group : ∀ i, Group (S i)),
    letI := group
    (∀ i, IsSimpleGroup (S i)) ∧ (∀ i, Group.IsPerfect (S i)) ∧
      Nonempty (G ≃* (∀ i, S i))

theorem isPerfectSimpleProduct_of_surjective {G H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : IsPerfectSimpleProduct G) :
    IsPerfectSimpleProduct H := by
  classical
  obtain ⟨I, hI, S, hS, hs, hp, ⟨e⟩⟩ := hG
  letI : Finite I := hI
  letI : ∀ i, Group (S i) := hS
  letI : ∀ i, IsSimpleGroup (S i) := hs
  letI : ∀ i, Group.IsPerfect (S i) := hp
  let g := f.comp e.symm.toMonoidHom
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective g (hf.comp e.symm.surjective)
  let e₁ := quotientPiEquivSurviving S g.ker
  exact ⟨_, inferInstance, _, inferInstance, inferInstance, inferInstance,
    ⟨e₀.symm.trans e₁⟩⟩

/-- A quotient is a product of perfect simple groups exactly when its kernel
contains the semisimple residual. -/
theorem quotient_isPerfectSimpleProduct_iff {G : Type v} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] :
    IsPerfectSimpleProduct (G ⧸ K) ↔ semisimpleResidual G ≤ K := by
  classical
  constructor
  · intro h x hx
    obtain ⟨I, hI, S, hS, hS', hS'', ⟨e⟩⟩ := h
    letI : Finite I := hI
    letI : ∀ i, Group (S i) := hS
    letI : ∀ i, IsSimpleGroup (S i) := hS'
    letI : ∀ i, Group.IsPerfect (S i) := hS''
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    funext i
    let f := (Pi.evalMonoidHom S i).comp (e.toMonoidHom.comp (QuotientGroup.mk' K))
    have hEval : Function.Surjective (Pi.evalMonoidHom S i) := by
      intro x
      refine ⟨Pi.mulSingle i x, ?_⟩
      change Pi.mulSingle i x i = x
      exact Pi.mulSingle_eq_same _ _
    have hf : Function.Surjective f :=
      hEval.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
    have hm := semisimpleResidual_le_ker_of_surj_perfect_simple f hf hx
    simpa [f] using MonoidHom.mem_ker.mp hm
  · intro h
    let R := semisimpleResidual G
    have hR : IsPerfectSimpleProduct (G ⧸ R) :=
      ⟨PerfectSimpleKernel G, inferInstance, fun M => G ⧸ M.1,
        inferInstance, inferInstance, inferInstance, ⟨quotientSemisimpleResidualEquivPi⟩⟩
    let f : (G ⧸ R) →* (G ⧸ K) := QuotientGroup.map R K (MonoidHom.id G) (by simpa using h)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
      exact ⟨QuotientGroup.mk' R x, rfl⟩
    exact isPerfectSimpleProduct_of_surjective f hf hR

/-- The semisimple residual test on a normal closure in the source group
is the exact test for semisimplicity of the normal closure in the quotient. -/
theorem quotient_mk_normalClosure_isPerfectSimpleProduct_iff {G : Type v} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (x : G) :
    IsPerfectSimpleProduct (normalClosure ({QuotientGroup.mk' K x} : Set (G ⧸ K))) ↔
      semisimpleResidual (normalClosure ({x} : Set G)) ≤ K.subgroupOf (normalClosure {x}) := by
  let H := normalClosure ({x} : Set G)
  let f := (QuotientGroup.mk' K).comp H.subtype
  have hker : f.ker = K.subgroupOf H := by
    ext y
    change QuotientGroup.mk' K (y : G) = 1 ↔ (y : G) ∈ K
    exact QuotientGroup.eq_one_iff _
  have hrange : f.range = normalClosure {QuotientGroup.mk' K x} := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_principalNormalClosure _ (QuotientGroup.mk'_surjective K) x
  rw [← hrange, ← hker, ← quotient_isPerfectSimpleProduct_iff]
  let e := QuotientGroup.quotientKerEquivRange f
  exact ⟨isPerfectSimpleProduct_of_surjective e.symm.toMonoidHom e.symm.surjective,
    isPerfectSimpleProduct_of_surjective e.toMonoidHom e.surjective⟩

end PerfectSimpleProducts


end Mathproof.MinimumGenerationResidual


#print axioms Mathproof.MinimumGenerationResidual.quotient_mk_mem_solvableRadical_iff
#print axioms Mathproof.MinimumGenerationResidual.solvableRadical_quotient_solvableRadical_eq_bot
#print axioms Mathproof.MinimumGenerationResidual.exists_normalClosure_singleton_eq_solvableResidual
#print axioms Mathproof.MinimumGenerationResidual.conjNormal_socle_injective
#print axioms Mathproof.MinimumGenerationResidual.max_perfect_normalClosure_eq_solvableResidual
#print axioms Mathproof.MinimumGenerationResidual.quotient_mk_mem_solvableRadical_iff_forall_generator

#print axioms Mathproof.MinimumGenerationResidual.quotient_isPerfectSimpleProduct_iff
#print axioms Mathproof.MinimumGenerationResidual.quotient_mk_normalClosure_isPerfectSimpleProduct_iff
