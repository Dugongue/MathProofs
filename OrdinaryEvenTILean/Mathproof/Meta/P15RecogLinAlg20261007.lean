import Mathproof.Meta.P15RecogOps20261007
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-! RECOG lane: correctness of the generic linear algebra of `P15RecogOps20261007` over a field.

* `rref_spec`: the RREF basis is pivoted and spans the input vectors;
* `rank_eq_finrank_span`: `rank = finrank (span vs)`;
* `kerVec_orth`, `kerVec_self`, `freeCol_exists`: a nonzero vector orthogonal (for the dot
  product) to all rows, whenever the rank is deficient;
* `dot_field`, `lincomb_field`, `matMul_field`, `matPow_field`, `traceMul_field`. -/

set_option linter.unusedSectionVars false

namespace Mathproof.P15RecogLinAlg20261007

open Module
open Mathproof.P15RecogOps20261007

variable {K : Type} [Field K] [DecidableEq K]

local notation "O" => Ops.ofField K

@[simp] theorem ofField_zero : (Ops.ofField K).zero = 0 := rfl
@[simp] theorem ofField_one : (Ops.ofField K).one = 1 := rfl
@[simp] theorem ofField_add (x y : K) : (Ops.ofField K).add x y = x + y := rfl
@[simp] theorem ofField_neg (x : K) : (Ops.ofField K).neg x = -x := rfl
@[simp] theorem ofField_mul (x y : K) : (Ops.ofField K).mul x y = x * y := rfl
@[simp] theorem ofField_inv (x : K) : (Ops.ofField K).inv x = x⁻¹ := rfl
@[simp] theorem ofField_isZero (x : K) : (Ops.ofField K).isZero x = decide (x = 0) := rfl

variable {ι : Type} [DecidableEq ι]

theorem axpy_field (v : ι → K) (c : K) (w : ι → K) : axpy O v c w = v - c • w := by
  funext i; simp [axpy, sub_eq_add_neg]

theorem smul_field (c : K) (v : ι → K) : smul O c v = c • v := by
  funext i; simp [smul]

theorem firstNZ_none {idx : List ι} (hidx : ∀ i, i ∈ idx) {v : ι → K}
    (h : firstNZ O idx v = none) : v = 0 := by
  funext i
  have := List.find?_eq_none.1 h i (hidx i)
  simpa using this

theorem firstNZ_some {idx : List ι} {v : ι → K} {p : ι} (h : firstNZ O idx v = some p) :
    v p ≠ 0 := by
  have := List.find?_some h
  simpa using this

theorem isZeroVec_field {idx : List ι} (hidx : ∀ i, i ∈ idx) (v : ι → K) :
    isZeroVec O idx v = true ↔ v = 0 := by
  simp only [isZeroVec, List.all_eq_true, ofField_isZero, decide_eq_true_eq]
  constructor
  · intro h; funext i; exact h i (hidx i)
  · rintro rfl; simp

/-! ### Pivoted bases -/

def spanB (bs : List (ι × (ι → K))) : Submodule K (ι → K) :=
  Submodule.span K {v | ∃ pb ∈ bs, pb.2 = v}

def Pivoted (bs : List (ι × (ι → K))) : Prop :=
  (bs.map Prod.fst).Nodup ∧ (∀ pb ∈ bs, pb.2 pb.1 = 1) ∧
    (∀ pb ∈ bs, ∀ pb' ∈ bs, pb.1 ≠ pb'.1 → pb'.2 pb.1 = 0)

theorem mem_spanB {bs : List (ι × (ι → K))} {pb : ι × (ι → K)} (h : pb ∈ bs) :
    pb.2 ∈ spanB bs :=
  Submodule.subset_span ⟨pb, h, rfl⟩

theorem Pivoted.inj {bs : List (ι × (ι → K))} (hP : Pivoted bs) {x y : ι × (ι → K)}
    (hx : x ∈ bs) (hy : y ∈ bs) (hxy : x.1 = y.1) : x = y :=
  List.inj_on_of_nodup_map hP.1 hx hy hxy

theorem reduceBy_cons (pb : ι × (ι → K)) (bs : List (ι × (ι → K))) (v : ι → K) :
    reduceBy O (pb :: bs) v = reduceBy O bs (v - v pb.1 • pb.2) := by
  simp [reduceBy, axpy_field]

theorem reduceBy_sub_mem (bs : List (ι × (ι → K))) (v : ι → K) :
    v - reduceBy O bs v ∈ spanB bs := by
  induction bs generalizing v with
  | nil => simp [reduceBy]
  | cons pb bs ih =>
    rw [reduceBy_cons]
    have h1 : v - reduceBy O bs (v - v pb.1 • pb.2) =
        v pb.1 • pb.2 + ((v - v pb.1 • pb.2) - reduceBy O bs (v - v pb.1 • pb.2)) := by abel
    rw [h1]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_spanB List.mem_cons_self)) ?_
    have := ih (v - v pb.1 • pb.2)
    exact Submodule.span_mono (by
      rintro x ⟨y, hy, hyx⟩; exact ⟨y, List.mem_cons_of_mem _ hy, hyx⟩) this

theorem reduceBy_pivots_zero {L : List (ι × (ι → K))} (hP : Pivoted L) :
    ∀ (bs S : List (ι × (ι → K))) (v : ι → K), (∀ x ∈ bs, x ∈ L) → (∀ x ∈ S, x ∈ L) →
      (∀ x ∈ S, v x.1 = 0) → ∀ x, (x ∈ S ∨ x ∈ bs) → reduceBy O bs v x.1 = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro S v _ _ hv x hx
    rcases hx with hx | hx
    · exact hv x hx
    · simp at hx
  | cons pb bs ih =>
    intro S v hbs hS hv x hx
    rw [reduceBy_cons]
    have hpbL : pb ∈ L := hbs pb List.mem_cons_self
    apply ih (pb :: S) _ (fun y hy => hbs y (List.mem_cons_of_mem _ hy))
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hpbL
      · exact hS y hy
    · intro y hy
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hP.2.1 _ hpbL]; ring
      · by_cases hyp : y.1 = pb.1
        · rw [hyp, hP.2.1 _ hpbL]; have := hv y hy; rw [hyp] at this; rw [this]; ring
        · rw [hv y hy, hP.2.2 y (hS y hy) pb hpbL hyp]; ring
    · rcases hx with hx | hx
      · exact Or.inl (List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl List.mem_cons_self
        · exact Or.inr hx

theorem reduceBy_pivot_eq_zero {bs : List (ι × (ι → K))} (hP : Pivoted bs) (v : ι → K)
    {pb : ι × (ι → K)} (h : pb ∈ bs) : reduceBy O bs v pb.1 = 0 :=
  reduceBy_pivots_zero hP bs [] v (fun _ hx => hx) (by simp) (by simp) pb (Or.inr h)

/-- Elements of the span are determined by their pivot coordinates. -/
theorem eq_zero_of_pivots {bs : List (ι × (ι → K))} (hP : Pivoted bs) {u : ι → K}
    (hu : u ∈ spanB bs) (hz : ∀ pb ∈ bs, u pb.1 = 0) : u = 0 := by
  classical
  let E : (ι → K) →ₗ[K] (ι → K) :=
    LinearMap.id - ∑ pb ∈ bs.toFinset, (LinearMap.proj pb.1).smulRight pb.2
  have hE : ∀ w, E w = w - ∑ pb ∈ bs.toFinset, w pb.1 • pb.2 := by
    intro w; simp [E, LinearMap.sum_apply]
  have hgen : spanB bs ≤ LinearMap.ker E := by
    apply Submodule.span_le.2
    rintro _ ⟨pb', hpb', rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hE]
    rw [Finset.sum_eq_single pb', hP.2.1 _ hpb', one_smul, sub_self]
    · intro pb hpb hne
      rw [hP.2.2 pb (List.mem_toFinset.1 hpb) pb' hpb'
        (fun h => hne (hP.inj (List.mem_toFinset.1 hpb) hpb' h)), zero_smul]
    · intro h; exact absurd (List.mem_toFinset.2 hpb') h
  have h1 := hgen hu
  rw [LinearMap.mem_ker, hE] at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  exact Finset.sum_eq_zero (fun pb hpb => by rw [hz pb (List.mem_toFinset.1 hpb), zero_smul])

theorem finrank_spanB {bs : List (ι × (ι → K))} [Fintype ι] (hP : Pivoted bs) :
    finrank K (spanB bs) = bs.length := by
  let g : Fin bs.length → (ι → K) := fun i => (bs.get i).2
  have hrange : {v | ∃ pb ∈ bs, pb.2 = v} = Set.range g := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_range, g]
    constructor
    · rintro ⟨pb, hpb, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hpb
      exact ⟨i, by rw [hi]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨bs.get i, List.get_mem _ _, rfl⟩
  have hli : LinearIndependent K g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc (bs.get i).1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · rwa [show g i (bs.get i).1 = 1 from hP.2.1 _ (List.get_mem _ _), mul_one] at this
    · intro j _ hji
      have hne : (bs.get i).1 ≠ (bs.get j).1 := by
        intro h
        apply hji
        have := (List.Nodup.get_inj_iff hP.1 (i := ⟨j, by simp⟩) (j := ⟨i, by simp⟩)).1
          (by simpa using h.symm)
        exact Fin.ext (by simpa using congrArg Fin.val this)
      rw [show g j (bs.get i).1 = 0 from
        hP.2.2 _ (List.get_mem _ _) _ (List.get_mem _ _) hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  unfold spanB
  rw [hrange, finrank_span_eq_card hli, Fintype.card_fin]

theorem Pivoted.linearIndependent {bs : List (ι × (ι → K))} (hP : Pivoted bs) :
    LinearIndependent K (fun i : Fin bs.length => (bs.get i).2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrFun hc (bs.get i).1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [Finset.sum_eq_single i] at this
  · rwa [hP.2.1 _ (List.get_mem _ _), mul_one] at this
  · intro j _ hji
    have hne : (bs.get i).1 ≠ (bs.get j).1 := by
      intro h
      apply hji
      have := (List.Nodup.get_inj_iff hP.1 (i := ⟨j, by simp⟩) (j := ⟨i, by simp⟩)).1
        (by simpa using h.symm)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    rw [hP.2.2 _ (List.get_mem _ _) _ (List.get_mem _ _) hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem spanB_eq_range (bs : List (ι × (ι → K))) :
    spanB bs = Submodule.span K (Set.range (fun i : Fin bs.length => (bs.get i).2)) := by
  unfold spanB
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨pb, hpb, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hpb
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨bs.get i, List.get_mem _ _, rfl⟩

/-! ### Insertion and RREF -/

theorem insertVec_spec {idx : List ι} (hidx : ∀ i, i ∈ idx) {bs : List (ι × (ι → K))}
    (hP : Pivoted bs) (v : ι → K) :
    Pivoted (insertVec O idx bs v) ∧ spanB (insertVec O idx bs v) = spanB bs ⊔ K ∙ v := by
  have hvr := reduceBy_sub_mem bs v
  set r := reduceBy O bs v with hr
  unfold insertVec
  rw [← hr]
  cases hfp : firstNZ O idx r with
  | none =>
    have hr0 : r = 0 := firstNZ_none hidx hfp
    refine ⟨hP, ?_⟩
    rw [hr0, sub_zero] at hvr
    symm
    rw [sup_eq_left, Submodule.span_singleton_le_iff_mem]
    exact hvr
  | some p =>
    have hrp : r p ≠ 0 := firstNZ_some hfp
    have hrpiv : ∀ pb ∈ bs, r pb.1 = 0 := fun pb h => reduceBy_pivot_eq_zero hP v h
    simp only [axpy_field, smul_field, ofField_inv]
    set w := (r p)⁻¹ • r with hw
    have hwp : w p = 1 := by simp [hw, inv_mul_cancel₀ hrp]
    have hwpiv : ∀ pb ∈ bs, w pb.1 = 0 := fun pb h => by simp [hw, hrpiv pb h]
    have hpnot : ∀ pb ∈ bs, pb.1 ≠ p := by
      intro pb h hpe; apply hrp; rw [← hpe]; exact hrpiv pb h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.map_append, List.map_map]
      have : (Prod.fst ∘ fun pb : ι × (ι → K) => (pb.1, pb.2 - pb.2 p • w)) = Prod.fst := rfl
      rw [this, List.nodup_append]
      refine ⟨hP.1, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 ha
      rw [hb]; exact hpnot pb hpb
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 hx
        simp [hP.2.1 pb hpb, hwpiv pb hpb]
      · simp only [List.mem_singleton] at hx; subst hx; exact hwp
    · intro x hx y hy hxy
      rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 hx
        obtain ⟨pb', hpb', rfl⟩ := List.mem_map.1 hy
        simp [hP.2.2 pb hpb pb' hpb' hxy, hwpiv pb hpb]
      · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 hx
        simp only [List.mem_singleton] at hy; subst hy
        exact hwpiv pb hpb
      · simp only [List.mem_singleton] at hx; subst hx
        obtain ⟨pb', hpb', rfl⟩ := List.mem_map.1 hy
        simp [hwp]
      · simp only [List.mem_singleton] at hx hy; subst hx; subst hy; exact absurd rfl hxy
    · -- spans
      have hrmem : r ∈ spanB bs ⊔ K ∙ v := by
        have : r = v - (v - r) := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
          (Submodule.mem_sup_left hvr)
      have hwmem : w ∈ spanB bs ⊔ K ∙ v := Submodule.smul_mem _ _ hrmem
      apply le_antisymm
      · apply Submodule.span_le.2
        rintro _ ⟨x, hx, rfl⟩
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.1 hx
          exact Submodule.sub_mem _ (Submodule.mem_sup_left (mem_spanB hpb))
            (Submodule.smul_mem _ _ hwmem)
        · simp only [List.mem_singleton] at hx; subst hx; exact hwmem
      · set nb := bs.map (fun pb : ι × (ι → K) => (pb.1, pb.2 - pb.2 p • w)) ++ [(p, w)]
        have hwnb : w ∈ spanB nb := mem_spanB (List.mem_append_right _ List.mem_cons_self)
        apply sup_le
        · apply Submodule.span_le.2
          rintro _ ⟨pb, hpb, rfl⟩
          have h1 : pb.2 - pb.2 p • w ∈ spanB nb :=
            mem_spanB (pb := (pb.1, pb.2 - pb.2 p • w))
              (List.mem_append_left _ (List.mem_map.2 ⟨pb, hpb, rfl⟩))
          have : pb.2 = (pb.2 - pb.2 p • w) + pb.2 p • w := by abel
          rw [SetLike.mem_coe, this]
          exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ hwnb)
        · rw [Submodule.span_singleton_le_iff_mem]
          have hbs : spanB bs ≤ spanB nb := by
            apply Submodule.span_le.2
            rintro _ ⟨pb, hpb, rfl⟩
            have h1 : pb.2 - pb.2 p • w ∈ spanB nb :=
              mem_spanB (pb := (pb.1, pb.2 - pb.2 p • w))
                (List.mem_append_left _ (List.mem_map.2 ⟨pb, hpb, rfl⟩))
            have : pb.2 = (pb.2 - pb.2 p • w) + pb.2 p • w := by abel
            rw [SetLike.mem_coe, this]
            exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ hwnb)
          have hrw : r = r p • w := by
            rw [hw, smul_smul, mul_inv_cancel₀ hrp, one_smul]
          have : v = (v - r) + r p • w := by rw [← hrw]; abel
          rw [this]
          exact Submodule.add_mem _ (hbs hvr) (Submodule.smul_mem _ _ hwnb)

def spanL (vs : List (ι → K)) : Submodule K (ι → K) := Submodule.span K {v | v ∈ vs}

theorem rref_spec {idx : List ι} (hidx : ∀ i, i ∈ idx) (vs : List (ι → K)) :
    Pivoted (rref O idx vs) ∧ spanB (rref O idx vs) = spanL vs := by
  unfold rref
  suffices H : ∀ bs : List (ι × (ι → K)), Pivoted bs →
      Pivoted (vs.foldl (insertVec O idx) bs) ∧
        spanB (vs.foldl (insertVec O idx) bs) = spanB bs ⊔ spanL vs by
    have h0 : Pivoted ([] : List (ι × (ι → K))) := ⟨List.nodup_nil, by simp, by simp⟩
    obtain ⟨h1, h2⟩ := H [] h0
    refine ⟨h1, ?_⟩
    rw [h2]
    have : spanB ([] : List (ι × (ι → K))) = ⊥ := by simp [spanB]
    rw [this, bot_sup_eq]
  induction vs with
  | nil => intro bs hP; exact ⟨hP, by simp [spanL]⟩
  | cons v vs ih =>
    intro bs hP
    obtain ⟨hP', hspan'⟩ := insertVec_spec hidx hP v
    obtain ⟨h1, h2⟩ := ih _ hP'
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons]
    rw [h2, hspan']
    have : spanL (v :: vs) = K ∙ v ⊔ spanL vs := by
      unfold spanL
      rw [← Submodule.span_insert]
      congr 1
      ext x; simp
    rw [this, sup_assoc]

theorem rank_eq_finrank_span [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx)
    (vs : List (ι → K)) : rank O idx vs = finrank K (spanL vs) := by
  obtain ⟨hP, hs⟩ := rref_spec hidx vs
  rw [rank, ← finrank_spanB hP, hs]

/-! ### Kernel vectors -/

theorem find_pivot {bs : List (ι × (ι → K))} (hP : Pivoted bs) {pb : ι × (ι → K)}
    (h : pb ∈ bs) : bs.find? (fun x => decide (x.1 = pb.1)) = some pb := by
  cases hf : bs.find? (fun x => decide (x.1 = pb.1)) with
  | none =>
    have := List.find?_eq_none.1 hf pb h
    simp at this
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [hP.inj hx h hp]

theorem freeCol_spec {idx : List ι} {bs : List (ι × (ι → K))} {c : ι}
    (h : freeCol idx bs = some c) : ∀ pb ∈ bs, pb.1 ≠ c := by
  have := List.find?_some h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, decide_eq_true_eq] at this
  intro pb hpb hpc
  exact this pb hpb hpc

theorem freeCol_exists [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx)
    {bs : List (ι × (ι → K))} (hP : Pivoted bs) (hlt : bs.length < Fintype.card ι) :
    ∃ c, freeCol idx bs = some c := by
  classical
  cases hf : freeCol idx bs with
  | some c => exact ⟨c, rfl⟩
  | none =>
    exfalso
    have hall : ∀ i, i ∈ bs.map Prod.fst := by
      intro i
      have := List.find?_eq_none.1 hf i (hidx i)
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, List.any_eq_true,
        decide_eq_true_eq] at this
      obtain ⟨pb, hpb, rfl⟩ := this
      exact List.mem_map.2 ⟨pb, hpb, rfl⟩
    have : (Finset.univ : Finset ι) ⊆ (bs.map Prod.fst).toFinset := fun i _ =>
      List.mem_toFinset.2 (hall i)
    have h1 := Finset.card_le_card this
    rw [Finset.card_univ, List.toFinset_card_of_nodup hP.1, List.length_map] at h1
    omega

theorem kerVec_self (bs : List (ι × (ι → K))) (c : ι) : kerVec O bs c c = 1 := by
  simp [kerVec]

theorem kerVec_row [Fintype ι] {bs : List (ι × (ι → K))} (hP : Pivoted bs) {c : ι}
    (hc : ∀ pb ∈ bs, pb.1 ≠ c) {pb : ι × (ι → K)} (hpb : pb ∈ bs) :
    ∑ i, pb.2 i * kerVec O bs c i = 0 := by
  have key : ∀ i, pb.2 i * kerVec O bs c i =
      (if i = c then pb.2 c else 0) - (if i = pb.1 then pb.2 c else 0) := by
    intro i
    by_cases hic : i = c
    · subst hic
      rw [kerVec_self, if_pos rfl, if_neg (fun h => hc pb hpb h.symm)]; ring
    · rw [if_neg hic]
      simp only [kerVec, hic, if_false]
      by_cases hex : ∃ pb' ∈ bs, pb'.1 = i
      · obtain ⟨pb', hpb', rfl⟩ := hex
        rw [find_pivot hP hpb']
        by_cases hpp : pb' = pb
        · subst hpp; simp [hP.2.1 _ hpb']
        · have hne : pb'.1 ≠ pb.1 := fun h => hpp (hP.inj hpb' hpb h)
          simp [hP.2.2 pb' hpb' pb hpb hne, hne]
      · have hnone : bs.find? (fun x => decide (x.1 = i)) = none := by
          apply List.find?_eq_none.2
          intro x hx; simp only [decide_eq_true_eq]; exact fun h => hex ⟨x, hx, h⟩
        rw [hnone]
        have : i ≠ pb.1 := fun h => hex ⟨pb, hpb, h.symm⟩
        simp [this]
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem kerVec_orth [Fintype ι] {bs : List (ι × (ι → K))} (hP : Pivoted bs) {c : ι}
    (hc : ∀ pb ∈ bs, pb.1 ≠ c) {u : ι → K} (hu : u ∈ spanB bs) :
    ∑ i, u i * kerVec O bs c i = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨pb, hpb, rfl⟩ := hx
    exact kerVec_row hP hc hpb
  | zero => simp
  | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
  | smul a x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]

/-! ### Dot products, linear combinations, matrices -/

theorem dot_eq_list_sum (idx : List ι) (v w : ι → K) :
    dot O idx v w = (idx.map (fun i => v i * w i)).sum := by
  induction idx with
  | nil => simp [dot]
  | cons i idx ih => simp only [dot, List.foldr_cons] at ih ⊢; rw [ih]; simp

theorem list_sum_eq_univ [Fintype ι] {M : Type} [AddCommMonoid M] {idx : List ι}
    (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup) (g : ι → M) :
    (idx.map g).sum = ∑ i, g i := by
  rw [← List.sum_toFinset g hnd]
  congr 1
  ext i; simp [hidx i]

theorem dot_field [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx) (hnd : idx.Nodup)
    (v w : ι → K) : dot O idx v w = ∑ i, v i * w i := by
  rw [dot_eq_list_sum, list_sum_eq_univ hidx hnd]

theorem lincomb_eq_list_sum {κ : Type} (idxK : List κ) (x : κ → K) (B : κ → ι → K) (i : ι) :
    lincomb O idxK x B i = (idxK.map (fun a => x a * B a i)).sum := by
  simp only [lincomb]
  induction idxK with
  | nil => simp
  | cons a idxK ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons]; rw [ih]; rfl

theorem lincomb_field {κ : Type} [Fintype κ] {idxK : List κ} (hidx : ∀ a, a ∈ idxK)
    (hnd : idxK.Nodup) (x : κ → K) (B : κ → ι → K) :
    lincomb O idxK x B = ∑ a, x a • B a := by
  classical
  funext i
  rw [lincomb_eq_list_sum, list_sum_eq_univ hidx hnd, Finset.sum_apply]
  simp

theorem finRange_complete (n : ℕ) : ∀ i : Fin n, i ∈ List.finRange n := List.mem_finRange

theorem matMul_field {n : ℕ} (X Y : Matrix (Fin n) (Fin n) K) :
    matMul O X Y = (X * Y : Matrix (Fin n) (Fin n) K) := by
  funext i j
  simp only [matMul]
  rw [dot_field (finRange_complete n) (List.nodup_finRange n)]
  rfl

theorem matOne_field {n : ℕ} : matOne O = (1 : Matrix (Fin n) (Fin n) K) := by
  funext i j
  by_cases h : i = j
  · subst h; simp [matOne]
  · simp [matOne, h, Matrix.one_apply_ne h]

theorem matPow_field {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    matPow O X k = (X ^ k : Matrix (Fin n) (Fin n) K) := by
  induction k with
  | zero => rw [pow_zero]; exact matOne_field
  | succ k ih =>
    show matMul O (matPow O X k) X = (X ^ (k + 1) : Matrix (Fin n) (Fin n) K)
    rw [ih, matMul_field, pow_succ]

theorem traceMul_field {n : ℕ} (X Y : Matrix (Fin n) (Fin n) K) :
    traceMul O X Y = (X * Y).trace := by
  simp only [traceMul]
  rw [dot_field (finRange_complete n) (List.nodup_finRange n)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ofField_one, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  rw [dot_field (finRange_complete n) (List.nodup_finRange n)]

end Mathproof.P15RecogLinAlg20261007
