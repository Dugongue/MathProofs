import EvenP6CellsProjector

/-! Problem 1.7's checked scalar refinement over an arbitrary finite
commutative algebra, with the physical driver dependencies removed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.CellProducer
open Module
open scoped BigOperators

variable {K A : Type*} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] [DecidableEq A]

private theorem list_sum_filter_ne_zero (xs : List A) :
    (xs.filter (fun x => decide (x ≠ 0))).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    by_cases h : x = 0
    · rw [if_neg (by simp [h]), ih, List.sum_cons, h, zero_add]
    · rw [if_pos (by simp [h]), List.sum_cons, List.sum_cons, ih]

private theorem list_sum_flatMap (xs : List A) (f : A → List A) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sum_append, ih]


def pieces (enum : Fin (Fintype.card K) ≃ K) (x e : A) : List A :=
  (List.ofFn fun i => e * projector x (enum i)).filter fun z => decide (z ≠ 0)

def refine (enum : Fin (Fintype.card K) ≃ K) (x : A) (es : List A) : List A :=
  es.flatMap (pieces enum x)

def IsPartition (es : List A) : Prop :=
  (∀ e ∈ es, e ≠ 0 ∧ e*e=e) ∧ es.Pairwise (fun a b => a*b=0) ∧ es.sum=1

def ActsScalar (x : A) (es : List A) : Prop :=
  ∀ e ∈ es, ∃ c : K, x*e=algebraMap K A c*e

theorem mem_pieces {enum : Fin (Fintype.card K) ≃ K} {x e z : A} :
    z ∈ pieces enum x e ↔ z ≠ 0 ∧ ∃ c : K, e*projector x c=z := by
  simp only [pieces, List.mem_filter, decide_eq_true_eq, List.mem_ofFn]
  constructor
  · rintro ⟨⟨i, hi⟩, hn⟩
    exact ⟨hn, enum i, hi⟩
  · rintro ⟨hn, c, hc⟩
    exact ⟨⟨enum.symm c, by simpa using hc⟩, hn⟩

theorem pieces_sum (enum : Fin (Fintype.card K) ≃ K) (x e : A)
    (hx : x ^ Fintype.card K = x) (he : e*e=e) : (pieces enum x e).sum=e := by
  rw [pieces, list_sum_filter_ne_zero, List.sum_ofFn]
  exact (Equiv.sum_comp enum (fun c => e * projector x c)).trans (projector_partition x hx e he).1

theorem pieces_orthogonal (enum : Fin (Fintype.card K) ≃ K) (x e : A)
    (hx : x ^ Fintype.card K = x) (he : e*e=e) :
    (pieces enum x e).Pairwise (fun a b => a*b=0) := by
  unfold pieces
  apply List.Pairwise.filter
  rw [List.pairwise_iff_get]
  intro i j hij
  simp only [List.get_ofFn]
  apply (projector_partition x hx e he).2.1
  intro h
  have hi : i.val = j.val := by
    simpa only [Fin.val_cast] using congrArg Fin.val (enum.injective h)
  exact (ne_of_lt hij) (Fin.ext hi)

theorem refine_partition (enum : Fin (Fintype.card K) ≃ K) (x : A)
    (hx : x ^ Fintype.card K = x) {es : List A} (he : IsPartition es) :
    IsPartition (refine enum x es) := by
  obtain ⟨hn, ho, hsum⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, hmem⟩ := List.mem_flatMap.mp he
    obtain ⟨hne, c, rfl⟩ := mem_pieces.mp hmem
    exact ⟨hne, (projector_partition x hx a (hn a ha).2).2.2.1 c⟩
  · rw [refine, List.pairwise_flatMap]
    refine ⟨fun a ha => pieces_orthogonal enum x a hx (hn a ha).2, ho.imp ?_⟩
    intro a b hab u hu v hv
    obtain ⟨_, c, rfl⟩ := mem_pieces.mp hu
    obtain ⟨_, d, rfl⟩ := mem_pieces.mp hv
    calc
      (a*projector x c)*(b*projector x d) = (a*b)*(projector x c*projector x d) := by ring
      _ = 0 := by rw [hab, zero_mul]
  · rw [refine, list_sum_flatMap]
    have hm : es.map (fun a => (pieces enum x a).sum) = es := by
      calc
        _ = es.map id := List.map_congr_left (fun a ha => pieces_sum enum x a hx (hn a ha).2)
        _ = es := List.map_id _
    rw [hm, hsum]

theorem refine_scalar (enum : Fin (Fintype.card K) ≃ K) (x : A)
    (hx : x ^ Fintype.card K = x) {es : List A} (he : IsPartition es) :
    ActsScalar (K := K) x (refine enum x es) := by
  intro z hz
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hz
  obtain ⟨_, c, rfl⟩ := mem_pieces.mp hm
  exact ⟨c, (projector_partition x hx a (he.1 a ha).2).2.2.2 c⟩

theorem refine_preserve_scalar (enum : Fin (Fintype.card K) ≃ K) (x y : A)
    {es : List A} (hy : ActsScalar (K := K) y es) : ActsScalar (K := K) y (refine enum x es) := by
  intro z hz
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hz
  obtain ⟨_, c, rfl⟩ := mem_pieces.mp hm
  obtain ⟨b, hb⟩ := hy a ha
  refine ⟨b, ?_⟩
  rw [← mul_assoc, hb, mul_assoc]

def run (enum : Fin (Fintype.card K) ≃ K) (xs : List A) (es : List A) : List A :=
  xs.foldl (fun es x => refine enum x es) es

theorem run_partition (enum : Fin (Fintype.card K) ≃ K) (xs : List A)
    (hx : ∀ x ∈ xs, x ^ Fintype.card K = x) {es : List A} (he : IsPartition es) :
    IsPartition (run enum xs es) := by
  induction xs generalizing es with
  | nil => exact he
  | cons x xs ih =>
    exact ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (refine_partition enum x (hx x (by simp)) he)

theorem run_preserve_scalar (enum : Fin (Fintype.card K) ≃ K) (xs : List A) (x : A)
    {es : List A} (h : ActsScalar (K := K) x es) : ActsScalar (K := K) x (run enum xs es) := by
  induction xs generalizing es with
  | nil => exact h
  | cons y ys ih => exact ih (refine_preserve_scalar enum y x h)

theorem run_acts_scalar (enum : Fin (Fintype.card K) ≃ K) (xs : List A)
    (hx : ∀ x ∈ xs, x ^ Fintype.card K = x) {es : List A} (he : IsPartition es) :
    ∀ x ∈ xs, ActsScalar (K := K) x (run enum xs es) := by
  induction xs generalizing es with
  | nil => simp
  | cons x xs ih =>
    have hfix := hx x (by simp)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact run_preserve_scalar enum xs y (refine_scalar enum y hfix he)
    · exact ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (refine_partition enum x hfix he) y hy

theorem get_orthogonal {es : List A} (h : IsPartition es)
    (i j : Fin es.length) (hij : i ≠ j) : es.get i * es.get j = 0 := by
  rcases lt_or_gt_of_ne hij with hl | hg
  · exact List.pairwise_iff_get.mp h.2.1 i j hl
  · rw [mul_comm]
    exact List.pairwise_iff_get.mp h.2.1 j i hg

theorem partition_length_le [FiniteDimensional K A] {es : List A}
    (h : IsPartition es) : es.length ≤ finrank K A := by
  classical
  have hli : LinearIndependent K es.get := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have hh := congrArg (fun x : A => x * es.get j) hc
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at hh
    rw [Finset.sum_eq_single j] at hh
    · rw [(h.1 _ (List.get_mem es j)).2] at hh
      exact (smul_eq_zero.mp hh).resolve_right (h.1 _ (List.get_mem es j)).1
    · intro i _ hij
      rw [get_orthogonal h i j hij, smul_zero]
    · simp
  simpa using hli.fintype_card_le_finrank

#print axioms run_partition
#print axioms run_acts_scalar
#print axioms partition_length_le

end EvenTI.CellProducer
