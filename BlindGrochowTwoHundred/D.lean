import Mathlib

namespace TwoHundred.Coverage

open Finset
open scoped BigOperators

section FinitePanels
variable {S T U : Type*} [DecidableEq S] [DecidableEq T] [DecidableEq U]

def succeeds (G : S → T → Prop) [DecidableRel G] (panel : Finset S) (t : T) : Finset S :=
  panel.filter (fun s => G s t)

def misses (G : S → T → Prop) [DecidableRel G] (panel : Finset S) (t : T) : Finset S :=
  panel.filter (fun s => ¬ G s t)

variable (G : S → T → Prop) [DecidableRel G]

private theorem mem_hit {P : Finset S} {s : S} {t : T} :
    s ∈ succeeds G P t ↔ s ∈ P ∧ G s t := by simp [succeeds]

private theorem mem_miss {P : Finset S} {s : S} {t : T} :
    s ∈ misses G P t ↔ s ∈ P ∧ ¬ G s t := by simp [misses]

private theorem misses_sdiff (P : Finset S) (t : T) :
    misses G P t = P \ succeeds G P t := by
  ext x
  simp only [mem_miss, mem_sdiff, mem_hit]
  tauto

private theorem hit_card_add_miss_card (P : Finset S) (t : T) :
    (succeeds G P t).card + (misses G P t).card = P.card := by
  rw [misses_sdiff]
  rw [Nat.add_comm]
  exact card_sdiff_add_card_eq_card (filter_subset _ _)

/-- Exact robustness criterion for arbitrary admissible erasures. -/
theorem erasure_robust_iff (P : Finset S) (R : Finset T) (k : ℕ) :
    (∀ E : Finset S, E.card ≤ k → ∀ t ∈ R, ∃ s ∈ P \ E, G s t) ↔
    ∀ t ∈ R, k < (succeeds G P t).card := by
  constructor
  · intro h t ht
    by_contra! hn
    obtain ⟨s, hs, hg⟩ := h (succeeds G P t) hn t ht
    exact (mem_sdiff.mp hs).2 ((mem_hit G).mpr ⟨(mem_sdiff.mp hs).1, hg⟩)
  · intro h E he t ht
    have hle : ¬ succeeds G P t ⊆ E := fun hsub => (Nat.not_le_of_lt (h t ht)) ((card_le_card hsub).trans he)
    obtain ⟨s, hs, hn⟩ := not_subset.mp hle
    exact ⟨s, mem_sdiff.mpr ⟨((mem_hit G).mp hs).1, hn⟩, ((mem_hit G).mp hs).2⟩

/-- Requiring several surviving seeds after every erasure is also an exact cardinal criterion. -/
theorem multiplicity_after_erasures_iff (P : Finset S) (R : Finset T) (k r : ℕ)
    (hr : 0 < r) :
    (∀ E : Finset S, E.card ≤ k → ∀ t ∈ R, r ≤ (succeeds G (P \ E) t).card) ↔
      ∀ t ∈ R, k + r ≤ (succeeds G P t).card := by
  have change_set (E : Finset S) (t : T) : succeeds G (P \ E) t = succeeds G P t \ E := by
    ext s
    simp only [mem_hit, mem_sdiff]
    tauto
  constructor
  · intro h t ht
    let H := succeeds G P t
    have nonempty : k < H.card := by
      by_contra! hn
      have hv := h H hn t ht
      rw [change_set] at hv
      change r ≤ (H \ H).card at hv
      have : r = 0 := by simpa using hv
      omega
    obtain ⟨E, hE, hcard⟩ := Finset.exists_subset_card_eq (s := H) nonempty.le
    have hv := h E hcard.le t ht
    rw [change_set] at hv
    have ha := card_sdiff_add_card_eq_card hE
    change r ≤ (H \ E).card at hv
    change k + r ≤ H.card
    omega
  · intro h E he t ht
    have hc := h t ht
    rw [change_set]
    have hbound := Finset.card_le_card (show succeeds G P t ⊆ (succeeds G P t \ E) ∪ E by
      intro x hx
      by_cases hex : x ∈ E
      · exact mem_union_right _ hex
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hex⟩))
    have hsum := Finset.card_union_le (succeeds G P t \ E) E
    omega

/-- With heterogeneous nonnegative erasure costs, the least attack deletes the full
successful fiber, yielding the exact cost of disabling a chosen target. -/
theorem weighted_erasure_robust_iff (P : Finset S) (R : Finset T) (cost : S → ℕ) (budget : ℕ) :
    (∀ E : Finset S, (∑ s ∈ E, cost s) ≤ budget → ∀ t ∈ R, ∃ s ∈ P \ E, G s t) ↔
      ∀ t ∈ R, budget < ∑ s ∈ succeeds G P t, cost s := by
  constructor
  · intro h t ht
    by_contra! hn
    obtain ⟨s, hs, hg⟩ := h (succeeds G P t) hn t ht
    exact (mem_sdiff.mp hs).2 ((mem_hit G).mpr ⟨(mem_sdiff.mp hs).1, hg⟩)
  · intro h E he t ht
    have hsub : ¬ succeeds G P t ⊆ E := by
      intro hs
      exact (Nat.not_le_of_lt (h t ht)) ((Finset.sum_le_sum_of_subset hs).trans he)
    obtain ⟨s, hs, hn⟩ := not_subset.mp hsub
    exact ⟨s, mem_sdiff.mpr ⟨((mem_hit G).mp hs).1, hn⟩, ((mem_hit G).mp hs).2⟩

/-- Simultaneous disabling of several test targets has an exact cost certificate
given by the weighted union of successful fibers. -/
theorem disable_many_iff (P : Finset S) (R : Finset T) (cost : S → ℕ) (budget : ℕ) :
    (∃ E : Finset S, (∑ s ∈ E, cost s) ≤ budget ∧ ∀ t ∈ R, ∀ s ∈ P \ E, ¬ G s t) ↔
      (∑ s ∈ R.biUnion (succeeds G P), cost s) ≤ budget := by
  constructor
  · rintro ⟨E, he, h⟩
    apply le_trans (Finset.sum_le_sum_of_subset ?_) he
    intro s hs
    obtain ⟨t, ht, hg⟩ := mem_biUnion.mp hs
    obtain ⟨hp, hgt⟩ := (mem_hit G).mp hg
    by_contra hn
    exact h t ht s (mem_sdiff.mpr ⟨hp, hn⟩) hgt
  · intro h
    refine ⟨R.biUnion (succeeds G P), h, ?_⟩
    intro t ht s hs hg
    exact (mem_sdiff.mp hs).2 (mem_biUnion.mpr ⟨t, ht, (mem_hit G).mpr ⟨(mem_sdiff.mp hs).1, hg⟩⟩)

/-- Protection against two separate erasure budgets reduces to their sum, with no slack. -/
theorem separate_budgets_iff (P : Finset S) (R : Finset T) (a b : ℕ) :
    (∀ E F : Finset S, E.card ≤ a → F.card ≤ b →
      ∀ t ∈ R, ∃ s ∈ P \ (E ∪ F), G s t) ↔
      ∀ t ∈ R, a + b < (succeeds G P t).card := by
  constructor
  · intro h
    apply (erasure_robust_iff G P R (a + b)).1
    intro E he
    by_cases hs : E.card ≤ a
    · simpa using h E ∅ hs (by simp)
    · obtain ⟨F, hF, ha⟩ := Finset.exists_subset_card_eq (s := E) (by omega : a ≤ E.card)
      have eq : F ∪ (E \ F) = E := by
        ext s
        simp only [mem_union, mem_sdiff]
        exact ⟨fun h => h.elim (fun hs => hF hs) And.left,
          fun h => by by_cases hx : s ∈ F; exact Or.inl hx; exact Or.inr ⟨h,hx⟩⟩
      rw [← eq]
      have hc := Finset.card_sdiff_add_card_eq_card hF
      exact h F (E \ F) ha.le (by omega)
  · intro h E F he hf
    exact (erasure_robust_iff G P R (a+b)).2 h _ ((Finset.card_union_le _ _).trans (add_le_add he hf))

/-- Even overlapping panels add coverage after subtracting their shared success fiber. -/
theorem exact_union_overlap (P Q : Finset S) (t : T) :
    (succeeds G (P ∪ Q) t).card + (succeeds G (P ∩ Q) t).card =
      (succeeds G P t).card + (succeeds G Q t).card := by
  have hu : succeeds G (P ∪ Q) t = succeeds G P t ∪ succeeds G Q t := by
    ext s; simp only [mem_hit, mem_union]; tauto
  have hi : succeeds G (P ∩ Q) t = succeeds G P t ∩ succeeds G Q t := by
    ext s; simp only [mem_hit, mem_inter]; tauto
  rw [hu, hi, card_union_add_card_inter]

/-- A panel with sufficiently high individual success always has a common seed
for any demanded subcollection whose total failure cost is small. -/
theorem common_seed_of_few_failures (P : Finset S) (R : Finset T)
    (h : (∑ t ∈ R, (misses G P t).card) < P.card) :
    ∃ s ∈ P, ∀ t ∈ R, G s t := by
  let bad := R.biUnion (misses G P)
  have hb : bad.card < P.card := (Finset.card_biUnion_le.trans_lt h)
  have hn : ¬ P ⊆ bad := fun hsub => (Nat.not_le_of_lt hb) (card_le_card hsub)
  obtain ⟨s, hs, hnot⟩ := not_subset.mp hn
  refine ⟨s, hs, ?_⟩
  intro t ht
  by_contra hg
  exact hnot (mem_biUnion.mpr ⟨t, ht, (mem_miss G).mpr ⟨hs, hg⟩⟩)

/-- If all demands have the same successful fraction bound, a single seed
can satisfy the entire finite demand list under the counting threshold. -/
theorem common_seed_of_uniform_deficit (P : Finset S) (R : Finset T) (b : ℕ)
    (hb : ∀ t ∈ R, (misses G P t).card ≤ b) (h : R.card * b < P.card) :
    ∃ s ∈ P, ∀ t ∈ R, G s t := by
  apply common_seed_of_few_failures G P R
  exact (Finset.sum_le_sum hb).trans_lt (by simpa using h)

/-- A robust panel gives a robust common witness when the sum of failures and
the adversary budget leave a strict margin. -/
theorem simultaneous_after_erasures (P : Finset S) (R : Finset T) (k : ℕ)
    (h : (∑ t ∈ R, (misses G P t).card) + k < P.card)
    (E : Finset S) (hE : E.card ≤ k) : ∃ s ∈ P \ E, ∀ t ∈ R, G s t := by
  let bad := R.biUnion (misses G P) ∪ E
  have hc₁ : bad.card ≤ (R.biUnion (misses G P)).card + E.card := card_union_le _ _
  have hc₂ : (R.biUnion (misses G P)).card ≤ ∑ t ∈ R, (misses G P t).card := card_biUnion_le
  have hn : ¬ P ⊆ bad := by intro hs; have := card_le_card hs; omega
  obtain ⟨s, hs, hn⟩ := not_subset.mp hn
  refine ⟨s, mem_sdiff.mpr ⟨hs, fun e => hn (mem_union_right _ e)⟩, ?_⟩
  intro t ht
  by_contra hg
  exact hn (mem_union_left _ (mem_biUnion.mpr ⟨t, ht, (mem_miss G).mpr ⟨hs, hg⟩⟩))

/-- Positivity of the full incidence relation can be compressed to one
seed per demand, regardless of the original number of seeds. -/
theorem one_seed_per_target (P : Finset S) (R : Finset T)
    (h : ∀ t ∈ R, ∃ s ∈ P, G s t) :
    ∃ Q : Finset S, Q ⊆ P ∧ Q.card ≤ R.card ∧ ∀ t ∈ R, ∃ s ∈ Q, G s t := by
  classical
  let choose (t : R) := (h t t.property).choose
  have wit (t : R) : choose t ∈ P ∧ G (choose t) t := (h t t.property).choose_spec
  refine ⟨R.attach.image choose, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, _, rfl⟩ := mem_image.mp hs
    exact (wit t).1
  · simpa using Finset.card_image_le (s := R.attach) (f := choose)
  · intro t ht
    exact ⟨choose ⟨t,ht⟩, mem_image.mpr ⟨⟨t,ht⟩, mem_attach _ _, rfl⟩, (wit ⟨t,ht⟩).2⟩

/-- Independent nonempty choice in each demand yields a simultaneous certificate
of cardinality bounded by the required number of hits per demand. -/
theorem multiplicity_compression (P : Finset S) (R : Finset T) (q : ℕ)
    (h : ∀ t ∈ R, q ≤ (succeeds G P t).card) :
    ∃ Q : Finset S, Q ⊆ P ∧ Q.card ≤ R.card * q ∧
      ∀ t ∈ R, q ≤ (succeeds G Q t).card := by
  classical
  induction R using Finset.induction_on with
  | empty => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | @insert t R hn ih =>
    obtain ⟨Q, hQP, hQ, H⟩ := ih (fun x hx => h x (mem_insert_of_mem hx))
    obtain ⟨F, hF, hcard⟩ := exists_subset_card_eq (s := succeeds G P t) (h t (mem_insert_self _ _))
    refine ⟨Q ∪ F, union_subset hQP (hF.trans (filter_subset _ _)), ?_, ?_⟩
    · have hi := card_union_le Q F
      rw [card_insert_of_notMem hn, Nat.add_mul, Nat.one_mul]
      omega
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · rw [← hcard]
        apply card_le_card
        intro s hs
        exact (mem_hit G).mpr ⟨mem_union_right _ hs, ((mem_hit G).mp (hF hs)).2⟩
      · apply (H x hx).trans
        apply card_le_card
        intro s hs
        exact (mem_hit G).mpr ⟨mem_union_left _ ((mem_hit G).mp hs).1, ((mem_hit G).mp hs).2⟩

/-- A seed reindexing carrying the success relation preserves every exact erasure budget. -/
theorem reindex_preserves_incidence {S' T' : Type*} [DecidableEq S'] [DecidableEq T']
    (e : S ≃ S') (f : T ≃ T') (H : S' → T' → Prop) [DecidableRel H]
    (he : ∀ s t, H (e s) (f t) ↔ G s t) (P : Finset S) (t : T) :
    (succeeds H (P.map e.toEmbedding) (f t)).card = (succeeds G P t).card := by
  have hh : succeeds H (P.map e.toEmbedding) (f t) = (succeeds G P t).map e.toEmbedding := by
    ext s
    obtain ⟨x, rfl⟩ := e.surjective s
    simp only [mem_hit, mem_map, Equiv.toEmbedding_apply, e.injective.eq_iff, he, exists_eq_right]
  rw [hh, card_map]

end FinitePanels


section Greedy
variable {S T : Type*} [DecidableEq S] [DecidableEq T]
variable (G : S → T → Prop) [DecidableRel G]

def served (R : Finset T) (s : S) : Finset T := R.filter (G s)

def weight (w : T → ℕ) (R : Finset T) : ℕ := ∑ t ∈ R, w t

/-- Weighted coverage admits an exact dual count over the successful fibers. -/
theorem incidence_mass_identity (P : Finset S) (R : Finset T) (w : T → ℕ) :
    (∑ s ∈ P, weight w (served G R s)) =
      ∑ t ∈ R, (succeeds G P t).card * w t := by
  simp only [weight, served, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rfl

/-- A finite cover obeys every weighted capacity lower bound on its size. -/
theorem weighted_capacity_lower_bound (P : Finset S) (R : Finset T) (w : T → ℕ)
    (capacity multiplicity : ℕ)
    (hm : ∀ t ∈ R, multiplicity ≤ (succeeds G P t).card)
    (hc : ∀ s ∈ P, weight w (served G R s) ≤ capacity) :
    multiplicity * weight w R ≤ P.card * capacity := by
  calc
    _ = ∑ t ∈ R, multiplicity * w t := mul_sum ..
    _ ≤ ∑ t ∈ R, (succeeds G P t).card * w t := sum_le_sum (fun t ht => Nat.mul_le_mul_right _ (hm t ht))
    _ = ∑ s ∈ P, weight w (served G R s) := (incidence_mass_identity G _ _ _).symm
    _ ≤ ∑ _s ∈ P, capacity := sum_le_sum hc
    _ = _ := by simp

/-- A witness attaining at least the weighted average coverage always exists. -/
theorem weighted_greedy_step (P : Finset S) (R : Finset T) (w : T → ℕ) (q : ℕ)
    (hP : P.Nonempty) (h : ∀ t ∈ R, q ≤ (succeeds G P t).card) :
    ∃ s ∈ P, q * weight w R ≤ P.card * weight w (served G R s) := by
  obtain ⟨s, hs, hbest⟩ := Finset.exists_max_image P (fun s => weight w (served G R s)) hP
  exact ⟨s, hs, weighted_capacity_lower_bound G P R w _ q h hbest⟩

/-- The exact one-step bound on residual demand weight after greedy selection. -/
theorem greedy_weight_contraction (P : Finset S) (R : Finset T) (w : T → ℕ) (q : ℕ)
    (hP : P.Nonempty) (hq : q ≤ P.card) (h : ∀ t ∈ R, q ≤ (succeeds G P t).card) :
    ∃ s ∈ P, P.card * weight w (R.filter (fun t => ¬ G s t)) ≤ (P.card - q) * weight w R := by
  obtain ⟨s, hs, hrow⟩ := weighted_greedy_step G P R w q hP h
  refine ⟨s, hs, ?_⟩
  have he : weight w (served G R s) + weight w (R.filter (fun t => ¬ G s t)) = weight w R := by
    simp only [weight, served, sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    by_cases hG : G s t <;> simp [hG]
  have hn : P.card * weight w (served G R s) +
      P.card * weight w (R.filter (fun t => ¬ G s t)) = P.card * weight w R := by
    rw [← Nat.mul_add, he]
  have ha : (P.card - q) * weight w R + q * weight w R = P.card * weight w R := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hq]
  omega

def residual : List S → Finset T → Finset T
  | [], R => R
  | s :: tail, R => residual tail (R.filter (fun t => ¬ G s t))

private theorem mem_residual (seq : List S) (R : Finset T) (t : T) :
    t ∈ residual G seq R ↔ t ∈ R ∧ ∀ s ∈ seq, ¬ G s t := by
  induction seq generalizing R with
  | nil => simp [residual]
  | cons s seq ih =>
    simp only [residual, ih, mem_filter, List.mem_cons]
    constructor
    · rintro ⟨⟨ht, hs⟩, h⟩
      exact ⟨ht, fun z hz => hz.elim (fun e => e ▸ hs) (h z)⟩
    · rintro ⟨ht, h⟩
      exact ⟨⟨ht, h s (Or.inl rfl)⟩, fun z hz => h z (Or.inr hz)⟩

/-- Greedy selection quantifies the remaining demand weight after any prescribed number of stages. -/
theorem greedy_geometric_decay (P : Finset S) (R : Finset T) (w : T → ℕ) (q steps : ℕ)
    (hP : P.Nonempty) (hq : q ≤ P.card) (h : ∀ t ∈ R, q ≤ (succeeds G P t).card) :
    ∃ seq : List S, seq.length = steps ∧ (∀ s ∈ seq, s ∈ P) ∧
      P.card ^ steps * weight w (residual G seq R) ≤ (P.card - q) ^ steps * weight w R := by
  induction steps generalizing R with
  | zero => exact ⟨[], rfl, by simp, by simp [residual]⟩
  | succ n ih =>
    obtain ⟨s, hs, hstep⟩ := greedy_weight_contraction G P R w q hP hq h
    obtain ⟨tail, htail, hmem, hrec⟩ :=
      ih (R.filter (fun t => ¬ G s t)) (fun t ht => h t (mem_filter.mp ht).1)
    refine ⟨s :: tail, by simp [htail], ?_, ?_⟩
    · intro x hx
      exact (List.mem_cons.mp hx).elim (fun e => e ▸ hs) (hmem x)
    · change P.card ^ (n+1) * weight w (residual G tail (R.filter (fun t => ¬ G s t))) ≤ _
      rw [pow_succ, pow_succ]
      calc
        _ = P.card * (P.card ^ n * weight w (residual G tail (R.filter (fun t => ¬ G s t)))) := by ring
        _ ≤ P.card * ((P.card - q)^n * weight w (R.filter (fun t => ¬ G s t))) :=
          Nat.mul_le_mul_left _ hrec
        _ = (P.card - q)^n * (P.card * weight w (R.filter (fun t => ¬ G s t))) := by ring
        _ ≤ (P.card - q)^n * ((P.card - q) * weight w R) := Nat.mul_le_mul_left _ hstep
        _ = _ := by ring

/-- An explicit power inequality gives a small hitting panel independently of the ambient seed set. -/
theorem greedy_cover_at_power_bound (P : Finset S) (R : Finset T) (q steps : ℕ)
    (hP : P.Nonempty) (hq : q ≤ P.card) (h : ∀ t ∈ R, q ≤ (succeeds G P t).card)
    (hb : (P.card - q) ^ steps * R.card < P.card ^ steps) :
    ∃ seq : List S, seq.length = steps ∧ (∀ s ∈ seq, s ∈ P) ∧ ∀ t ∈ R, ∃ s ∈ seq, G s t := by
  obtain ⟨seq, hlen, hs, hdecay⟩ := greedy_geometric_decay G P R (fun _ => 1) q steps hP hq h
  have hc : P.card ^ steps * (residual G seq R).card < P.card ^ steps := by
    exact (show P.card ^ steps * (residual G seq R).card ≤ (P.card - q)^steps * R.card by
      simpa [weight] using hdecay).trans_lt hb
  have hz : (residual G seq R).card = 0 := by
    by_contra hn
    exact (not_le_of_gt hc) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn))
  refine ⟨seq, hlen, hs, ?_⟩
  intro t ht
  by_contra hn
  have ha : ∀ s ∈ seq, ¬ G s t := fun s hs hG => hn ⟨s, hs, hG⟩
  have hm := (mem_residual G seq R t).mpr ⟨ht, ha⟩
  rw [card_eq_zero.mp hz] at hm
  exact notMem_empty _ hm

/-- A joint test on product seeds has an exact factorized success count. -/
theorem product_success_count {S' T' : Type*} [DecidableEq S']
    (H : S' → T' → Prop) [DecidableRel H] (P : Finset S) (P' : Finset S') (t : T) (t' : T') :
    (succeeds (fun s u : _ => G s.1 u.1 ∧ H s.2 u.2) (P ×ˢ P') (t,t')).card =
      (succeeds G P t).card * (succeeds H P' t').card := by
  have eq : succeeds (fun s : S × S' => fun u : T × T' => G s.1 u.1 ∧ H s.2 u.2)
      (P ×ˢ P') (t,t') = (succeeds G P t) ×ˢ (succeeds H P' t') := by
    ext p
    simp only [succeeds, mem_filter, mem_product]
    tauto
  rw [eq, card_product]

/-- Combination by logical disjunction leaves exactly the product of the two miss counts. -/
theorem product_disjunctive_failure {S' T' : Type*} [DecidableEq S']
    (H : S' → T' → Prop) [DecidableRel H] (P : Finset S) (P' : Finset S') (t : T) (t' : T') :
    (misses (fun s : S × S' => fun u : T × T' => G s.1 u.1 ∨ H s.2 u.2)
      (P ×ˢ P') (t,t')).card = (misses G P t).card * (misses H P' t').card := by
  have eq : misses (fun s : S × S' => fun u : T × T' => G s.1 u.1 ∨ H s.2 u.2)
      (P ×ˢ P') (t,t') = (misses G P t) ×ˢ (misses H P' t') := by
    ext p
    simp only [misses, mem_filter, mem_product]
    tauto
  rw [eq, card_product]

/-- Exact finite characterization of inclusion-minimal hitting panels by private witnesses. -/
theorem inclusion_minimal_cover_iff (P : Finset S) (R : Finset T)
    (cover : ∀ t ∈ R, ∃ s ∈ P, G s t) :
    (∀ Q ⊂ P, ∃ t ∈ R, ∀ s ∈ Q, ¬ G s t) ↔
      ∀ s ∈ P, ∃ t ∈ R, G s t ∧ ∀ x ∈ P, G x t → x = s := by
  constructor
  · intro m s hs
    obtain ⟨t, ht, hall⟩ := m (P.erase s) (erase_ssubset hs)
    obtain ⟨x, hx, hg⟩ := cover t ht
    have eq : x = s := by
      by_contra hn
      exact hall x (mem_erase.mpr ⟨hn, hx⟩) hg
    refine ⟨t, ht, eq ▸ hg, ?_⟩
    intro y hy hG
    by_contra hn
    exact hall y (mem_erase.mpr ⟨hn,hy⟩) hG
  · intro witnesses Q hQ
    obtain ⟨s, hs, hn⟩ := not_subset.mp (not_subset_of_ssubset hQ)
    obtain ⟨t, ht, hG, huniq⟩ := witnesses s hs
    exact ⟨t, ht, fun x hx hg => hn (huniq x (hQ.subset hx) hg ▸ hx)⟩

/-- A family of pairwise disjoint successful fibers gives a matching lower bound
on the cardinality of every subpanel serving all of those targets. -/
theorem separated_demands_lower_bound (P : Finset S) (R : Finset T)
    (separate : ∀ t ∈ R, ∀ u ∈ R, t ≠ u → Disjoint (succeeds G P t) (succeeds G P u))
    (Q : Finset S) (hQP : Q ⊆ P) (h : ∀ t ∈ R, ∃ s ∈ Q, G s t) :
    R.card ≤ Q.card := by
  classical
  let f (t : R) := (h t t.property).choose
  have hf (t : R) : f t ∈ Q ∧ G (f t) t := (h t t.property).choose_spec
  have inj : Function.Injective f := by
    intro t u eq
    apply Subtype.ext
    by_contra hn
    have he := separate t t.property u u.property hn
    exact Finset.disjoint_left.mp he ((mem_hit G).mpr ⟨hQP (hf t).1, (hf t).2⟩)
      (eq ▸ (mem_hit G).mpr ⟨hQP (hf u).1, (hf u).2⟩)
  have hb : R.attach.image f ⊆ Q := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := mem_image.mp hx
    exact (hf t).1
  have := Finset.card_le_card hb
  rwa [Finset.card_image_of_injective _ inj, Finset.card_attach] at this

/-- With disjoint nonempty successful fibers the optimum is exactly one seed per demand. -/
theorem separated_demands_exact_optimum (P : Finset S) (R : Finset T)
    (h : ∀ t ∈ R, ∃ s ∈ P, G s t)
    (separate : ∀ t ∈ R, ∀ u ∈ R, t ≠ u → Disjoint (succeeds G P t) (succeeds G P u)) :
    ∃ Q : Finset S, Q ⊆ P ∧ Q.card = R.card ∧ ∀ t ∈ R, ∃ s ∈ Q, G s t := by
  obtain ⟨Q, hQP, hcard, hQ⟩ := one_seed_per_target G P R h
  exact ⟨Q, hQP, le_antisymm hcard (separated_demands_lower_bound G _ _ separate _ hQP hQ), hQ⟩

end Greedy


section LinearPanels
variable {K V W Z : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]

/-- Losslessness concerns the intersection of the source subspace and the seed kernel. -/
def lossless (E : Submodule K V) (f : V →ₗ[K] W) : Prop :=
  Function.Injective (f.domRestrict E)

private theorem zero_of_mem_bot (x : V) (h : x ∈ (⊥ : Submodule K V)) : x = 0 := by
  simpa only [Submodule.mem_bot] using h

private theorem lossless_iff (E : Submodule K V) (f : V →ₗ[K] W) :
    lossless E f ↔ Disjoint E f.ker := by
  rw [lossless, ← LinearMap.ker_eq_bot, disjoint_iff_inf_le]
  constructor
  · intro h x hx
    obtain ⟨he,hf⟩ := Submodule.mem_inf.mp hx
    have hk : (⟨x,he⟩ : E) ∈ (f.domRestrict E).ker := LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hf)
    rw [h, Submodule.mem_bot] at hk
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val hk
  · intro h
    apply bot_unique
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact zero_of_mem_bot (K := K) _ (h (Submodule.mem_inf.mpr
      ⟨x.property, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)⟩))

/-- A lossless observation has a unique linear inverse on its actual image. -/
theorem unique_reconstruction_on_image (E : Submodule K V) (f : V →ₗ[K] W)
    (h : lossless E f) :
    ∃! e : E ≃ₗ[K] (f.domRestrict E).range,
      ∀ x : E, ((e x : (f.domRestrict E).range) : W) = f x := by
  let e := LinearEquiv.ofInjective (f.domRestrict E) h
  refine ⟨e, fun _ => rfl, ?_⟩
  intro g hg
  ext x
  exact hg x

/-- A single kernel clearance condition handles every subspace of a prescribed test space. -/
theorem all_subspaces_lossless_iff (P : Submodule K V) (f : V →ₗ[K] W) :
    (∀ E ≤ P, lossless E f) ↔ Disjoint P f.ker := by
  constructor
  · intro h
    exact (lossless_iff P f).mp (h P le_rfl)
  · intro h E hE
    exact (lossless_iff E f).mpr (Disjoint.mono_left hE h)

/-- A quotient test is lossless exactly on complements to its fixed ambiguity space. -/
theorem quotient_test_classification (E N : Submodule K V) :
    lossless E N.mkQ ↔ Disjoint E N := by
  rw [lossless_iff, Submodule.ker_mkQ]

/-- Two simultaneous observations preserve precisely the directions neither kills. -/
theorem stacked_seed_classification (E : Submodule K V) (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    lossless E (f.prod g) ↔ Disjoint E (f.ker ⊓ g.ker) := by
  rw [lossless_iff, LinearMap.ker_prod]

/-- Successive lossy observations have an exact inverse criterion on the transferred subspace. -/
theorem composition_lossless_iff (E : Submodule K V) (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    lossless E (g.comp f) ↔ lossless E f ∧ lossless (E.map f) g := by
  constructor
  · intro h
    refine ⟨fun x y hxy => h (congrArg g hxy), ?_⟩
    intro x y hxy
    obtain ⟨a, ha, hax⟩ := Submodule.mem_map.mp x.property
    obtain ⟨b, hb, hby⟩ := Submodule.mem_map.mp y.property
    have e : (⟨a,ha⟩ : E) = ⟨b,hb⟩ := h (by
      change g (f a) = g (f b)
      rw [hax,hby]
      exact hxy)
    apply Subtype.ext
    rw [← hax, ← hby]
    exact congrArg (fun z : E => f z) e
  · rintro ⟨hf,hg⟩ x y hxy
    have ex : (⟨f x, Submodule.mem_map.mpr ⟨x,x.property,rfl⟩⟩ : E.map f) =
        ⟨f y, Submodule.mem_map.mpr ⟨y,y.property,rfl⟩⟩ := hg hxy
    exact hf (congrArg Subtype.val ex)

/-- Characteristic-independent reconstruction on direct sums is equivalent to
separate reconstruction and disjoint recovered images. -/
theorem sum_lossless_iff (E F : Submodule K V) (f : V →ₗ[K] W) (hEF : Disjoint E F) :
    lossless (E ⊔ F) f ↔ lossless E f ∧ lossless F f ∧ Disjoint (E.map f) (F.map f) := by
  simp only [lossless_iff]
  constructor
  · intro h
    refine ⟨Disjoint.mono_left le_sup_left h, Disjoint.mono_left le_sup_right h, ?_⟩
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hx₁,hx₂⟩ := Submodule.mem_inf.mp hx
    obtain ⟨u,hu,he⟩ := Submodule.mem_map.mp hx₁
    obtain ⟨v,hv,hv'⟩ := Submodule.mem_map.mp hx₂
    have e : u - v = 0 := zero_of_mem_bot (K := K) _ ((disjoint_iff_inf_le.mp h)
      (Submodule.mem_inf.mpr ⟨(E ⊔ F).sub_mem ((le_sup_left : E ≤ E ⊔ F) hu) ((le_sup_right : F ≤ E ⊔ F) hv),
        LinearMap.mem_ker.mpr (by rw [map_sub,he,hv',sub_self])⟩))
    have euv := sub_eq_zero.mp e
    have h0 : u = 0 := zero_of_mem_bot (K := K) _ ((disjoint_iff_inf_le.mp hEF)
      (Submodule.mem_inf.mpr ⟨hu,euv ▸ hv⟩))
    rw [← he, h0, map_zero]
    exact Submodule.zero_mem _
  · rintro ⟨hE,hF,hm⟩
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hx₁,hx₂⟩ := Submodule.mem_inf.mp hx
    obtain ⟨u,hu,v,hv,he⟩ := Submodule.mem_sup.mp hx₁
    have hsum : f u + f v = 0 := by
      rw [← map_add, he]
      exact LinearMap.mem_ker.mp hx₂
    have he' : f u = -(f v) := eq_neg_of_add_eq_zero_left hsum
    have h0 : f u = 0 := zero_of_mem_bot (K := K) _ ((disjoint_iff_inf_le.mp hm)
      (Submodule.mem_inf.mpr ⟨Submodule.mem_map_of_mem hu,
        he' ▸ (F.map f).neg_mem (Submodule.mem_map_of_mem hv)⟩))
    have h0' : f v = 0 := by simpa [h0] using hsum
    have hu0 := zero_of_mem_bot (K := K) _ ((disjoint_iff_inf_le.mp hE)
      (Submodule.mem_inf.mpr ⟨hu, LinearMap.mem_ker.mpr h0⟩))
    have hv0 := zero_of_mem_bot (K := K) _ ((disjoint_iff_inf_le.mp hF)
      (Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr h0'⟩))
    rw [← he, hu0, hv0, add_zero]
    exact Submodule.zero_mem _

private noncomputable def restrictedKernelEquiv (E : Submodule K V) (f : V →ₗ[K] W) :
    (f.domRestrict E).ker ≃ₗ[K] ↥(E ⊓ f.ker) :=
  LinearEquiv.ofLinearMap
    { toFun := fun x => ⟨x.val, Submodule.mem_inf.mpr
        ⟨x.val.property, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.property)⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    { toFun := fun x => ⟨⟨x.val, (Submodule.mem_inf.mp x.property).1⟩,
        LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp (Submodule.mem_inf.mp x.property).2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by ext; rfl) (by ext; rfl)

/-- Exact rank loss is the dimension of the portion killed by the seed. -/
theorem exact_rank_loss (E : Submodule K V) [FiniteDimensional K E] (f : V →ₗ[K] W) :
    Module.finrank K (f.domRestrict E).range + Module.finrank K ↥(E ⊓ f.ker) =
      Module.finrank K E := by
  rw [← (restrictedKernelEquiv E f).finrank_eq]
  exact (f.domRestrict E).finrank_range_add_finrank_ker

/-- A rank computation suffices to certify losslessness on a finite-dimensional source. -/
theorem rank_certificate_iff (E : Submodule K V) [FiniteDimensional K E] (f : V →ₗ[K] W) :
    Module.finrank K (f.domRestrict E).range = Module.finrank K E ↔ lossless E f := by
  constructor
  · intro h
    have hk := (f.domRestrict E).finrank_range_add_finrank_ker
    have hz : Module.finrank K (f.domRestrict E).ker = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
  · intro h
    exact LinearMap.finrank_range_of_inj h

/-- Dimension loss under serial compression is the sum of the first kernel defect
and the second kernel's intersection with the transferred image. -/
theorem composition_rank_loss (E : Submodule K V) [FiniteDimensional K V]
    (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    Module.finrank K ((g.comp f).domRestrict E).range +
      Module.finrank K ↥(E.map f ⊓ g.ker) + Module.finrank K ↥(E ⊓ f.ker) =
      Module.finrank K E := by
  have h₁ := exact_rank_loss E f
  have hmap : (f.domRestrict E).range = E.map f := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact Submodule.mem_map.mpr ⟨y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  rw [hmap] at h₁
  haveI : FiniteDimensional K (E.map f) := hmap ▸ inferInstanceAs (FiniteDimensional K (f.domRestrict E).range)
  have h₂ := exact_rank_loss (E.map f) g
  have hh : (g.domRestrict (E.map f)).range = ((g.comp f).domRestrict E).range := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨x,hx,hex⟩ := Submodule.mem_map.mp y.property
      exact ⟨⟨x,hx⟩,congrArg g hex⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨f x, Submodule.mem_map.mpr ⟨x,x.property,rfl⟩⟩,rfl⟩
  rw [hh] at h₂
  omega

/-- The full obstruction space of a panel is the intersection of its kernels,
and no individual kernel needs to be zero. -/
theorem joint_lossless_panel_iff {I : Type*} (E : Submodule K V) (f : I → V →ₗ[K] W) :
    lossless E (LinearMap.pi f) ↔ Disjoint E (⨅ i, (f i).ker) := by
  rw [lossless_iff, LinearMap.ker_pi]

/-- If each seed kills a different disjoint direction space, stacking two
suffices to recover every ambient input. -/
theorem stacked_reconstruction_from_disjoint (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (h : Disjoint f.ker g.ker) :
    ∃ e : V ≃ₗ[K] (f.prod g).range, ∀ x, (e x : W × Z) = f.prod g x := by
  have hf : Function.Injective (f.prod g) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_prod]
    exact h.eq_bot
  exact ⟨LinearEquiv.ofInjective _ hf, fun _ => rfl⟩

/-- A high rank test is automatically lossless on any domain section which
misses the kernel. In particular one of the sections has the full observed rank. -/
theorem lossless_section_exists (f : V →ₗ[K] W) [FiniteDimensional K V] :
    ∃ E : Submodule K V, IsCompl E f.ker ∧ lossless E f ∧
      Module.finrank K E = Module.finrank K f.range := by
  obtain ⟨E, hE⟩ := Submodule.exists_isCompl f.ker
  have inj := (lossless_iff E f).mpr hE.disjoint.symm
  refine ⟨E,hE.symm,inj,?_⟩
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := Submodule.finrank_add_eq_of_isCompl hE
  omega

/-- The same source split recovers a lift of every target in the observation image. -/
theorem exact_section_for_image (f : V →ₗ[K] W) (E : Submodule K V)
    (hE : IsCompl E f.ker) :
    ∃ e : E ≃ₗ[K] f.range, ∀ x : E, (e x : W) = f x := by
  let g : E →ₗ[K] f.range := f.rangeRestrict.domRestrict E
  have hinj : Function.Injective g := by
    intro x y he
    exact (lossless_iff E f).mpr hE.disjoint (congrArg Subtype.val he)
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨x,hx⟩ := z.property
    have hx' : x ∈ E ⊔ f.ker := by rw [hE.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, e⟩ := Submodule.mem_sup.mp hx'
    refine ⟨⟨u,hu⟩, Subtype.ext ?_⟩
    change f u = z
    have hh := congrArg f e
    rw [map_add, LinearMap.mem_ker.mp hv, add_zero, hx] at hh
    exact hh
  exact ⟨LinearEquiv.ofBijective g ⟨hinj,hsurj⟩,fun _ => rfl⟩

/-- A scalar test either kills a whole source subspace or loses exactly all but one dimension. -/
theorem scalar_seed_rank_dichotomy (E : Submodule K V) [FiniteDimensional K E] (f : V →ₗ[K] K) :
    (E ≤ f.ker ∧ Module.finrank K (f.domRestrict E).range = 0) ∨
      (¬ E ≤ f.ker ∧ Module.finrank K (f.domRestrict E).range = 1) := by
  have hle := Submodule.finrank_le (f.domRestrict E).range
  rw [Module.finrank_self] at hle
  have eq_zero_iff : (f.domRestrict E).range = ⊥ ↔ E ≤ f.ker := by
    rw [LinearMap.range_eq_bot]
    constructor
    · intro h x hx
      exact LinearMap.mem_ker.mpr (show f x = 0 from LinearMap.congr_fun h ⟨x,hx⟩)
    · intro h; ext x
      exact LinearMap.mem_ker.mp (h x.property)
  by_cases h : E ≤ f.ker
  · exact Or.inl ⟨h, Submodule.finrank_eq_zero.mpr (eq_zero_iff.mpr h)⟩
  · have hn : Module.finrank K (f.domRestrict E).range ≠ 0 := fun h0 =>
      h (eq_zero_iff.mp (Submodule.finrank_eq_zero.mp h0))
    exact Or.inr ⟨h, by omega⟩

end LinearPanels


section Certificates
variable {S T : Type*} [DecidableEq S] [DecidableEq T]
variable (G : S → T → Prop) [DecidableRel G]

/-- A combined seed serving every target exists exactly when the union of bad
fibers fails to cover the full panel. Its entire successful count is given. -/
theorem common_seed_exact_count (P : Finset S) (R : Finset T) :
    (P.filter fun s => ∀ t ∈ R, G s t).card + (R.biUnion (misses G P)).card = P.card := by
  classical
  let U := R.biUnion (misses G P)
  have hU : U ⊆ P := by
    intro s hs
    obtain ⟨t,ht,h⟩ := mem_biUnion.mp hs
    exact ((mem_miss G).mp h).1
  have hs : P.filter (fun s => ∀ t ∈ R, G s t) = P \ U := by
    ext s
    simp only [mem_filter, mem_sdiff, U, mem_biUnion, mem_miss]
    constructor
    · rintro ⟨hp,h⟩
      exact ⟨hp, fun ⟨t,ht,_,hn⟩ => hn (h t ht)⟩
    · rintro ⟨hp,h⟩
      refine ⟨hp, fun t ht => ?_⟩
      by_contra hn
      exact h ⟨t,ht,hp,hn⟩
  rw [hs]
  exact card_sdiff_add_card_eq_card hU

/-- Fragility can itself be measured from the total failure mass. -/
theorem fragile_target_budget (P : Finset S) (R : Finset T) (k : ℕ) :
    (R.filter fun t => (succeeds G P t).card ≤ k).card * (P.card - k) ≤
      ∑ t ∈ R, (misses G P t).card := by
  calc
    _ = ∑ _t ∈ R.filter (fun t => (succeeds G P t).card ≤ k), (P.card - k) := by simp
    _ ≤ ∑ t ∈ R.filter (fun t => (succeeds G P t).card ≤ k), (misses G P t).card := by
      apply sum_le_sum
      intro t ht
      have h := (mem_filter.mp ht).2
      have he := hit_card_add_miss_card G P t
      omega
    _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)

/-- Incidence multiplicity adds exactly across a split population of target classes. -/
theorem classwise_multiplicity_cost (P : Finset S) (R₁ R₂ : Finset T) (h : Disjoint R₁ R₂)
    (q₁ q₂ b : ℕ) (h₁ : ∀ t ∈ R₁, q₁ ≤ (succeeds G P t).card)
    (h₂ : ∀ t ∈ R₂, q₂ ≤ (succeeds G P t).card)
    (hc : ∀ s ∈ P, (served G (R₁ ∪ R₂) s).card ≤ b) :
    R₁.card * q₁ + R₂.card * q₂ ≤ P.card * b := by
  have sumR :
      (∑ t ∈ R₁, (succeeds G P t).card) + (∑ t ∈ R₂, (succeeds G P t).card) =
        ∑ t ∈ R₁ ∪ R₂, (succeeds G P t).card :=
    (Finset.sum_union h).symm
  calc
    _ = (∑ _t ∈ R₁, q₁) + (∑ _t ∈ R₂, q₂) := by simp
    _ ≤ (∑ t ∈ R₁, (succeeds G P t).card) + (∑ t ∈ R₂, (succeeds G P t).card) :=
      add_le_add (sum_le_sum h₁) (sum_le_sum h₂)
    _ = ∑ t ∈ R₁ ∪ R₂, (succeeds G P t).card := sumR
    _ = ∑ s ∈ P, (served G (R₁ ∪ R₂) s).card := by
      simpa [weight] using (incidence_mass_identity G P (R₁ ∪ R₂) (fun _ => 1)).symm
    _ ≤ ∑ _s ∈ P, b := sum_le_sum hc
    _ = _ := by simp

/-- Pairwise separated demands require disjoint allocations even after adversarial
erasures, giving a sharp multiplicity lower bound. -/
theorem disjoint_multiplicity_lower_bound (P : Finset S) (R : Finset T) (q : ℕ)
    (hf : ∀ t ∈ R, q ≤ (succeeds G P t).card)
    (sep : ∀ t ∈ R, ∀ u ∈ R, t ≠ u → Disjoint (succeeds G P t) (succeeds G P u)) :
    R.card * q ≤ P.card := by
  have H : (R : Set T).PairwiseDisjoint (succeeds G P) := by
    intro t ht u hu hne
    exact sep t ht u hu hne
  calc
    _ = ∑ _t ∈ R, q := by simp
    _ ≤ ∑ t ∈ R, (succeeds G P t).card := sum_le_sum hf
    _ = (R.biUnion (succeeds G P)).card := (card_biUnion H).symm
    _ ≤ P.card := card_le_card (by
      intro s hs
      obtain ⟨t,ht,h⟩ := mem_biUnion.mp hs
      exact ((mem_hit G).mp h).1)

/-- Disjoint successful fibers give an exact optimum for simultaneous q-fold coverage. -/
theorem disjoint_multiplicity_optimum (P : Finset S) (R : Finset T) (q : ℕ)
    (hf : ∀ t ∈ R, q ≤ (succeeds G P t).card)
    (sep : ∀ t ∈ R, ∀ u ∈ R, t ≠ u → Disjoint (succeeds G P t) (succeeds G P u)) :
    ∃ Q : Finset S, Q ⊆ P ∧ Q.card = R.card * q ∧ ∀ t ∈ R, q ≤ (succeeds G Q t).card := by
  obtain ⟨Q,hQP,hn,hQ⟩ := multiplicity_compression G P R q hf
  refine ⟨Q,hQP,le_antisymm hn (disjoint_multiplicity_lower_bound G Q R q hQ ?_),hQ⟩
  intro t ht u hu he
  have sub (y : T) : succeeds G Q y ⊆ succeeds G P y := by
    intro s hs
    exact (mem_hit G).mpr ⟨hQP ((mem_hit G).mp hs).1, ((mem_hit G).mp hs).2⟩
  exact Disjoint.mono (sub t) (sub u) (sep t ht u hu he)

/-- A finite weighted demand lower bound survives compression by any coarse
target labelling whenever representatives dominate their fibers. -/
theorem coverage_lifts_from_representatives {U : Type*} (P : Finset S) (R : Finset T)
    (f : T → U) (rep : U → T) (q : ℕ)
    (hrep : ∀ t ∈ R, q ≤ (succeeds G P (rep (f t))).card)
    (hdom : ∀ t ∈ R, ∀ s ∈ P, G s (rep (f t)) → G s t) :
    ∀ t ∈ R, q ≤ (succeeds G P t).card := by
  intro t ht
  apply (hrep t ht).trans
  apply card_le_card
  intro s hs
  obtain ⟨hp,hg⟩ := (mem_hit G).mp hs
  exact (mem_hit G).mpr ⟨hp,hdom t ht s hp hg⟩

/-- Two alternative implementations can be unioned at the level of success
relations. Even with overlap the exact joint success mass is available. -/
theorem alternative_implementations_count (H : S → T → Prop) [DecidableRel H]
    (P : Finset S) (t : T) :
    (succeeds (fun s x => G s x ∨ H s x) P t).card +
        (succeeds (fun s x => G s x ∧ H s x) P t).card =
      (succeeds G P t).card + (succeeds H P t).card := by
  have hu : succeeds (fun s x => G s x ∨ H s x) P t = succeeds G P t ∪ succeeds H P t := by
    ext s; simp only [succeeds, mem_filter, mem_union]; tauto
  have hi : succeeds (fun s x => G s x ∧ H s x) P t = succeeds G P t ∩ succeeds H P t := by
    ext s; simp only [succeeds, mem_filter, mem_inter]; tauto
  rw [hu,hi,card_union_add_card_inter]

/-- Complete one-step failure certificates compose under a resource-weighted
budget when the successful seed fibers of the two implementations are disjoint. -/
theorem alternative_weighted_robustness (H : S → T → Prop) [DecidableRel H]
    (P : Finset S) (R : Finset T) (cost : S → ℕ) (u v : ℕ)
    (hd : ∀ t ∈ R, Disjoint (succeeds G P t) (succeeds H P t))
    (hg : ∀ t ∈ R, u ≤ ∑ s ∈ succeeds G P t, cost s)
    (hh : ∀ t ∈ R, v ≤ ∑ s ∈ succeeds H P t, cost s)
    (E : Finset S) (he : (∑ s ∈ E, cost s) < u+v) :
    ∀ t ∈ R, ∃ s ∈ P \ E, G s t ∨ H s t := by
  intro t ht
  have hset :
      succeeds (fun s x => G s x ∨ H s x) P t = succeeds G P t ∪ succeeds H P t := by
    ext s; simp only [succeeds, mem_filter, mem_union]; tauto
  have hmass : u+v ≤ ∑ s ∈ succeeds (fun s x => G s x ∨ H s x) P t, cost s := by
    rw [hset, sum_union (hd t ht)]
    exact Nat.add_le_add (hg t ht) (hh t ht)
  have hsub : ¬ succeeds (fun s x => G s x ∨ H s x) P t ⊆ E :=
    fun h => (not_le_of_gt he) (hmass.trans (sum_le_sum_of_subset h))
  obtain ⟨s,hs,hn⟩ := not_subset.mp hsub
  have hp := Finset.mem_filter.mp hs
  exact ⟨s,mem_sdiff.mpr ⟨hp.1,hn⟩,hp.2⟩

/-- A seed optimizer is unchanged by duplicate demand labels when it is defined
through success fibers. The equality is at the level of all feasible panels. -/
theorem duplicate_demands_preserve_feasibility {U : Type*} [DecidableEq U]
    (f : T → U) (H : S → U → Prop)
    (compat : ∀ s t, G s t ↔ H s (f t)) (P : Finset S) (R : Finset T) :
    (∀ t ∈ R, ∃ s ∈ P, G s t) ↔ ∀ u ∈ R.image f, ∃ s ∈ P, H s u := by
  constructor
  · intro h u hu
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hu
    obtain ⟨s,hs,hg⟩ := h t ht
    exact ⟨s,hs,(compat s t).mp hg⟩
  · intro h t ht
    obtain ⟨s,hs,hh⟩ := h (f t) (mem_image_of_mem _ ht)
    exact ⟨s,hs,(compat s t).mpr hh⟩

end Certificates

section AdditionalLinear
variable {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- Killing a direction space by a quotient leaves exactly the complementary
number of observable dimensions in any finite-dimensional input section. -/
theorem quotient_rank_loss (E N : Submodule K V) [FiniteDimensional K E] :
    Module.finrank K (N.mkQ.domRestrict E).range + Module.finrank K ↥(E ⊓ N) =
      Module.finrank K E := by
  have h := exact_rank_loss E N.mkQ
  have eq : E ⊓ N.mkQ.ker = E ⊓ N := congrArg (fun P => E ⊓ P) N.ker_mkQ
  have he := (LinearEquiv.ofEq _ _ eq).finrank_eq
  omega

/-- A common ambiguity subspace of two observations can be removed without
altering their ability to separate the remaining quotient classes. -/
theorem quotient_joint_recovery (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (N : Submodule K V) (hN : f.ker ⊓ g.ker = N) :
    ∃ e : (V ⧸ N) ≃ₗ[K] (f.prod g).range,
      ∀ x : V, (e (N.mkQ x) : W × Z) = (f x,g x) := by
  have h : (f.prod g).ker = N := (LinearMap.ker_prod f g).trans hN
  let e := (Submodule.quotEquivOfEq N (f.prod g).ker h.symm).trans
    (f.prod g).quotKerEquivRange
  refine ⟨e,?_⟩
  intro x
  change (((f.prod g).quotKerEquivRange (Submodule.Quotient.mk x) :
    (f.prod g).range) : W × Z) = _
  exact (f.prod g).quotKerEquivRange_apply_mk x

end AdditionalLinear


section RankConsequences
variable {K V W S : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [DecidableEq S]

/-- Pointwise lossless fractions yield a small deterministic subpanel for a prescribed
family of subspaces. Both the size and rank guarantee are part of the conclusion. -/
theorem greedy_rank_panel (P : Finset S) (R : Finset (Submodule K V))
    (f : S → V →ₗ[K] W) (steps q : ℕ) (hP : P.Nonempty) (hq : q ≤ P.card)
    (h : letI := Classical.propDecidable
      ∀ E ∈ R, q ≤ (P.filter (fun s => lossless E (f s))).card)
    (hb : (P.card-q)^steps * R.card < P.card^steps) :
    ∃ Q : Finset S, Q ⊆ P ∧ Q.card ≤ steps ∧ ∀ E ∈ R, ∃ s ∈ Q, lossless E (f s) := by
  classical
  let G := fun s E => lossless E (f s)
  have h' : ∀ E ∈ R, q ≤ (succeeds G P E).card := h
  obtain ⟨seq, hl, hmem, hc⟩ := greedy_cover_at_power_bound G P R q steps hP hq h' hb
  refine ⟨seq.toFinset, ?_, ?_, ?_⟩
  · intro s hs
    exact hmem s (List.mem_toFinset.mp hs)
  · simpa [hl] using List.toFinset_card_le seq
  · intro E hE
    obtain ⟨s, hs, hf⟩ := hc E hE
    exact ⟨s, List.mem_toFinset.mpr hs, hf⟩

/-- A rank-test panel keeps a concrete inverse on each requested image after
any weighted erasure whose cost is below every successful fiber's weight. -/
theorem weighted_erasure_rank_reconstruction (P : Finset S) (R : Finset (Submodule K V))
    (f : S → V →ₗ[K] W) (cost : S → ℕ) (budget : ℕ)
    (h : letI := Classical.propDecidable
      ∀ E ∈ R, budget < ∑ s ∈ P.filter (fun s => lossless E (f s)), cost s) :
    ∀ F : Finset S, (∑ s ∈ F, cost s) ≤ budget →
      ∀ E ∈ R, ∃ s ∈ P \ F, ∃ e : E ≃ₗ[K] ((f s).domRestrict E).range,
        ∀ x : E, (e x : W) = f s x := by
  classical
  let G := fun s E => lossless E (f s)
  have h' : ∀ E ∈ R, budget < ∑ s ∈ succeeds G P E, cost s := h
  intro F hF E hE
  obtain ⟨s, hs, hi⟩ := (weighted_erasure_robust_iff G P R cost budget).mpr h' F hF E hE
  obtain ⟨e, he, _⟩ := unique_reconstruction_on_image E (f s) hi
  exact ⟨s,hs,e,he⟩

end RankConsequences

end TwoHundred.Coverage
