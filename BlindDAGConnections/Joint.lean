import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.GroupTheory.Complement

namespace BlindDAG.Relation

/-- A finite observation supplies a single maximizer which bounds all limiting scores. -/
theorem finite_observation {X : Type*} [PseudoMetricSpace X] {s t : Set X}
    (hs : (closure s).Nonempty) (ht : t.Finite)
    (hfin : Metric.hausdorffEDist s t ≠ ⊤)
    (f : X → ℝ) (hf : ∀ x y, f x - f y ≤ dist x y) :
    ∃ b ∈ t, (∀ y ∈ t, f y ≤ f b) ∧
      ∀ x ∈ closure s, f x ≤ f b + Metric.hausdorffDist s t := by
  obtain ⟨b, hb, hmax⟩ := Set.exists_max_image t f ht
    (Metric.nonempty_of_hausdorffEDist_ne_top hs.of_closure hfin)
  refine ⟨b, hb, hmax, ?_⟩
  intro x hx
  by_contra! h
  have hlt : Metric.hausdorffDist (closure s) t < f x - f b := by
    simpa only [Metric.hausdorffDist, Metric.hausdorffEDist_closure_left] using
      (show Metric.hausdorffDist s t < f x - f b by linarith)
  obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx hlt
    (by simpa only [Metric.hausdorffEDist_closure_left] using hfin)
  have := hf x y
  have := hmax y hy
  linarith

/-- Finite score separation, with both Hausdorff errors, certifies disjoint orbit closures
when the underlying sets are taken to be orbits. -/
theorem robust_separation {X : Type*} [PseudoMetricSpace X] {s t a b : Set X}
    (hs : (closure s).Nonempty) (ht : (closure t).Nonempty)
    (ha : a.Finite) (hb : b.Finite)
    (hsa : Metric.hausdorffEDist s a ≠ ⊤) (htb : Metric.hausdorffEDist t b ≠ ⊤)
    (f : X → ℝ) (hf : ∀ x y, f x - f y ≤ dist x y)
    (gap : ∀ u ∈ a, ∀ v ∈ b,
      f u + Metric.hausdorffDist s a + Metric.hausdorffDist t b < f v) :
    Disjoint (closure s) (closure t) := by
  obtain ⟨u, hu, _, hup⟩ := finite_observation hs ha hsa f hf
  have hn : ∀ x y, (-f x) - (-f y) ≤ dist x y := by
    intro x y
    have h := hf y x
    rw [dist_comm y x] at h
    linarith
  obtain ⟨v, hv, _, hlo⟩ := finite_observation ht hb htb (fun z => -f z) hn
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h₁ := hup x hx
  have h₂ := hlo x hx'
  have h₃ := gap u hu v hv
  linarith

end BlindDAG.Relation


namespace BlindSplice

open scoped Pointwise NNReal

/-- A finite small-product probe of diameter at most D gives an internal D-net. -/
theorem internal_net {G : Type*} [SeminormedCommGroup G] {A B : Set G}
    {D K : ℝ} (ha : A.Finite) (hb : B.Finite) (hne : B.Nonempty)
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ D)
    (hsmall : (Nat.card (A * B) : ℝ) ≤ K * Nat.card B) :
    ∃ F ⊆ A, (Nat.card F : ℝ) ≤ K ∧ F.Finite ∧
      ∀ a ∈ A, ∃ f ∈ F, dist a f ≤ D := by
  obtain ⟨F, hFA, hcard, hcov, hfin⟩ := Set.ruzsa_covering_mul ha hb hne hsmall
  refine ⟨F, hFA, hcard, hfin, ?_⟩
  intro a ha'
  obtain ⟨f, hf, z, hz, rfl⟩ := Set.mem_mul.mp (hcov ha')
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_div.mp hz
  refine ⟨f, hf, ?_⟩
  simpa only [dist_eq_norm_div, mul_div_cancel_left] using hdiam x hx y hy

/-- The probe may be supplied through a cover of a cofinal set above a transversal. -/
theorem cofinal_probe {G : Type*} [SeminormedCommGroup G] [Preorder G]
    {A B S T U : Set G} {ε : ℝ≥0} {D K : ℝ}
    (hst : Subgroup.IsComplement S T) (hsu : IsCofinalFor S U)
    (hub : Metric.IsCover ε U B) (ha : A.Finite) (hb : B.Finite)
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ D)
    (hsmall : (Nat.card (A * B) : ℝ) ≤ K * Nat.card B) :
    ∃ F ⊆ A, (Nat.card F : ℝ) ≤ K ∧ F.Finite ∧
      ∀ a ∈ A, ∃ f ∈ F, dist a f ≤ D :=
  internal_net ha hb (hub.nonempty (hsu.nonempty hst.nonempty_left)) hdiam hsmall

/-- The product with the whole covered set uses the same bound on the number of centers. -/
theorem product_net {G : Type*} [SeminormedCommGroup G] [Preorder G]
    {A B S T U : Set G} {ε : ℝ≥0} {R K : ℝ} (c : G)
    (hst : Subgroup.IsComplement S T) (hsu : IsCofinalFor S U)
    (hub : Metric.IsCover ε U B) (ha : A.Finite) (hb : B.Finite)
    (hball : ∀ b ∈ B, dist b c ≤ R)
    (hsmall : (Nat.card (A * B) : ℝ) ≤ K * Nat.card B) :
    ∃ F ⊆ A, (Nat.card F : ℝ) ≤ K ∧ F.Finite ∧
      ∀ z ∈ A * U, ∃ f ∈ F, dist z (f * c) ≤ (2 * R + (ε : ℝ)) + R := by
  have hd : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ 2 * R := by
    intro x hx y hy
    calc
      dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ ≤ R + R := add_le_add (hball _ hx) (by simpa only [dist_comm c y] using hball y hy)
      _ = 2 * R := (two_mul R).symm
  obtain ⟨F, hFA, hK, hfin, hnet⟩ := cofinal_probe hst hsu hub ha hb hd hsmall
  refine ⟨F, hFA, hK, hfin, ?_⟩
  intro z hz
  obtain ⟨a, hA, u, hU, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨f, hF, haf⟩ := hnet a hA
  have hu := hub.subset_iUnion_closedBall hU
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hu
  obtain ⟨b, hB, hub'⟩ := hu
  refine ⟨f, hF, ?_⟩
  calc
    dist (a * u) (f * c) ≤ dist (a * u) (f * u) + dist (f * u) (f * c) :=
      dist_triangle _ _ _
    _ = dist a f + dist u c := by
      simp only [dist_eq_norm_div, mul_div_mul_right_eq_div, mul_div_mul_left_eq_div]
    _ ≤ 2 * R + ((ε : ℝ) + R) :=
      add_le_add haf ((dist_triangle u b c).trans (add_le_add hub' (hball _ hB)))
    _ = _ := (add_assoc _ _ _).symm

end BlindSplice
namespace BlindJoint

open scoped Pointwise NNReal

/-- One set of centers works for every real 1-Lipschitz observable on the product closure. -/
theorem finite_score_envelope {G : Type*} [SeminormedCommGroup G] [Preorder G]
    {A B S T U : Set G} {ε : ℝ≥0} {R K : ℝ} (c : G)
    (hst : Subgroup.IsComplement S T) (hsu : IsCofinalFor S U)
    (hub : Metric.IsCover ε U B) (ha : A.Finite) (hb : B.Finite)
    (hne : (A * U).Nonempty) (hball : ∀ b ∈ B, dist b c ≤ R)
    (hsmall : (Nat.card (A * B) : ℝ) ≤ K * Nat.card B) :
    ∃ F ⊆ A, (Nat.card F : ℝ) ≤ K ∧ F.Finite ∧
      ∀ φ : G → ℝ, LipschitzWith 1 φ → ∃ t ∈ F,
        ∀ z ∈ closure (A * U), φ z ≤ φ (t * c) + ((2 * R + (ε : ℝ)) + R) := by
  obtain ⟨F, hFA, hK, hfin, hnet⟩ :=
    BlindSplice.product_net c hst hsu hub ha hb hball hsmall
  refine ⟨F, hFA, hK, hfin, ?_⟩
  intro φ hφ
  have hLip (x y : G) : φ x - φ y ≤ dist x y := by
    exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hφ.dist_le_mul x y)
  obtain ⟨w, hw⟩ := hne
  obtain ⟨a, haF, _⟩ := hnet w hw
  let C := (fun t : G => t * c) '' F
  have haC : a * c ∈ C := ⟨a, haF, rfl⟩
  obtain ⟨v, hv, hmax, _⟩ := BlindDAG.Relation.finite_observation
    (s := C) (t := C) ⟨a * c, subset_closure haC⟩ (hfin.image _)
    (by simp [Metric.hausdorffEDist_self]) φ hLip
  obtain ⟨t, ht, rfl⟩ := hv
  refine ⟨t, ht, ?_⟩
  have hsub : A * U ⊆ {z | φ z ≤ φ (t * c) + ((2 * R + (ε : ℝ)) + R)} := by
    intro z hz
    obtain ⟨f, hf, hdist⟩ := hnet z hz
    have h₁ := hLip z (f * c)
    have h₂ := hmax (f * c) ⟨f, hf, rfl⟩
    change φ z ≤ _
    linarith
  exact closure_minimal hsub (isClosed_le hφ.continuous continuous_const)

theorem uniform_score_envelope {G : Type*} [SeminormedCommGroup G]
    {A B U : Set G} {ε : ℝ≥0} {R K : ℝ} (c : G)
    (hub : Metric.IsCover ε U B) (ha : A.Finite) (hb : B.Finite)
    (hne : (A * U).Nonempty) (hball : ∀ b ∈ B, dist b c ≤ R)
    (hsmall : (Nat.card (A * B) : ℝ) ≤ K * Nat.card B) :
    ∃ F ⊆ A, (Nat.card F : ℝ) ≤ K ∧ F.Finite ∧
      ∀ φ : G → ℝ, LipschitzWith 1 φ → ∃ t ∈ F,
        ∀ z ∈ closure (A * U), φ z ≤ φ (t * c) + ((2 * R + (ε : ℝ)) + R) := by
  letI : Preorder G := { le := fun _ _ => True, le_refl := fun _ => trivial,
                         le_trans := fun _ _ _ _ _ => trivial }
  obtain ⟨w, hw⟩ := hne
  obtain ⟨a, haA, u, hu, _⟩ := Set.mem_mul.mp hw
  have hcof : IsCofinalFor ({u} : Set G) U := fun _ _ => ⟨u, hu, trivial⟩
  exact finite_score_envelope c Subgroup.isComplement_singleton_univ hcof hub ha hb
    ⟨w, hw⟩ hball hsmall

end BlindJoint
