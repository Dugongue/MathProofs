import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Card

/-!
For an exact translate packing, a coordinate supported by an isotropic space whose
projection to the centers is full belongs to the period class of a unique center.
This is the rigidity step in the classification of maximum isotropic spaces.
-/

namespace TranslatePacking

variable {G F : Type*} [AddGroup G] [Field F]

/-- A left translate of a finite tile. -/
def translate (x : G) (B : Finset G) : Finset G :=
  B.map ⟨(x + ·), fun _ _ h => add_left_cancel h⟩

theorem mem_translate (x b : G) (B : Finset G) (hb : b ∈ B) :
    x + b ∈ translate x B :=
  Finset.mem_map.mpr ⟨b, hb, rfl⟩

/-- Every point lies in a translate indexed by exactly one center. -/
def ExactPacking (B C : Finset G) : Prop :=
  ∀ z : G, ∃! c, c ∈ C ∧ z ∈ translate c B

/-- The alternating form for two overlapping tiles vanishes on the subspace. -/
def Isotropic (B : Finset G) (U : Submodule F (G → F)) : Prop :=
  ∀ u v : U, ∀ x y z : G, z ∈ translate x B → z ∈ translate y B →
    (u : G → F) x * (v : G → F) y = (u : G → F) y * (v : G → F) x

/-- Standard coordinate vectors on the centers have lifts to the subspace. -/
def FullCenterProjection (C : Finset G) (U : Submodule F (G → F)) : Prop :=
  ∀ c ∈ C, ∃ v : U, (v : G → F) c = 1 ∧
    ∀ d ∈ C, d ≠ c → (v : G → F) d = 0

/-- A coordinate meeting two full-projection centers vanishes on the isotropic space. -/
theorem inactive_of_two_tile_overlaps
    (B C : Finset G) (U : Submodule F (G → F))
    (hU : Isotropic B U) (hfull : FullCenterProjection C U)
    (x c d z₁ z₂ : G) (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≠ d)
    (h₁x : z₁ ∈ translate x B) (h₁c : z₁ ∈ translate c B)
    (h₂x : z₂ ∈ translate x B) (h₂d : z₂ ∈ translate d B)
    (u : U) : (u : G → F) x = 0 := by
  obtain ⟨v, hvc, hvzero⟩ := hfull c hc
  obtain ⟨w, hwd, _⟩ := hfull d hd
  have hvx := hU v w x d z₂ h₂x h₂d
  rw [hwd, mul_one, hvzero d hd (Ne.symm hcd), zero_mul] at hvx
  have hux := hU u v x c z₁ h₁x h₁c
  rw [hvc, mul_one, hvx, mul_zero] at hux
  exact hux
theorem active_coordinate_recovers_tile
    (B C : Finset G) (hB : B.Nonempty) (hC : ExactPacking B C)
    (U : Submodule F (G → F)) (hU : Isotropic B U)
    (hfull : FullCenterProjection C U)
    (x : G) (u : U) (hux : (u : G → F) x ≠ 0) :
    ∃ c ∈ C, translate x B = translate c B ∧
      ∃ a : F, a ≠ 0 ∧ ∀ w : U, (w : G → F) x = a * (w : G → F) c := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, ⟨hc, hzc⟩, _⟩ := hC (x + b)
  obtain ⟨v, hvc, _⟩ := hfull c hc
  have factor (w : U) : (w : G → F) x = (v : G → F) x * (w : G → F) c := by
    have h := hU w v x c (x + b) (mem_translate x b B hb) hzc
    rw [hvc, mul_one, mul_comm] at h
    exact h
  have hvx : (v : G → F) x ≠ 0 := by
    intro hzero
    exact hux (by rw [factor u, hzero, zero_mul])
  have hsub : translate x B ⊆ translate c B := by
    intro z hzx
    obtain ⟨d, ⟨hd, hzd⟩, _⟩ := hC z
    have hdc : d = c := by
      by_contra hne
      exact hux (inactive_of_two_tile_overlaps B C U hU hfull x c d (x + b) z hc hd
        (Ne.symm hne) (mem_translate x b B hb) hzc hzx hzd u)
    rwa [hdc] at hzd
  refine ⟨c, hc, Finset.eq_of_subset_of_card_le hsub ?_, (v : G → F) x, hvx, factor⟩
  simp [translate]

/-- For an aperiodic tile the normalized isotropic space is the coordinate space. -/
theorem aperiodic_isotropic_coordinate_space
    (B C : Finset G) (hB : B.Nonempty) (hC : ExactPacking B C)
    (hperiod : Function.Injective (fun x : G => translate x B))
    (U : Submodule F (G → F)) (hU : Isotropic B U)
    (hfull : FullCenterProjection C U) (f : G → F) :
    f ∈ U ↔ ∀ x ∉ C, f x = 0 := by
  classical
  have stays_on_centers (u : U) (x : G) (hx : x ∉ C) : (u : G → F) x = 0 := by
    by_contra hux
    obtain ⟨c, hc, heq, _⟩ := active_coordinate_recovers_tile B C hB hC U hU hfull x u hux
    exact hx ((hperiod heq).symm ▸ hc)
  refine ⟨fun hf x hx => stays_on_centers ⟨f, hf⟩ x hx, ?_⟩
  intro hf
  let v (c : G) : U := if hc : c ∈ C then Classical.choose (hfull c hc) else 0
  have hdiag {c : G} (hc : c ∈ C) : (v c : G → F) c = 1 := by
    simpa only [v, dif_pos hc] using (Classical.choose_spec (hfull c hc)).1
  have hoff {c x : G} (hc : c ∈ C) (hx : x ∈ C) (hne : x ≠ c) :
      (v c : G → F) x = 0 := by
    simpa only [v, dif_pos hc] using (Classical.choose_spec (hfull c hc)).2 x hx hne
  let g : G → F := ∑ c ∈ C, f c • (v c : G → F)
  have hg : g ∈ U := U.sum_mem fun c _ => U.smul_mem (f c) (v c).property
  have heq : g = f := by
    ext x
    by_cases hx : x ∈ C
    · simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single x (fun c hc hne => by rw [hoff hc hx (Ne.symm hne), mul_zero])
        (fun h => (h hx).elim), hdiag hx, mul_one]
    · exact (stays_on_centers ⟨g, hg⟩ x hx).trans (hf x hx).symm
  exact heq ▸ hg

end TranslatePacking

#print axioms TranslatePacking.inactive_of_two_tile_overlaps
#print axioms TranslatePacking.active_coordinate_recovers_tile
#print axioms TranslatePacking.aperiodic_isotropic_coordinate_space



