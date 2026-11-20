import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.Basic

namespace SystematicAlphabetEquivalence

open scoped BigOperators

variable {I J G H : Type*} [Fintype I] [AddCommGroup G] [AddCommGroup H]

/-- The systematic encoding has input block x and parity block parity A x. -/
def parity (A : J → I → G →+ G) (x : I → G) (j : J) : G :=
  ∑ i, A j i (x i)

/-- Each parity coordinate has two independent sources of every alphabet letter. -/
def DisjointParityRealizations (A : J → I → G →+ G) : Prop :=
  ∀ j u v, ∃ x y : I → G,
    parity A x j = u ∧ parity A y j = v ∧ ∀ i, x i = 0 ∨ y i = 0

/-- Every input letter is determined by its parity contributions at all outputs. -/
def SeparatingColumns (B : J → I → H →+ H) : Prop :=
  ∀ i u v, (∀ j, B j i u = B j i v) → u = v

/-- Coordinatewise alphabet maps carry the systematic graph of A into that of B. -/
def Carries (A : J → I → G →+ G) (B : J → I → H →+ H)
    (f : I → G → H) (g : J → G → H) : Prop :=
  ∀ x j, g j (parity A x j) = parity B (fun i => f i (x i)) j

def centered (f : G → H) (x : G) : H := f x - f 0

private theorem centered_carries
    {A : J → I → G →+ G} {B : J → I → H →+ H}
    {f : I → G → H} {g : J → G → H} (h : Carries A B f g) :
    Carries A B (fun i => centered (f i)) (fun j => centered (g j)) := by
  intro x j
  have hz : g j 0 = ∑ i, B j i (f i 0) := by
    simpa [parity] using h (fun _ => 0) j
  change g j (parity A x j) - g j 0 = parity B (fun i => centered (f i) (x i)) j
  rw [h x j, hz]
  simp only [parity, centered, map_sub, Finset.sum_sub_distrib]

private theorem parity_add (A : J → I → G →+ G) (x y : I → G) (j : J) :
    parity A (fun i => x i + y i) j = parity A x j + parity A y j := by
  simp only [parity, map_add, Finset.sum_add_distrib]

private theorem parity_impulse (A : J → I → G →+ G)
    (i : I) (u : G) (j : J) [DecidableEq I] :
    parity A (fun k => if k = i then u else 0) j = A j i u := by
  unfold parity
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki]
  · simp

private def centeredEquiv (f : G ≃ H)
    (h : ∀ u v, centered f (u + v) = centered f u + centered f v) : G ≃+ H where
  toFun := centered f
  invFun y := f.symm (y + f 0)
  left_inv x := by simp [centered]
  right_inv y := by simp [centered]
  map_add' := h

/-- Under disjoint parity realizations and column separation, every alphabet
equivalence of a fixed systematic alignment is a translation of an additive one. -/
theorem recovers_centered_additive_equivalence
    (A : J → I → G →+ G) (B : J → I → H →+ H)
    (hrows : DisjointParityRealizations A) (hcols : SeparatingColumns B)
    (f : I → G ≃ H) (g : J → G ≃ H)
    (h : Carries A B (fun i => f i) (fun j => g j)) :
    ∃ (f' : I → G ≃+ H) (g' : J → G ≃+ H),
      Carries A B (fun i => f' i) (fun j => g' j) ∧
      (∀ i x, f' i x = f i x - f i 0) ∧
      (∀ j x, g' j x = g j x - g j 0) := by
  classical
  have hc := centered_carries h
  have hg : ∀ j u v, centered (g j) (u + v) =
      centered (g j) u + centered (g j) v := by
    intro j u v
    obtain ⟨x, y, hx, hy, hdisj⟩ := hrows j u v
    have hpair (i : I) : centered (f i) (x i + y i) =
        centered (f i) (x i) + centered (f i) (y i) := by
      rcases hdisj i with hx0 | hy0
      · simp [hx0, centered]
      · simp [hy0, centered]
    calc
      centered (g j) (u + v) =
          centered (g j) (parity A (fun i => x i + y i) j) := by
        rw [parity_add, hx, hy]
      _ = parity B (fun i => centered (f i) (x i + y i)) j := hc _ _
      _ = parity B (fun i => centered (f i) (x i) + centered (f i) (y i)) j := by
        simp only [hpair]
      _ = centered (g j) u + centered (g j) v := by
        rw [parity_add, ← hc x j, ← hc y j, hx, hy]
  have hsingle (i : I) (u : G) (j : J) :
      centered (g j) (A j i u) = B j i (centered (f i) u) := by
    have hpoint (k : I) : centered (f k) (if k = i then u else 0) =
        if k = i then centered (f i) u else 0 := by
      by_cases hki : k = i
      · subst k
        simp
      · simp [hki, centered]
    simpa only [parity_impulse, hpoint] using hc (fun k => if k = i then u else 0) j
  have hf : ∀ i u v, centered (f i) (u + v) =
      centered (f i) u + centered (f i) v := by
    intro i u v
    apply hcols i
    intro j
    rw [map_add, ← hsingle i (u + v) j, ← hsingle i u j, ← hsingle i v j,
      map_add, hg]
  exact ⟨(fun i => centeredEquiv (f i) (hf i)), (fun j => centeredEquiv (g j) (hg j)),
    hc, (fun _ _ => rfl), (fun _ _ => rfl)⟩

end SystematicAlphabetEquivalence
