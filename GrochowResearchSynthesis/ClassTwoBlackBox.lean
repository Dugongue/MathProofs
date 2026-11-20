import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Abel

namespace ClassTwoBlackBox

/-- Contraction with a perfect private pair, together with its residual block. -/
def pairedContraction {X P W : Type*} [AddCommGroup X] [AddCommGroup W]
    (pairToX : P ≃ X) (pairToP : X ≃ P) (xx : X → X) (xw : W → X)
    (wx : X → W) (ww : W → W) : X × P × W → X × P × W :=
  fun (x, p, w) => (xx x + pairToX p + xw w, pairToP x, wx x + ww w)

/-- A perfect pair removes exactly the other blocks involving its named carrier. -/
theorem paired_range_iff {X P W : Type*} [AddCommGroup X] [AddCommGroup W]
    (pairToX : P ≃ X) (pairToP : X ≃ P) (xx : X → X) (xw : W → X)
    (wx : X → W) (ww : W → W) (y : X) (q : P) (z : W) :
    (y, q, z) ∈ Set.range (pairedContraction pairToX pairToP xx xw wx ww) ↔
      z - wx (pairToP.symm q) ∈ Set.range ww := by
  constructor
  · rintro ⟨⟨x, p, w⟩, h⟩
    change (xx x + pairToX p + xw w, pairToP x, wx x + ww w) = (y, q, z) at h
    have hq : pairToP x = q := congrArg (fun u : X × P × W => u.2.1) h
    have hz : wx x + ww w = z := congrArg (fun u : X × P × W => u.2.2) h
    refine ⟨w, ?_⟩
    rw [← hq, pairToP.symm_apply_apply, ← hz]
    abel
  · rintro ⟨w, hw⟩
    let x := pairToP.symm q
    let p := pairToX.symm (y - xx x - xw w)
    refine ⟨(x, p, w), ?_⟩
    change (xx x + pairToX p + xw w, pairToP x, wx x + ww w) = (y, q, z)
    have hp : pairToX p = y - xx x - xw w := pairToX.apply_symm_apply _
    have hq : pairToP x = q := pairToP.apply_symm_apply _
    rw [hp, hq, hw]
    change (xx x + (y - xx x - xw w) + xw w, q, wx x + (z - wx x)) = (y, q, z)
    congr 1
    · abel
    · congr 1
      abel

/-- The anchor bracket and power constraints force the common unit to be one. -/
theorem unit_power_anchor {R : Type*} [Monoid R] (u : Rˣ)
    (h : (u : R) * (u : R) = (u : R)) : (u : R) = 1 := by
  have hu : u * u = u := Units.ext h
  have h_one : u = 1 := mul_left_cancel (hu.trans (mul_one u).symm)
  simp [h_one]

/-- Heavy weights indexed from zero through seven. -/
def weight (d i : ℕ) : ℕ := 2 * (9 + i) * (d + 1)

/-- Distinct singleton bands have disjoint ranges. -/
theorem singleton_bands_disjoint (d i j : ℕ) (hij : i < j) :
    weight d i + d < weight d j := by
  have h : 2 * (9 + i) + 2 ≤ 2 * (9 + j) := by omega
  unfold weight
  calc
    2 * (9 + i) * (d + 1) + d < (2 * (9 + i) + 2) * (d + 1) := by
      rw [Nat.add_mul]
      omega
    _ ≤ 2 * (9 + j) * (d + 1) := Nat.mul_le_mul_right _ h

/-- Any two unit markers have combined weight beyond all eight singleton bands. -/
theorem two_markers_above_singletons (d : ℕ) : weight d 7 + d < 2 * weight d 0 := by
  unfold weight
  omega

end ClassTwoBlackBox

#print axioms ClassTwoBlackBox.paired_range_iff
#print axioms ClassTwoBlackBox.unit_power_anchor
#print axioms ClassTwoBlackBox.singleton_bands_disjoint
#print axioms ClassTwoBlackBox.two_markers_above_singletons
