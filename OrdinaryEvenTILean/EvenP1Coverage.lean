import EvenP1BadMass
import EvenP1DenseMarginal
import EvenP1Geometry
import EvenP1ProbSurjectivity

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped Matrix Classical
open Matrix EvenTI.Action

noncomputable section

private def swapHalves {K : Type*} [Field K] {s n : ℕ}
    (T : Tensor K (s+s) n) : Tensor K (s+s) n :=
  fun v => T (cutEquiv (cutEquiv.symm v).swap)

private theorem flatten_swapHalves {K : Type*} [Field K] {s n : ℕ}
    (T : Tensor K (s+s) n) : flatten (swapHalves T) = (flatten T)ᵀ := by
  ext a b
  change T (cutEquiv (cutEquiv.symm (cutEquiv (a,b))).swap) = T (cutEquiv (b,a))
  rw [Equiv.symm_apply_apply]
  rfl

private theorem swapHalves_twice {K : Type*} [Field K] {s n : ℕ}
    (T : Tensor K (s+s) n) : swapHalves (swapHalves T) = T := by
  funext v
  simp [swapHalves]

/-- Both orientations of the raw square cut have the same conditioned law. -/
def orientCut {K : Type*} [Field K] {s n : ℕ} (mirror : Bool) :
    InvertibleCut K s n ≃ InvertibleCut K s n :=
  if mirror then
    let f (T : InvertibleCut K s n) : InvertibleCut K s n :=
      ⟨swapHalves T.val, by rw [flatten_swapHalves, Matrix.isUnit_transpose]; exact T.property⟩
    ⟨f, f, fun T => Subtype.ext (swapHalves_twice T.val),
      fun T => Subtype.ext (swapHalves_twice T.val)⟩
  else Equiv.refl _

abbrev HigherRows (l n : ℕ) := Sum (High l n) (Low l n) × Option (OtherModes n)
abbrev HigherCols (l n : ℕ) := Fin n × Coord l n

open scoped BigOperators

/-- On the uniform dense source conditioned on an invertible square cut,
each chosen physical anchor in either half is exponentially close to its
uniform comparison law. The dimension threshold works for every even
order at least six and every finite field. -/
def HigherOrderReciprocalCoverage : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (l n : ℕ), 2 ≤ l → ∀ hn : 200 ≤ n,
    ∀ (i j : Fin (l+1)) (mirror : Bool),
      let eL := leftRegroup (l := l) (n := n) (by omega) i
      let eR := rightRegroup j
      let orient := orientCut (K := K) (s := l+1) (n := n) mirror
      (∀ [CharP K 2],
        marginalError (denseTraceAnchor eL eR ∘ orient) ≤ 9 * anchorError K (Fin n)) ∧
      ((2 : K) ≠ 0 →
        marginalError (denseAnchor eL eR ∘ orient) ≤ 9 * anchorError K (Fin n))

theorem higherOrder_reciprocal_coverage : HigherOrderReciprocalCoverage := by
  intro K _ _ l n hl hn i j mirror
  classical
  have hn1 : 1 ≤ n := by omega
  let eL := leftRegroup hn1 i
  let eR := rightRegroup (n := n) j
  let orient := orientCut (K := K) (s := l+1) (n := n) mirror
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (BasisPairs K (HigherRows l n) (HigherCols l n)) :=
    ⟨(basisPairsEquivUnits eL eR).symm 1⟩
  have hm : n^2 ≤ Fintype.card (Coord l n) :=
    higherOrderBundle_size hl (by omega)
  have hJ : Fintype.card (OtherModes n) = Fintype.card (Fin n) - 1 := by simp
  have hI : 200 ≤ Fintype.card (Fin n) := by simpa
  have hT : 8 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have ha : Fintype.card (Coord l n) / 5 = n^l / 5 := by rw [cut_side_card]
  let hChoice : Fin (Fintype.card (Coord l n) / 5) ↪ High l n :=
    (Fin.castLEEmb ha.le).trans (highChoice l n)
  have hbad₀ := actual_reciprocal_bad_mass_le_model (K := K) (H := High l n) (L := Low l n)
    (J := OtherModes n) (I := Fin n) (B := Coord l n) (BL := Chosen l n)
    hChoice (lowChoice l n) hJ (by simpa only [Fintype.card_fin] using ha.symm) hI
    (by simpa only [Fintype.card_fin] using hm)
  have hmodel := PartOne.unconditioned_reciprocal_bad_le
    (K := K) (I := Fin n) (L := Chosen l n) (J := OtherModes n) (B := Coord l n)
    hJ (by simpa only [Fintype.card_fin] using ha.symm) hI
    (by simpa only [Fintype.card_fin] using hm)
  have hbad := hbad₀.trans (mul_le_mul_of_nonneg_left hmodel (by norm_num : (0:ℝ) ≤ 4))
  rw [one_div] at hbad
  have hfinal : anchorError K (Fin n) +
      2 * EvenTI.Primary.event (fun A : BasisPairs K (HigherRows l n) (HigherCols l n) =>
        ¬ Function.Surjective (Next.baselineRows A)) ≤ 9 * anchorError K (Fin n) := by
    calc
      _ ≤ anchorError K (Fin n) + 2 * (4 * anchorError K (Fin n)) :=
        add_le_add (le_refl (anchorError K (Fin n)))
          (mul_le_mul_of_nonneg_left hbad (by norm_num : (0:ℝ) ≤ 2))
      _ = _ := by ring
  constructor
  · intro _
    change marginalError (denseTraceAnchor eL eR ∘ orient) ≤ _
    rw [marginalError_equiv_source]
    exact (denseTrace_marginal_of_bad_mass eL eR hJ hT).trans hfinal
  · intro h₂
    change marginalError (denseAnchor eL eR ∘ orient) ≤ _
    rw [marginalError_equiv_source]
    exact (denseOdd_marginal_of_bad_mass eL eR hJ hT h₂).trans hfinal

#print axioms higherOrder_reciprocal_coverage

end
end Mathproof.EvenTI.Reciprocal.Coverage
