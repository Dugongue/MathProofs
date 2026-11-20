import EvenP5InvCut
import EvenP4HigherRecip
import EvenP3RecipPrimary

/-! Executable reciprocal anchors. Renaming the two contracted left coordinates
does not affect the result, so the evaluator uses the physical indices directly. -/

namespace EvenTI.Contract

open EvenTI.Action Matrix
open Mathproof.EvenTI.Reciprocal
open Mathproof.EvenTI.Reciprocal.Coverage
open scoped BigOperators Matrix

variable {K : Type} [Field K] {X A J I B : Type}
variable [Fintype A] [Fintype J] [Fintype I] [Fintype B]

private def physicalCrossed (M N : Matrix X X K) (left : A × J ≃ X) (right : I × B ≃ X) :
    Matrix (J × I) (J × I) K :=
  fun p q => ∑ a : A, ∑ b : B, M (left (a,p.1)) (right (p.2,b)) *
    N (right (q.2,b)) (left (a,q.1))

private def physicalAnchor (M N : Matrix X X K) (left : A × J ≃ X) (right : I × B ≃ X) :
    Matrix I I K :=
  Small.partialTraceRight ((physicalCrossed M N left right) * (physicalCrossed M N left right))

private theorem physicalCrossed_reindex_left {A' J' : Type} [Fintype A'] [Fintype J']
    (M N : Matrix X X K) (left : A × J ≃ X) (right : I × B ≃ X)
    (ea : A' ≃ A) (ej : J' ≃ J) (p q : J' × I) :
    physicalCrossed M N ((Equiv.prodCongr ea ej).trans left) right p q =
      physicalCrossed M N left right (ej p.1,p.2) (ej q.1,q.2) := by
  simp only [physicalCrossed, Equiv.trans_apply, Equiv.prodCongr_apply]
  exact Equiv.sum_comp ea (fun a : A => ∑ b : B, M (left (a,ej p.1)) (right (p.2,b)) *
    N (right (q.2,b)) (left (a,ej q.1)))

private theorem physicalAnchor_reindex_left {A' J' : Type} [Fintype A'] [Fintype J']
    (M N : Matrix X X K) (left : A × J ≃ X) (right : I × B ≃ X)
    (ea : A' ≃ A) (ej : J' ≃ J) :
    physicalAnchor M N ((Equiv.prodCongr ea ej).trans left) right =
      physicalAnchor M N left right := by
  let left' := (Equiv.prodCongr ea ej).trans left
  ext i j
  change (∑ a : J', (physicalCrossed M N left' right * physicalCrossed M N left' right) (a,i) (a,j)) =
    (∑ a : J, (physicalCrossed M N left right * physicalCrossed M N left right) (a,i) (a,j))
  simp only [Matrix.mul_apply, left', physicalCrossed_reindex_left]
  let e : J' × I ≃ J × I := Equiv.prodCongr ej (Equiv.refl I)
  let c := physicalCrossed M N left right
  change (∑ a : J', ∑ r : J' × I, c (ej a,i) (e r) * c (e r) (ej a,j)) =
    ∑ a : J, ∑ r : J × I, c (a,i) r * c r (a,j)
  calc
    _ = ∑ a : J', ∑ r : J × I, c (ej a,i) r * c r (ej a,j) :=
      Finset.sum_congr rfl fun a _ => Equiv.sum_comp e (fun r : J × I => c (ej a,i) r * c r (ej a,j))
    _ = _ := Equiv.sum_comp ej (fun a : J => ∑ r : J × I, c (a,i) r * c r (a,j))

private theorem denseAnchor_eq_physicalAnchor {H L : Type} [Fintype H] [Fintype L]
    [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B] {s n : Nat}
    (left : (Sum H L × Option J) ≃ Coord s n) (right : I × B ≃ Coord s n) (T : InvertibleCut K s n) :
    denseAnchor left right T = physicalAnchor (flatten T.val) (flatten T.val)⁻¹ left right := by
  unfold denseAnchor physicalAnchor
  rw [pow_two]
  rfl

private def orientMatrix (mirror : Bool) (M : Matrix X X K) : Matrix X X K :=
  if mirror then M.transpose else M

private theorem flatten_orientCut {s n : Nat} (mirror : Bool) (T : InvertibleCut K s n) :
    flatten (orientCut mirror T).val = orientMatrix mirror (flatten T.val) := by
  cases mirror with
  | false => rfl
  | true =>
    ext a b
    change T.val (cutEquiv (cutEquiv.symm (cutEquiv (a,b))).swap) = T.val (cutEquiv (b,a))
    rw [Equiv.symm_apply_apply]
    rfl

private theorem inverse_orientCut {s n : Nat} (mirror : Bool) (T : InvertibleCut K s n) :
    (flatten (orientCut mirror T).val)⁻¹ = orientMatrix mirror ((flatten T.val)⁻¹) := by
  rw [flatten_orientCut]
  cases mirror
  · rfl
  · exact (Matrix.transpose_nonsing_inv (flatten T.val)).symm

private def physicalLeft {l n : Nat} : Coord l n × Fin n ≃ Coord (l + 1) n :=
  (Equiv.prodComm _ _).trans (retainedMode 0)

/-- The anchor for one physical mode, taking a previously computed reciprocal cut. -/
def rawReciprocalAnchor {l n : Nat} (T : Tensor K ((l + 1) + (l + 1)) n)
    (N : Matrix (Coord (l + 1) n) (Coord (l + 1) n) K) (i : HigherModes l) : Matrix (Fin n) (Fin n) K :=
  physicalAnchor (orientMatrix i.1 (flatten T)) (orientMatrix i.1 N)
    physicalLeft (retainedMode i.2)

theorem rawReciprocalAnchor_eq_higher [Fintype K] {l n : Nat} (hn : 1 ≤ n)
    (T : InvertibleCut K (l + 1) n) (i : HigherModes l) :
    rawReciprocalAnchor T.val (flatten T.val)⁻¹ i = higherDenseModeAnchor hn i T := by
  unfold rawReciprocalAnchor higherDenseModeAnchor
  rw [denseAnchor_eq_physicalAnchor, inverse_orientCut, flatten_orientCut]
  exact (physicalAnchor_reindex_left _ _ physicalLeft (rightRegroup i.2)
    (bundleEquiv l n) (distinguishedEquiv n hn)).symm

theorem rawReciprocalAnchor_eq_square [Fintype K] {n : Nat} (hn : 5 ≤ n)
    (T : InvertibleCut K 2 n) (i : FourModes) :
    rawReciprocalAnchor (l := 1) T.val (flatten T.val)⁻¹ i = squareDenseModeAnchor hn i T := by
  unfold squareDenseModeAnchor rawReciprocalAnchor
  rw [denseAnchor_eq_physicalAnchor, inverse_orientCut, flatten_orientCut]
  let ej : Option (SquareGroups n) ≃ Fin n := (Equiv.optionCongr (Fintype.equivOfCardEq (by
    rw [squareGroups_card n hn, Fintype.card_fin]))).trans (distinguishedEquiv n (by omega))
  exact (physicalAnchor_reindex_left _ _ physicalLeft (rightRegroup i.2) (bundleEquiv 1 n) ej).symm

/-- All reciprocal anchors of the raw tensor, or failure exactly when the cut is singular. -/
def rawReciprocalAnchors [DecidableEq K] {l n : Nat} (T : Tensor K ((l + 1) + (l + 1)) n) :
    Option (HigherModes l → Matrix (Fin n) (Fin n) K) :=
  (rawCutInverse T).map (rawReciprocalAnchor T)

theorem rawReciprocalAnchors_eq_none_iff [DecidableEq K] {l n : Nat}
    (T : Tensor K ((l + 1) + (l + 1)) n) :
    rawReciprocalAnchors T = none ↔ ¬ IsUnit (flatten (l := l + 1) (r := l + 1) T) := by
  rw [rawReciprocalAnchors, Option.map_eq_none_iff, rawCutInverse_eq_none_iff]

theorem rawReciprocalAnchors_eq_higher [Fintype K] [DecidableEq K] {l n : Nat} (hn : 1 ≤ n)
    (T : InvertibleCut K (l + 1) n) :
    rawReciprocalAnchors T.val = some (fun i => higherDenseModeAnchor hn i T) := by
  unfold rawReciprocalAnchors
  rw [(rawCutInverse_eq_some_iff T.val _).mpr ⟨T.property, rfl⟩, Option.map_some]
  congr 1
  funext i
  exact rawReciprocalAnchor_eq_higher hn T i

theorem rawReciprocalAnchors_eq_square [Fintype K] [DecidableEq K] {n : Nat} (hn : 5 ≤ n)
    (T : InvertibleCut K 2 n) :
    rawReciprocalAnchors (l := 1) T.val = some (fun i => squareDenseModeAnchor hn i T) := by
  unfold rawReciprocalAnchors
  rw [(rawCutInverse_eq_some_iff T.val _).mpr ⟨T.property, rfl⟩, Option.map_some]
  congr 1
  funext i
  exact rawReciprocalAnchor_eq_square hn T i

#print axioms rawReciprocalAnchors_eq_none_iff
#print axioms rawReciprocalAnchors_eq_higher
#print axioms rawReciprocalAnchors_eq_square

end EvenTI.Contract
