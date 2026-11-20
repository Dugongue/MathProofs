import EvenP5InvAnchor
import EvenP5TransportDense

/-! Covariance of the actual reciprocal-anchor bank, including its failure branch. -/

namespace EvenTI.Contract

open EvenTI.Action Matrix
open Mathproof.EvenTI.Reciprocal.Coverage
open scoped Matrix

variable {K : Type} [Field K] {s l n : Nat}

private theorem cutUnit_act (g : Changes K (s + s) n) (T : Tensor K (s + s) n)
    (h : IsUnit (flatten (l := s) (r := s) T)) : IsUnit (flatten (l := s) (r := s) (act g T)) := by
  rw [flatten_action]
  have hr : IsUnit (productMatrix (rightModes g))ᵀ := by
    rw [Matrix.isUnit_transpose]
    exact (productUnit (rightModes g)).isUnit
  exact ((productUnit (leftModes g)).isUnit.mul h).mul hr

theorem cutUnit_act_iff (g : Changes K (s + s) n) (T : Tensor K (s + s) n) :
    IsUnit (flatten (l := s) (r := s) (act g T)) ↔ IsUnit (flatten (l := s) (r := s) T) := by
  refine ⟨?_, cutUnit_act g T⟩
  intro h
  have h' := cutUnit_act g⁻¹ (act g T) h
  rwa [← act_mul, inv_mul_cancel, act_one] at h'

/-- Effective transport of a reciprocal bank by the prescribed physical changes. -/
def conjugateReciprocalAnchors (g : Changes K ((l + 1) + (l + 1)) n)
    (A : HigherModes l → Matrix (Fin n) (Fin n) K) (i : HigherModes l) : Matrix (Fin n) (Fin n) K :=
  let q := if i.1 then leftModes g i.2 else rightModes g i.2
  q.val * A i * q.inv

theorem rawReciprocalAnchors_transport [Fintype K] [DecidableEq K] (hn : 1 ≤ n)
    (g : Changes K ((l + 1) + (l + 1)) n) (T : Tensor K ((l + 1) + (l + 1)) n) :
    rawReciprocalAnchors (act g T) = (rawReciprocalAnchors T).map (conjugateReciprocalAnchors g) := by
  by_cases hT : IsUnit (flatten (l := l + 1) (r := l + 1) T)
  · let U : InvertibleCut K (l + 1) n := ⟨T, hT⟩
    let V : InvertibleCut K (l + 1) n := ⟨act g T, cutUnit_act g T hT⟩
    have hU : rawReciprocalAnchors T = some (fun i => higherDenseModeAnchor hn i U) :=
      rawReciprocalAnchors_eq_higher hn U
    have hV : rawReciprocalAnchors (act g T) = some (fun i => higherDenseModeAnchor hn i V) :=
      rawReciprocalAnchors_eq_higher hn V
    rw [hU, hV, Option.map_some]
    congr 1
    funext i
    exact higherDenseModeAnchor_transport hn i U V g rfl
  · have hS := (cutUnit_act_iff g T).not.mpr hT
    rw [(rawReciprocalAnchors_eq_none_iff _).mpr hT, (rawReciprocalAnchors_eq_none_iff _).mpr hS,
      Option.map_none]

/-- Every genuine transporter sends the actual source bank to the actual target bank. -/
theorem rawReciprocalAnchors_target [Fintype K] [DecidableEq K] (hn : 1 ≤ n)
    {T S : Tensor K ((l + 1) + (l + 1)) n} (g : Changes K ((l + 1) + (l + 1)) n)
    (hg : act g T = S) {A : HigherModes l → Matrix (Fin n) (Fin n) K}
    (hA : rawReciprocalAnchors T = some A) :
    rawReciprocalAnchors S = some (conjugateReciprocalAnchors g A) := by
  rw [← hg, rawReciprocalAnchors_transport hn, hA, Option.map_some]

#print axioms cutUnit_act_iff
#print axioms rawReciprocalAnchors_transport
#print axioms rawReciprocalAnchors_target

end EvenTI.Contract
