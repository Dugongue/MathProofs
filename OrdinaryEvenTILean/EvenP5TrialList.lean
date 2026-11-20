import EvenP5InvTransport
import EvenP5KernelScan
import EvenP5PhysicalExecution
import EvenP5EnlargedExecution

namespace EvenTI.TrialProducer

open EvenTI.Action EvenTI.Contract Matrix
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

abbrev Dense (K : Type) [Field K] (l n : ℕ) := Tensor K ((l + 1) + (l + 1)) n

inductive PreparedTrial (K : Type) [Field K] [DecidableEq K] (l n : ℕ)
  | reciprocal (anchors : HigherModes l → Matrix (Fin n) (Fin n) K)
  | orderFour (order : l = 1) (p : CutFormPair K 2 2 n)
      (left : Matrix (RawEnlargedIndex p.1) (RawEnlargedIndex p.1) K)
      (right : Matrix (RawEnlargedIndex p.2) (RawEnlargedIndex p.2) K)
  | higher (p : CutFormPair K (l + 1) (l + 1) n)
      (anchors : Fin (l + 1) × Bool → Matrix (Fin n) (Fin n) K)

def castFour (h : l = 1) (T : Dense K l n) : Dense K 1 n :=
  h ▸ T

def fourTrial (h : l = 1) (T : Dense K l n) (p : CutFormPair K 2 2 n) :
    PreparedTrial K l n :=
  let A := rawEnlargedAnchors p.1 p.2 (castFour h T)
  .orderFour h p A.1 A.2

def higherTrial (T : Dense K l n) (p : CutFormPair K (l + 1) (l + 1) n) :
    PreparedTrial K l n :=
  .higher p (rawHigherSingularAnchors p.1 p.2 T)

/-- Load the reciprocal anchors if inversion succeeds, otherwise feed the
actual kernel banks to the checked form scan and materialize its trial data. -/
def prepareTrials (F : FieldEncoding K) (T : Dense K l n) : List (PreparedTrial K l n) :=
  match rawReciprocalAnchors T with
  | some A => [.reciprocal A]
  | none =>
    if h : l = 1 then
      (rawUnfilteredCutForms F (castFour h T)).map (fourTrial h T)
    else
      (rawFullRankCutForms F T).map (higherTrial T)

theorem prepareTrials_reciprocal (F : FieldEncoding K) (T : Dense K l n)
    (A : HigherModes l → Matrix (Fin n) (Fin n) K) (h : rawReciprocalAnchors T = some A) :
    prepareTrials F T = [.reciprocal A] := by
  simp [prepareTrials, h]

theorem prepareTrials_four (F : FieldEncoding K) (T : Dense K 1 n)
    (h : ¬ IsUnit (flatten (l := 2) (r := 2) T)) :
    prepareTrials F T = (rawUnfilteredCutForms F T).map (fourTrial rfl T) := by
  simp [prepareTrials, (rawReciprocalAnchors_eq_none_iff T).mpr h, castFour]

theorem prepareTrials_higher (F : FieldEncoding K) (T : Dense K l n)
    (hl : l ≠ 1) (h : ¬ IsUnit (flatten (l := l + 1) (r := l + 1) T)) :
    prepareTrials F T = (rawFullRankCutForms F T).map (higherTrial T) := by
  simp [prepareTrials, (rawReciprocalAnchors_eq_none_iff T).mpr h, hl]

theorem prepareTrials_length_le (F : FieldEncoding K) (T : Dense K l n) :
    (prepareTrials F T).length ≤ max 1 (n^2) := by
  unfold prepareTrials
  split
  · simp
  · split
    · rw [List.length_map, rawUnfilteredCutForms]
      exact (rawCutBankForms_length F _ _ _).trans (Nat.le_max_right _ _)
    · rw [List.length_map, rawFullRankCutForms]
      exact (rawCutBankForms_length F _ _ _).trans (Nat.le_max_right _ _)

/-- A source pair appears with its transported forms in the target's actual
order-four scan, for the very same tensor transporter. -/
theorem fourTrials_follow (F : FieldEncoding K) (T : Dense K 1 n)
    (g : Changes K (2 + 2) n) (h : ¬ IsUnit (flatten (l := 2) (r := 2) T))
    (p : CutFormPair K 2 2 n) (hp : p ∈ rawUnfilteredCutForms F T) :
    fourTrial rfl T p ∈ prepareTrials F T ∧
    fourTrial rfl (act g T) (moveLeftForm (l := 2) (r := 2) g p.1,
      moveRightForm (l := 2) (r := 2) g p.2) ∈
      prepareTrials F (act g T) := by
  rw [prepareTrials_four F T h, prepareTrials_four F _ (fun hg => h ((cutUnit_act_iff g T).mp hg))]
  exact ⟨List.mem_map_of_mem hp,
    List.mem_map_of_mem (rawUnfilteredCutForms_transport F g rfl p.1 p.2 hp)⟩

/-- A source pair appears with its transported forms in the target's actual
higher-order scan. The rank checks and corank gates survive transport. -/
theorem higherTrials_follow (F : FieldEncoding K) (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (hl : l ≠ 1)
    (h : ¬ IsUnit (flatten (l := l + 1) (r := l + 1) T))
    (p : CutFormPair K (l + 1) (l + 1) n) (hp : p ∈ rawFullRankCutForms F T) :
    higherTrial T p ∈ prepareTrials F T ∧
    higherTrial (act g T) (moveLeftForm g p.1, moveRightForm g p.2) ∈
      prepareTrials F (act g T) := by
  rw [prepareTrials_higher F T hl h,
    prepareTrials_higher F _ hl (fun hg => h ((cutUnit_act_iff g T).mp hg))]
  exact ⟨List.mem_map_of_mem hp,
    List.mem_map_of_mem (rawFullRankCutForms_transport F g rfl p.1 p.2 hp)⟩

#print axioms prepareTrials_length_le
#print axioms fourTrials_follow
#print axioms higherTrials_follow

end EvenTI.TrialProducer
