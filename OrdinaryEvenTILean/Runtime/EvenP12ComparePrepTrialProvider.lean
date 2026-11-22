import EvenP12ComparePrepFourBudget
import EvenP12ComparePrepSpectral

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Form trials directly from the four placed kernel banks. The reciprocal
case and the anchor constructors retain their existing definitions. -/
noncomputable def trialsFromCutState (D : FieldEncoding K) (F : FieldPresentation K)
    {l n : ℕ} (T S : Dense K l n) (target : Bool) (σ : Env) :
    List (PreparedTrial K l n) :=
  let U := if target then S else T
  match rawReciprocalAnchors U with
  | some A => [.reciprocal A]
  | none =>
    if h : l = 1 then
      (placedFormPairs (a := 2) (n := n) D F target σ (fun _ => true) (fun _ => true)).map
        (fourTrial h U)
    else
      (placedFormPairs (a := l+1) (n := n) D F target σ rawRetainedFullRank rawRetainedFullRank).map
        (higherTrial U)

/-- The installed banks give exactly the reference trial set. Their order may
differ because the physical row-kernel routine chooses its own basis order. -/
theorem mem_trialsFromCutState (D : FieldEncoding K) (F : FieldPresentation K)
    {l n : ℕ} (T S : Dense K l n) (target : Bool) (σ : Env)
    (left : InstalledCut F T S (leftCutAt target) σ)
    (right : InstalledCut F T S (rightCutAt target) σ) (p : PreparedTrial K l n) :
    p ∈ trialsFromCutState D F T S target σ ↔ p ∈ prepareTrials D (if target then S else T) := by
  by_cases hl : l=1
  · subst l
    unfold trialsFromCutState prepareTrials
    cases hr : rawReciprocalAnchors (if target then S else T) with
    | some A => simp only [hr]
    | none =>
      simp only [hr,dif_pos rfl,dif_pos True.intro,castFour,rawUnfilteredCutForms,List.mem_map]
      exact exists_congr fun q => and_congr
        (mem_placedFormPairs D F T S target σ left right (fun _ => true) (fun _ => true) q) Iff.rfl
  · unfold trialsFromCutState prepareTrials
    cases hr : rawReciprocalAnchors (if target then S else T) with
    | some A => simp only [hr]
    | none =>
      simp only [hr,dif_neg hl,rawFullRankCutForms,List.mem_map]
      exact exists_congr fun q => and_congr
        (mem_placedFormPairs D F T S target σ left right rawRetainedFullRank rawRetainedFullRank q) Iff.rfl

private theorem listProduct_length {A B : Type} (xs : List A) (ys : List B) :
    (xs.product ys).length = xs.length*ys.length := List.length_product xs ys

theorem placedFormPairs_length_le (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (target : Bool) (σ : Env) (goodL goodR : (Coord a n → K) → Bool) :
    (placedFormPairs D F target σ goodL goodR).length ≤ n^2 := by
  unfold placedFormPairs bankCutFormPairs bankForms linearChoices
  simp only [listProduct_length,pow_two]
  apply Nat.mul_le_mul
  all_goals
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_map]
    exact coefficientChoices_length_le D _ n

theorem trialsFromCutState_length_le (D : FieldEncoding K) (F : FieldPresentation K)
    {l n : ℕ} (T S : Dense K l n) (target : Bool) (σ : Env) :
    (trialsFromCutState D F T S target σ).length ≤ max 1 (n^2) := by
  cases hr : rawReciprocalAnchors (if target then S else T) with
  | some A =>
    simp only [trialsFromCutState,hr,List.length_singleton]
    exact Nat.le_max_left _ _
  | none =>
    by_cases h : l=1
    · simp only [trialsFromCutState,hr,dif_pos h,List.length_map]
      exact (placedFormPairs_length_le D F target σ _ _).trans (Nat.le_max_right _ _)
    · simp only [trialsFromCutState,hr,dif_neg h,List.length_map]
      exact (placedFormPairs_length_le D F target σ _ _).trans (Nat.le_max_right _ _)
noncomputable def automaticCutState (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (ha : 2 ≤ a) (hn : 2 ≤ n) : Env :=
  (comparisonFourBinarySized_run D F T S (fun _ => 0) ha hn).choose

theorem automaticCutState_run (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (ha : 2 ≤ a) (hn : 2 ≤ n) :
    let w := comparisonInput D T S
    let L := bitSize w
    Run ((comparisonWordPoly F).eval L) (comparisonFourReadyProgram D F)
      (initEnv (comparisonInitExt F (pairCutSlotCount.value (n^a)) w.length (fun _ => 0)) (w.length::w))
      (automaticCutState D F T S ha hn)
      (40*(L+1)+3*F.e+26+4*oneCutCostBound F L) := by
  exact (comparisonFourBinarySized_run D F T S (fun _ => 0) ha hn).choose_spec.1
theorem automaticCutState_installed (D : FieldEncoding K) (F : FieldPresentation K)
    {a n : ℕ} (T S : Tensor K (a+a) n) (ha : 2 ≤ a) (hn : 2 ≤ n) (j : Fin 4) :
    InstalledCut F T S j (automaticCutState D F T S ha hn) := by
  obtain ⟨_,_,_,_,_,_,hReady,_,_⟩ := (comparisonFourBinarySized_run D F T S (fun _ => 0) ha hn).choose_spec
  exact hReady j

/-- The exact source/target trial list for a reference plan. On its admitted
shape it reads the state of the sized physical four-cut run. Outside that
shape the abstract reference list keeps the provider total. -/
noncomputable def automaticCutTrialProvider (D : FieldEncoding K) (F : FieldPresentation K) :
    BalancedTrialPairs K :=
  fun {d n} h T S =>
    if hReady : 2 ≤ cutHalf d+1 ∧ 2 ≤ n then
      let T' := castDense (cutHalf d) h T
      let S' := castDense (cutHalf d) h S
      let τ := automaticCutState D F T' S' hReady.1 hReady.2
      (trialsFromCutState D F T' S' false τ).product (trialsFromCutState D F T' S' true τ)
    else pairsAt D (cutHalf d) h T S

theorem automaticCutTrialProvider_exact (D : FieldEncoding K) (F : FieldPresentation K) :
    ExactRawTrialPairs D (automaticCutTrialProvider D F) := by
  intro d n h T S p
  dsimp only [automaticCutTrialProvider]
  by_cases hReady : 2 ≤ cutHalf d+1 ∧ 2 ≤ n
  · rw [dif_pos hReady]
    let T' := castDense (cutHalf d) h T
    let S' := castDense (cutHalf d) h S
    let τ := automaticCutState D F T' S' hReady.1 hReady.2
    have checks (j : Fin 4) : InstalledCut F T' S' j τ :=
      automaticCutState_installed D F T' S' hReady.1 hReady.2 j
    obtain ⟨p,q⟩ := p
    exact List.mem_product.trans ((and_congr
      (mem_trialsFromCutState D F T' S' false τ (checks _) (checks _) p)
      (mem_trialsFromCutState D F T' S' true τ (checks _) (checks _) q)).trans List.mem_product.symm)
  · rw [dif_neg hReady]

theorem automaticCutTrialProvider_covers (D : FieldEncoding K) (F : FieldPresentation K) :
    CoversRawTrialPairs D (automaticCutTrialProvider D F) :=
  fun h T S p => (automaticCutTrialProvider_exact D F h T S p).mpr

#print axioms automaticCutState_run
#print axioms automaticCutState_installed
#print axioms mem_trialsFromCutState
#print axioms automaticCutTrialProvider_exact
end EvenTI.P12ComparePrep
