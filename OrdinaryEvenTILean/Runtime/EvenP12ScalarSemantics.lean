import EvenP12ScalarSelfPair
import EvenP12CompareBasisIndependent
import EvenP9FullScannerSound

namespace EvenTI.P12Scalar

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.CellPreparation EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12Compare

open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option autoImplicit false
set_option maxHeartbeats 520000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ}

theorem decodePair_selfPairWords (F : FieldEncoding K) (w : List ℕ) (p : ParsedSource K)
    (hw : decodeSource F w = some p) :
    decodePair F (selfPairWords w) = some ⟨p.d,p.n,p.tensor,p.tensor⟩ := by
  cases w with
  | nil => simp [decodeSource] at hw
  | cons d w =>
    cases w with
    | nil => simp [decodeSource] at hw
    | cons n ws =>
      simp only [decodeSource] at hw
      split at hw
      · rename_i h
        have hAND := h
        simp only [Bool.and_eq_true] at hAND
        obtain ⟨⟨ha,hL⟩,hD⟩ := hAND
        have hL' : ws.length = n^d := of_decide_eq_true hL
        have hd : admissibleHeader d n (ws++ws).length = true := by
          simp only [admissibleHeader, decide_eq_true_eq, List.length_append] at ha ⊢
          omega
        have ht : (ws ++ ws).take (n^d) = ws := by rw [← hL']; simp
        have hb : (ws ++ ws).drop (n^d) = ws := by rw [← hL']; simp
        cases hw
        change decodePair F (d::n::(ws++ws)) = _
        simp only [decodePair, hd, List.all_append, hD, Bool.and_self, Bool.and_true]
        have hlen : ((ws++ws).length = 2*n^d) := by
          rw [List.length_append,hL',Nat.two_mul]
        simp [hlen,ht,hb]
      · simp at hw

noncomputable def checkSelfPair (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) {l n : ℕ} (T : Dense K l n) (P Q : PreparedTrial K l n) : Bool :=
  match h : compileTrialBanks F T T P Q with
  | none => true
  | some out => out.branches.attach.all (checkSelfBranch F FP enum T P Q out h)

private theorem all_pair_product {A B : Type} (l : List A) (r : List B) (f : A → B → Bool) :
    (l.product r).all (fun p => f p.1 p.2) = l.all (fun a => r.all (f a)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h a ha b hb
    exact h ⟨a,b⟩ (List.mem_product.mpr ⟨ha,hb⟩)
  · intro h p hp
    obtain ⟨hl,hr⟩ := List.mem_product.mp hp
    exact h p.1 hl p.2 hr

theorem checkScalarOnDense_eq_product (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) {l n : ℕ} (T : Dense K l n) :
    checkScalarOnDense F FP enum T =
      ((decide (T ≠ 0) && rawRetainedFullRank (l := (l+1)+l) T) &&
        ((prepareTrials F T).product (prepareTrials F T)).all
          (fun p => checkSelfPair F FP enum T p.1 p.2)) := by
  rw [all_pair_product]
  rfl

theorem checkScalarOnDense_eq_banks (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T)
    {l n : ℕ} (T : Dense K l n) :
    checkScalarOnDense F FP enum T =
      ((decide (T ≠ 0) && rawRetainedFullRank (l := (l+1)+l) T) &&
        ((prepareFromBanks F banks T).product (prepareFromBanks F banks T)).all
          (fun p => checkSelfPair F FP enum T p.1 p.2)) := by
  rw [checkScalarOnDense_eq_product,all_pair_product,all_pair_product]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,List.all_eq_true,mem_prepareFromBanks]

/-- The local self-pair call uses exactly the comparison request layout. Its
output is a decision bit and each feasible branch is checked. -/
noncomputable def preparedSelfWords (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (w : List ℕ) : List ℕ :=
  let (words, encoded) := unpairW w
  match decodePair F words with
  | none => [0]
  | some p =>
    if h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) then
      let (left,right) := unpairW encoded
      match decodePreparedTrialWords (l := cutHalf p.d) (n := p.n) F left,
            decodePreparedTrialWords (l := cutHalf p.d) (n := p.n) F right with
      | some P, some Q =>
        if checkSelfPair F FP enum (castDense (cutHalf p.d) h p.source) P Q then [1] else [0]
      | _,_ => [0]
    else [0]

theorem preparedSelfWords_encode (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (words : List ℕ) (p : ParsedPair K)
    (hp : decodePair F words = some p)
    (h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1))
    (b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n) :
    preparedSelfWords F FP enum
      (pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2))) =
      if checkSelfPair F FP enum (castDense (cutHalf p.d) h p.source) b.1 b.2
      then [1] else [0] := by
  rcases b with ⟨P,Q⟩
  simp only [preparedSelfWords,unpairW_pairW,hp,dif_pos h,decodePreparedTrialWords_encode]

theorem preparedSelfWords_bit (F : FieldEncoding K) (FP : FieldPresentation K)
    (enum : Fin q ≃ Kˣ) (w : List ℕ) :
    preparedSelfWords F FP enum w = [0] ∨ preparedSelfWords F FP enum w = [1] := by
  unfold preparedSelfWords
  repeat' first | exact Or.inl rfl | exact Or.inr rfl | split

#print axioms decodePair_selfPairWords
#print axioms checkScalarOnDense_eq_banks
#print axioms preparedSelfWords_encode
#print axioms preparedSelfWords_bit

end EvenTI.P12Scalar
