import EvenP5Contract
import EvenP5TransportRawEnlarged

/-! View the actual trial anchors as square arrays on numeric indices.
The two ordinary branches use physical mode order. The enlarged order-four
branch retains one numbered anchor per cut side. -/

namespace EvenTI.PrimaryAlignment

open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open Mathproof.EvenOrdinaryTISingular.EnlargedCut
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)
open Mathproof.Problem17RepeatedBudget
open scoped BigOperators

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

structure NumberedAnchor (K : Type) where
  width : ℕ
  matrix : Matrix (Fin width) (Fin width) K

abbrev numeric {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : NumberedAnchor K := ⟨n, A⟩

def enlargedOrder (a k : ℕ) : Index a k ≃ Fin (k + (a + k)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def numberEnlarged {a k : ℕ} (A : Matrix (Index a k) (Index a k) K) : NumberedAnchor K :=
  numeric (Matrix.reindexAlgEquiv K _ (enlargedOrder a k) A)

private def sideOrder (l : ℕ) : Fin ((l + 1) + (l + 1)) ≃ Fin (l + 1) ⊕ Fin (l + 1) :=
  finSumFinEquiv.symm

def reciprocalOrder (l : ℕ) : Fin ((l + 1) + (l + 1)) ≃ HigherModes l :=
  (sideOrder l).trans ((Equiv.sumComm _ _).trans (Equiv.boolProdEquivSum _).symm)

def singularOrder (l : ℕ) : Fin ((l + 1) + (l + 1)) ≃ Fin (l + 1) × Bool :=
  (sideOrder l).trans ((Equiv.boolProdEquivSum _).symm.trans (Equiv.prodComm _ _))

/-- Number the actual stored anchors without making any further choices. -/
def numberedAnchors : PreparedTrial K l n → List (NumberedAnchor K)
  | .reciprocal A => List.ofFn fun i => numeric (A (reciprocalOrder l i))
  | .higher _ A => List.ofFn fun i => numeric (A (singularOrder l i))
  | .orderFour _ _ L R => [numberEnlarged L, numberEnlarged R]

def MatchedAnchors (S T : NumberedAnchor K) : Prop :=
  ∃ h : T.width = S.width,
    ∃ P : (Matrix (Fin S.width) (Fin S.width) K)ˣ,
      T.matrix.submatrix (finCongr h).symm (finCongr h).symm =
        P.val * S.matrix * P.inv

private theorem matchedNumeric {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (P : (Matrix (Fin n) (Fin n) K)ˣ) (h : B = P.val * A * P.inv) :
    MatchedAnchors (numeric A) (numeric B) := ⟨rfl, P, h⟩

private theorem matchedEnlarged {a k a' k' : ℕ} (ha : a' = a) (hk : k' = k)
    (A : Matrix (Index a k) (Index a k) K) (B : Matrix (Index a' k') (Index a' k') K)
    (P : (Matrix (Index a k) (Index a k) K)ˣ)
    (h : B.submatrix (enlargedIndexEquiv ha hk) (enlargedIndexEquiv ha hk) =
      P.val * A * P.inv) :
    MatchedAnchors (numberEnlarged A) (numberEnlarged B) := by
  subst a'
  subst k'
  have h' : B = P.val * A * P.inv := by
    simpa only [enlargedIndexEquiv, Equiv.coe_refl, Matrix.submatrix_id_id] using h
  let E : Matrix (Index a k) (Index a k) K ≃ₐ[K]
      Matrix (Fin (k + (a + k))) (Fin (k + (a + k))) K :=
    Matrix.reindexAlgEquiv K _ (enlargedOrder a k)
  apply matchedNumeric (Units.map E.toMonoidHom P)
  exact (congrArg E h').trans (by simp only [map_mul]; rfl)

private theorem forall₂_ofFn {S T : Type} (R : S → T → Prop) {m : ℕ}
    (s : Fin m → S) (t : Fin m → T) (h : ∀ i, R (s i) (t i)) :
    List.Forall₂ R (List.ofFn s) (List.ofFn t) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (ih _ _ fun i => h i.succ)

/-- Genuine trial pairings from the raw generator preserve the numeric
anchor order and each anchor is conjugate in its common coordinate width. -/
theorem numberedAnchors_follow (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (P Q : PreparedTrial K l n)
    (h : PreparedMatch T g P Q) :
    List.Forall₂ MatchedAnchors (numberedAnchors P) (numberedAnchors Q) := by
  cases h with
  | reciprocal A hbudget =>
    apply forall₂_ofFn
    intro i
    let j := reciprocalOrder l i
    exact matchedNumeric (if j.1 then leftModes g j.2 else rightModes g j.2) rfl
  | higher hl p hbudget =>
    apply forall₂_ofFn
    intro i
    let j := singularOrder l i
    exact matchedNumeric (if j.2 then rightModes g j.1 else leftModes g j.1)
      (rawHigherSingularAnchors_follow T g p.1 p.2 j)
  | four hl p hbudget =>
    subst l
    let hL := rawFrameWidth_move (leftModes (l := 2) (r := 2) g) p.1
    let hR := rawFrameWidth_move (rightModes (l := 2) (r := 2) g) p.2
    obtain ⟨U, V, hUV⟩ := rawEnlargedAnchors_transport g T p.1 p.2
    simp only [numberedAnchors, fourTrial, castFour, castFourChanges]
    apply List.Forall₂.cons
    · exact matchedEnlarged hL (congrArg (fun a => n - a) hL) _ _ U (congrArg Prod.fst hUV)
    · exact .cons (matchedEnlarged hR (congrArg (fun a => n - a) hR) _ _ V
        (congrArg Prod.snd hUV)) .nil

noncomputable def numberedBudget (A : List (NumberedAnchor K)) : ℕ :=
  (A.map (fun x => repeatedBudget x.matrix.charpoly)).sum

@[simp] theorem numberEnlarged_charpoly {a k : ℕ} (A : Matrix (Index a k) (Index a k) K) :
    (numberEnlarged A).matrix.charpoly = A.charpoly :=
  Matrix.charpoly_reindex (enlargedOrder a k) A

theorem numberedAnchors_gate (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (P Q : PreparedTrial K l n)
    (h : PreparedMatch T g P Q) :
    Fintype.card K ^ numberedBudget (numberedAnchors P) ≤
      (if l = 1 then n else n ^ ((l + 1) + (l + 1))) := by
  cases h with
  | reciprocal A hbudget =>
    have hsum := (reciprocalOrder l).sum_comp (fun i => repeatedBudget (A i).charpoly)
    simp only [numberedBudget, numberedAnchors, List.map_ofFn, List.sum_ofFn]
    change Fintype.card K ^ (∑ i, repeatedBudget (A (reciprocalOrder l i)).charpoly) ≤ _
    rw [hsum]
    exact hbudget
  | higher hl p hbudget =>
    have hsum := (singularOrder l).sum_comp (fun i =>
      repeatedBudget ((rawHigherSingularAnchors p.1 p.2 T) i).charpoly)
    have hl' : l ≠ 1 := by omega
    simp only [numberedBudget, numberedAnchors, higherTrial, List.map_ofFn, List.sum_ofFn,
      if_neg hl']
    change Fintype.card K ^ (∑ i, repeatedBudget
      ((rawHigherSingularAnchors p.1 p.2 T) (singularOrder l i)).charpoly) ≤ _
    rw [hsum]
    exact hbudget
  | four hl p hbudget =>
    subst l
    simpa [numberedBudget, numberedAnchors, fourTrial, enlargedBudget] using hbudget

#print axioms numberedAnchors_follow
#print axioms numberedAnchors_gate

end EvenTI.PrimaryAlignment
