import EvenDenseDecode
import EvenFilteredTransport

/-! The comparison driver using a finite list of prepared trials and the
counting interface for sources with certified scalar stabilizers. -/
namespace EvenTI.Contract

open Action

variable {K : Type} [Field K]

structure TrialPlan (K : Type) [Field K] where
  Index : Nat → Nat → Type
  enumerate : ∀ {d n}, Tensor K d n → Tensor K d n → List (Index d n)
  attempt : ∀ {d n}, Tensor K d n → Tensor K d n → Index d n → Option (Changes K d n)

variable {d n : Nat}

/-- The loop tries the actual candidates in list order and returns the
first successful transporter. -/
def search (P : TrialPlan K) (T S : Tensor K d n) : Option (Changes K d n) :=
  (P.enumerate T S).findSome? (P.attempt T S)

structure CompleteTrials (P : TrialPlan K) (T S : Tensor K d n) : Prop where
  sound : ∀ b ∈ P.enumerate T S, ∀ g, P.attempt T S b = some g → act g T = S
  complete : (∃ g, act g T = S) → ∃ b ∈ P.enumerate T S, ∃ g, P.attempt T S b = some g

theorem search_sound (P : TrialPlan K) {T S : Tensor K d n} (h : CompleteTrials P T S)
    {g : Changes K d n} (hg : search P T S = some g) : act g T = S := by
  obtain ⟨b, hb, hbg⟩ := List.exists_of_findSome?_eq_some hg
  exact h.sound b hb g hbg

theorem search_none_iff (P : TrialPlan K) {T S : Tensor K d n} (h : CompleteTrials P T S) :
    search P T S = none ↔ ∀ g, act g T ≠ S := by
  constructor
  · intro hn g hg
    obtain ⟨b, hb, a, ha⟩ := h.complete ⟨g, hg⟩
    unfold search at hn
    rw [List.findSome?_eq_none_iff] at hn
    have hnone := hn b hb
    rw [ha] at hnone
    cases hnone
  · intro hn
    unfold search
    apply List.findSome?_eq_none_iff.mpr
    intro b hb
    cases ha : P.attempt T S b with
    | none => rfl
    | some g => exact False.elim (hn g (h.sound b hb g ha))

/-- Exact list-level cost for the branch visits, with the cost of each
attempt supplied by the corresponding instantiated trial procedure. -/
def chargeScan {A B : Type*} (visit : A → Option B) (cost : A → Nat) :
    List A → Nat
  | [] => 0
  | a :: tail => cost a + if (visit a).isSome then 0 else chargeScan visit cost tail

theorem chargeScan_le {A B : Type*} (visit : A → Option B) (cost : A → Nat)
    (xs : List A) (C : Nat) (h : ∀ x ∈ xs, cost x ≤ C) :
    chargeScan visit cost xs ≤ xs.length * C := by
  induction xs with
  | nil => simp [chargeScan]
  | cons a xs ih =>
    have hhead := h a (by simp)
    have htail := ih (fun x hx => h x (by simp [hx]))
    simp only [chargeScan, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

variable [Fintype K] [DecidableEq K]

def recognizeWords (F : FieldEncoding K)
    (accept : ∀ {d n}, Tensor K d n → Bool) (words : List Nat) : List Nat :=
  match decodeSource F words with
  | none => [0]
  | some p => if accept p.tensor then [1] else [0]

def compareWords (F : FieldEncoding K) (P : TrialPlan K) (words : List Nat) : List Nat :=
  match decodePair F words with
  | none => [0]
  | some p =>
    match search P p.source p.target with
    | none => [0]
    | some g => transporterOutput F g ((Fintype.card K - 1) ^ (p.d - 1))

def countWords {q : Nat} (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (test : List Nat → List Nat) (words : List Nat) : List Nat :=
  match words with
  | length :: body =>
    match decodePair F (body.drop length) with
    | none => [0]
    | some p =>
      [countFromSearch enum (search P p.source p.target) fun i a =>
        decide (test (filterInput F (body.take length) i.val a) = [1])]
  | [] => [0]

theorem recognizeWords_encode (F : FieldEncoding K)
    (accept : ∀ {d n}, Tensor K d n → Bool) (T : Tensor K d n)
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) :
    recognizeWords F accept (sourceInput F T) = (if accept T then [1] else [0]) := by
  simp [recognizeWords, decodeSource_encode F T hd he hn]

theorem compareWords_correct (F : FieldEncoding K) (P : TrialPlan K)
    {T S : Tensor K d n} (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n)
    (hnz : T ≠ 0) (trials : CompleteTrials P T S)
    (scalarOnly : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u) :
    (compareWords F P (comparisonInput F T S) = [0] ∧ ∀ g, act g T ≠ S) ∨
    ∃ g : Changes K d n, act g T = S ∧
      compareWords F P (comparisonInput F T S) =
        transporterOutput F g (Nat.card {a : Changes K d n // act a T = S}) := by
  unfold compareWords
  rw [decodePair_encode F T S hd he hn]
  cases hs : search P T S with
  | none =>
    exact Or.inl ⟨by simpa only [hs], (search_none_iff P trials).mp hs⟩
  | some g =>
    have hg := search_sound P trials hs
    right
    refine ⟨g, hg, ?_⟩
    cases d with
    | zero => omega
    | succ m =>
      simp only [hs, Nat.succ_sub_one]
      rw [unfilteredTransport_card (by omega : 0 < n) hnz g hg scalarOnly]

theorem countWords_correct {q : Nat} (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (test : List Nat → List Nat) (parameters : List Nat)
    {T S : Tensor K d n} (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n)
    (hnz : T ≠ 0) (trials : CompleteTrials P T S)
    (scalarOnly : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u) :
    countWords F P enum test (filteredComparisonInput F parameters T S) =
      [Nat.card {a : Changes K d n // act a T = S ∧
        ∀ i, test (filterInput F parameters i.val (a i)) = [1]}] := by
  simp only [countWords, filteredComparisonInput, List.cons_append, List.nil_append,
    List.drop_left, List.take_left, decodePair_encode F T S hd he hn]
  have h := countFromSearch_correct enum (by omega : 0 < n) hnz (search P T S)
    (fun g hg => search_sound P trials hg) ((search_none_iff P trials).mp) scalarOnly
    (fun i a => decide (test (filterInput F parameters i.val a) = [1]))
  rw [h]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun _ => by simp [and_comm]

#print axioms search_none_iff
#print axioms chargeScan_le
#print axioms recognizeWords_encode
#print axioms compareWords_correct
#print axioms countWords_correct

end EvenTI.Contract
