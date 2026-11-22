
import EvenP12CountPreFrame
import EvenP10ScanCompare

namespace EvenTI.P12CountPre

open EvenTI.Action EvenTI.Contract EvenTI.Counting EvenTI.P10Oracle
open Lax51.TuringPolytime
open EvenTI.P10Scan (decodePair_some)

set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : Nat}


def dropPrefix : List ℕ → List ℕ
  | length :: body => body.drop length
  | [] => []

/-- Field-table multiplication of one digit by a scalar unit. -/
def mulDigit (F : FieldEncoding K) (u : Kˣ) (w : ℕ) : ℕ :=
  (F ((u : K) * decodeDigit F w)).val

/-- Query list read from the input header and the comparison output words. -/
def preK (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (words tw : List ℕ) : List (List ℕ) :=
  match words with
  | length :: body =>
    match body.drop length with
    | d :: n :: _ =>
      if tw.head? = some 2 then
        List.ofFn fun x : Fin (d * q) =>
          [(body.take length).length] ++ body.take length ++
            [(finProdFinEquiv.symm x).1.val, n] ++
            ((tw.drop (2 + (finProdFinEquiv.symm x).1.val * (n * n))).take (n * n)).map
              (mulDigit F (enum (finProdFinEquiv.symm x).2))
      else []
    | _ => []
  | [] => []

theorem drop_len_append {α : Type*} :
    ∀ (a b : List α) (i : ℕ), (a ++ b).drop (a.length + i) = b.drop i
  | [], b, i => by simp
  | x :: a, b, i => by
    rw [List.length_cons, Nat.add_right_comm]
    exact drop_len_append a b i

theorem drop_two_cons {α : Type*} (m : ℕ) (a b : α) (L : List α) :
    (a :: b :: L).drop (2 + m) = L.drop m := by
  rw [show 2 + m = m + 1 + 1 by omega]
  rfl

theorem flatMap_finRange_block {α : Type*} {m : ℕ} :
    ∀ {d : ℕ} (f : Fin d → List α), (∀ i, (f i).length = m) → ∀ i : Fin d,
      (((List.finRange d).flatMap f).drop (i.val * m)).take m = f i
  | 0, _, _, i => i.elim0
  | d + 1, f, hf, i => by
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero]
      exact List.take_left' (hf 0)
    | succ j =>
      have hj : (j.succ : Fin (d + 1)).val * m = (f 0).length + j.val * m := by
        rw [Fin.val_succ, hf 0]; ring
      rw [hj, drop_len_append]
      exact flatMap_finRange_block (fun k => f k.succ) (fun k => hf k.succ) j

theorem scalar_mul_entry {n : ℕ} (a : (Matrix (Fin n) (Fin n) K)ˣ) (u : Kˣ) (j k : Fin n) :
    (a * scalar u).val j k = (u : K) * a.val j k := by
  simp [Units.val_mul, scalar_val, Matrix.mul_smul, Matrix.smul_apply]

theorem transporter_block (F : FieldEncoding K) {d n : ℕ} (g : Changes K d n) (c : ℕ)
    (i : Fin d) (u : Kˣ) :
    (((transporterOutput F g c).drop (2 + i.val * (n * n))).take (n * n)).map (mulDigit F u) =
      (List.finRange n).flatMap fun j => (List.finRange n).flatMap fun k =>
        fieldWords F ((g i * scalar u).val j k) := by
  let blk : Fin d → List ℕ := fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).flatMap fun k => fieldWords F ((g i).val j k)
  have hdrop : (transporterOutput F g c).drop (2 + i.val * (n * n)) =
      ((List.finRange d).flatMap blk).drop (i.val * (n * n)) :=
    drop_two_cons _ _ _ _
  have hlen : ∀ i, (blk i).length = n * n := fun i => by
    simp [blk, List.length_flatMap, fieldWords, List.map_const', List.sum_replicate_nat]
  rw [hdrop, flatMap_finRange_block blk hlen i]
  simp [blk, List.map_flatMap, fieldWords, mulDigit, decodeDigit_encode, scalar_mul_entry]

theorem countPre_eq_preK (F : FieldEncoding K) (P : TrialPlan K) (enum : Fin q ≃ Kˣ)
    (words : List ℕ) :
    countPre F P enum words = preK F enum words (compareWords F P (dropPrefix words)) := by
  match words with
  | [] => rfl
  | length :: body =>
    simp only [countPre, dropPrefix]
    cases hp : decodePair F (body.drop length) with
    | none =>
      have hc : compareWords F P (body.drop length) = [0] := by
        unfold compareWords; rw [hp]
      rw [hc]
      simp only [preK]
      split <;> simp
    | some p =>
      obtain ⟨rest, hw, -⟩ := decodePair_some hp
      cases hs : search P p.source p.target with
      | none =>
        have hc : compareWords F P (body.drop length) = [0] := by
          unfold compareWords; rw [hp]; simp only [hs]
        rw [hc]
        simp [preK, hs, hw]
      | some g =>
        have hc : compareWords F P (body.drop length) =
            transporterOutput F g ((Fintype.card K - 1) ^ (p.d - 1)) := by
          unfold compareWords; rw [hp]; simp only [hs]
        rw [hc]
        simp only [preK, hw, hs]
        rw [if_pos (by simp [transporterOutput])]
        unfold queryList filterInput
        congr 1
        funext x
        rw [transporter_block]




theorem transporterOutput_length (F : FieldEncoding K) {d n : Nat} (g : Changes K d n) (c : Nat) :
    (transporterOutput F g c).length = 2 + d * (n * n) := by
  simp [transporterOutput, fieldWords, List.length_flatMap, List.map_const', List.sum_replicate_nat,
    Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The query emitter is guarded by the actual lengths before reading any matrix block.
For a successfully compared input all guards follow from the input or witness encoding. -/
def guardedQueries (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (w tw : List Nat) : List (List Nat) :=
  match comparisonInputOf w with
  | d :: n :: _ =>
    if d ≤ w.length ∧ n ≤ w.length ∧ 2 + d * (n*n) ≤ tw.length then preK F enum w tw else []
  | _ => []

theorem comparisonInputOf_eq_dropPrefix (w : List Nat) : comparisonInputOf w = dropPrefix w := by
  cases w <;> rfl

private theorem decodePair_dimensions_le (F : FieldEncoding K) (w : List Nat) {p : ParsedPair K}
    (hp : decodePair F w = some p) : p.d ≤ w.length ∧ p.n ≤ w.length := by
  match w, hp with
  | d :: n :: rest, hp =>
    simp only [decodePair] at hp
    split_ifs at hp with hc
    obtain rfl := Option.some.inj hp
    simp only [admissibleHeader, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1.2.2.2.1.trans (by simp only [List.length_cons]; omega), hc.1.1.2.2.2.2.trans (by simp only [List.length_cons]; omega)⟩

private theorem comparisonInputOf_length_le (w : List Nat) : (comparisonInputOf w).length ≤ w.length := by
  simp [comparisonInputOf]

private theorem preK_zero (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (w : List Nat) :
    preK F enum w [0] = [] := by
  cases w with
  | nil => rfl
  | cons h body =>
    simp only [preK]
    split <;> rfl

theorem countPre_eq_guardedQueries (F : FieldEncoding K) (P : TrialPlan K) (enum : Fin q ≃ Kˣ)
    (w : List Nat) :
    countPre F P enum w = guardedQueries F enum w (compareWords F P (comparisonInputOf w)) := by
  rw [countPre_eq_preK, ← comparisonInputOf_eq_dropPrefix]
  unfold guardedQueries
  split
  · rename_i d n rest hInput
    by_cases hp : decodePair F (comparisonInputOf w) = none
    · have hc : compareWords F P (comparisonInputOf w) = [0] := by simp [compareWords,hp]
      rw [hc]
      rw [preK_zero]
      simp
    · obtain ⟨p,hp⟩ := Option.ne_none_iff_exists'.mp hp
      obtain ⟨tail,hhead,_⟩ := decodePair_some hp
      have he := List.cons.inj (hInput.symm.trans hhead)
      have hd : p.d = d := he.1.symm
      have hn : p.n = n := (List.cons.inj he.2).1.symm
      obtain ⟨hpd,hpn⟩ := decodePair_dimensions_le F _ hp
      have hwd : d ≤ w.length := hd ▸ hpd.trans (comparisonInputOf_length_le w)
      have hwn : n ≤ w.length := hn ▸ hpn.trans (comparisonInputOf_length_le w)
      cases hs : search P p.source p.target with
      | none =>
        have hc : compareWords F P (comparisonInputOf w) = [0] := by simp [compareWords,hp,hs]
        rw [hc]
        rw [preK_zero]
        simp
      | some g =>
        have hc : compareWords F P (comparisonInputOf w) =
            transporterOutput F g ((Fintype.card K - 1) ^ (p.d - 1)) := by
          simp [compareWords,hp,hs]
        rw [if_pos ⟨hwd,hwn,by rw [hc,transporterOutput_length,hd,hn]⟩]
  · rename_i h
    cases w with
    | nil => rfl
    | cons length body =>
      have hh : comparisonInputOf (length :: body) = body.drop length := rfl
      rw [hh] at h
      simp only [preK]


/-- Parse the preserved context and the one comparator result on the packed tape,
then emit the checked query list, in exactly the expected oracle encoding. -/
def emitQueries (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (z : List Nat) : List Nat :=
  (cut z).1 ++ 0 :: packSegments
    (guardedQueries F enum (unpositiveWords (cut z).1) (unpositiveWords (cut (cut z).2).1))

theorem comparisonFrame_eq (w : List Nat) :
    comparisonFrame w = positiveWords w ++ 0 :: positiveWords (comparisonInputOf w) ++ [0] := rfl

theorem countPreZ_eq_emitQueries (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (P : TrialPlan K) :
    countPreZ F P enum =
      emitQueries F enum ∘ mapZ (positiveCallback (compareWords F P)) ∘ comparisonFrame := by
  funext w
  simp [Function.comp_def, comparisonFrame_eq, mapRest_positiveWords, positiveCallback,
    emitQueries, countPreZ, countPre_eq_guardedQueries, List.append_assoc]

theorem countPreZ_turingPolytime_of_emitQueries (F : FieldEncoding K) (enum : Fin q ≃ Kˣ)
    (P : TrialPlan K) (hCompare : TuringPolytime (compareWords F P))
    (hEmit : TuringPolytime (emitQueries F enum)) :
    TuringPolytime (countPreZ F P enum) := by
  rw [countPreZ_eq_emitQueries]
  exact turingPolytime_comp
    (turingPolytime_comp comparisonFrame_turingPolytime
      (turingPolytime_mapZ (positiveCallback_turingPolytime hCompare))) hEmit

#print axioms countPreZ_eq_emitQueries
#print axioms countPreZ_turingPolytime_of_emitQueries
end EvenTI.P12CountPre

