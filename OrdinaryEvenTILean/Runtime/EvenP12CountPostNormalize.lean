import EvenP12CountPostMachine
import EvenP11OracleIntegration
import EvenP10ScanCompare

namespace EvenTI.P12CountPost

open EvenTI.Action EvenTI.Contract EvenTI.Counting EvenTI.P10Oracle
open EvenTI.P10Scan (decodePair_some)
open Lax51.TuringPolytime
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 440000

variable {G : Type} [CommGroup G] [DecidableEq G] {q : ℕ}

def tableRows (enum : Fin q ≃ G) :
    (d : ℕ) → (Fin d → G → Bool) → List (Fin q → ℕ)
  | 0, _ => []
  | d+1, allow => tableRows enum d (fun i => allow i.succ) ++
    [fun k => if allow 0 (enum k) then 1 else 0]

theorem tableRows_length (enum : Fin q ≃ G) (d : ℕ) (allow : Fin d → G → Bool) :
    (tableRows enum d allow).length = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [tableRows,ih]

@[simp] private theorem vectorOfFn_get (f : Fin q → Nat) (j : Fin q) :
    (Vector.ofFn f).get j = f j := by
  change (Vector.ofFn f)[j.val] = f j
  exact Vector.getElem_ofFn j.isLt

theorem finishRows_tableRows (enum : Fin q ≃ G) (d : ℕ) (allow : Fin d → G → Bool) :
    finishRows enum (initial (enum.symm 1)) (tableRows enum d allow) =
      (productTable enum d allow).get := by
  induction d with
  | zero =>
    funext j
    have he : enum j = 1 ↔ j = enum.symm 1 := (Equiv.eq_symm_apply enum).symm
    simp [tableRows, finishRows, initial, productTable, he]
  | succ d ih =>
    unfold tableRows finishRows
    rw [List.foldl_append]
    change rowValue enum (fun k => if allow 0 (enum k) then 1 else 0)
      (finishRows enum (initial (enum.symm 1)) (tableRows enum d (fun i => allow i.succ))) = _
    rw [ih]
    funext j
    unfold rowValue
    simp only [productTable, vectorOfFn_get]
    apply Finset.sum_congr rfl
    intro k _
    have hbit (b : Bool) (v : ℕ) :
        (if (if b then 1 else 0) = 1 then v else 0) = (if b then v else 0) := by
      cases b <;> simp
    simpa only [lookupIndex] using hbit (allow 0 (enum k))
      ((productTable enum d (fun i => allow i.succ)).get (lookupIndex enum j k))

theorem rowWords_length (rows : List (Fin q → ℕ)) :
    (rowWords rows).length = q*rows.length := by
  induction rows with
  | nil => simp [rowWords]
  | cons a rows ih =>
    change ((List.finRange q).map a ++ rowWords rows).length = _
    simp [ih, Nat.mul_add, Nat.add_comm]

theorem collectRows_rowWords (rows : List (Fin q → ℕ)) :
    collectRows q rows.length (rowWords rows) = rows := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    have hlen : ((List.finRange q).map a).length = q := by simp
    have hd : (rowWords (a :: rows)).drop q = rowWords rows := by
      change ((List.finRange q).map a ++ rowWords rows).drop q = _
      have hdrop : ((List.finRange q).map a ++ rowWords rows).drop
          ((List.finRange q).map a).length = rowWords rows := by simp
      simpa only [hlen] using hdrop
    have hget (i : Fin q) : (rowWords (a :: rows)).getD i.val 0 = a i := by
      change ((List.finRange q).map a ++ rowWords rows).getD i.val 0 = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa only [hlen] using i.isLt)]
      simp [List.finRange, List.map_ofFn, List.getElem?_ofFn, i.isLt]
    change (fun i => (rowWords (a :: rows)).getD i.val 0) ::
      collectRows q rows.length ((rowWords (a :: rows)).drop q) = _
    rw [hd, ih, funext hget]

def encodeTable (enum : Fin q ≃ G) (d : ℕ) (allow : Fin d → G → Bool) : List ℕ :=
  d :: rowWords (tableRows enum d allow)

theorem tableKernel_encodeTable (enum : Fin q ≃ G) (d : ℕ) (allow : Fin d → G → Bool) :
    tableKernel enum (encodeTable enum d allow) =
      [(productTable enum d allow).get (enum.symm 1)] := by
  have hlen := tableRows_length enum d allow
  have hEq := collectRows_rowWords (tableRows enum d allow)
  rw [hlen] at hEq
  simp only [encodeTable, tableKernel, rowWords_length, hlen, le_refl, if_true,
    hEq, finishRows_tableRows]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def postDrop : List ℕ → List ℕ
  | d :: w => w.drop d
  | [] => []

def postZSource (w : List ℕ) : List ℕ := postDrop (unpositiveWords (cut w).1)

/-- Prepare one normalized bit per answer, from last mode to first.
The header is included only when the comparison has returned a witness. -/
def postNormalizeParsed (enum : Fin q ≃ Kˣ) (w cmp src : List ℕ) : List ℕ :=
  match src with
  | d :: _ =>
    if cmp.head? = some 2 ∧ d ≤ (cut w).1.length then
      let as := unpackSegments (cut w).2
      encodeTable enum d fun i u =>
        decide (as.getD (finProdFinEquiv (i,enum.symm u)).val [] = [1])
    else []
  | [] => []

def postNormalize (enum : Fin q ≃ Kˣ) (w cmp : List ℕ) : List ℕ :=
  postNormalizeParsed enum w cmp (postZSource w)
theorem postCutLength_le (w : List ℕ) : (cut w).1.length ≤ w.length := by
  induction w with
  | nil => simp [cut]
  | cons a w ih =>
    cases a with
    | zero => simp [cut]
    | succ a => simpa only [cut, List.length_cons] using Nat.succ_le_succ ih

private theorem countPostBody_eq_tableKernel (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (w input : List ℕ) (hinput : input.length ≤ (cut w).1.length) :
    (match decodePair F input with
      | none => [0]
      | some p => match search P p.source p.target with
        | none => [0]
        | some _ => [tableFromAnswers enum p.d (unpackSegments (cut w).2)]) =
      tableKernel enum (postNormalizeParsed enum w (compareWords F P input) input) := by
  cases hd : decodePair F input with
  | none =>
    have hc : compareWords F P input = [0] := by simp [compareWords,hd]
    rw [hc]
    cases input <;> simp [postNormalizeParsed,tableKernel]
  | some p =>
    obtain ⟨tail, hshape, hlen, _, _, hn⟩ := decodePair_some hd
    have hdp : p.d ≤ (cut w).1.length := calc
      p.d ≤ p.n ^ p.d := (Nat.lt_two_pow_self (n := p.d)).le.trans (Nat.pow_le_pow_left hn _)
      _ ≤ tail.length := by rw [hlen]; omega
      _ ≤ input.length := by rw [hshape]; simp only [List.length_cons]; omega
      _ ≤ (cut w).1.length := hinput
    have hc : compareWords F P input =
        match search P p.source p.target with
        | none => [0]
        | some g => transporterOutput F g ((Fintype.card K - 1)^ (p.d-1)) := by
      simp only [compareWords, hd] <;> rfl
    rw [hc,hshape]
    cases hs : search P p.source p.target with
    | none => simp [hs,postNormalizeParsed,tableKernel]
    | some g =>
      simpa [hs,postNormalizeParsed,transporterOutput,hdp,tableFromAnswers] using
        (tableKernel_encodeTable enum p.d (fun i u =>
          decide ((unpackSegments (cut w).2).getD (finProdFinEquiv (i,enum.symm u)).val [] = [1]))).symm

theorem countPostZ_eq_tableKernel (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (w : List ℕ) :
    countPostZ F P enum w =
      tableKernel enum (postNormalize enum w (compareWords F P (postZSource w))) := by
  unfold countPostZ postNormalize postZSource
  cases hx : unpositiveWords (cut w).1 with
  | nil => rfl
  | cons n ws =>
    simp only [postDrop, countPost]
    apply countPostBody_eq_tableKernel
    have h : List.length (unpositiveWords (cut w).1) = (cut w).1.length := by simp [unpositiveWords]
    rw [hx,List.length_cons] at h
    have h' : (ws.drop n).length ≤ ws.length := by simp
    omega
/-- The actual post target requires one shared comparison and one
normalizer over the output words. No tensor work remains in the verified
binary table consumer. -/
theorem countPostZ_turingPolytime_of_normalize (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ)
    (h : TuringPolytime (fun w => postNormalize enum w (compareWords F P (postZSource w)))) :
    TuringPolytime (countPostZ F P enum) := by
  have he : countPostZ F P enum =
      tableKernel enum ∘ (fun w => postNormalize enum w (compareWords F P (postZSource w))) :=
    funext (countPostZ_eq_tableKernel F P enum)
  rw [he]
  exact turingPolytime_comp h (tableKernel_turingPolytime enum)

#print axioms tableKernel_encodeTable
#print axioms countPostZ_eq_tableKernel
#print axioms countPostZ_turingPolytime_of_normalize
end EvenTI.P12CountPost
