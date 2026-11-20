import EvenNextBankPairs
import EvenNextTargetPairs
import EvenDenseDecode
import EvenP5KernelCore

namespace EvenTI.Contract

open EvenTI.Action Matrix
open Mathproof.P15RecogOps20261007

/-- The dense mixed-radix order of the coordinates of one side of a cut. -/
def cutOrder (d n : Nat) : Coord d n ≃ Fin (n ^ d) :=
  finFunctionFinEquiv

def orderedIndices {I : Type} {m : Nat} (ord : I ≃ Fin m) : List I :=
  (List.finRange m).map ord.symm

theorem mem_orderedIndices {I : Type} {m : Nat} (ord : I ≃ Fin m) (i : I) :
    i ∈ orderedIndices ord :=
  List.mem_map.mpr ⟨ord i, List.mem_finRange _, ord.symm_apply_apply i⟩

theorem orderedIndices_nodup {I : Type} {m : Nat} (ord : I ≃ Fin m) :
    (orderedIndices ord).Nodup :=
  (List.nodup_finRange _).map ord.symm.injective

section MatrixBasis

variable {K : Type} [Field K] [DecidableEq K] {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq J] {a b : Nat}

/-- Compute one kernel vector for each free column in the existing checked RREF. -/
def rawKernelVectors (M : Matrix I J K) (rowOrder : I ≃ Fin a) (colOrder : J ≃ Fin b) :
    List (J → K) :=
  EvenTI.KernelDonor.kerBasis (Ops.ofField K) (orderedIndices colOrder)
    ((orderedIndices rowOrder).map fun i => M i)

private theorem rowKer_eq_mulVecKer (M : Matrix I J K) (rowOrder : I ≃ Fin a) :
    EvenTI.KernelDonor.rowKer ((orderedIndices rowOrder).map fun i => M i) =
      M.mulVecLin.ker := by
  ext v
  change (∀ u ∈ (orderedIndices rowOrder).map (fun i => M i), ∑ j, u j * v j = 0) ↔
    M.mulVec v = 0
  constructor
  · intro h
    funext i
    exact h (M i) (List.mem_map.mpr ⟨i, mem_orderedIndices rowOrder i, rfl⟩)
  · intro h u hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    exact congrFun h i

theorem rawKernelVectors_independent (M : Matrix I J K)
    (rowOrder : I ≃ Fin a) (colOrder : J ≃ Fin b) :
    LinearIndependent K (fun i : Fin (rawKernelVectors M rowOrder colOrder).length =>
      (rawKernelVectors M rowOrder colOrder).get i) :=
  EvenTI.KernelDonor.rows_kernel_independent _ _
    (orderedIndices_nodup colOrder)

theorem rawKernelVectors_span (M : Matrix I J K) (rowOrder : I ≃ Fin a) (colOrder : J ≃ Fin b) :
    Submodule.span K (Set.range (fun i : Fin (rawKernelVectors M rowOrder colOrder).length =>
      (rawKernelVectors M rowOrder colOrder).get i)) = M.mulVecLin.ker := by
  have hSet : Set.range (fun i : Fin (rawKernelVectors M rowOrder colOrder).length =>
      (rawKernelVectors M rowOrder colOrder).get i) =
      {v | v ∈ rawKernelVectors M rowOrder colOrder} := by
    ext v
    exact List.mem_iff_get.symm
  rw [hSet, ← rowKer_eq_mulVecKer M rowOrder]
  exact (EvenTI.KernelDonor.kerBasis_spec (mem_orderedIndices colOrder)
    (orderedIndices_nodup colOrder) _).2

end MatrixBasis

section WordBank

variable {K : Type} [Field K] [Fintype K] {I : Type} {m : Nat}

private def basisBankDigit (F : FieldEncoding K) (ord : I ≃ Fin m) (xs : List (I → K))
    (k : Fin (xs.length * m)) : Nat :=
  let ij := finProdFinEquiv.symm k
  (F (xs.get ij.1 (ord.symm ij.2))).val

/-- The checked basis vectors serialized at the addresses expected by the bank scan. -/
def basisBankWords (F : FieldEncoding K) (ord : I ≃ Fin m) (xs : List (I → K)) : List Nat :=
  List.ofFn (basisBankDigit F ord xs)

theorem basisBankWords_length (F : FieldEncoding K) (ord : I ≃ Fin m) (xs : List (I → K)) :
    (basisBankWords F ord xs).length = xs.length * m := by
  simp [basisBankWords]

def readBasisWords (F : FieldEncoding K) (bank : List Nat) (addr : Nat) : K :=
  decodeDigit F (bank.getD addr 0)

theorem readBasisWords_row (F : FieldEncoding K) (ord : I ≃ Fin m) (xs : List (I → K))
    (i : Fin xs.length) (j : I) :
    readBasisWords F (basisBankWords F ord xs) (i.val * m + (ord j).val) = xs.get i j := by
  let k : Fin (xs.length * m) := finProdFinEquiv (i, ord j)
  have hk : k.val = i.val * m + (ord j).val := by
    change (ord j).val + m * i.val = _
    ac_rfl
  change decodeDigit F ((List.ofFn (basisBankDigit F ord xs)).getD
    (i.val * m + (ord j).val) 0) = _
  have hlt : k.val < (List.ofFn (basisBankDigit F ord xs)).length := by
    rw [List.length_ofFn]
    exact k.isLt
  rw [← hk, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  change decodeDigit F (F (xs.get (finProdFinEquiv.symm k).1
    (ord.symm (finProdFinEquiv.symm k).2))).val = _
  have hpair : finProdFinEquiv.symm k = (i, ord j) :=
    finProdFinEquiv.symm_apply_apply _
  rw [hpair, ord.symm_apply_apply, decodeDigit_encode]

end WordBank

section Cuts

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

def rawLeftBasis (T : Tensor K (l + r) n) : List (Coord l n → K) :=
  rawKernelVectors (flatten T).transpose (cutOrder r n) (cutOrder l n)

def rawRightBasis (T : Tensor K (l + r) n) : List (Coord r n → K) :=
  rawKernelVectors (flatten T) (cutOrder l n) (cutOrder r n)

/-- The mathematical frame proved to be represented by the computed output words. -/
noncomputable def rawCutFrames (T : Tensor K (l + r) n) : CutFrames T :=
  ⟨(rawLeftBasis T).length, (rawRightBasis T).length,
    frameFromVectors (leftCutKernel T) (rawLeftBasis T).get
      (rawKernelVectors_independent _ _ _) (rawKernelVectors_span _ _ _),
    frameFromVectors (rightCutKernel T) (rawRightBasis T).get
      (rawKernelVectors_independent _ _ _) (rawKernelVectors_span _ _ _)⟩

/-- Compute both kernel banks directly from the tensor, then enumerate checked cut forms. -/
def rawCutBankForms (F : FieldEncoding K) (T : Tensor K (l + r) n)
    (leftGood : (Coord l n → K) → Bool) (rightGood : (Coord r n → K) → Bool) :
    List (CutFormPair K l r n) :=
  let L := rawLeftBasis T
  let R := rawRightBasis T
  let lo := cutOrder l n
  let ro := cutOrder r n
  bankCutFormPairs (c := L.length) (e := R.length) F lo ro
    (readBasisWords F (basisBankWords F lo L))
    (readBasisWords F (basisBankWords F ro R)) 0 0 leftGood rightGood

theorem rawCutBankForms_eq (F : FieldEncoding K) (T : Tensor K (l + r) n)
    (leftGood : (Coord l n → K) → Bool) (rightGood : (Coord r n → K) → Bool) :
    rawCutBankForms F T leftGood rightGood = cutFormPairs F T (rawCutFrames T) leftGood rightGood := by
  unfold rawCutBankForms rawCutFrames
  exact bankCutFormPairs_eq F T _ _ _ _ 0 0 leftGood rightGood _ _
    (fun i j => by rw [Nat.zero_add]; exact readBasisWords_row F (cutOrder l n) (rawLeftBasis T) i j)
    (fun i j => by rw [Nat.zero_add]; exact readBasisWords_row F (cutOrder r n) (rawRightBasis T) i j)
    (rawKernelVectors_independent _ _ _) (rawKernelVectors_independent _ _ _)
    (rawKernelVectors_span _ _ _) (rawKernelVectors_span _ _ _)

theorem rawCutBankForms_transport_of_ranks (F : FieldEncoding K)
    {T S : Tensor K ((l + 1) + (r + 1)) n}
    (g : Changes K ((l + 1) + (r + 1)) n) (hg : act g T = S)
    (gLeft : (Coord (l + 1) n → K) → Bool) (gRight : (Coord (r + 1) n → K) → Bool)
    (leftSpec : ∀ x, gLeft x = true ↔ ∀ i, (retainedForm i x).rank = n)
    (rightSpec : ∀ y, gRight y = true ↔ ∀ i, (retainedForm i y).rank = n)
    (x : Coord (l + 1) n → K) (y : Coord (r + 1) n → K)
    (hsrc : (x, y) ∈ rawCutBankForms F T gLeft gRight) :
    (moveLeftForm g x, moveRightForm g y) ∈ rawCutBankForms F S gLeft gRight := by
  rw [rawCutBankForms_eq] at hsrc ⊢
  exact cutFormPairs_transport_of_ranks F _ _ g hg gLeft gRight leftSpec rightSpec x y hsrc

end Cuts

#print axioms rawKernelVectors_independent
#print axioms rawKernelVectors_span
#print axioms readBasisWords_row
#print axioms rawCutBankForms_eq
#print axioms rawCutBankForms_transport_of_ranks

end EvenTI.Contract

