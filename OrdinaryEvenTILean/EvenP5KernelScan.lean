import EvenP5KernelBasis

namespace EvenTI.Contract

open EvenTI.Action Matrix

section BasisDimension

variable {K I J : Type} [Field K] [DecidableEq K]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {a b : Nat}

theorem rawKernelVectors_length (M : Matrix I J K) (ro : I ≃ Fin a) (co : J ≃ Fin b) :
    (rawKernelVectors M ro co).length = Module.finrank K M.mulVecLin.ker := by
  let e := frameFromVectors M.mulVecLin (rawKernelVectors M ro co).get
    (rawKernelVectors_independent M ro co) (rawKernelVectors_span M ro co)
  simpa using e.finrank_eq

theorem rawKernelVectors_length_le (M : Matrix I J K) (ro : I ≃ Fin a) (co : J ≃ Fin b) :
    (rawKernelVectors M ro co).length ≤ b := by
  rw [rawKernelVectors_length]
  have hk := Submodule.finrank_le M.mulVecLin.ker
  have hcard := Fintype.card_congr co
  simpa [hcard] using hk

end BasisDimension

section CutScan

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

/-- A balanced cut needs at most two dense-input lengths of basis words. -/
theorem rawCutBanks_words_le (F : FieldEncoding K) (T : Tensor K (l + l) n) :
    (basisBankWords F (cutOrder l n) (rawLeftBasis T)).length +
      (basisBankWords F (cutOrder l n) (rawRightBasis T)).length ≤ 2 * n ^ (l + l) := by
  rw [basisBankWords_length, basisBankWords_length, Nat.pow_add, Nat.two_mul]
  apply Nat.add_le_add <;> apply Nat.mul_le_mul_right
  · exact rawKernelVectors_length_le (flatten T).transpose (cutOrder l n) (cutOrder l n)
  · exact rawKernelVectors_length_le (flatten T) (cutOrder l n) (cutOrder l n)

/-- The bank scan contains exactly the nonzero kernel pairs allowed by the
two corank gates and the caller's tests. Its specification does not depend
on the basis or its ordering. -/
theorem mem_rawCutBankForms (F : FieldEncoding K) (T : Tensor K (l + r) n)
    (goodLeft : (Coord l n → K) → Bool) (goodRight : (Coord r n → K) → Bool)
    (x : Coord l n → K) (y : Coord r n → K) :
    (x, y) ∈ rawCutBankForms F T goodLeft goodRight ↔
      ((leftCutKernel T x = 0 ∧ Fintype.card K ^ Module.finrank K (leftCutKernel T).ker ≤ n) ∧
        x ≠ 0 ∧ goodLeft x = true) ∧
      ((rightCutKernel T y = 0 ∧ Fintype.card K ^ Module.finrank K (rightCutKernel T).ker ≤ n) ∧
        y ≠ 0 ∧ goodRight y = true) := by
  rw [rawCutBankForms_eq, cutFormPairs]
  refine List.mem_product.trans ?_
  simp only [mem_kernelForms]
  have hL : (rawCutFrames T).leftDim = Module.finrank K (leftCutKernel T).ker := by
    simpa using (rawCutFrames T).left.finrank_eq
  have hR : (rawCutFrames T).rightDim = Module.finrank K (rightCutKernel T).ker := by
    simpa using (rawCutFrames T).right.finrank_eq
  rw [hL, hR]

theorem rawCutBankForms_length (F : FieldEncoding K) (T : Tensor K (l + r) n)
    (goodLeft : (Coord l n → K) → Bool) (goodRight : (Coord r n → K) → Bool) :
    (rawCutBankForms F T goodLeft goodRight).length ≤ n ^ 2 := by
  rw [rawCutBankForms_eq]
  exact cutFormPairs_length F T _ _ _

/-- A dense scan of the retained flattenings. Each full-row-rank test is
implemented by checking that the transpose kernel basis is empty. -/
def rawRetainedFullRank (x : Coord (l + 1) n → K) : Bool :=
  (List.finRange (l + 1)).all fun i =>
    (rawKernelVectors (retainedForm i x).transpose (cutOrder l n)
      (Equiv.refl (Fin n))).isEmpty

theorem rawRetainedFullRank_spec (x : Coord (l + 1) n → K) :
    rawRetainedFullRank x = true ↔ ∀ i, (retainedForm i x).rank = n := by
  unfold rawRetainedFullRank
  rw [List.all_eq_true]
  simp only [List.mem_finRange, true_implies]
  apply forall_congr'
  intro i
  rw [List.isEmpty_iff_length_eq_zero, rawKernelVectors_length]
  have h := (retainedForm i x).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (retainedForm i x).transpose.rank +
    Module.finrank K (retainedForm i x).transpose.mulVecLin.ker = _ at h
  rw [Matrix.rank_transpose] at h
  have hn : Module.finrank K (Fin n → K) = n := by simp
  rw [hn] at h
  omega

/-- The order-four singular branch scans every nonzero allowed pair. It
applies no full retained-rank test, since the crop can handle deficient forms. -/
def rawUnfilteredCutForms (F : FieldEncoding K) (T : Tensor K (l + r) n) :
    List (CutFormPair K l r n) :=
  rawCutBankForms F T (fun _ => true) (fun _ => true)

theorem rawUnfilteredCutForms_transport (F : FieldEncoding K)
    {T S : Tensor K (l + r) n} (g : Changes K (l + r) n) (hg : act g T = S)
    (x : Coord l n → K) (y : Coord r n → K) (h : (x,y) ∈ rawUnfilteredCutForms F T) :
    (moveLeftForm g x, moveRightForm g y) ∈ rawUnfilteredCutForms F S := by
  unfold rawUnfilteredCutForms at h ⊢
  rw [rawCutBankForms_eq] at h ⊢
  obtain ⟨hx, hy⟩ := List.mem_product.mp h
  obtain ⟨⟨hxk, hxg⟩, hx0, _⟩ := (mem_kernelForms F _ _ _ _ _).mp hx
  obtain ⟨⟨hyk, hyg⟩, hy0, _⟩ := (mem_kernelForms F _ _ _ _ _).mp hy
  obtain ⟨hL, hR⟩ := cutFrames_dimensions_transport g hg (rawCutFrames T) (rawCutFrames S)
  exact cutFormPairs_covers_transporter F (rawCutFrames S) g hg _ _ x y hxk hyk hx0 hy0
    (hL ▸ hxg) (hR ▸ hyg) rfl rfl

/-- For the higher-order singular branch, use the executable rank filter
on both lists. -/
def rawFullRankCutForms (F : FieldEncoding K)
    (T : Tensor K ((l + 1) + (r + 1)) n) :
    List (CutFormPair K (l + 1) (r + 1) n) :=
  rawCutBankForms F T rawRetainedFullRank rawRetainedFullRank

theorem rawFullRankCutForms_transport (F : FieldEncoding K)
    {T S : Tensor K ((l + 1) + (r + 1)) n} (g : Changes K ((l + 1) + (r + 1)) n)
    (hg : act g T = S) (x : Coord (l + 1) n → K) (y : Coord (r + 1) n → K)
    (h : (x,y) ∈ rawFullRankCutForms F T) :
    (moveLeftForm g x, moveRightForm g y) ∈ rawFullRankCutForms F S :=
  rawCutBankForms_transport_of_ranks F g hg _ _ rawRetainedFullRank_spec
    rawRetainedFullRank_spec x y h

end CutScan

#print axioms rawKernelVectors_length_le
#print axioms rawCutBanks_words_le
#print axioms mem_rawCutBankForms
#print axioms rawCutBankForms_length
#print axioms rawRetainedFullRank_spec
#print axioms rawUnfilteredCutForms_transport
#print axioms rawFullRankCutForms_transport

end EvenTI.Contract

