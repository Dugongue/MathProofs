import EvenP21PadSite
import EvenP6ChartTuple

set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 17500

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover
open EvenTI.P20Pad

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {q n : ℕ} {width : Fin q → ℕ} {dim : ∀ i, Fin (width i) → ℕ}
  {A : ∀ i, Fin (width i) → Type} [∀ i v, Field (A i v)] [∀ i v, Algebra K (A i v)]

/-- A native source chart recovered as UBU⁻¹ has scalar crop exactly
when each relevant native block multiplier is the same scalar. Relevance
reads one retained column of U⁻¹ in the actual padded site order. -/
theorem orderFour_cropScalar_ofBlockConjugacy
    (ell rho : Coord 2 n → K) (G : FourNumericUnits ell rho)
    (T : Tensor K 4 n) (hRank : rawRetainedFullRank (l:=3) T=true)
    (hAction : wordAction (fun i => (G i).val)
      (reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T)) =
      reindexWords fourSiteOrder (fourNumericOrder ell rho) (rawEnlargedWords ell rho T))
    (j : Fin (2+2)) (i : Fin q)
    (t : ∀ k v, WordTable K (Fin (dim k v)))
    (E : ∀ k v, (Fin (dim k v) → K) ≃ₗ[K] A k v)
    (hOne : ∀ k v, E k v (t k v).one=1)
    (hMul : ∀ k v a b, E k v ((t k v).multiply a b)=E k v a*E k v b)
    (a : ∀ v, A i v)
    (e : (Σ v, Fin (dim i v)) ≃ Fin (fourRecoveryWidth ell rho j))
    (U : (Matrix (Fin (fourRecoveryWidth ell rho j)) (Fin (fourRecoveryWidth ell rho j)) K)ˣ)
    (hConj : (G j).val=U.val*
      (liveActionMatrix t E i a).submatrix e.symm e.symm*U.inv)
    (c : K) :
    recoverFourMatrices ell rho ell rho rfl rfl G j=c • 1 ↔
      ∀ v, inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j) e U.inv v →
        a v=c • (1 : A i v) := by
  let P := sourcePadNumeric ell rho j
  let Q := targetCropNumeric ell rho ell rho rfl rfl j
  let B := liveActionMatrix t E i a
  let N := U.val*B.submatrix e.symm e.symm*U.inv
  have hN : (G j).val=N := hConj
  have hInvariant : N*P=P*(Q*N*P) := by
    rw [←hN]
    exact numericPad_invariant ell rho G T hRank hAction j
  have hCrop : recoverFourMatrices ell rho ell rho rfl rfl G j=Q*N*P :=
    (recoverFourMatrices_numeric ell rho ell rho rfl rfl G j).trans
      (congrArg (fun X => Q*X*P) hN)
  have hStable := stableCrop_conjugate_iff P Q U (B.submatrix e.symm e.symm) c
    (targetCropNumeric_sourcePad_left ell rho j) hInvariant
  have hIndex := reindexBlock_mul_iff e B (U.inv*P) c
  have hBlock := liveAction_mul_restriction_iff t E hOne hMul i a ((U.inv*P).submatrix e id) c
  have hLocal : (∀ v, (∃ (r : Fin (dim i v)) (k : Fin n),
      ((U.inv*P).submatrix e id) ⟨v,r⟩ k≠0) → a v=c • (1 : A i v)) ↔
      (∀ v, inverseBlockSupported (fourSiteOrder j).2 (siteCutoff ell rho j) e U.inv v →
        a v=c • (1 : A i v)) := by
    constructor
    · intro h v hv
      exact h v ((inverseBlockSupported_iff ell rho j e U.inv v).mpr hv)
    · intro h v hv
      exact h v ((inverseBlockSupported_iff ell rho j e U.inv v).mp hv)
  rw [hCrop]
  exact hStable.trans (hIndex.trans (hBlock.trans hLocal))

#print axioms orderFour_cropScalar_ofBlockConjugacy
end EvenTI.P21Pad

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P21Pad

open scoped BigOperators Matrix
open Matrix EvenTI.PrimaryAlignment EvenTI.CellPreparation EvenTI.LiveAlgebra

variable {K : Type} [Field K]

/-- An invertible native block scale preserves the active retained-column
support, with the given literal block order. -/
theorem orderedDiagonal_inverseSupport_iff {t n : ℕ} {w : Fin t → ℕ}
    (h : (∑ v, w v)=n)
    (G : ∀ v, Matrix (Fin (w v)) (Fin (w v)) K) (hG : ∀ v, IsUnit (G v))
    (X : Matrix (Fin n) (Fin n) K) (right : Bool) (cutoff : ℕ) (v : Fin t) :
    inverseBlockSupported right cutoff (blockOrder h) (orderedDiagonal h G*X) v ↔
      inverseBlockSupported right cutoff (blockOrder h) X v := by
  have hEntry (c : Fin n) (r : Fin (w v)) :
      (orderedDiagonal h G*X) (blockOrder h ⟨v,r⟩) c =
        ((G v).mulVec (fun q => X (blockOrder h ⟨v,q⟩) c)) r :=
    orderedDiagonal_mulVec_slot h G (fun q => X q c) v r
  constructor
  · rintro ⟨r,c,hKeep,hR⟩
    have hh : ∃ q : Fin (w v), X (blockOrder h ⟨v,q⟩) c≠0 := by
      by_contra! hz
      have h0 : (fun q => X (blockOrder h ⟨v,q⟩) c) = 0 := funext hz
      apply hR
      rw [hEntry,h0,Matrix.mulVec_zero] <;> rfl
    obtain ⟨q,hq⟩ := hh
    exact ⟨q,c,hKeep,hq⟩
  · rintro ⟨r,c,hKeep,hR⟩
    have hh : ∃ q : Fin (w v), (orderedDiagonal h G*X) (blockOrder h ⟨v,q⟩) c≠0 := by
      by_contra! hz
      let x : Fin (w v) → K := fun q => X (blockOrder h ⟨v,q⟩) c
      have h0 : (G v).mulVec x=0 := by
        funext q
        exact (hEntry c q).symm.trans (hz q)
      have hv := (Matrix.mulVec_injective_iff_isUnit.mpr (hG v))
        (h0.trans (Matrix.mulVec_zero _).symm)
      exact hR (congrFun hv r)
    obtain ⟨q,hq⟩ := hh
    exact ⟨q,c,hKeep,hq⟩

variable [Fintype K] [DecidableEq K]

/-- The dual source inverse has precisely the primary-block support of
the transpose of the original source frame. No inverse or Gram multiplication
has to be executed to find that support. -/
theorem dualChart_inverseSupport_iff (m : PreparedMode K) (h : ModeLayout m)
    (choice : ModeChoice m) (Ud Vd : (Matrix (Fin m.n) (Fin m.n) K)ˣ)
    (hDual : makeSiteChart m h choice true=some (Ud,Vd))
    (hSrc : IsUnit (modeSourceFrame m h))
    (hTgt : IsUnit (modeTargetFrame m h choice))
    (hField : ∀ b ∈ m.blocks, b.HasFieldModel)
    (right : Bool) (cutoff : ℕ) (v : Fin m.blocks.length) :
    inverseBlockSupported right cutoff (blockOrder h) Ud.inv v ↔
      inverseBlockSupported right cutoff (blockOrder h) (modeSourceFrame m h)ᵀ v := by
  obtain ⟨S,T,hPair,hS,_⟩ := makeSiteChart_dual m h choice hSrc hTgt
    (modeGramMatrix_isUnit m h hField)
  have hEq : (S,T)=(Ud,Vd) := Option.some.inj (hPair.symm.trans hDual)
  have hU : Ud.val=((modeSourceFrame m h)⁻¹)ᵀ * modeGramMatrix m h :=
    (congrArg (fun x => x.1.val) hEq).symm.trans hS
  let P := modeSourceFrame m h
  let J := modeGramMatrix m h
  change Ud.val=(P⁻¹)ᵀ*J at hU
  have hL : Pᵀ*(P⁻¹)ᵀ=1 := by
    rw [←Matrix.transpose_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hSrc),
      Matrix.transpose_one]
  have hShift : J*Ud.inv=Pᵀ := by
    calc
      _ = (Pᵀ*(P⁻¹)ᵀ)*(J*Ud.inv) := by rw [hL,Matrix.one_mul]
      _ = Pᵀ*(((P⁻¹)ᵀ*J)*Ud.inv) := by simp only [Matrix.mul_assoc]
      _ = Pᵀ := by rw [←hU,Ud.val_inv,Matrix.mul_one]
  change inverseBlockSupported right cutoff (blockOrder h) Ud.inv v ↔
    inverseBlockSupported right cutoff (blockOrder h) Pᵀ v
  rw [←hShift]
  exact (orderedDiagonal_inverseSupport_iff h
    (fun b => blockDualGram (m.blocks.get b))
    (fun b => blockDualGram_isUnit _ (hField _ (List.get_mem _ _))) Ud.inv right cutoff v).symm

/-- The existing per-column raw source frame bank is row-major for the
transposed frame used by the dual branch. -/
theorem sourceFrameTranspose_entry (m : PreparedMode K) (h : ModeLayout m)
    (v : Fin m.blocks.length) (r : Fin (m.blocks.get v).width) (c : Fin m.n) :
    (modeSourceFrame m h)ᵀ (blockOrder h ⟨v,r⟩) c =
      (m.blocks.get v).sourceColumns c r := by
  change (m.blocks.get ((blockOrder h).symm (blockOrder h ⟨v,r⟩)).1).sourceColumns
    c ((blockOrder h).symm (blockOrder h ⟨v,r⟩)).2=_
  rw [Equiv.symm_apply_apply]

#print axioms orderedDiagonal_inverseSupport_iff
#print axioms dualChart_inverseSupport_iff
#print axioms sourceFrameTranspose_entry
end EvenTI.P21Pad
