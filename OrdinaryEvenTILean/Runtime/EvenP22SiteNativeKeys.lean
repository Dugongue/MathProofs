import EvenP21SiteRowOrder
import EvenP22SiteKeys

namespace EvenTI.P22Site.NativeKeys
open scoped Polynomial
open Polynomial UniqueFactorizationMonoid
open Matrix EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.PrimaryProducer
open EvenTI.CellPreparation EvenTI.LiveAlgebra
open Mathproof.P15FactorRef20261007 (toPoly)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax13Proofs.Imp (Env)

set_option autoImplicit false
set_option maxHeartbeats 500000

private theorem mapM_recover {X Y : Type} (f : X → Option Y) (key : Y → X)
    (good : ∀ x y, f x = some y → key y = x) (xs : List X) (ys : List Y)
    (h : xs.mapM f = some ys) : ys.map key = xs := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := (Option.some.inj h).symm
    simp only [he,List.map_nil]
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some zs =>
        have he : y::zs = ys := by simpa [List.mapM_cons,hx,ht] using h
        rw [← he,List.map_cons,good x y hx,ih zs ht]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The actual native constructor retains every source polynomial/multiplicity
row in exactly its reference list order; no guessed key assignment is supplied. -/
theorem prepareAnchorPair_factorRows (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) :
    mode.blocks.map (fun b => b.factor) = anchorFactors D A.matrix := by
  unfold prepareAnchorPair at h
  split at h
  · rename_i hw
    dsimp only at h
    split at h
    · let C := B.matrix.submatrix (finCongr hw).symm (finCongr hw).symm
      change ((anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix C)).map
        (PreparedMode.mk A.width) = some mode at h
      cases ht : (anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix C) with
      | none => rw [ht] at h; contradiction
      | some bs =>
        rw [ht] at h
        have hm : (PreparedMode.mk A.width bs : PreparedMode K) = mode := Option.some.inj h
        rw [← hm]
        exact mapM_recover _ (fun b => b.factor)
          (fun row b hb => (EvenTI.P21Site.Prepare.prepareModeBlock_tags D budget A.matrix C row b hb).1)
          _ _ ht
    · contradiction
  · contradiction

noncomputable def blockPolys (mode : PreparedMode K) : List K[X] :=
  mode.blocks.map (fun b => toPoly b.factor.1)

private theorem anchorPolys_spec {n : ℕ} (D : FieldEncoding K) (A : Matrix (Fin n) (Fin n) K) :
    ((anchorFactors D A).map (fun row => toPoly row.1) : Multiset K[X]) =
      (normalizedFactors A.charpoly).dedup := by
  have h := congrArg (fun s : Multiset (K[X] × ℕ) => s.map Prod.fst) (anchorFactors_spec D A)
  simpa only [Multiset.map_coe,List.map_map,Multiset.map_map,Function.comp_def,Multiset.map_id'] using h

theorem blockPolys_spec (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) :
    (blockPolys mode : Multiset K[X]) = (normalizedFactors A.matrix.charpoly).dedup := by
  have hm := prepareAnchorPair_factorRows D budget A B mode h
  have hk : blockPolys mode = (anchorFactors D A.matrix).map (fun row => toPoly row.1) := by
    rw [← hm,List.map_map]
    rfl
  rw [hk]
  exact anchorPolys_spec D A.matrix

/-- Any literal archive of the source charpoly lists precisely the native
block keys, even when the actual archive and reference constructor orders differ. -/
theorem archive_perm_native (F : FieldPresentation K) (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode)
    {s : Env} {words mult : String} {cap : ℕ} {L : List K[X]}
    (ha : Archived F words mult cap A.matrix.charpoly L s) : L.Perm (blockPolys mode) :=
  Multiset.coe_eq_coe.mp (ha.list.trans (blockPolys_spec D budget A B mode h).symm)

/-- The pure semantic key matching is unique, and the computed finite scan in
Keys.archiveEquiv realizes it whenever the native key table is also installed. -/
theorem native_keys_nodup (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) : (blockPolys mode).Nodup := by
  apply Multiset.coe_nodup.mp
  rw [blockPolys_spec D budget A B mode h]
  exact Multiset.nodup_dedup _

/-- The actual native key also determines the saved multiplicity. -/
theorem nativeBlock_multiplicity (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) (j : Fin mode.blocks.length) :
    (mode.blocks.get j).factor.2 =
      (normalizedFactors A.matrix.charpoly).count (toPoly (mode.blocks.get j).factor.1) := by
  have hr : (mode.blocks.get j).factor ∈ anchorFactors D A.matrix := by
    rw [← prepareAnchorPair_factorRows D budget A B mode h]
    exact List.mem_map.mpr ⟨mode.blocks.get j,List.get_mem _ _,rfl⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  have hc := (liveFactor_mem D A.matrix i).2
  change ((anchorFactors D A.matrix).get i).2 = (normalizedFactors A.matrix.charpoly).count (toPoly ((anchorFactors D A.matrix).get i).1) at hc
  rw [hi] at hc
  exact hc

theorem prepareAnchorPair_tags (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) :
    ∀ b ∈ mode.blocks, EvenTI.P21Site.Prepare.isRepeated b = decide (b.factor.2 ≠ 1) := by
  unfold prepareAnchorPair at h
  split at h
  · rename_i hw
    dsimp only at h
    split at h
    · let C := B.matrix.submatrix (finCongr hw).symm (finCongr hw).symm
      change ((anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix C)).map
        (PreparedMode.mk A.width) = some mode at h
      cases ht : (anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix C) with
      | none => rw [ht] at h; contradiction
      | some bs =>
        rw [ht] at h
        have hm : (PreparedMode.mk A.width bs : PreparedMode K) = mode := Option.some.inj h
        rw [← hm]
        intro b hb
        obtain ⟨row,hr,hb'⟩ := mem_optionMapM _ _ _ ht b hb
        have tag := EvenTI.P21Site.Prepare.prepareModeBlock_tags D budget A.matrix C row b hb'
        rw [tag.1]
        exact tag.2.2
    · contradiction
  · contradiction

/-- A matched polynomial key transports the literal archived multiplicity to
its unique native block. This is independent of mutable archive addresses. -/
theorem archive_multiplicity_native (F : FieldPresentation K) (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode)
    {s : Env} {words mult : String} {cap : ℕ} {L : List K[X]}
    (ha : Archived F words mult cap A.matrix.charpoly L s)
    (i : Fin L.length) (j : Fin mode.blocks.length)
    (key : L.get i = toPoly (mode.blocks.get j).factor.1) :
    (s.arrs mult).getD i.val 0 = (mode.blocks.get j).factor.2 := by
  rw [ha.multiplicity i.val i.isLt,nativeBlock_multiplicity D budget A B mode h j]
  simpa only [List.get_eq_getElem] using congrArg (fun p => (normalizedFactors A.matrix.charpoly).count p) key

/-- The required remap direction is archive block → native block. A free
archived block gets that native block's positive source address; pinned blocks
get zero regardless of their many native coordinate origins. -/
theorem archive_match_site (F : FieldPresentation K) (D : FieldEncoding K) (budget : ℕ)
    (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K) (r : Fin (w.sites+2))
    (A B : NumberedAnchor K)
    (h : prepareAnchorPair D budget A B = some (m (w.mode r)))
    {s : Env} {words mult : String} {cap : ℕ} {L : List K[X]}
    (ha : Archived F words mult cap A.matrix.charpoly L s)
    (i : Fin L.length) (j : Fin (m (w.mode r)).blocks.length)
    (key : L.get i = toPoly ((m (w.mode r)).blocks.get j).factor.1)
    (localOrigin : Fin (blockOriginCount ((m (w.mode r)).blocks.get j))) (t d : ℕ) :
    (EvenTI.P20Scalar.sharedBlockPhysicalSlot w.mode (branchIsFree w m) t d r
      (modeOriginOrder (m (w.mode r)) ⟨j,localOrigin⟩)).val =
    if (s.arrs mult).getD i.val 0 = 1 then
      2*(EvenTI.P21Site.RowOrder.nativeModeOffset m (w.mode r)+
        EvenTI.P21Site.RowOrder.nativeBlockOffset (m (w.mode r)) j)+1 else 0 := by
  have hm := archive_multiplicity_native F D budget A B (m (w.mode r)) h ha i j key
  have ht := prepareAnchorPair_tags D budget A B (m (w.mode r)) h
    ((m (w.mode r)).blocks.get j) (List.get_mem _ _)
  have hFixed : originIsFixed (m (w.mode r)) ⟨j,localOrigin⟩ =
      decide (((m (w.mode r)).blocks.get j).factor.2 ≠ 1) := by
    have hp := EvenTI.P21Site.Prepare.nativeBlock_fixed (m (w.mode r)) j localOrigin
    simpa only [EvenTI.LiveAlgebra.numberedOrigin,Equiv.symm_apply_apply] using hp.trans ht
  rw [EvenTI.P21Site.RowOrder.physical_row_site]
  unfold EvenTI.LiveAlgebra.numberedOrigin
  rw [Equiv.symm_apply_apply,hFixed,hm]
  by_cases he : ((m (w.mode r)).blocks.get j).factor.2 = 1 <;> simp [he]

#print axioms nativeBlock_multiplicity
#print axioms prepareAnchorPair_tags
#print axioms archive_multiplicity_native
#print axioms archive_match_site
#print axioms prepareAnchorPair_factorRows
#print axioms blockPolys_spec
#print axioms archive_perm_native
#print axioms native_keys_nodup
end EvenTI.P22Site.NativeKeys

