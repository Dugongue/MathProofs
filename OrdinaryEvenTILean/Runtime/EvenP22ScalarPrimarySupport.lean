import EvenP22ScalarCoverage
import EvenP21PadBasisSupport

set_option autoImplicit false

namespace EvenTI.P22Scalar
open Matrix EvenTI.P20Pad EvenTI.P21Pad EvenTI.P21ScalarScan

variable {K L : Type} [Field K]

/-- Multiple native origins can describe one primary block. The support of
that block is the existence of a supported row in any of its origins. -/
theorem primarySupport_iff_exists_origin
    {n s : ℕ} {C : Fin s → Type} (e : (Σ i, C i) ≃ Fin n)
    (label : Fin s → L) (V : Matrix (Fin n) (Fin n) K)
    (right : Bool) (cutoff : ℕ) (f : L) :
    (∃ c : Fin n, columnKept right cutoff c.val=true ∧
      ∃ r, label (e.symm r).1=f ∧ V r c≠0) ↔
      ∃ i, label i=f ∧ inverseBlockSupported right cutoff e V i := by
  constructor
  · rintro ⟨c,hc,r,hr,hnz⟩
    refine ⟨(e.symm r).1,hr,⟨(e.symm r).2,c,hc,?_⟩⟩
    simpa only [Sigma.eta,Equiv.apply_symm_apply] using hnz
  · rintro ⟨i,hi,a,c,hc,hnz⟩
    exact ⟨c,hc,e ⟨i,a⟩,by simpa using hi,hnz⟩

/-- The raw archived inverse chart and the reference inverse chart agree
on supported primary labels even when their within-block bases differ. -/
theorem archivedPrimary_support
    {n s t : ℕ} {A : Fin s → Type} {B : Fin t → Type}
    (archiveOrder : (Σ i, A i) ≃ Fin n) (nativeOrder : (Σ j, B j) ≃ Fin n)
    (archiveLabel : Fin s → L) (nativeLabel : Fin t → L)
    (archive native : (Matrix (Fin n) (Fin n) K)ˣ)
    (spans : ∀ f, Submodule.span K (archive.val.col '' {r | archiveLabel (archiveOrder.symm r).1=f}) =
      Submodule.span K (native.val.col '' {r | nativeLabel (nativeOrder.symm r).1=f}))
    (right : Bool) (cutoff : ℕ) (f : L) :
    (∃ i, archiveLabel i=f ∧ inverseBlockSupported right cutoff archiveOrder archive.inv i) ↔
      ∃ j, nativeLabel j=f ∧ inverseBlockSupported right cutoff nativeOrder native.inv j := by
  refine (primarySupport_iff_exists_origin archiveOrder archiveLabel archive.inv right cutoff f).symm.trans ?_
  refine (inverseMatrixSupport_iff_of_columnSpans archive native
    (fun r => archiveLabel (archiveOrder.symm r).1)
    (fun r => nativeLabel (nativeOrder.symm r).1) spans
    (fun c => columnKept right cutoff c.val=true) f).trans ?_
  exact primarySupport_iff_exists_origin nativeOrder nativeLabel native.inv right cutoff f

/-- A primary label may be shared by several repeated origins. A label
and its one CRT slot suffice to transfer exact physical chart coverage. -/
theorem ChartCoverage.of_primaryLabels {W N : ℕ} {I J : Type}
    {plan : ScanModeInput W N} (a : I → L) (b : J → L) (slot : L → Fin N)
    (A : I → Prop) (B : J → Prop)
    (covered : ChartCoverage plan (slot ∘ a) A)
    (same : ∀ f, (∃ i, a i=f ∧ A i) ↔ (∃ j, b j=f ∧ B j)) :
    ChartCoverage plan (slot ∘ b) B := by
  apply covered.of_sameSites (slot ∘ b) B
  intro k
  constructor
  · rintro ⟨i,hi,hs⟩
    obtain ⟨j,hj,hj'⟩ := (same (a i)).mp ⟨i,rfl,hi⟩
    exact ⟨j,hj',by simpa only [Function.comp_apply,hj] using hs⟩
  · rintro ⟨j,hj,hs⟩
    obtain ⟨i,hi,hi'⟩ := (same (b j)).mpr ⟨j,rfl,hj⟩
    exact ⟨i,hi',by simpa only [Function.comp_apply,hi] using hs⟩

#print axioms primarySupport_iff_exists_origin
#print axioms archivedPrimary_support
#print axioms ChartCoverage.of_primaryLabels
end EvenTI.P22Scalar
