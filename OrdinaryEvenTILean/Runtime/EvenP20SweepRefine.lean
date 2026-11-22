import EvenP20ScalarNativeCRTMeaning
import Mathlib.LinearAlgebra.Matrix.Bilinear

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvenTI.P20SweepRefine

open scoped BigOperators Matrix
open Matrix EvenTI.Part8 EvenOrdinaryTI.LiveRows EvenTI.P20Scalar

variable {K : Type} [Field K] {I J : Type} [Fintype J] {r p : ℕ}

/-- Split each coarse chart row against all native projectors. This avoids
assigning a coarse primary cell to a single native CRT variable. -/
def refinedRows (X : I → Matrix (Fin r) (Fin r) K) (E : J → Matrix (Fin r) (Fin r) K) :
    I × J → Matrix (Fin r) (Fin r) K := fun ij => X ij.1*E ij.2

/-- The refined chart still spans the identity, even if a coarse row touches
several distinct native cells. -/
theorem one_mem_span_refinedRows (X : I → Matrix (Fin r) (Fin r) K)
    (E : J → Matrix (Fin r) (Fin r) K)
    (hX : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hE : ∑ j, E j = 1) :
    (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range (refinedRows X E)) := by
  refine (Submodule.span_le.mpr ?_) hX
  rintro Z ⟨i,rfl⟩
  have hx : X i=∑ j, refinedRows X E (i,j) := by
    simp only [refinedRows,← Finset.mul_sum,hE,Matrix.mul_one]
  rw [hx]
  exact Submodule.sum_mem _ (fun j _ => Submodule.subset_span ⟨(i,j),rfl⟩)

theorem refinedRows_eigen (X : I → Matrix (Fin r) (Fin r) K)
    (E : J → Matrix (Fin r) (Fin r) K) (N : Matrix (Fin r) (Fin r) K)
    (a : J → K) (hE : ∀ j, E j*N=a j • E j) (ij : I × J) :
    refinedRows X E ij*N=a ij.2 • refinedRows X E ij := by
  unfold refinedRows
  rw [Matrix.mul_assoc,hE,Matrix.mul_smul]

variable [Fintype K] [DecidableEq K]

/-- Native slot equality decides scalarity using the refined chart and one
supported reference. A row may have been split into several native sites. -/
theorem scalarCrop_iff_refinedNativeWords {s t d : ℕ}
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (N : Matrix (Fin r) (Fin r) K) (X : I → Matrix (Fin r) (Fin r) K)
    (E : J → Matrix (Fin r) (Fin r) K) (L : BaseUnitLog K)
    (site : J → Option (Fin s)) (negative : Bool)
    (z : Fin (VarCount (s*2+1) (t+s+1) (d+2)) → ZMod (Fintype.card K-1))
    (reference : I × J) (hRef : refinedRows X E reference*P ≠ 0)
    (hLeft : Q*P=1) (hInvariant : N*P=P*(Q*N*P))
    (hSpan : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hSum : ∑ j, E j=1)
    (hEigen : ∀ j, E j*N=(L.decode
        (if negative then -(z (nativeSourcePhysicalSlot t d (site j))-z (nativePinPhysicalSlot s t d))
          else z (nativeSourcePhysicalSlot t d (site j))-z (nativePinPhysicalSlot s t d)) : K) • E j) :
    (∃ a : K, Q*N*P=a • (1 : Matrix (Fin p) (Fin p) K)) ↔
      ∀ ij, refinedRows X E ij*P ≠ 0 →
        (z (nativeSourcePhysicalSlot t d (site ij.2))).val=
          (z (nativeSourcePhysicalSlot t d (site reference.2))).val :=
  scalarCrop_iff_nativePositiveWords P Q N (refinedRows X E) L (fun ij => site ij.2)
    negative z reference hRef hLeft hInvariant (one_mem_span_refinedRows X E hSpan hSum)
    (refinedRows_eigen X E N _ hEigen)

/-- A nonzero crop has a supported reference in the refined chart, so the
selector can scan the live prefix instead of requiring a chosen reference. -/
theorem exists_supported_refinedRow (X : I → Matrix (Fin r) (Fin r) K)
    (E : J → Matrix (Fin r) (Fin r) K) (P : Matrix (Fin r) (Fin p) K)
    (Q : Matrix (Fin p) (Fin r) K) (hp : 0 < p) (hLeft : Q*P=1)
    (hX : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hE : ∑ j, E j=1) :
    ∃ ij, refinedRows X E ij*P≠0 := by
  classical
  by_contra! h
  let f := mulRightLinearMap (Fin r) K P
  have hk : Submodule.span K (Set.range (refinedRows X E)) ≤ f.ker :=
    Submodule.span_le.mpr (by
      rintro _ ⟨ij,rfl⟩
      exact LinearMap.mem_ker.mpr (h ij))
  have h0 := LinearMap.mem_ker.mp (hk (one_mem_span_refinedRows X E hX hE))
  change (1 : Matrix (Fin r) (Fin r) K)*P=0 at h0
  rw [Matrix.one_mul] at h0
  rw [h0,Matrix.mul_zero] at hLeft
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  exact zero_ne_one hLeft


#print axioms exists_supported_refinedRow
#print axioms scalarCrop_iff_refinedNativeWords
end EvenTI.P20SweepRefine


