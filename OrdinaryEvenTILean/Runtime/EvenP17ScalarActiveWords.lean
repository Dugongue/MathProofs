import EvenP15ScalarActiveDiagonal
import EvenP8BaseUnitLog

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P17Scalar

open EvenTI.P15Scalar EvenTI.Part8 Matrix

variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- On the base-unit part of a capped kernel, raw scalarity is exactly
equality of the CRT residue words at active chart rows. This bypasses
construction of the corresponding field action matrix for each probe. -/
theorem scalarCrop_iff_activeExponentWords
    (P : Matrix I J K) (Q : Matrix J I K) (N : Matrix I I K)
    (U : (Matrix I I K)ˣ) (L : BaseUnitLog K) {c : ℕ}
    (slot : I → Fin c) (x : Fin c → ZMod (Fintype.card K-1))
    (reference : I) (hRef : ∃ j, (U.inv*P) reference j ≠ 0)
    (hLeft : Q*P=1)
    (hConj : N = U.val *
      Matrix.diagonal (fun i => (L.decode (x (slot i)) : K)) * U.inv)
    (hInvariant : N*P=P*(Q*N*P)) :
    (∃ a : K, Q*N*P = a • (1 : Matrix J J K)) ↔
      ∀ i, (∃ j, (U.inv*P) i j ≠ 0) →
        (x (slot i)).val = (x (slot reference)).val := by
  letI : NeZero (Fintype.card K-1) :=
    ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩
  have hDecode : Function.Injective (fun z : ZMod (Fintype.card K-1) =>
      (L.decode z : K)) := by
    intro u v huv
    have he : L.decode u = L.decode v := Units.ext huv
    have hz := L.mulEquiv.injective he
    exact congrArg Multiplicative.toAdd hz
  constructor
  · rintro ⟨a,ha⟩ i hi
    have hAll := (scalarCrop_iff_activeChartRows P Q N U
      (fun i => (L.decode (x (slot i)) : K)) a hLeft hConj hInvariant).mp ha
    exact congrArg ZMod.val (hDecode ((hAll i hi).trans (hAll reference hRef).symm))
  · intro h
    refine ⟨(L.decode (x (slot reference)) : K),?_⟩
    apply (scalarCrop_iff_activeChartRows P Q N U
      (fun i => (L.decode (x (slot i)) : K))
      (L.decode (x (slot reference)) : K) hLeft hConj hInvariant).mpr
    intro i hi
    exact congrArg (fun z => (L.decode z : K))
      (ZMod.val_injective _ (h i hi))

#print axioms scalarCrop_iff_activeExponentWords
end EvenTI.P17Scalar
