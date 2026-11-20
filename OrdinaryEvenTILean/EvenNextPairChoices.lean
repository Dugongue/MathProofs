import EvenNextEnumeration
import EvenNextKernelTransport
import Mathlib.Data.List.ProdSigma

namespace EvenTI.Contract

open Action

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

structure CutFrames (T : Tensor K (l + r) n) where
  leftDim : Nat
  rightDim : Nat
  left : (Fin leftDim → K) ≃ₗ[K] (leftCutKernel T).ker
  right : (Fin rightDim → K) ≃ₗ[K] (rightCutKernel T).ker

abbrev CutFormPair (K : Type) (l r n : Nat) := (Coord l n → K) × (Coord r n → K)

def cutFormPairs (F : FieldEncoding K) (T : Tensor K (l + r) n) (frames : CutFrames T)
    (goodLeft : (Coord l n → K) → Bool) (goodRight : (Coord r n → K) → Bool) :
    List (CutFormPair K l r n) :=
  (kernelForms F (leftCutKernel T) frames.left n goodLeft).product
    (kernelForms F (rightCutKernel T) frames.right n goodRight)

theorem cutFormPairs_length (F : FieldEncoding K) (T : Tensor K (l + r) n)
    (frames : CutFrames T) (goodLeft : (Coord l n → K) → Bool)
    (goodRight : (Coord r n → K) → Bool) :
    (cutFormPairs F T frames goodLeft goodRight).length ≤ n ^ 2 := by
  let L := kernelForms F (leftCutKernel T) frames.left n goodLeft
  let R := kernelForms F (rightCutKernel T) frames.right n goodRight
  change (L.product R).length ≤ n ^ 2
  have h : (L.product R).length = L.length * R.length := List.length_product L R
  rw [h, pow_two]
  exact Nat.mul_le_mul (kernelForms_length_le F _ _ n _) (kernelForms_length_le F _ _ n _)

theorem cutFormPairs_covers_transporter (F : FieldEncoding K)
    {T S : Tensor K (l + r) n} (frames : CutFrames S) (g : Changes K (l + r) n)
    (hg : act g T = S) (gLeft : (Coord l n → K) → Bool)
    (gRight : (Coord r n → K) → Bool) (x : Coord l n → K) (y : Coord r n → K)
    (hx : leftCutKernel T x = 0) (hy : rightCutKernel T y = 0)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hLeft : Fintype.card K ^ frames.leftDim ≤ n)
    (hRight : Fintype.card K ^ frames.rightDim ≤ n)
    (hxAllow : gLeft (moveLeftForm g x) = true) (hyAllow : gRight (moveRightForm g y) = true) :
    (moveLeftForm g x, moveRightForm g y) ∈ cutFormPairs F S frames gLeft gRight := by
  apply List.mem_product.mpr
  refine ⟨(mem_kernelForms F _ _ _ _ _).mpr ⟨⟨?_, hLeft⟩, ?_, hxAllow⟩,
    (mem_kernelForms F _ _ _ _ _).mpr ⟨⟨?_, hRight⟩, ?_, hyAllow⟩⟩
  · rw [← hg]
    exact (leftCutKernel_transport g T x).mpr hx
  · exact moveCutForm_ne_zero _ hx0
  · rw [← hg]
    exact (rightCutKernel_transport g T y).mpr hy
  · exact moveCutForm_ne_zero _ hy0

#print axioms cutFormPairs_length
#print axioms cutFormPairs_covers_transporter

end EvenTI.Contract
