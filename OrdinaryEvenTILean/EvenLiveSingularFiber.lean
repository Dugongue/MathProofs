import EvenLiveSingularBasis
import EvenLiveSingularBlock
import EvenLiveSingularKernels

/-! The exact conditional law on retained coordinates of a two-kernel fiber. -/
namespace Mathproof.EvenOrdinaryTISingular
open Module

noncomputable section

variable {K U V Z : Type*} [Field K] [Fintype K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Module.Finite K U] [Fintype V]

/-- The observed columns of a uniform isomorphism are uniform independent
columns. The observation can apply any subsequent projection or anchor. -/
theorem uniformFraction_equiv_retained {b t : ℕ}
    (y : Independent K U b) (hU : b+t = finrank K U) (hV : b+t = finrank K V)
    (f : V → Z) (P : (Fin b → Z) → Prop) :
    uniformFraction (U ≃ₗ[K] V) (fun g => P (fun i => f (g (y.val i)))) =
      uniformFraction (Independent K V b) (fun x => P (fun i => f (x.val i))) := by
  classical
  obtain ⟨B, hB⟩ := suffix_basis_exists y hU
  let e := linearEquivColumns B hV
  let g := LinearEquiv.ofFinrankEq U V (hU.symm.trans hV)
  letI : Nonempty (Independent K V (b+t)) := ⟨e g⟩
  let S (x : Independent K V (b+t)) := P (fun i => f (suffix t x.val i))
  have hS (x : U ≃ₗ[K] V) : S (e x) = P (fun i => f (x (y.val i))) := by
    change P (fun i => f (suffix t (x ∘ ⇑B) i)) = _
    rw [suffix_comp, hB]
    rfl
  have h := uniformFraction_equiv e S
  simp only [hS] at h
  rw [h]
  exact uniformFraction_independent_suffix (K := K) (V := V) (b := b) (t := t)
    (fun a => P (fun i => f (a i)))

variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [Module.Finite K A] [Fintype B]

/-- The exact two-kernel conditioning retains the uniform law on independent
columns of the induced image, tested after any chosen observation. -/
theorem uniformFraction_twoKernels_retained {b t : ℕ}
    (R : Submodule K A) (L : Submodule K B)
    (y : Independent K (A ⧸ R) b) (hR : b+t = finrank K (A ⧸ R))
    (hL : b+t = finrank K L) (f : L → Z) (P : (Fin b → Z) → Prop) :
    uniformFraction (TwoKernels R L.dualAnnihilator)
      (fun x => P (fun i => f (toKernelRangeEquiv R L (twoKernelsEquiv R L x) (y.val i)))) =
      uniformFraction (Independent K L b) (fun x => P (fun i => f (x.val i))) := by
  classical
  letI : Fintype L := Fintype.ofFinite _
  let e := (twoKernelsEquiv R L).trans (kernelRangeEquiv R L)
  have he := uniformFraction_equiv e
    (fun x : ((A ⧸ R) ≃ₗ[K] L) => P (fun i => f (x (y.val i))))
  change uniformFraction (TwoKernels R L.dualAnnihilator)
    (fun x => P (fun i => f (toKernelRangeEquiv R L (twoKernelsEquiv R L x) (y.val i)))) = _ at he
  rw [he]
  exact uniformFraction_equiv_retained (V := L) y hR hL f P

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_equiv_retained
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_twoKernels_retained
