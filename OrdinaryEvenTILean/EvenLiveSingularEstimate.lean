import EvenLiveSingularFiber

/-! Quantitative comparison after restriction to retained independent columns. -/
namespace Mathproof.EvenOrdinaryTISingular
open Module

noncomputable section

variable {K V W : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W]

/-- A surjective crop of a uniform independent tuple is close to uniform,
since discarding dependent tuples costs precisely their fraction. -/
theorem uniformFraction_independent_observation {b : ℕ}
    [Nonempty (Independent K V b)] (hb : b ≤ finrank K V)
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (P : (Fin b → W) → Prop) :
    |uniformFraction (Independent K V b) (fun x => P (fun i => f (x.val i))) -
      uniformFraction (Fin b → W) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
       ((Fintype.card K : ℝ)^(finrank K V) * ((Fintype.card K : ℝ) - 1)) := by
  let g : (Fin b → V) →ₗ[K] (Fin b → W) := LinearMap.pi fun i => f.comp (LinearMap.proj i)
  have hg : Function.Surjective g := by
    intro x
    exact ⟨fun i => Function.surjInv hf (x i), funext fun i => Function.surjInv_eq hf (x i)⟩
  have eq := uniformFraction_linear_surjective g hg P
  change |uniformFraction (Independent K V b) (fun x => P (g x.val)) - _| ≤ _
  rw [← eq]
  have hc := uniformFraction_conditioning_gap (A := Fin b → V) (fun x => P (g x))
    (fun x : Fin b → V => LinearIndependent K x)
  have hd := independent_discard_fraction_le (K := K) (V := V) b hb
  exact le_trans hc hd

variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [Module.Finite K A] [Fintype B]

/-- Every event tested after an arbitrary surjective row crop on the exact
two-kernel fiber differs from its uniform probability by the displayed error. -/
theorem uniformFraction_twoKernels_crop {b t : ℕ}
    (R : Submodule K A) (L : Submodule K B)
    (y : Independent K (A ⧸ R) b) (hR : b+t = finrank K (A ⧸ R))
    (hL : b+t = finrank K L) (f : L →ₗ[K] W) (hf : Function.Surjective f)
    (P : (Fin b → W) → Prop) :
    |uniformFraction (TwoKernels R L.dualAnnihilator)
        (fun x => P (fun i => f (toKernelRangeEquiv R L (twoKernelsEquiv R L x) (y.val i)))) -
      uniformFraction (Fin b → W) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(b+t) * ((Fintype.card K : ℝ) - 1)) := by
  letI : Fintype L := Fintype.ofFinite _
  let g := LinearEquiv.ofFinrankEq (A ⧸ R) L (hR.symm.trans hL)
  letI : Nonempty (Independent K L b) :=
    ⟨⟨g ∘ y.val, y.property.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)⟩⟩
  rw [uniformFraction_twoKernels_retained R L y hR hL f P]
  have hb : b ≤ finrank K L := hL ▸ Nat.le_add_right b t
  simpa only [← hL] using uniformFraction_independent_observation (K := K) hb f hf P

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_independent_observation
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_twoKernels_crop
