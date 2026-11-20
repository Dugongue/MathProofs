import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Mathproof.Problem17TracePairing
open Module LinearMap
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- A symmetric pairing has a nondegenerate subspace in any restriction,
with loss at most twice the original codimension. -/
theorem exists_nondegenerate_subspace (B : BilinForm K V) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (S : Submodule K V) :
    ∃ U : Submodule K V, U ≤ S ∧ (B.restrict U).Nondegenerate ∧
      finrank K (V ⧸ U) ≤ 2 * finrank K (V ⧸ S) := by
  let R := (B.restrict S).ker
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R
  let U := C.map S.subtype
  have hU : U ≤ S := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hR : finrank K R ≤ finrank K (V ⧸ S) := by
    let j : R →ₗ[K] B.orthogonal S :=
      (S.subtype.comp R.subtype).codRestrict _ (by
        intro x
        rw [BilinForm.mem_orthogonal_iff]
        intro y hy
        change B y x.val.val = 0
        have hx : (B.restrict S) x.val = 0 := x.property
        have he := LinearMap.congr_fun hx ⟨y, hy⟩
        change B x.val.val y = 0 at he
        rw [hs.eq, he])
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : B.orthogonal S => (z : V)) h
    have hh := LinearMap.finrank_le_finrank_of_injective hj
    rwa [BilinForm.finrank_orthogonal hn, ← S.finrank_quotient] at hh
  have hdim : finrank K (V ⧸ U) ≤ 2 * finrank K (V ⧸ S) := by
    have h₁ := Submodule.finrank_add_eq_of_isCompl hC
    have h₂ := U.finrank_quotient_add_finrank
    have h₃ := S.finrank_quotient_add_finrank
    have h₄ : finrank K U = finrank K C := Submodule.finrank_map_subtype_eq S C
    omega
  have hleft : (B.restrict U).SeparatingLeft := by
    intro x hx
    obtain ⟨a, ha, he⟩ := x.property
    have haR : a ∈ R := by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro z
      have hz : z ∈ R ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨r, hr, c, hc, rfl⟩ := Submodule.mem_sup.mp hz
      have hRz : B a.val r.val = 0 := by
        have hh : (B.restrict S) r = 0 := hr
        rw [hs.eq]
        exact LinearMap.congr_fun hh a
      have hCz : B a.val c.val = 0 := by
        have hh := hx ⟨c.val, ⟨c, hc, rfl⟩⟩
        change B x.val c.val = 0 at hh
        change B (S.subtype a) c.val = 0
        rw [he]
        exact hh
      change B a.val (r.val + c.val) = 0
      rw [map_add, hRz, hCz, add_zero]
    have haz : a = 0 := by
      have hh : a ∈ R ⊓ C := ⟨haR, ha⟩
      rwa [hC.inf_eq_bot, Submodule.mem_bot] at hh
    apply Subtype.ext
    change x.val = 0
    rw [← he, haz]
    rfl

  refine ⟨U, hU, ⟨hleft, ?_⟩, hdim⟩
  intro x hx
  apply hleft x
  intro y
  change B x.val y.val = 0
  rw [hs.eq]
  exact hx y
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tracePairing : LinearMap.BilinForm K (Matrix ι ι K) where
  toFun A := {
    toFun := fun B => (A * B).trace
    map_add' := by intro B C; rw [Matrix.mul_add, Matrix.trace_add]
    map_smul' := by intro a B; simp [Matrix.trace_smul] }
  map_add' A B := by ext C; simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' a A := by ext C; simp [Matrix.trace_smul]

theorem tracePairing_symmetric : (tracePairing (K := K) (ι := ι)).IsSymm :=
  ⟨fun A B => Matrix.trace_mul_comm A B⟩

theorem tracePairing_nondegenerate : (tracePairing (K := K) (ι := ι)).Nondegenerate := by
  have hleft : (tracePairing (K := K) (ι := ι)).SeparatingLeft := by
    intro A hA
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro B
    have hb : (A * B).trace = 0 := hA B
    simpa using hb
  refine ⟨hleft, ?_⟩
  intro A hA
  apply hleft A
  intro B
  exact (tracePairing_symmetric.eq A B).trans (hA B)

theorem trace_zero_contains_nondegenerate_large [Nonempty ι] :
    ∃ U : Submodule K (Matrix ι ι K),
      U ≤ (Matrix.traceLinearMap (α := K) ι K).ker ∧
      ((tracePairing (K := K) (ι := ι)).restrict U).Nondegenerate ∧
      finrank K (Matrix ι ι K ⧸ U) ≤ 2 := by
  let f := Matrix.traceLinearMap (α := K) ι K
  have hF : f.range = ⊤ := LinearMap.range_eq_top.mpr Matrix.trace_surjective
  have hcodim : finrank K (Matrix ι ι K ⧸ f.ker) = 1 := by
    rw [f.quotKerEquivRange.finrank_eq, hF, finrank_top, Module.finrank_self]
  obtain ⟨U, hu, hn, hb⟩ := exists_nondegenerate_subspace
    tracePairing tracePairing_symmetric tracePairing_nondegenerate f.ker
  exact ⟨U, hu, hn, by simpa [hcodim] using hb⟩

end Mathproof.Problem17TracePairing

#print axioms Mathproof.Problem17TracePairing.exists_nondegenerate_subspace
#print axioms Mathproof.Problem17TracePairing.trace_zero_contains_nondegenerate_large


