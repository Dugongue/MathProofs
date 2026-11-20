import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-! Direct translation of the cyclic-isotropy argument in
`Problem18PfaffianInformalProof20260930.md`. It supplies the exclusion of a
cyclic h²-primary block needed by the exact Pfaffian orbit count. -/
namespace Mathproof.Problem18CyclicIsotropy20260930

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Powers of a self-adjoint operator move across the bilinear pairing. -/
theorem selfAdjoint_pow_move (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hS : B.IsSelfAdjoint S) (i : ℕ) (x y : V) :
    B ((S ^ i) x) y = B x ((S ^ i) y) := by
  induction i generalizing x y with
  | zero => simp
  | succ i ih =>
    calc
      B ((S ^ (i + 1)) x) y = B (S ((S ^ i) x)) y := by
        rw [pow_succ']
        rfl
      _ = B ((S ^ i) x) (S y) := hS _ _
      _ = B x ((S ^ i) (S y)) := ih _ _
      _ = B x ((S ^ (i + 1)) y) := by
        rw [pow_succ]
        rfl

/-- Alternation of both B and B(-,S-) kills every cyclic diagonal pairing.
No division by two is used, so this includes characteristic two. -/
theorem selfAdjoint_cyclic_diagonal_zero
    (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hB : B.IsAlt) (hS : B.IsSelfAdjoint S)
    (hBS : ∀ v : V, B v (S v) = 0) (k : ℕ) (v : V) :
    B v ((S ^ k) v) = 0 := by
  induction k using Nat.twoStepInduction generalizing v with
  | zero => simpa using hB v
  | one => simpa using hBS v
  | more k ih _ =>
    have he : S ^ (k + 2) = S * (S ^ k) * S := by
      rw [← pow_succ', ← pow_succ]
    calc
      B v ((S ^ (k + 2)) v) = B v (S ((S ^ k) (S v))) := by
        rw [he]
        rfl
      _ = B (S v) ((S ^ k) (S v)) := (hS _ _).symm
      _ = 0 := ih (S v)

/-- Any two power iterates of the same vector are orthogonal. -/
theorem selfAdjoint_cyclic_powers_zero
    (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hB : B.IsAlt) (hS : B.IsSelfAdjoint S)
    (hBS : ∀ v : V, B v (S v) = 0) (i j : ℕ) (v : V) :
    B ((S ^ i) v) ((S ^ j) v) = 0 := by
  rw [selfAdjoint_pow_move B S hS i]
  have he : (S ^ i) ((S ^ j) v) = (S ^ (i + j)) v := by
    rw [pow_add]
    rfl
  rw [he]
  exact selfAdjoint_cyclic_diagonal_zero B S hB hS hBS (i + j) v

/-- The actual cyclic span is totally isotropic, as required to exclude the
cyclic elementary divisor h² in a nonsingular simple Pfaffian primary block. -/
theorem selfAdjoint_cyclic_span_isotropic
    (B : LinearMap.BilinForm K V) (S : Module.End K V)
    (hB : B.IsAlt) (hS : B.IsSelfAdjoint S)
    (hBS : ∀ v : V, B v (S v) = 0) (v x y : V)
    (hx : x ∈ Submodule.span K (Set.range fun i : ℕ => (S ^ i) v))
    (hy : y ∈ Submodule.span K (Set.range fun i : ℕ => (S ^ i) v)) :
    B x y = 0 := by
  have h := LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (⊥ : Submodule K K) (Set.range fun i : ℕ => (S ^ i) v)
    (Set.range fun i : ℕ => (S ^ i) v) B
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      simpa using selfAdjoint_cyclic_powers_zero B S hB hS hBS i j v)
    x y hx hy
  simpa using h

end Mathproof.Problem18CyclicIsotropy20260930
