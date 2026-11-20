import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.List.FinRange

/-! The Frobenius gauge method from the Problem 1.7 finite-field transport
proof, using the current Mathlib cyclic Frobenius and embedding counts. -/
namespace EvenTI.CellPreparation

open Module

variable {K A B : Type} [Field K] [Fintype K] [Field A] [Field B]
  [Algebra K A] [Algebra K B] [Finite A] [Finite B] [DecidableEq B] {d : ℕ}

private theorem iterateFrob_apply (k : ℕ) (x : A) :
    ((FiniteField.frobeniusAlgHom K A) ^ k) x = x ^ (Fintype.card K ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
    change (x ^ (Fintype.card K ^ k)) ^ Fintype.card K = _
    rw [← pow_mul, ← pow_succ]

private theorem embeddingOrbit (f : A →ₐ[K] B) :
    Function.Bijective (fun k : Fin (finrank K A) =>
      f.comp ((FiniteField.frobeniusAlgHom K A) ^ k.val)) := by
  have hdvd := FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨f⟩
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro a b hab
    apply (FiniteField.bijective_frobeniusAlgHom_pow K A).1
    ext x
    exact f.injective (DFunLike.congr_fun hab x)
  · rw [FiniteField.natCard_algHom_of_finrank_dvd hdvd, Nat.card_fin]

/-- Try only the extension-degree many Frobenius powers. Each test checks
the images of the supplied coordinate basis. -/
def gaugeIndex (basis : Fin d → A) (reference live : A →ₐ[K] B) : Option (Fin d) :=
  (List.finRange d).find? fun k =>
    (List.finRange d).all fun i => decide (live (basis i) = reference (basis i) ^
      (Fintype.card K ^ k.val))

theorem gaugeIndex_sound (basis : Basis (Fin d) K A) (reference live : A →ₐ[K] B)
    (k : Fin d) (h : gaugeIndex basis reference live = some k) :
    ∀ x, live x = reference x ^ (Fintype.card K ^ k.val) := by
  have hm := List.find?_some h
  have hp (i : Fin d) := List.all_eq_true.mp hm i (List.mem_finRange _)
  let g := reference.comp ((FiniteField.frobeniusAlgHom K A) ^ k.val)
  have hg (x : A) : g x = reference x ^ (Fintype.card K ^ k.val) := by
    change reference (((FiniteField.frobeniusAlgHom K A) ^ k.val) x) = _
    rw [iterateFrob_apply, map_pow]
  have hEq : live.toLinearMap = g.toLinearMap := by
    apply basis.ext
    intro i
    change live (basis i) = g (basis i)
    rw [hg]
    exact of_decide_eq_true (hp i)
  intro x
  exact (LinearMap.congr_fun hEq x).trans (hg x)

theorem gaugeIndex_total (basis : Basis (Fin d) K A) (reference live : A →ₐ[K] B) :
    (gaugeIndex basis reference live).isSome := by
  obtain ⟨k, hk⟩ := (embeddingOrbit reference).2 live
  have hd : finrank K A = d := by
    simpa using (finrank_eq_card_basis basis)
  let j : Fin d := (finCongr hd) k
  have hpass : (List.finRange d).all (fun i => decide
      (live (basis i) = reference (basis i) ^ (Fintype.card K ^ j.val))) = true := by
    apply List.all_eq_true.mpr
    intro i _
    apply decide_eq_true
    rw [← hk]
    change reference (((FiniteField.frobeniusAlgHom K A) ^ k.val) (basis i)) = _
    rw [iterateFrob_apply, map_pow]
    rfl
  apply Option.isSome_iff_ne_none.mpr
  intro hnone
  exact List.find?_eq_none.mp hnone j (List.mem_finRange _) hpass

#print axioms gaugeIndex_sound
#print axioms gaugeIndex_total

end EvenTI.CellPreparation
