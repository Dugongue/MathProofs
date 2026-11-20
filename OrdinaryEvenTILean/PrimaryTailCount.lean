import PrimaryTailBlock
import Mathproof.Meta.Problem18SubspaceCountNarrow20260929

namespace Mathproof.Problem17PrimaryTail
open Module Matrix LinearMap Polynomial
open scoped BigOperators
noncomputable section
set_option linter.style.haveILetI false

variable {K V W U : Type*} [Field K] [Fintype K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]

local instance finiteMap {A B : Type*} [AddCommGroup A] [Module K A] [Finite A]
    [AddCommGroup B] [Module K B] [Finite B] : Finite (A →ₗ[K] B) :=
  Finite.of_injective (fun T : A →ₗ[K] B => (T : A → B)) DFunLike.coe_injective
def PolyEvent (p : K[X] → Prop) (V : Type*) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :=
  {T : End K V // p T.charpoly}

abbrev Coord (K : Type*) (n : ℕ) := Fin n → K

omit [Fintype K] in
theorem polyEvent_congr (p : K[X] → Prop) (e : V ≃ₗ[K] W) :
    Nat.card (PolyEvent p V) = Nat.card (PolyEvent p W) :=
  Nat.card_congr (e.conj.toEquiv.subtypeEquiv fun _ =>
    (by rw [LinearEquiv.coe_toEquiv, LinearEquiv.charpoly_conj]))

omit [Fintype K] in
theorem polyEvent_coord (p : K[X] → Prop) (n : ℕ) (hn : finrank K V = n) :
    Nat.card (PolyEvent p V) = Nat.card (PolyEvent p (Coord K n)) :=
  polyEvent_congr p (LinearEquiv.ofFinrankEq V (Coord K n) (by simpa [Coord]))

theorem hom_card :
    Nat.card (U →ₗ[K] W) = Nat.card K ^ (finrank K U * finrank K W) := by
  classical
  letI : Finite U := Module.finite_of_finite (R := K)
  letI : Finite W := Module.finite_of_finite (R := K)
  letI : Fintype (U →ₗ[K] W) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := K), Module.card_eq_pow_finrank (K := K),
    Module.finrank_linearMap, Nat.mul_comm]

theorem end_card (n : ℕ) : Nat.card (End K (Coord K n)) = Nat.card K ^ (n * n) := by
  simpa [Coord] using (hom_card (K := K) (U := Coord K n) (W := Coord K n))

theorem split_count {n d : ℕ} (S : Submodule K (Coord K n)) (hS : finrank K S = d)
    (p q : K[X] → Prop) :
    Nat.card {T : End K (Coord K n) // SplitPred S (fun A => p A.charpoly)
        (fun D => q D.charpoly) T} =
      Nat.card (PolyEvent p (Coord K d)) * Nat.card (PolyEvent q (Coord K (n-d))) *
      Nat.card K ^ (d*(n-d)) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  have hq : finrank K (Coord K n ⧸ S) = n - d := by
    rw [Submodule.finrank_quotient, hS]
    simp [Coord]
  have hc : finrank K C = n - d :=
    ((S.quotientEquivOfIsCompl C hC).finrank_eq).symm.trans hq
  rw [Nat.card_congr (invariantSplitEquiv S C hC (fun A => p A.charpoly) (fun D => q D.charpoly)),
    Nat.card_prod, Nat.card_prod, hom_card, hS, hc]
  change Nat.card (PolyEvent p S) * (Nat.card K ^ ((n-d)*d) *
    Nat.card (PolyEvent q (Coord K n ⧸ S))) = _
  rw [polyEvent_coord p d hS, polyEvent_coord q (n-d) hq, Nat.mul_comm (n-d) d]
  ring

abbrev Grass (K : Type*) [Field K] (n d : ℕ) :=
  {S : Submodule K (Coord K n) // finrank K S = d}

local instance finiteGrass (n d : ℕ) : Finite (Grass K n d) := by
  have : Finite (Submodule K (Coord K n)) :=
    Finite.of_injective (fun S : Submodule K (Coord K n) => (S : Set (Coord K n)))
      SetLike.coe_injective
  infer_instance

set_option maxHeartbeats 1000000 in
/-- Count over all invariant subspaces, paying only the basis multiplicity once. -/
theorem invariant_union_card {n d : ℕ} (hd : d ≤ n) (p q t : K[X] → Prop)
    (witness : ∀ T : PolyEvent t (Coord K n),
      ∃ S : Grass K n d, SplitPred S.val (fun A => p A.charpoly) (fun D => q D.charpoly) T.val) :
    Nat.card (PolyEvent t (Coord K n)) * Nat.card (GL (Fin d) K) ≤
      Nat.card (PolyEvent p (Coord K d)) * Nat.card (PolyEvent q (Coord K (n-d))) *
      Nat.card K ^ (d*n+d*(n-d)) := by
  classical
  let S := Grass K n d
  let C := (Σ s : S, {T : End K (Coord K n) //
    SplitPred s.val (fun A => p A.charpoly) (fun D => q D.charpoly) T})
  let C' := {c : C // t c.2.val.charpoly}
  have : Finite C := by
    dsimp [C]
    infer_instance
  have hsur : Function.Surjective (fun x : C' =>
      (⟨x.val.2.val, x.property⟩ : PolyEvent t (Coord K n))) := by
    intro y
    obtain ⟨s, hs⟩ := witness y
    exact ⟨⟨⟨s, y.val, hs⟩, y.property⟩, rfl⟩
  have hle : Nat.card (PolyEvent t (Coord K n)) ≤ Nat.card C :=
    (Nat.card_le_card_of_surjective _ hsur).trans
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
  letI : Fintype S := Fintype.ofFinite _
  have hC : Nat.card C = Nat.card S *
      (Nat.card (PolyEvent p (Coord K d)) * Nat.card (PolyEvent q (Coord K (n-d))) *
        Nat.card K ^ (d*(n-d))) := by
    let P := fun s : S => {T : End K (Coord K n) //
      SplitPred s.val (fun A => p A.charpoly) (fun D => q D.charpoly) T}
    have hconst (s : S) : Nat.card (P s) =
        Nat.card (PolyEvent p (Coord K d)) * Nat.card (PolyEvent q (Coord K (n-d))) *
          Nat.card K ^ (d*(n-d)) := split_count s.val s.property p q
    change Nat.card (Sigma P) = _
    rw [Nat.card_sigma]
    simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := S)]
    rfl
  have hS : Nat.card S * Nat.card (GL (Fin d) K) ≤ Nat.card K ^ (d*n) := by
    rw [Matrix.card_GL_field, Mathproof.Problem18SubspaceCountNarrow20260929.subspace_card_mul_bases hd,
      Nat.card_eq_fintype_card (α := K)]
    calc
      _ ≤ ∏ _ : Fin d, Fintype.card K ^ n :=
        Finset.prod_le_prod' (fun i _ => Nat.sub_le _ _)
      _ = _ := by simp [← pow_mul, Nat.mul_comm]
  calc
    _ ≤ Nat.card C * Nat.card (GL (Fin d) K) := Nat.mul_le_mul_right _ hle
    _ = (Nat.card S * Nat.card (GL (Fin d) K)) *
        (Nat.card (PolyEvent p (Coord K d)) * Nat.card (PolyEvent q (Coord K (n-d))) *
          Nat.card K ^ (d*(n-d))) := by rw [hC]; ring
    _ ≤ Nat.card K ^ (d*n) * _ := Nat.mul_le_mul_right _ hS
    _ = _ := by rw [pow_add]; ring

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.invariant_union_card