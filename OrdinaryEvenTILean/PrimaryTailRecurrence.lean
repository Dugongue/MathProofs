import PrimaryTailCount
import PrimaryTailPeel

namespace Mathproof.Problem17PrimaryTail
open Module Matrix LinearMap Polynomial
open Mathproof.Problem18IrreducibleOperatorCard20260930
noncomputable section
set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [Fintype K]

local instance finiteCoordinateEnd (n : ℕ) : Finite (End K (Coord K n)) :=
  Finite.of_injective (fun A : End K (Coord K n) => (A : Coord K n → Coord K n)) DFunLike.coe_injective

abbrev powerEvent (f : K[X]) (k n : ℕ) :=
  PolyEvent (fun p => f^k ∣ p) (Coord K n)

theorem irreducible_coord_count (f : K[X]) (hf : f.Monic) (hi : Irreducible f) :
    Nat.card (PolyEvent (· = f) (Coord K f.natDegree)) *
      (Nat.card K ^ f.natDegree - 1) = Nat.card (GL (Fin f.natDegree) K) := by
  letI : Fact (Irreducible f) := ⟨hi⟩
  let E := AdjoinRoot f
  letI : FiniteDimensional K E := (AdjoinRoot.powerBasis hi.ne_zero).finite
  letI : Finite E := Module.finite_of_finite (R := K)
  letI : Fintype E := Fintype.ofFinite _
  have hdim : finrank K E = f.natDegree := by
    change finrank K (AdjoinRoot f) = f.natDegree
    exact finrank_quotient_span_eq_natDegree
  let e : E ≃ₗ[K] Coord K f.natDegree :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Coord] using hdim)
  have he : Nat.card E = Nat.card K ^ f.natDegree := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := K),
      Module.card_eq_pow_finrank (K := K), hdim]
  have hc := irreducible_operator_card f hf
  change Nat.card (PolyEvent (· = f) E) * (Nat.card E - 1) = _ at hc
  rw [polyEvent_congr (· = f) e, he] at hc
  let g : (E ≃ₗ[K] E) ≃ (Coord K f.natDegree ≃ₗ[K] Coord K f.natDegree) :=
    { toFun := fun A => (e.symm.trans A).trans e
      invFun := fun A => (e.trans A).trans e.symm
      left_inv := by intro A; ext x; simp
      right_inv := by intro A; ext x; simp }
  let h : GL (Fin f.natDegree) K ≃* (Coord K f.natDegree ≃ₗ[K] Coord K f.natDegree) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Coord K f.natDegree))
  rw [Nat.card_congr (g.trans h.toEquiv.symm)] at hc
  exact hc

theorem power_event_card_le (f : K[X]) (hf : f.Monic) (hi : Irreducible f) (k n : ℕ) :
    Nat.card (powerEvent f k n) * (Nat.card K ^ f.natDegree - 1)^k ≤
      Nat.card K ^ (n*n) := by
  induction k generalizing n with
  | zero =>
    simpa only [pow_zero, mul_one, ← end_card (K := K) n] using
      (Nat.card_le_card_of_injective (fun a : powerEvent f 0 n => a.val) Subtype.val_injective)
  | succ k ih =>
    let d := f.natDegree
    let q := Nat.card K
    let c := Nat.card (PolyEvent (· = f) (Coord K d))
    by_cases hn : Nonempty (powerEvent f (k+1) n)
    · obtain ⟨T⟩ := hn
      have hW := exists_peel T.val f hf hi k T.property
      obtain ⟨S, hS, hdS, _, _⟩ := hW
      have hdn : d ≤ n := by
        have hd := Submodule.finrank_le S
        rw [hdS] at hd
        simpa [Coord] using hd
      have hcount := invariant_union_card (K := K) hdn (· = f) (fun g => f^k ∣ g)
        (fun g => f^(k+1) ∣ g) (fun A => by
          obtain ⟨U, hU, hu, ha, hq⟩ := exists_peel A.val f hf hi k A.property
          exact ⟨⟨U, hu⟩, hU, ha, hq⟩)
      have hweight := irreducible_coord_count f hf hi
      have hc : 0 < c := by
        by_contra! hz
        have he : c = 0 := Nat.eq_zero_of_le_zero hz
        change c * (q^d-1) = Nat.card (GL (Fin d) K) at hweight
        rw [he, zero_mul] at hweight
        exact (Nat.card_pos (α := GL (Fin d) K)).ne' hweight.symm
      rw [← hweight] at hcount
      have hStep : Nat.card (powerEvent f (k+1) n) * (q^d - 1) ≤
          Nat.card (powerEvent f k (n-d)) * q^(d*n+d*(n-d)) := by
        refine Nat.le_of_mul_le_mul_left ?_ hc
        calc
          _ = Nat.card (powerEvent f (k+1) n) * (c * (q^d-1)) := by ring
          _ ≤ c * Nat.card (powerEvent f k (n-d)) * q^(d*n+d*(n-d)) := hcount
          _ = _ := by ring
      have hexp : (n-d)*(n-d) + (d*n+d*(n-d)) = n*n := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdn
        rw [Nat.add_sub_cancel_left]
        ring
      calc
        _ = (Nat.card (powerEvent f (k+1) n) * (q^d-1)) * (q^d-1)^k := by
          change Nat.card (powerEvent f (k+1) n) * (q^d-1)^(k+1) = _
          rw [pow_succ']; ring
        _ ≤ (Nat.card (powerEvent f k (n-d)) * q^(d*n+d*(n-d))) * (q^d-1)^k :=
          Nat.mul_le_mul_right _ hStep
        _ = (Nat.card (powerEvent f k (n-d)) * (q^d-1)^k) * q^(d*n+d*(n-d)) := by ring
        _ ≤ q^((n-d)*(n-d)) * q^(d*n+d*(n-d)) := Nat.mul_le_mul_right _ (ih (n-d))
        _ = _ := by rw [← pow_add, hexp]
    · haveI : IsEmpty (powerEvent f (k+1) n) := not_nonempty_iff.mp hn
      simp

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.power_event_card_le
