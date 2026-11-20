import PrimaryTailRecurrence
import PrimaryTailGroup
import PrimaryTailBinary
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace Mathproof.Problem17PrimaryTail
open Module Matrix LinearMap Polynomial
noncomputable section
set_option linter.style.haveILetI false

variable {K : Type*} [Field K] [Fintype K]

local instance finiteCoordinateEndAll (n : ℕ) : Finite (End K (Coord K n)) :=
  Finite.of_injective (fun A : End K (Coord K n) => (A : Coord K n → Coord K n)) DFunLike.coe_injective

theorem binary_power_event_card_le (f : K[X]) (hf : f.Monic) (hi : Irreducible f)
    (hd : f.natDegree = 1) (hq : Nat.card K = 2) (k n : ℕ) :
    Nat.card (powerEvent f (2*k) n) * 3^k ≤ 2^k * Nat.card K ^ (n*n) := by
  induction k generalizing n with
  | zero =>
    simp only [mul_zero, pow_zero, mul_one, one_mul, ← end_card (K := K) n]
    exact Nat.card_le_card_of_injective (fun a : powerEvent f 0 n => a.val) Subtype.val_injective
  | succ k ih =>
    have he : 2*(k+1) = 2*k+2 := by omega
    rw [he]
    by_cases hn : Nonempty (powerEvent f (2*k+2) n)
    · obtain ⟨T⟩ := hn
      obtain ⟨S, hS, hdS, _, _⟩ := exists_peel_two T.val f hf hi (2*k) T.property
      have hdn : 2 ≤ n := by
        have hd' := Submodule.finrank_le S
        rw [hdS, hd, one_mul] at hd'
        simpa [Coord] using hd'
      have hcount := invariant_union_card (K := K) hdn (· = f^2) (fun g => f^(2*k) ∣ g)
        (fun g => f^(2*k+2) ∣ g) (fun A => by
          obtain ⟨U, hU, hu, ha, hq⟩ := exists_peel_two A.val f hf hi (2*k) A.property
          rw [hd, one_mul] at hu
          exact ⟨⟨U, hu⟩, hU, ha, hq⟩)
      have hw : 3 * Nat.card (PolyEvent (· = f^2) (Coord K 2)) ≤
          2 * Nat.card (GL (Fin 2) K) := by
        rw [hf.eq_X_add_C hd]
        simpa only [Polynomial.C_neg, sub_neg_eq_add] using binary_double_block_weight hq (-(f.coeff 0))
      let G := Nat.card (GL (Fin 2) K)
      let R := Nat.card (PolyEvent (· = f^2) (Coord K 2))
      let a := Nat.card (powerEvent f (2*k+2) n)
      let b := Nat.card (powerEvent f (2*k) (n-2))
      let Q := Nat.card K ^ (2*n+2*(n-2))
      have hStep : a*3 ≤ 2*b*Q := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := GL (Fin 2) K))
        change a*3*G ≤ 2*b*Q*G
        calc
          _ = 3*(a*G) := by ring
          _ ≤ 3*(R*b*Q) := Nat.mul_le_mul_left _ hcount
          _ = (3*R)*(b*Q) := by ring
          _ ≤ (2*G)*(b*Q) := Nat.mul_le_mul_right _ hw
          _ = _ := by ring
      have hexp : (n-2)*(n-2) + (2*n+2*(n-2)) = n*n := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdn
        rw [Nat.add_sub_cancel_left]
        ring
      calc
        _ = (a*3)*3^k := by change a*3^(k+1) = _; rw [pow_succ']; ring
        _ ≤ (2*b*Q)*3^k := Nat.mul_le_mul_right _ hStep
        _ = 2*(b*3^k)*Q := by ring
        _ ≤ 2*(2^k * Nat.card K ^ ((n-2)*(n-2)))*Q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (ih (n-2)))
        _ = _ := by
          dsimp [Q]
          rw [pow_succ']
          calc
            _ = (2*2^k) * (Nat.card K ^ ((n-2)*(n-2)) * Nat.card K ^ (2*n+2*(n-2))) := by ring
            _ = _ := by rw [← pow_add, hexp]
    · haveI : IsEmpty (powerEvent f (2*k+2) n) := not_nonempty_iff.mp hn
      simp

/-- An even power gives geometric decay uniformly, including the binary linear exception. -/
theorem even_power_event_card_le (f : K[X]) (hf : f.Monic) (hi : Irreducible f) (k n : ℕ) :
    Nat.card (powerEvent f (2*k) n) * 3^k ≤ 2^k * Nat.card K ^ (n*n) := by
  let q := Nat.card K
  let d := f.natDegree
  have hq : 2 ≤ q := Finite.one_lt_card
  have hd : 1 ≤ d := hi.natDegree_pos
  by_cases hqd : 3 ≤ q^d
  · have ha : 2 ≤ q^d-1 := by omega
    have hs : 3 ≤ (q^d-1)^2 := by
      have hm := Nat.pow_le_pow_left ha 2
      omega
    have hp : 3^k ≤ (q^d-1)^(2*k) := by rw [pow_mul]; exact Nat.pow_le_pow_left hs k
    have h2k : 1 ≤ (2:ℕ)^k := Nat.one_le_pow k 2 (by decide)
    have hscale : Nat.card K ^ (n*n) ≤ 2^k * Nat.card K ^ (n*n) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (Nat.card K ^ (n*n)) h2k
    exact (Nat.mul_le_mul_left _ hp).trans ((power_event_card_le f hf hi (2*k) n).trans hscale)
  · have hd' : d = 1 := by
      by_contra hne
      have h2 : 2 ≤ d := by omega
      have h4 : 4 ≤ q^d := by
        calc
          4 = 2^2 := rfl
          _ ≤ q^2 := Nat.pow_le_pow_left hq _
          _ ≤ q^d := Nat.pow_le_pow_right (by omega) h2
      omega
    have hq' : q = 2 := by rw [hd', pow_one] at hqd; omega
    exact binary_power_event_card_le f hf hi hd' hq' k n

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.even_power_event_card_le
