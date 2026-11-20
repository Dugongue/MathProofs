import EvenP3RecipHighActual
import EvenP3RecipHighNumbers
import Mathlib.Data.Fin.Embedding

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)
open Mathproof.Problem17PolarAssembly (matAnti)

noncomputable section

private theorem pow_ratio_le {q : ℝ} (hq : 1 < q) {u v w : ℕ} (h : u+w ≤ v) :
    q^u / q^v ≤ 1 / q^w := by
  calc
    _ ≤ q^u / q^(u+w) := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hq.le h)
    _ = _ := by rw [pow_add]; field_simp

private theorem repeated_pow_ratio {q : ℝ} (hq : 1 < q) (u v s : ℕ) :
    ((q^u / q^(u+v)))^s = 1 / q^(s*v) := by
  have he : q^u/q^(u+v) = 1/q^v := by rw [pow_add]; field_simp
  rw [he, div_pow, one_pow, ← pow_mul, mul_comm v s]

variable {K H L J I B : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option J) (I := I) (B := B)
local notation "n" => (Fintype.card I)
local notation "q" => (Fintype.card K : ℝ)

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- All high Fourier labels of a square-cut reciprocal basis have physical
polar rank at least four times the square mode size, off one vanishing event. -/
theorem square_high_common_bad_mass_le [Nonempty Bases] [Fintype Bases]
    (hn : 10^19 ≤ n) (hB : Fintype.card B = n) (hJ : Fintype.card J = n - 1)
    (hH : n/2 ≤ Fintype.card H) (hL : n/2 ≤ Fintype.card L) :
    uniformFraction Bases (fun U => ∃ P : Matrix I I K,
      highCutoff n ≤ finrank K (matAnti P).range ∧ squareHighFullRank U P < 4*n^2) ≤
      16 / q^(highExponent n) := by
  let G := high_budgets n hn
  let S := {P : Matrix I I K // highCutoff n ≤ finrank K (matAnti P).range}
  letI : Fintype S := Fintype.ofFinite _
  let a := highDualSize n
  let c := highColumns n
  let g := highRows n
  let b := highPrimalSize
  let s := highBatches
  let a₀ := highBatchWidth n
  let d := highDefect n
  let h := highRowRank n
  let ρ := highRelationRank n
  let x := highExponent n
  let hi : Fin a ↪ H := (Fin.castLEEmb (G.dualEmbed.trans hH)).trans (Fintype.equivFin H).symm.toEmbedding
  let lo : Fin b ↪ L := (Fin.castLEEmb (G.primalEmbed.trans hL)).trans (Fintype.equivFin L).symm.toEmbedding
  let eA : (Fin s × Fin a₀) ≃ Fin a := Fintype.equivOfCardEq (by simp [a,s,a₀,highDualSize])
  let e : Fin c ⊕ Fin g ≃ J := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum,Fintype.card_fin,hJ] using G.groupCard)
  have htotal : Fintype.card (Fin a × J) + Fintype.card (Fin b) + 1 ≤ finrank K (Matrix I B K) := by
    simpa [Fintype.card_prod, hJ, hB, Module.finrank_matrix, pow_two, a, b] using G.conditionLaw
  have hρ : ∀ z : S, ρ + Fintype.card (Fin b) + 2*(n*d) ≤ finrank K (matAnti z.val).range := by
    intro z
    rw [Fintype.card_fin]
    exact G.relRank.trans z.property
  have hh : h + Fintype.card (Fin b) ≤ Fintype.card (Fin a₀) * Fintype.card (Fin b) := by
    simpa only [Fintype.card_fin] using G.rowRank
  have hτ : 4*n^2 ≤ finrank K (Fin c → (Fin s × Fin a₀) → Fin b → K) - n^2 := by
    have hp := G.physicalRank
    change 5*n^2 ≤ c*a*b at hp
    have he : finrank K (Fin c → (Fin s × Fin a₀) → Fin b → K) = c*a*b := by
      simp [Module.finrank_pi_fintype, Module.finrank_pi, Fintype.card_prod, nsmul_eq_mul, a,s,a₀,highDualSize] <;> ac_rfl
    rw [he]
    omega
  have hmodel := square_high_physical_bad_mass_le s g d h ρ (4*n^2) hi lo eA e
    (fun z : S => z.val) hB.ge htotal hρ hh hτ
  have himp (U : Bases) (hx : ∃ P : Matrix I I K,
      highCutoff n ≤ finrank K (matAnti P).range ∧ squareHighFullRank U P < 4*n^2) :
      ∃ z : S, squareHighFullRank U z.val < 4*n^2 := by
    obtain ⟨P,hp,hr⟩ := hx
    exact ⟨⟨P,hp⟩,hr⟩
  refine ((uniformFraction_le_of_imp himp).trans hmodel).trans ?_
  have hq : 1 < q := by exact_mod_cast (Fintype.one_lt_card (α := K))
  have hS : (Fintype.card S : ℝ) ≤ q^(n^2) := by
    have hle := Fintype.card_le_of_injective (Subtype.val : S → Matrix I I K) Subtype.val_injective
    change Fintype.card S ≤ Fintype.card (I → I → K) at hle
    rw [Fintype.card_fun, Fintype.card_fun, ← pow_mul, ← pow_two] at hle
    exact_mod_cast hle
  have hC : (Fintype.card (Fin c → Fin b → K) : ℝ) = q^(c*b) := by
    simp [Fintype.card_fun, ← pow_mul, Nat.mul_comm]
  have hY : (Nat.card (Fin c → (Fin s × Fin a₀) → Fin b → K) : ℝ) = q^(c*a*b) := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod, ← pow_mul,
      a,s,a₀,highDualSize] <;> ac_rfl
  rw [Fintype.card_prod, Nat.cast_mul, hC, hY, Fintype.card_fin, Fintype.card_fin]
  change 4 * (q^b * (2/q^d) + (((Fintype.card S : ℝ) * q^(c*b)) *
    ((q^(a₀*b) / q^(a₀*b+n^2/2000000))^s) + (Fintype.card S : ℝ) * (q^(c*a*b) / q^(g*h)))) ≤ 16 / q^x
  rw [repeated_pow_ratio hq]
  have h1 : q^b * (2/q^d) ≤ 2/q^x := by
    have hw := pow_ratio_le hq G.primalExponent
    calc
      _ = 2 * (q^b/q^d) := by simp only [div_eq_mul_inv]; ac_rfl
      _ ≤ 2 * (1/q^x) := mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = _ := by simp only [div_eq_mul_inv, one_mul]
  have h2 : ((Fintype.card S : ℝ) * q^(c*b)) * (1/q^(s*(n^2/2000000))) ≤ 1/q^x := by
    calc
      _ ≤ (q^(n^2)*q^(c*b)) * (1/q^(s*(n^2/2000000))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS (by positivity)) (by positivity)
      _ = q^(n^2+c*b) / q^(s*(n^2/2000000)) := by rw [pow_add]; ring
      _ ≤ _ := pow_ratio_le hq G.colExponent
  have h3 : (Fintype.card S : ℝ) * (q^(c*a*b) / q^(g*h)) ≤ 1/q^x := by
    calc
      _ ≤ q^(n^2) * (q^(c*a*b) / q^(g*h)) := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = q^(n^2+c*a*b) / q^(g*h) := by rw [pow_add]; ring
      _ ≤ _ := pow_ratio_le hq G.rowExponent
  calc
    _ ≤ 4 * (2/q^x + (1/q^x + 1/q^x)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 (add_le_add h2 h3)) (by norm_num)
    _ = _ := by ring

#print axioms square_high_common_bad_mass_le

end
end Mathproof.EvenTI.Reciprocal.Four