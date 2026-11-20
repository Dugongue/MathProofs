import EvenP6SignedPrefix
import EvenP6DenseBounds
import EvenNextSmithReference
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenOrdinaryTI.LiveRows EvenOrdinaryTI.LCMProjection

variable {s t d : ℕ}

/-- The degree schedule follows the exact address order of the signed prefix. -/
def signedVarDegrees (shared : Fin s → ℕ) : Fin (s * 2 + 1) → ℕ :=
  fun i => ((signedVariableOrder s) i).elim 1 (fun v => shared v.1)

def signedCellDegrees (cell : Fin t → ℕ) (shared : Fin s → ℕ) :
    Fin (t + s + 1) → ℕ :=
  fun i => ((signedCellOrder t s) i).elim 1 (Sum.elim cell shared)

def prefixVarDegrees (dv : Fin s → ℕ) (dc : Fin t → ℕ) :
    Fin (VarCount s t d) → ℕ :=
  fun v => (varIndex.symm v).elim dv (fun j => dc j.1)

def prefixRowDegrees (dc : Fin t → ℕ) : Fin (RowCount t d) → ℕ :=
  fun r => dc (rowIndex.symm r).1

/-- Orders are produced from the stored dimensions. No enumeration of the
elements of the extension fields is used to compute these words. -/
def numericalRefOrders (q : ℕ) (dv : Fin s → ℕ) (dc : Fin t → ℕ) :
    Fin (VarCount s t d) ⊕ Fin (RowCount t d) → ℕ :=
  fun i => q ^ (i.elim (prefixVarDegrees dv dc) (prefixRowDegrees dc)) - 1

def numericalReferenceVariables (q : ℕ) (dv : Fin s → ℕ) (dc : Fin t → ℕ)
    (i : Fin (VarCount s t d) ⊕ Fin (RowCount t d))
    (v : Fin (VarCount s t d)) : ℕ :=
  Nat.gcd (q ^ prefixVarDegrees dv dc v - 1) (numericalRefOrders q dv dc i)

/-- The exact word identities for the existing reference-verdict proof. -/
theorem numericalRefOrders_eq (q : ℕ) (dv : Fin s → ℕ) (dc : Fin t → ℕ)
    (X : Fin s → Type) (Y : Fin t → Type)
    [∀ i, Field (X i)] [∀ j, Field (Y j)] [∀ i, Fintype (X i)] [∀ j, Fintype (Y j)]
    (hx : ∀ i, Fintype.card (X i) = q ^ dv i)
    (hy : ∀ j, Fintype.card (Y j) = q ^ dc j) :
    numericalRefOrders (d := d) q dv dc = prefixRefOrder (d := d) X Y := by
  funext i
  rcases i with v | r
  · have h : Nat.card (physicalVarField X Y v) = q ^ prefixVarDegrees (d := d) dv dc v := by
      unfold physicalVarField prefixVarDegrees
      generalize varIndex.symm v = z
      rcases z with a | ⟨j, k⟩
      · simpa only [varField, Sum.elim_inl, Nat.card_eq_fintype_card] using hx a
      · simpa only [varField, Sum.elim_inr, Nat.card_eq_fintype_card] using hy j
    unfold numericalRefOrders prefixRefOrder
    simp only [Sum.elim_inl]
    have hc {A : Type} (f : Fintype A) : @Fintype.card A f = Nat.card A :=
      (@Nat.card_eq_fintype_card A f).symm
    simp only [hc, h]
  · exact congrArg (· - 1) (hy (rowIndex.symm r).1).symm

theorem numericalRefOrder_bounds (q bits N : ℕ) (dv : Fin s → ℕ) (dc : Fin t → ℕ)
    (hq : 2 ≤ q) (hb : q ≤ 2 ^ bits)
    (hv : ∀ v, 0 < dv v ∧ dv v ≤ N)
    (hc : ∀ j, 0 < dc j ∧ dc j ≤ N)
    (i : Fin (VarCount s t d) ⊕ Fin (RowCount t d)) :
    0 < numericalRefOrders q dv dc i ∧ numericalRefOrders q dv dc i < 2 ^ (bits * N) := by
  have hd : 0 < (i.elim (prefixVarDegrees dv dc) (prefixRowDegrees dc)) ∧
      (i.elim (prefixVarDegrees dv dc) (prefixRowDegrees dc)) ≤ N := by
    rcases i with v | r
    · change 0 < prefixVarDegrees (d := d) dv dc v ∧ prefixVarDegrees (d := d) dv dc v ≤ N
      unfold prefixVarDegrees
      cases varIndex.symm v with
      | inl a => exact hv a
      | inr a => exact hc a.1
    · exact hc (rowIndex.symm r).1
  unfold numericalRefOrders
  have hq' : 1 < q ^ (i.elim (prefixVarDegrees dv dc) (prefixRowDegrees dc)) :=
    one_lt_pow₀ (by omega) (Nat.ne_of_gt hd.1)
  exact ⟨by omega, orderWord_bound q _ bits N (by omega) hb hd.2⟩

/-- The LCM can be big as a value but has polynomial bit length in the
number and maximum degree of the stored fields. -/
theorem commonOrder_bit_bound {I : Type} [Fintype I] (m : I → ℕ) (bits : ℕ)
    (hm : ∀ i, 0 < m i ∧ m i ≤ 2 ^ bits) :
    commonOrder m < 2 ^ (bits * Fintype.card I + 1) := by
  have hd : commonOrder m ∣ ∏ i, m i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem m hi
  have hp : 0 < ∏ i, m i := Finset.prod_pos fun i _ => (hm i).1
  have hb : ∏ i, m i ≤ (2 ^ bits) ^ Fintype.card I := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod' (s := (Finset.univ : Finset I))
        (f := m) (g := fun _ => 2 ^ bits) (fun i _ => (hm i).2))
  rw [← pow_mul] at hb
  have hc := (Nat.le_of_dvd hp hd).trans hb
  rw [pow_succ]
  have hpos := Nat.two_pow_pos (bits * Fintype.card I)
  omega

#print axioms numericalRefOrders_eq
#print axioms numericalRefOrder_bounds
#print axioms commonOrder_bit_bound

end EvenTI.CellPreparation
