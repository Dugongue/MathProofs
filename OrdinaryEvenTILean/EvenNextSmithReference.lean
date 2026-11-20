import EvenNextSmithBanks
import EvenNextSmithLCM
import Mathlib.FieldTheory.Finite.Basic

/-! The exact reference-order and powered-RHS contract for the existing
three-slot Smith sweep, with a narrow axiom-audited dependency closure. -/
namespace EvenOrdinaryTI.LiveRows

open scoped BigOperators
open EvenOrdinaryTI.LCMProjection

variable {s t d : Nat}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ i, Field (X i)] [∀ j, Field (Y j)]
  [∀ i, Fintype (X i)] [∀ j, Fintype (Y j)]
  (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →+* Y j)

local instance variableFintype (v : Fin (VarCount s t d)) :
    Fintype (physicalVarField X Y v) := by
  unfold physicalVarField
  generalize (varIndex (s := s) (t := t) (d := d)).symm v = z
  rcases z with i | ⟨j, k⟩
  · exact inferInstanceAs (Fintype (X i))
  · exact inferInstanceAs (Fintype (Y j))

local instance equationFintype (r : Fin (RowCount t d)) :
    Fintype (physicalRowField Y r) := inferInstanceAs (Fintype (Y (rowIndex.symm r).1))

private def rowHom :
    (∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ) →*
      ∀ r : Fin (RowCount t d), (physicalRowField Y r)ˣ where
  toFun x r := physicalValue X Y orig emb x r
  map_one' := by
    funext r
    simp [physicalValue, EvenOrdinaryTI.CellPrefix.ternary]
  map_mul' x y := by
    funext r
    simp [physicalValue, EvenOrdinaryTI.CellPrefix.ternary, mul_inv_rev]
    ac_rfl

/-- The reference field list used by the old sweep, with variable fields
first and row fields second. -/
def prefixRefOrder : Fin (VarCount s t d) ⊕ Fin (RowCount t d) → Nat :=
  Sum.elim (fun v => Fintype.card (physicalVarField X Y v) - 1)
    (fun r => Fintype.card (physicalRowField Y r) - 1)

def prefixRefVariableOrder (i : Fin (VarCount s t d) ⊕ Fin (RowCount t d))
    (v : Fin (VarCount s t d)) : Nat :=
  Nat.gcd (Fintype.card (physicalVarField X Y v) - 1) (prefixRefOrder (d := d) X Y i)

def prefixRefRHS (c : ∀ j, (Y j)ˣ) (i : Fin (VarCount s t d) ⊕ Fin (RowCount t d))
    (r : Fin (RowCount t d)) : (physicalRowField Y r)ˣ :=
  physicalRHS Y c r ^ (commonOrder (prefixRefOrder (d := d) X Y) / prefixRefOrder (d := d) X Y i)

def PrefixReferenceSolvable (c : ∀ j, (Y j)ˣ)
    (i : Fin (VarCount s t d) ⊕ Fin (RowCount t d)) : Prop :=
  ∃ x : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ,
    (∀ v, x v ^ prefixRefVariableOrder X Y i v = 1) ∧
    ∀ r, physicalValue X Y orig emb x r = prefixRefRHS X Y c i r

/-- The existing sweep's reference-by-reference predicates are sufficient
for exact feasibility of the original arbitrary-arity rows. -/
theorem prefixReferenceSolvable_iff (c : ∀ j, (Y j)ˣ) :
    (∀ i, PrefixReferenceSolvable X Y orig emb c i) ↔
      ∃ x : ∀ i, (X i)ˣ, ∀ j,
        (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j := by
  classical
  let m := prefixRefOrder (d := d) X Y
  let y := physicalRHS (d := d) Y c
  have hm (i) : 0 < m i := by
    cases i with
    | inl v => exact Nat.sub_pos_of_lt (Fintype.one_lt_card (α := physicalVarField X Y v))
    | inr r => exact Nat.sub_pos_of_lt (Fintype.one_lt_card (α := physicalRowField Y r))
  have hLocal (v : Fin (VarCount s t d)) (u : (physicalVarField X Y v)ˣ) :
      u ^ m (.inl v) = 1 := by
    simpa only [m, prefixRefOrder, Sum.elim_inl, Fintype.card_units] using
      (pow_card_eq_one : u ^ Fintype.card (physicalVarField X Y v)ˣ = 1)
  have hDomain (a : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ) :
      a ^ commonOrder m = 1 := by
    funext v
    obtain ⟨b, hb⟩ := order_dvd_common m (.inl v)
    change a v ^ commonOrder m = 1
    rw [hb, pow_mul, hLocal, one_pow]
  have hTarget : y ^ commonOrder m = 1 := by
    funext r
    obtain ⟨b, hb⟩ := order_dvd_common m (.inr r)
    have hLocalR : y r ^ m (.inr r) = 1 := by
      simpa only [m, prefixRefOrder, Sum.elim_inr, Fintype.card_units] using
        (pow_card_eq_one : y r ^ Fintype.card (physicalRowField Y r)ˣ = 1)
    change y r ^ commonOrder m = 1
    rw [hb, pow_mul, hLocalR, one_pow]
  have hGcd (i) (x : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ) :
      x ^ m i = 1 ↔ ∀ v, x v ^ prefixRefVariableOrder X Y i v = 1 := by
    constructor
    · intro h v
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hLocal v (x v)))
        (orderOf_dvd_of_pow_eq_one (congrFun h v))
    · intro h
      funext v
      change x v ^ m i = 1
      exact orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_pow_eq_one (h v)).trans (Nat.gcd_dvd_right _ _))
  have h := lcm_projection_iff (rowHom X Y orig emb) m hm y hDomain hTarget
  have he : (∃ a, ∀ r, physicalValue X Y orig emb a r = physicalRHS Y c r) ↔
      ∀ i, PrefixReferenceSolvable X Y orig emb c i := by
    simpa only [rowHom, MonoidHom.coe_mk, OneHom.coe_mk, funext_iff, Pi.pow_apply,
      hGcd, m, y, PrefixReferenceSolvable, prefixRefRHS] using h
  exact he.symm.trans (physical_solves_iff X Y orig emb c)

/-- Connect the bit emitted by the reference sweep to the original cells. -/
theorem prefixSweepBit_iff (c : ∀ j, (Y j)ˣ)
    (result : Fin (VarCount s t d + RowCount t d) → Prop) (bit : Nat)
    (hbit : bit = 1 ↔ ∀ i, result i)
    (href : ∀ i : Fin (VarCount s t d) ⊕ Fin (RowCount t d),
      result (finSumFinEquiv i) ↔ PrefixReferenceSolvable X Y orig emb c i) :
    bit = 1 ↔ ∃ x : ∀ i, (X i)ˣ, ∀ j,
      (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j := by
  refine hbit.trans (?_ : (∀ i, result i) ↔ _)
  refine (show (∀ i, result i) ↔ ∀ i, PrefixReferenceSolvable X Y orig emb c i from ?_).trans
    (prefixReferenceSolvable_iff X Y orig emb c)
  exact ⟨fun h i => (href i).mp (h _), fun h i => by
    simpa only [Equiv.apply_symm_apply] using
      (href (finSumFinEquiv.symm i)).mpr (h (finSumFinEquiv.symm i))⟩

#print axioms prefixReferenceSolvable_iff
#print axioms prefixSweepBit_iff

end EvenOrdinaryTI.LiveRows
