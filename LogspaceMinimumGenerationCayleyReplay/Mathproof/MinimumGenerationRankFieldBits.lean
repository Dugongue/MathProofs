import Mathproof.MinimumGenerationRankCoefficientBits
import Mathproof.MinimumGenerationRankExtensionArithmetic
import Mathproof.MinimumGenerationRankExtensionBits
import Mathlib.Data.Fintype.BigOperators

namespace Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic

open Formula Module

private theorem subtractModBit_zmod {p width index : Nat} [NeZero p]
    (h : p ≤ 2^width) (x y : ZMod p) :
    PrimeWord.subtractModBit width p.testBit x.val.testBit y.val.testBit index =
      (x-y).val.testBit index := by
  rw [PrimeWord.subtractModBit_eq h x.val_lt y.val_lt.le]
  have he : ((↑(x.val + (p-y.val)) : ZMod p)) = x-y := by
    rw [Nat.cast_add, Nat.cast_sub y.val_lt.le, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    simp [sub_eq_add_neg]
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast] at hv
  rw [hv]

variable {R : Type*} [Field R] {p d : Nat} [Fact p.Prime] [Algebra (ZMod p) R]

noncomputable def reprBits (basis : Basis (Fin d) (ZMod p) R) (x : R) (a : Fin d × Nat) : Bool :=
  (basis.repr x a.1).val.testBit a.2

private def pair (d : Nat) : Fin (d*d) ≃ Fin d × Fin d :=
  finProdFinEquiv.symm

/-- The coefficient evaluator's arithmetic over a finite field in a supplied
basis. The table and unit bits may be supplied by independently prepared
polynomial-basis data. -/
noncomputable def basisBitOperations (basis : Basis (Fin d) (ZMod p) R) (width : Nat) (hWidth : p ≤ 2^width)
    (unitWord : Fin d × Nat → Bool) (hUnit : unitWord = reprBits basis 1)
    (table : Fin d → Fin d → Fin d → Nat → Bool)
    (hTable : ∀ i j k, table i j k = (basis.repr (basis i * basis j) k).val.testBit) :
    BitOperations R (Fin d × Nat) where
  encode := reprBits basis
  zero := fun _ => false
  one := unitWord
  add := fun x y a => PrimeWord.addModBit width p.testBit
    (fun b => x (a.1,b)) (fun b => y (a.1,b)) a.2
  sub := fun x y a => PrimeWord.subtractModBit width p.testBit
    (fun b => x (a.1,b)) (fun b => y (a.1,b)) a.2
  mul := fun x y a =>
    multiplyCoordinateBit (d*d) width p.testBit
      (2^numeratorWidth (d*d) width / p).testBit
      (fun i b => x ((pair d i).1,b)) (fun i b => y ((pair d i).2,b))
      (fun i => table (pair d i).1 (pair d i).2 a.1) a.2
  zero_exact := by funext a; simp [reprBits]
  one_exact := hUnit
  add_exact := by
    intro x y
    funext a
    simp only [reprBits, map_add, Finsupp.add_apply]
    exact PrimeWord.addModBit_zmod hWidth _ _
  sub_exact := by
    intro x y
    funext a
    simp only [reprBits, map_sub, Finsupp.sub_apply]
    exact subtractModBit_zmod hWidth _ _
  mul_exact := by
    intro x y
    funext a
    simp only [reprBits,hTable]
    rw [multiplyCoordinateBit_eq (Nat.pos_of_ne_zero (NeZero.ne p)) hWidth _ _ _
      (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _)]
    rw [product_digit_of_coordinate_words]
    have he := (pair d).sum_comp (fun ij : Fin d × Fin d =>
      (basis.repr x ij.1).val * (basis.repr y ij.2).val *
        (basis.repr (basis ij.1 * basis ij.2) a.1).val)
    rw [he, Fintype.sum_prod_type]

end Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic
