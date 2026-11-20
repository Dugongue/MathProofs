import EvenNextSmithBanks
import Mathlib.Data.Matrix.Basic

/-! The literal flattened input of the existing Smith controller after the
source, gauge and order banks have been installed. The two numeric routines
are the `signedTerm` and `transferWord` expressions from Problem 1.7, with
their arguments specialized to the checked even-order layout. -/
namespace EvenOrdinaryTI.LiveRows

open scoped BigOperators

variable {s t d : Nat}

/-- The sign convention of the physical three-slot packer. -/
def smithSign (e : Fin 3) : ℤ := if e.val = 0 then 1 else -1

def smithTerm (M : Nat) (src weights : Nat → Nat) (r c e : Nat) : Nat :=
  if src (3*r+e) = c then (if e = 0 then weights (3*r+e) else M-weights (3*r+e)) else 0

def smithEntry (M J V : Nat) (src weights orders : Nat → Nat) (a : Nat) : Nat :=
  let r := a/V
  let c := a%V
  if r < J then (smithTerm M src weights r c 0 +
    smithTerm M src weights r c 1 + smithTerm M src weights r c 2) % M
  else (if r-J = c then orders c else 0) % M

def SmithMatrixWords (M : Nat) (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat) (orders : Fin (VarCount s t d) → Nat) :
    List Nat :=
  List.ofFn fun a : Fin ((RowCount t d + VarCount s t d) * VarCount s t d) =>
    smithEntry M (RowCount t d) (VarCount s t d) (sourceWord orig)
      (boundedWord (gaugeWord M gauge)) (boundedWord orders) a.val

theorem smithMatrixWord_mem (M : Nat) (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat) (orders : Fin (VarCount s t d) → Nat)
    {a : Nat} (ha : a < (RowCount t d + VarCount s t d) * VarCount s t d) :
    a < (SmithMatrixWords M orig gauge orders).length ∧
      (SmithMatrixWords M orig gauge orders).getD a 0 =
        smithEntry M (RowCount t d) (VarCount s t d) (sourceWord orig)
          (boundedWord (gaugeWord M gauge)) (boundedWord orders) a := by
  have h := ofFn_boundedWord_ok (fun i : Fin ((RowCount t d + VarCount s t d) * VarCount s t d) =>
    smithEntry M (RowCount t d) (VarCount s t d) (sourceWord orig)
      (boundedWord (gaugeWord M gauge)) (boundedWord orders) i.val) ha
  simpa [SmithMatrixWords, boundedWord, ha] using h

def SmithMatrix (M : Nat) (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat) (orders : Fin (VarCount s t d) → Nat) :
    Matrix (Fin (RowCount t d + VarCount s t d)) (Fin (VarCount s t d)) (ZMod M) :=
  Fin.addCases
    (fun r c => ∑ e : Fin 3, if physicalSrc orig r e = c then
      smithSign e * (gauge r e : ℤ) else (0 : ℤ))
    (fun v c => (if v = c then orders c else 0 : Nat))

private theorem smithTerm_at_slot (M : Nat) (hM : 0 < M) (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat) (r : Fin (RowCount t d))
    (e : Fin 3) (c : Fin (VarCount s t d)) :
    (smithTerm M (sourceWord orig) (boundedWord (gaugeWord M gauge)) r.val c.val e.val : ZMod M) =
      ((if physicalSrc orig r e = c then smithSign e * (gauge r e : ℤ) else 0) : ZMod M) := by
  have hsrc : sourceWord orig (3 * r.val + e.val) = c.val ↔ physicalSrc orig r e = c := by
    rw [sourceWord_correct]
    exact ⟨Fin.ext, fun h => congrArg Fin.val h⟩
  by_cases h : physicalSrc orig r e = c
  · rw [smithTerm, if_pos (hsrc.mpr h), if_pos h, gaugeWord_at_slot]
    by_cases h0 : e.val = 0
    · simp [h0, smithSign, ZMod.natCast_mod]
    · rw [if_neg h0, Nat.cast_sub (Nat.mod_lt _ hM).le, ZMod.natCast_self, zero_sub, ZMod.natCast_mod]
      simp [smithSign, h0]
  · rw [smithTerm, if_neg (mt hsrc.mp h), if_neg h]
    simp

/-- Decoding the flat array yields the signed incidence matrix with its
variable-order rows, even when a row repeats a variable in several slots. -/
theorem smithMatrixWords_decode (M : Nat) (hM : 0 < M) (orig : Fin t → Fin d → Fin s)
    (gauge : Fin (RowCount t d) → Fin 3 → Nat) (orders : Fin (VarCount s t d) → Nat)
    (r : Fin (RowCount t d + VarCount s t d)) (c : Fin (VarCount s t d)) :
    ((SmithMatrixWords M orig gauge orders).getD (r.val * VarCount s t d + c.val) 0 : ZMod M) =
      SmithMatrix M orig gauge orders r c := by
  have hV : 0 < VarCount s t d := Nat.zero_lt_of_lt c.isLt
  have hpos : r.val * VarCount s t d + c.val < (RowCount t d + VarCount s t d) * VarCount s t d := by
    calc
      _ < r.val * VarCount s t d + VarCount s t d := Nat.add_lt_add_left c.isLt _
      _ = (r.val + 1) * VarCount s t d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ r.isLt
  rw [(smithMatrixWord_mem M orig gauge orders hpos).2]
  have hdiv : (r.val*VarCount s t d+c.val)/VarCount s t d = r.val := by
    rw [Nat.mul_comm r.val, Nat.add_comm, Nat.add_mul_div_left _ _ hV,
      Nat.div_eq_of_lt c.isLt, Nat.zero_add]
  have hmod : (r.val*VarCount s t d+c.val)%VarCount s t d = c.val := by
    rw [Nat.mul_comm r.val, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
  unfold smithEntry
  rw [hdiv, hmod]
  refine Fin.addCases ?_ ?_ r
  · intro j
    simp only [Fin.val_castAdd, if_pos j.isLt, ZMod.natCast_mod, Nat.cast_add,
      SmithMatrix, Fin.addCases_left, Fin.sum_univ_three, Int.cast_add]
    have h0 := smithTerm_at_slot M hM orig gauge j 0 c
    have h1 := smithTerm_at_slot M hM orig gauge j 1 c
    have h2 := smithTerm_at_slot M hM orig gauge j 2 c
    simpa using congrArg₂ (fun x y : ZMod M => x+y) (congrArg₂ (fun x y : ZMod M => x+y) h0 h1) h2
  · intro j
    have hj : ¬ RowCount t d + j.val < RowCount t d := by omega
    simp only [Fin.val_natAdd, if_neg hj, Nat.add_sub_cancel_left, ZMod.natCast_mod,
      SmithMatrix, Fin.addCases_right]
    rw [boundedWord_ok]
    by_cases h : j = c
    · subst j; simp
    · have hv : j.val ≠ c.val := fun e => h (Fin.ext e)
      simp [hv, h]

#print axioms smithMatrixWord_mem
#print axioms smithMatrixWords_decode

end EvenOrdinaryTI.LiveRows
