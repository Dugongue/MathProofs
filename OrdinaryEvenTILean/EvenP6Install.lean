import EvenNextSmithBanks
import Mathlib.Tactic.Linarith

namespace EvenTI.CellPreparation

open EvenOrdinaryTI.LiveRows

variable {s t d : ℕ}

structure PrefixBanks where
  source : List ℕ
  gauge : List ℕ
  orders : List ℕ

/-- Install the three numerical input banks of the checked prefix packer.
Every mode-and-block ID already in the live data is carried through exactly. -/
def installPrefixBanks (orig : Fin t → Fin d → Fin s)
    (twist : Fin t → Fin d → ℕ) (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ) :
    PrefixBanks :=
  ⟨SmithSourceBank orig, SmithGaugeBank modulus (extendSmithGauge twist), SmithOrderBank order⟩

theorem installPrefixBanks_lengths (orig : Fin t → Fin d → Fin s)
    (twist : Fin t → Fin d → ℕ) (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ) :
    let B := installPrefixBanks orig twist order modulus
    B.source.length = 3 * RowCount t d ∧
    B.gauge.length = 3 * RowCount t d ∧ B.orders.length = VarCount s t d := by
  simp [installPrefixBanks, SmithSourceBank, SmithGaugeBank, SmithOrderBank, Nat.mul_comm]

theorem installPrefixBanks_source (orig : Fin t → Fin d → Fin s)
    (twist : Fin t → Fin d → ℕ) (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    (installPrefixBanks orig twist order modulus).source.getD (3 * r.val + e.val) 0 =
      (physicalSrc orig r e).val := by
  have ha : 3 * r.val + e.val < 3 * RowCount t d := by
    simpa only [slotIndex_val r e, Nat.mul_comm 3] using (slotIndex r e).isLt
  change (SmithSourceBank orig).getD (3 * r.val + e.val) 0 = _
  rw [(sourceBank_mem orig ha).2.1, sourceWord_correct]

theorem installPrefixBanks_shared (orig : Fin t → Fin d → Fin s)
    (twist : Fin t → Fin d → ℕ) (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ)
    (j k : Fin t) (i u : Fin d)
    (h : orig j i = orig k u) :
    let B := installPrefixBanks orig twist order modulus
    B.source.getD (3 * (rowIndex (j, Sum.inl i)).val + 2) 0 =
      B.source.getD (3 * (rowIndex (k, Sum.inl u)).val + 2) 0 := by
  change (installPrefixBanks orig twist order modulus).source.getD
      (3 * (rowIndex (j, Sum.inl i)).val + (2 : Fin 3).val) 0 =
    (installPrefixBanks orig twist order modulus).source.getD
      (3 * (rowIndex (k, Sum.inl u)).val + (2 : Fin 3).val) 0
  rw [installPrefixBanks_source orig twist order modulus (rowIndex (j, Sum.inl i)) (2 : Fin 3),
    installPrefixBanks_source orig twist order modulus (rowIndex (k, Sum.inl u)) (2 : Fin 3)]
  simp [physicalSrc, src, h]

theorem installPrefixBanks_polynomial (orig : Fin t → Fin d → Fin s)
    (twist : Fin t → Fin d → ℕ) (order : Fin (VarCount s t d) → ℕ) (modulus N : ℕ)
    (hs : s ≤ N) (ht : t ≤ N) (hd : d ≤ N) :
    let B := installPrefixBanks orig twist order modulus
    B.source.length + B.gauge.length + B.orders.length ≤ 14 * (N + 1) ^ 2 := by
  let B := installPrefixBanks orig twist order modulus
  obtain ⟨hsrc, hgauge, horder⟩ := installPrefixBanks_lengths orig twist order modulus
  change B.source.length + B.gauge.length + B.orders.length ≤ _
  rw [hsrc, hgauge, horder]
  have hr : RowCount t d ≤ N * (N + 2) := Nat.mul_le_mul ht (Nat.add_le_add_right hd 2)
  have hv : VarCount s t d ≤ N + N * (N + 1) :=
    Nat.add_le_add hs (Nat.mul_le_mul ht (Nat.add_le_add_right hd 1))
  nlinarith

#print axioms installPrefixBanks_lengths
#print axioms installPrefixBanks_source
#print axioms installPrefixBanks_shared
#print axioms installPrefixBanks_polynomial

end EvenTI.CellPreparation
