import EvenP12ComparePrepKernelLayout

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open Mathproof.P15DecideIMPKerBasis20261007 (KBLay)
open Lax51.BinaryWordEncoding (bitSize)
set_option autoImplicit false

noncomputable def Address.rangePoly : Address → Polynomial Nat
  | .side => Polynomial.X
  | .litSucc k => Polynomial.C (k+1)
  | .add a b => a.rangePoly + b.rangePoly
  | .mul a b => a.rangePoly * b.rangePoly

theorem Address.evaluate_rangePoly (a : Address) (m : Nat) :
    a.rangePoly.eval m = a.value m := by
  induction a <;> simp [Address.rangePoly,Address.value, *]

theorem Address.monotone_value (a : Address) : Monotone (fun m => a.value m) := by
  intro m m' hm
  induction a with
  | side => exact hm
  | litSucc k => rfl
  | add a b ha hb => exact Nat.add_le_add ha hb
  | mul a b ha hb => exact Nat.mul_le_mul ha hb

theorem outputBanks_disjoint (m : Nat) {i j : Fin 4} (h : i < j) :
    (outputBase i).value m + m*m ≤ (outputBase j).value m := by
  rw [outputBase_value,outputBase_value]
  have hh := Nat.mul_le_mul_right (m*m) (show i.val+1 ≤ j.val from h)
  rw [Nat.succ_mul] at hh
  omega

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem decodedHalfSide_le (F : FieldEncoding K) (w : List Nat) {p : ParsedPair K}
    (h : decodePair F w = some p) : p.n^(p.d/2) ≤ w.length := by
  obtain ⟨rest,hHead,hLen,_,_,hN⟩ := decodePair_some h
  have hL := congrArg List.length hHead
  simp only [List.length_cons,hLen] at hL
  exact (Nat.pow_le_pow_right (by omega) (Nat.div_le_self ..)).trans (by omega)

theorem fourBanks_slots_poly (F : FieldEncoding K) (w : List Nat) {p : ParsedPair K}
    (h : decodePair F w = some p) :
    pairCutSlotCount.value (p.n^(p.d/2)) ≤ pairCutSlotCount.rangePoly.eval (bitSize w) := by
  rw [Address.evaluate_rangePoly]
  exact Address.monotone_value _ ((decodedHalfSide_le F w h).trans
    (Lax51Proofs.Encoding.length_le_bitSize w))

theorem kernelBindings_le (m : Nat) (target : Bool) (idx : Fin 4) (hm : 0 < m) :
    ∀ r ∈ kernelBindings target idx, r.2.value m ≤ pairCutSlotCount.value m := by
  have hB := concreteKernelLayout m idx hm (B := pairCutSlotCount.value m + m + m + 11)
    (by omega)
  have hA : m*m ≤ augmentedMatrixBase.value m := by simp [augmentedMatrixBase,Address.value,cutArea]
  have hRB : rawMatrixBase.value m ≤ augmentedMatrixBase.value m := by simp [augmentedMatrixBase,Address.value]
  have hmB : m ≤ m*m := by have := Nat.le_mul_self m; omega
  have hOut := hB.am_out
  have hZ := hB.out_z
  have hSn := hB.z_s
  intro r hr
  simp only [kernelBindings,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;>
    simp [Address.value,cutArea,inputOffset] <;> try omega
  cases target <;> simp [Address.value] <;> omega

theorem decodedOrder_eq_twice_half (F : FieldEncoding K) (w : List Nat) {p : ParsedPair K}
    (h : decodePair F w = some p) : p.d = p.d/2 + p.d/2 := by
  obtain ⟨_,_,_,_,he,_⟩ := decodePair_some h
  have hh := Nat.mod_add_div p.d 2
  rw [he] at hh
  omega

theorem decodedSide_square_eq_oneTensor (F : FieldEncoding K) (w : List Nat) {p : ParsedPair K}
    (h : decodePair F w = some p) : p.n^(p.d/2)*p.n^(p.d/2) = (w.length-2)/2 := by
  obtain ⟨rest,hw,hlen,_,_,_⟩ := decodePair_some h
  rw [← pow_add,← decodedOrder_eq_twice_half F w h]
  have hh := congrArg List.length hw
  simp only [List.length_cons,hlen] at hh
  omega

#print axioms fourBanks_slots_poly
#print axioms kernelBindings_le
end EvenTI.P12ComparePrep
