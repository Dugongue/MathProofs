import EvenP18RawLayout
import EvenP16AnchorWordClock

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep EvenTI.P12Compare
open EvenTI.P15Execution EvenTI.P16Execution EvenTI.P17Execution
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.BinaryWordEncoding Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def reciprocalExtraWord (F : FieldPresentation K) : ℕ :=
  F.e+1+15*(F.e+1)+16*(F.e+1)+(F.p+1)^2+(F.p+1)^(F.e+1)+Fintype.card K+8

noncomputable def rawReciprocalWordExponent (F : FieldPresentation K) : Polynomial ℕ :=
  anchorWordExponent F + C (reciprocalExtraWord F) * (X+1)^2

/-- The exact inverse's potentially large natural-number counters fit in
polynomial-length words even at the original input boundary. -/
theorem rawReciprocalWord_bounds (D : FieldEncoding K) (F : FieldPresentation K)
    {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n) (hl : 1 ≤ l) (hn : 2 ≤ n) :
    let w := comparisonInput D T U
    let L := bitSize w
    let m := n*n^l
    let B : ℕ := 2^((rawReciprocalWordExponent F).eval L+L+1)
    w.length < B ∧ (∀ x ∈ w, x<B) ∧ F.e+1+reciprocalRawSlots m*F.e<B ∧
    16*(F.e+1)<B ∧ (F.p+1)^2<B ∧ (F.p+1)^(F.e+1)<B ∧ reciprocalRawSlots m<B ∧
    Fintype.card K≤B ∧ 4<B ∧ (n^l)*(n^l)+1<B ∧
    Fintype.card K^(m*m+m+2)<B ∧ 1+((l+1)+(l+1))*(n*n+2)<B := by
  dsimp only
  let w := comparisonInput D T U
  let L := bitSize w
  let m := n*n^l
  let d := (l+1)+(l+1)
  let E := reciprocalExtraWord F
  let q := Fintype.card K
  let b := (rawReciprocalWordExponent F).eval L+L+1
  have hEval : b=(anchorWordExponent F).eval L+E*((L+1)*(L+1))+L+1 := by
    simp [b,rawReciprocalWordExponent,E,pow_two]
  have hAnchor : 2^((anchorWordExponent F).eval L+L+1) ≤ 2^b :=
    Nat.pow_le_pow_right (by decide) (by rw [hEval]; omega)
  obtain ⟨_,hInv,hFour,hCard,_,_,hA⟩ := anchorWordExponent_bounds D F T U hn
  have hLn : w.length ≤ L := Lax51Proofs.Encoding.length_le_bitSize w
  have hRaw : w.length=2+n^d+n^d := by
    simp [w,d,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
  have hD : d ≤ L := ((Nat.lt_two_pow_self (n:=d)).le.trans (Nat.pow_le_pow_left hn _)).trans (by omega)
  have hDim := cutInput_side_bounds D T U (show 1 ≤ l+1 by omega) hn
  have hm : m ≤ L := by simpa only [m,pow_succ'] using hDim.2.1
  have hNS : n*n ≤ m := by
    rw [show m=n^(l+1) by rw [pow_succ'],←pow_two]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hN : n ≤ L := (Nat.le_mul_self n).trans (hNS.trans hm)
  have hZ : 1 ≤ (L+1)*(L+1) := Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos L))
  have hMeta : E < b := by
    have := Nat.mul_le_mul_left E hZ
    rw [Nat.mul_one] at this
    omega
  have hB : b < 2^b := Nat.lt_two_pow_self
  have hSq : m*m ≤ (L+1)*(L+1) := Nat.mul_le_mul (by omega) (by omega)
  have hSlot : reciprocalRawSlots m ≤ 15*((L+1)*(L+1)) := by
    unfold reciprocalRawSlots
    omega
  have hMem : F.e+1+reciprocalRawSlots m*F.e < b := by
    have h₁ : reciprocalRawSlots m*F.e ≤ (15*F.e)*((L+1)*(L+1)) := by
      calc
        _ ≤ (15*((L+1)*(L+1)))*F.e := Nat.mul_le_mul_right _ hSlot
        _ = _ := by ring
    have h₂ : (15*F.e+(F.e+1))*((L+1)*(L+1)) ≤ E*((L+1)*(L+1)) := by
      apply Nat.mul_le_mul_right
      unfold E reciprocalExtraWord
      omega
    have h₃ := Nat.mul_le_mul_left (F.e+1) hZ
    rw [Nat.mul_one] at h₃
    rw [Nat.add_mul] at h₂
    omega
  have hSlotB : reciprocalRawSlots m < b := by
    have h₁ : 15*((L+1)*(L+1)) ≤ E*((L+1)*(L+1)) := by
      apply Nat.mul_le_mul_right
      unfold E reciprocalExtraWord
      omega
    omega
  have hFrame : 1+d*(n*n+2) < b := by
    have h₁ := Nat.mul_le_mul hD (Nat.add_le_add_right (hNS.trans hm) 2)
    have h₂ : 1+L*(L+2) = (L+1)*(L+1) := by ring
    have h₃ : (L+1)*(L+1) ≤ E*((L+1)*(L+1)) := by
      simpa using Nat.mul_le_mul_right ((L+1)*(L+1)) (show 1≤E by unfold E reciprocalExtraWord; omega)
    omega
  have hField (V : Tensor K ((l+1)+(l+1)) n) (x : ℕ) (hx : x ∈ tensorWords D V) : x<2^b := by
    rw [tensorWords_eq_inputCoordOrder] at hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (D _).isLt.trans_le (hCard.trans hAnchor)
  have hWords : ∀ x ∈ w, x<2^b := by
    intro x hx
    simp only [w,comparisonInput,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hx
    rcases hx with rfl|rfl|ht|hu
    · omega
    · omega
    · exact hField T x ht
    · exact hField U x hu
  have hFixed := hMeta.trans hB
  change w.length<2^b ∧ (∀ x ∈ w, x<2^b) ∧ _ ∧ _ 
  refine ⟨by omega,hWords,hMem.trans hB,?_,?_,?_,hSlotB.trans hB,
    hCard.trans hAnchor,hFour.trans_le hAnchor,hA.trans_le hAnchor,hInv.trans_le hAnchor,hFrame.trans hB⟩ <;>
    change _ < 2^b <;> unfold E reciprocalExtraWord at hFixed <;> omega

#print axioms rawReciprocalWord_bounds
end EvenTI.P18Execution



