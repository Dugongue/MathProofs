import EvenLiveRowAddress
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Init.Data.List.OfFn

/-! The ambient finite-field incidence and order banks for the three-slot
Smith packer. The addressing agrees with the `source3`, `gaugeWords`, and
`orderWords` ports of the checked Problem 1.7 command. -/
namespace EvenOrdinaryTI.LiveRows

open scoped BigOperators

variable {s t d : Nat}

/-- An arbitrary natural-word view of a bounded table, as expected by the
physical memory invariant. -/
def boundedWord {n : Nat} (a : Fin n → Nat) (i : Nat) : Nat :=
  if h : i < n then a ⟨i, h⟩ else 0

theorem boundedWord_ok {n : Nat} (a : Fin n → Nat) (i : Fin n) :
    boundedWord a i.val = a i := by
  simp [boundedWord, i.isLt]

theorem ofFn_boundedWord_ok {n : Nat} (a : Fin n → Nat) {i : Nat} (hi : i < n) :
    i < (List.ofFn a).length ∧ (List.ofFn a).getD i 0 = boundedWord a i := by
  have hLen : i < (List.ofFn a).length := by simpa using hi
  exact ⟨hLen, by rw [List.getD_eq_getElem _ _ hLen, List.getElem_ofFn]; simp [boundedWord, hi]⟩

def gaugeWord (M : Nat) (k : Fin (RowCount t d) → Fin 3 → Nat) :
    Fin (RowCount t d * 3) → Nat :=
  fun i => let ij := (finProdFinEquiv (m := RowCount t d) (n := 3)).symm i
           k ij.1 ij.2 % M

/-- All slots are present, including repeated variables and identity maps. -/
def SmithSourceBank (orig : Fin t → Fin d → Fin s) : List Nat :=
  List.ofFn fun i : Fin (RowCount t d * 3) => sourceWord orig i.val

def SmithGaugeBank (M : Nat) (k : Fin (RowCount t d) → Fin 3 → Nat) : List Nat :=
  List.ofFn (gaugeWord M k)

def SmithOrderBank {v : Nat} (n : Fin v → Nat) : List Nat :=
  List.ofFn n

theorem sourceBank_mem (orig : Fin t → Fin d → Fin s) {a : Nat}
    (ha : a < 3 * RowCount t d) :
    a < (SmithSourceBank orig).length ∧
      (SmithSourceBank orig).getD a 0 = sourceWord orig a ∧
      sourceWord orig a < VarCount s t d := by
  have h' : a < RowCount t d * 3 := by simpa [Nat.mul_comm 3] using ha
  have hL : a < (SmithSourceBank orig).length := by simpa [SmithSourceBank] using h'
  exact ⟨hL, by rw [List.getD_eq_getElem _ _ hL]; simp [SmithSourceBank],
    by simp [sourceWord, h']⟩

theorem gaugeBank_mem (M : Nat) (k : Fin (RowCount t d) → Fin 3 → Nat)
    (hM : 0 < M) {a : Nat} (ha : a < 3 * RowCount t d) :
    a < (SmithGaugeBank M k).length ∧
      (SmithGaugeBank M k).getD a 0 = boundedWord (gaugeWord M k) a ∧
      boundedWord (gaugeWord M k) a < M := by
  have h' : a < RowCount t d * 3 := by simpa [Nat.mul_comm 3] using ha
  refine ⟨(ofFn_boundedWord_ok (gaugeWord M k) h').1,
    (ofFn_boundedWord_ok (gaugeWord M k) h').2, ?_⟩
  unfold boundedWord
  rw [dif_pos h']
  exact Nat.mod_lt _ hM

theorem gaugeWord_at_slot (M : Nat) (k : Fin (RowCount t d) → Fin 3 → Nat)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    boundedWord (gaugeWord M k) (3 * r.val + e.val) = k r e % M := by
  rw [← slotIndex_val r e, boundedWord_ok]
  unfold gaugeWord slotIndex
  rw [Equiv.symm_apply_apply]

theorem gaugeBank_at_slot (M : Nat) (k : Fin (RowCount t d) → Fin 3 → Nat)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    (SmithGaugeBank M k).getD (3 * r.val + e.val) 0 = k r e % M := by
  have h := ofFn_boundedWord_ok (gaugeWord M k) (slotIndex r e).isLt
  rw [slotIndex_val] at h
  exact h.2.trans (gaugeWord_at_slot M k r e)

theorem orderBank_mem {v B : Nat} (n : Fin v → Nat) (hn : ∀ i, n i < B)
    {a : Nat} (ha : a < v) :
    a < (SmithOrderBank n).length ∧
      (SmithOrderBank n).getD a 0 = boundedWord n a ∧ boundedWord n a < B := by
  exact ⟨(ofFn_boundedWord_ok n ha).1, (ofFn_boundedWord_ok n ha).2,
    by simpa [boundedWord, ha] using hn ⟨a, ha⟩⟩

/-- Choose one gauge for each cell factor. All ports introduced by the
prefix conversion are identities, so their exponents are one. -/
def extendSmithGauge (k : Fin t → Fin d → Nat) (r : Fin (RowCount t d))
    (e : Fin 3) : Nat :=
  match (rowIndex.symm r).2 with
  | .inl i => if e.val = 2 then k (rowIndex.symm r).1 i else 1
  | .inr _ => 1

theorem extendSmithGauge_step (k : Fin t → Fin d → Nat)
    (j : Fin t) (i : Fin d) (e : Fin 3) :
    extendSmithGauge k (rowIndex (j, .inl i)) e = if e.val = 2 then k j i else 1 := by
  simp [extendSmithGauge]

theorem extendSmithGauge_pin (k : Fin t → Fin d → Nat)
    (j : Fin t) (p : Fin 2) (e : Fin 3) :
    extendSmithGauge k (rowIndex (j, .inr p)) e = 1 := by
  simp [extendSmithGauge]

#print axioms sourceBank_mem
#print axioms gaugeBank_mem
#print axioms gaugeBank_at_slot
#print axioms orderBank_mem
#print axioms extendSmithGauge_step
#print axioms extendSmithGauge_pin

end EvenOrdinaryTI.LiveRows
