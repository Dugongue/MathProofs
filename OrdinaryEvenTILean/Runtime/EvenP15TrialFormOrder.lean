import EvenP10TrialPayload
import EvenP11InputCoordOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P15Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan

/-- The public form packet orders mixed-radix coordinates little-endian,
whereas the original pair and live field banks use physical mode order. -/
def reverseModeNumber (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d+1, k => k%n*n^d + reverseModeNumber n d (k/n)

theorem inputCoordOrder_cons (n d : ℕ) (c : Fin n) (w : Coord d n) :
    ((inputCoordOrder n (d+1)) (Fin.cons c w)).val = c.val*n^d+((inputCoordOrder n d) w).val := by
  simp [inputCoordOrder,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv] <;> ac_rfl

private theorem cutOrder_decode_cons {n d : ℕ} (i : Fin (n^(d+1))) (hd : i.val/n < n^d) :
    (cutOrder (d+1) n).symm i = Fin.cons ⟨i.val%n,Nat.mod_lt _ (by
        have hi := i.isLt
        by_contra! h
        have hn : n=0 := by omega
        simp [hn] at hi)⟩ ((cutOrder d n).symm ⟨i.val/n,hd⟩) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · apply Fin.ext
    change i.val/n^0%n=i.val%n
    simp
  · apply Fin.ext
    change i.val/n^(k.val+1)%n=(i.val/n)/n^k.val%n
    rw [Nat.div_div_eq_div_mul]
    exact congrArg (fun v : ℕ => i.val/v%n) (pow_succ' n k.val)

theorem reverseModeNumber_eq {n : ℕ} (hn : 0 < n) (d : ℕ) (i : Fin (n^d)) :
    ((inputCoordOrder n d) ((cutOrder d n).symm i)).val = reverseModeNumber n d i.val := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hD : i.val/n < n^d := Nat.div_lt_of_lt_mul (by
      simpa [pow_succ,Nat.mul_comm] using i.isLt)
    rw [cutOrder_decode_cons i hD,inputCoordOrder_cons,ih]
    rfl

variable {K : Type} [Field K] [Fintype K]

theorem cutFormWords_as_gather {n d : ℕ} (hn : 0 < n) (D : FieldEncoding K)
    (form : Coord d n → K) (read : ℕ → K)
    (hRead : ∀ t, read ((inputCoordOrder n d) t).val = form t) :
    cutFormWords D form =
      List.ofFn (fun i : Fin (n^d) => (D (read (reverseModeNumber n d i.val))).val) := by
  unfold cutFormWords
  apply congrArg List.ofFn
  funext i
  rw [← reverseModeNumber_eq hn d i,hRead]

#print axioms cutFormWords_as_gather
end EvenTI.P15Trial
