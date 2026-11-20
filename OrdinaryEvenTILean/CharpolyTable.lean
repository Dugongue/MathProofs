import CharpolyBird

/-! Materialize each Bird round once. Only coefficients 0 through n are stored. -/
namespace Mathproof.Problem17CharpolyTable
open Mathproof.Problem17CharpolyBird
open scoped Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

abbrev Table (K : Type*) (n : ℕ) :=
  Vector (Vector (Vector K (n+1)) n) n

def get (T : Table K n) (i j : Fin n) (d : Fin (n+1)) : K :=
  T[i.val][j.val][d.val]

def tabulate (f : Fin n → Fin n → Fin (n+1) → K) : Table K n :=
  Vector.ofFn fun i => Vector.ofFn fun j => Vector.ofFn (f i j)

@[simp] theorem get_tabulate (f : Fin n → Fin n → Fin (n+1) → K)
    (i j : Fin n) (d : Fin (n+1)) : get (tabulate f) i j d = f i j d := by
  simp [get, tabulate]

def prev (f : Fin (n+1) → K) (d : Fin (n+1)) : K :=
  if h : 0 < d.val then f ⟨d.val - 1, by omega⟩ else 0

theorem prev_eq (f : ℕ → K) (d : Fin (n+1)) :
    prev (fun j => f j.val) d = previous f d.val := by
  unfold prev
  by_cases h : 0 < d.val
  · rw [dif_pos h]
    change f (d.val - 1) = previous f d.val
    conv_rhs => rw [show d.val = (d.val - 1) + 1 by omega]
    rfl
  · rw [dif_neg h]
    have hz : d.val = 0 := by omega
    simp [hz, previous]

def round (A : Matrix (Fin n) (Fin n) K) (T : Table K n) : Table K n :=
  tabulate fun i j d =>
    let p := fun s => -∑ k ∈ Finset.Ioi i, get T k k s
    timesEntry (A i j) (p d) (prev p d) (decide (i = j)) +
      ∑ k ∈ Finset.Ioi i, timesEntry (A k j) (get T i k d) (prev (get T i k) d) (decide (k = j))

def run (A : Matrix (Fin n) (Fin n) K) : ℕ → Table K n
  | 0 => tabulate fun i j d => entry A i j d.val
  | t+1 => round A (run A t)

theorem run_eq (A : Matrix (Fin n) (Fin n) K) (t : ℕ) (i j : Fin n) (d : Fin (n+1)) :
    get (run A t) i j d = iter A t i j d.val := by
  induction t generalizing i j d with
  | zero => simp [run, iter]
  | succ t ih =>
    rw [run, round, get_tabulate, iter]
    have ih' (a b : Fin n) : get (run A t) a b = fun s => iter A t a b s.val :=
      funext (ih a b)
    simp only [step, ih', prev_eq]
    rw [prev_eq (fun s => -∑ k ∈ Finset.Ioi i, iter A t k k s) d]

def coefficients : (n : ℕ) → Matrix (Fin n) (Fin n) K → Vector K (n+1)
  | 0, _ => Vector.ofFn fun _ => 1
  | t+1, A =>
    let T := run A t
    Vector.ofFn fun d => (-1 : K)^t * get T 0 0 d

theorem coefficients_eq (A : Matrix (Fin n) (Fin n) K) (d : Fin (n+1)) :
    (coefficients n A)[d.val] = A.charpoly.coeff d.val := by
  rw [← coeffs_eq]
  cases n with
  | zero => have h : d.val = 0 := by omega
            simp [coefficients, coeffs, h]
  | succ t => simp [coefficients, coeffs, run_eq]

end Mathproof.Problem17CharpolyTable

#print axioms Mathproof.Problem17CharpolyTable.coefficients_eq
