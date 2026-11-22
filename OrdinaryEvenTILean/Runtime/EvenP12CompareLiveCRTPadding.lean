import EvenP12CompareRecoverLinear

namespace EvenTI.P12Compare

open scoped BigOperators Matrix
open Mathproof.P15NetworkDefs20261007

variable {M m k n : ℕ} [NeZero M]

private theorem recoverCoordinate_minimum
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {s t : ZMod M} (hs : recoverCoordinate A b i = some s)
    (ht : ∃ x, A.mulVec x = b ∧ x i = t) : s.val ≤ t.val := by
  obtain ⟨hU₁,hU₂,hV₁,hV₂,hA,hD⟩ := ZDiag.zmodDiag_spec (appendCoordinate A i)
  exact valueFromBanks_min A b i ⟨hA,hU₁,hU₂,hV₁,hV₂⟩ hD hs ht

/-- Coordinate recovery depends only on the solution set. This permits an
outer loop to reuse one fixed-height Smith bank, padding unused rows by zero. -/
theorem recoverCoordinate_congr_solutions
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (B : Matrix (Fin k) (Fin n) (ZMod M))
    (a : Fin m → ZMod M) (b : Fin k → ZMod M) (i : Fin n)
    (h : ∀ x, A.mulVec x = a ↔ B.mulVec x = b) :
    recoverCoordinate A a i = recoverCoordinate B b i := by
  cases ha : recoverCoordinate A a i with
  | none =>
    cases hb : recoverCoordinate B b i with
    | none => rfl
    | some t =>
      obtain ⟨y,hy,_⟩ := recoverCoordinate_sound B b i hb
      have hSome := recoverCoordinate_complete A a i ((h y).mpr hy)
      simp [ha] at hSome
  | some s =>
    obtain ⟨x,hx,hxs⟩ := recoverCoordinate_sound A a i ha
    obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp (recoverCoordinate_complete B b i ((h x).mp hx))
    obtain ⟨y,hy,hyt⟩ := recoverCoordinate_sound B b i ht
    rw [ht]
    apply congrArg some
    apply ZMod.val_injective
    exact Nat.le_antisymm
      (recoverCoordinate_minimum A a i ha ⟨y,(h y).mpr hy,hyt⟩)
      (recoverCoordinate_minimum B b i ht ⟨x,(h x).mp hx,hxs⟩)

def padCoordinateMatrix (k : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod M)) :
    Matrix (Fin (m+k)) (Fin n) (ZMod M) :=
  fun r j => if h : r.val < m then A ⟨r.val,h⟩ j else 0

def padCoordinateRhs (k : ℕ) (b : Fin m → ZMod M) : Fin (m+k) → ZMod M :=
  fun r => if h : r.val < m then b ⟨r.val,h⟩ else 0

theorem padCoordinate_solutions (k : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (x : Fin n → ZMod M) :
    (padCoordinateMatrix k A).mulVec x = padCoordinateRhs k b ↔ A.mulVec x = b := by
  constructor
  · intro h
    funext j
    let j' : Fin (m+k) := ⟨j.val,by have := j.isLt; omega⟩
    have hj := congrFun h j'
    simpa [j',padCoordinateMatrix,padCoordinateRhs,Matrix.mulVec,dotProduct,j.isLt] using hj
  · intro h
    funext j
    by_cases hj : j.val < m
    · simpa [padCoordinateMatrix,padCoordinateRhs,Matrix.mulVec,dotProduct,hj]
        using congrFun h ⟨j.val,hj⟩
    · simp [padCoordinateMatrix,padCoordinateRhs,Matrix.mulVec,dotProduct,hj]

theorem recoverCoordinate_zeroPad (k : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n) :
    recoverCoordinate (padCoordinateMatrix k A) (padCoordinateRhs k b) i = recoverCoordinate A b i :=
  recoverCoordinate_congr_solutions _ _ _ _ i (padCoordinate_solutions k A b)

private def fixedTail (r : Fin (m+n)) (h : ¬ r.val < m) : Fin n :=
  ⟨r.val-m,by have := r.isLt; omega⟩

/-- A fixed-height bank with one reserved row for every coordinate. Only the
prefix of committed coordinates has a unit row; every other reserved row is zero. -/
def fixedCoordinateMatrix (A : Matrix (Fin m) (Fin n) (ZMod M)) (p : ℕ) :
    Matrix (Fin (m+n)) (Fin n) (ZMod M) :=
  fun r j => if h : r.val < m then A ⟨r.val,h⟩ j
    else if (fixedTail r h).val < p then (if j = fixedTail r h then 1 else 0) else 0

def fixedCoordinateRhs (b : Fin m → ZMod M) (w : Fin n → ZMod M) (p : ℕ) :
    Fin (m+n) → ZMod M :=
  fun r => if h : r.val < m then b ⟨r.val,h⟩
    else if (fixedTail r h).val < p then w (fixedTail r h) else 0

private theorem fixedUnitRow_dot (x : Fin n → ZMod M) (j : Fin n) :
    (∑ k : Fin n, (if k = j then (1 : ZMod M) else 0) * x k) = x j := by
  calc
    _ = (if j = j then (1 : ZMod M) else 0)*x j := Finset.sum_eq_single j
      (fun k _ h => by simp [h]) (by simp)
    _ = x j := by simp

private theorem fixedCoordinate_tail_dot (A : Matrix (Fin m) (Fin n) (ZMod M)) (p : ℕ)
    (x : Fin n → ZMod M) (r : Fin (m+n)) (h : ¬ r.val < m) :
    (fixedCoordinateMatrix A p).mulVec x r =
      if (fixedTail r h).val < p then x (fixedTail r h) else 0 := by
  by_cases hp : (fixedTail r h).val < p
  · simp only [Matrix.mulVec,dotProduct,fixedCoordinateMatrix,dif_neg h,if_pos hp]
    exact fixedUnitRow_dot x (fixedTail r h)
  · simp [Matrix.mulVec,dotProduct,fixedCoordinateMatrix,h,hp]

/-- The fixed-height physical layout imposes exactly the original equations
and the committed coordinate values. Its inactive rows impose no conditions. -/
theorem fixedCoordinate_solutions
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (w x : Fin n → ZMod M) (p : ℕ) :
    (fixedCoordinateMatrix A p).mulVec x = fixedCoordinateRhs b w p ↔
      A.mulVec x = b ∧ ∀ j : Fin n, j.val < p → x j = w j := by
  constructor
  · intro h
    constructor
    · funext r
      let r' : Fin (m+n) := ⟨r.val,by have := r.isLt; omega⟩
      have hv := congrFun h r'
      simpa [r',fixedCoordinateMatrix,fixedCoordinateRhs,Matrix.mulVec,dotProduct,r.isLt] using hv
    · intro j hj
      let r : Fin (m+n) := ⟨m+j.val,Nat.add_lt_add_left j.isLt m⟩
      have hr : ¬ r.val < m := by dsimp [r]; omega
      have heq : fixedTail r hr = j := by apply Fin.ext; dsimp [fixedTail,r]; omega
      have hv := congrFun h r
      rw [fixedCoordinate_tail_dot A p x r hr,heq,if_pos hj] at hv
      simpa [fixedCoordinateRhs,hr,heq,hj] using hv
  · rintro ⟨ha,hw⟩
    funext r
    by_cases hr : r.val < m
    · simpa [fixedCoordinateMatrix,fixedCoordinateRhs,Matrix.mulVec,dotProduct,hr]
        using congrFun ha ⟨r.val,hr⟩
    · rw [fixedCoordinate_tail_dot A p x r hr]
      simp only [fixedCoordinateRhs,dif_neg hr]
      by_cases hp : (fixedTail r hr).val < p
      · simp [hp,hw _ hp]
      · simp [hp]

/-- Extending the logical prefix writes one matrix word at (m+i,i). -/
theorem fixedCoordinateMatrix_succ
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) (r : Fin (m+n)) (j : Fin n) :
    fixedCoordinateMatrix A (i.val+1) r j =
      if r.val = m+i.val ∧ j = i then 1 else fixedCoordinateMatrix A i.val r j := by
  unfold fixedCoordinateMatrix
  by_cases hr : r.val < m
  · have hne : r.val ≠ m+i.val := by omega
    simp [hr,hne]
  · simp only [dif_neg hr]
    let k := fixedTail r hr
    have hEq : k.val = i.val ↔ r.val = m+i.val := by dsimp [k,fixedTail]; omega
    change (if k.val < i.val+1 then (if j = k then 1 else 0) else 0) =
      if r.val = m+i.val ∧ j = i then 1 else
        (if k.val < i.val then (if j = k then 1 else 0) else 0)
    by_cases hlt : k.val < i.val
    · have hnew : k.val < i.val+1 := by omega
      have hne : r.val ≠ m+i.val := fun h => (Nat.ne_of_lt hlt) (hEq.mpr h)
      simp [hlt,hnew,hne]
    · by_cases he : k.val = i.val
      · have hk : k = i := Fin.ext he
        have hh : k.val < i.val+1 := by omega
        have hr' := hEq.mp he
        simp [hlt,hh,hr',hk]
      · have hh : ¬ k.val < i.val+1 := by omega
        have hr' : r.val ≠ m+i.val := fun h => he (hEq.mpr h)
        simp [hlt,hh,hr']

/-- The RHS update writes exactly the chosen residue in the matching fixed row. -/
theorem fixedCoordinateRhs_succ
    (b : Fin m → ZMod M) (w : Fin n → ZMod M) (i : Fin n) (s : ZMod M) (r : Fin (m+n)) :
    fixedCoordinateRhs b (Function.update w i s) (i.val+1) r =
      if r.val = m+i.val then s else fixedCoordinateRhs b w i.val r := by
  unfold fixedCoordinateRhs
  by_cases hr : r.val < m
  · have hne : r.val ≠ m+i.val := by omega
    simp [hr,hne]
  · simp only [dif_neg hr]
    let k := fixedTail r hr
    have hEq : k.val = i.val ↔ r.val = m+i.val := by dsimp [k,fixedTail]; omega
    change (if k.val < i.val+1 then Function.update w i s k else 0) =
      if r.val = m+i.val then s else (if k.val < i.val then w k else 0)
    by_cases hlt : k.val < i.val
    · have hnew : k.val < i.val+1 := by omega
      have he : k.val ≠ i.val := Nat.ne_of_lt hlt
      have hne : r.val ≠ m+i.val := fun h => he (hEq.mpr h)
      have hk : k ≠ i := fun h => he (congrArg Fin.val h)
      simp [hlt,hnew,hne,Function.update_of_ne hk]
    · by_cases he : k.val = i.val
      · have hk : k = i := Fin.ext he
        have hh : k.val < i.val+1 := by omega
        have hr' := hEq.mp he
        simp [hh,hr',hk]
      · have hh : ¬ k.val < i.val+1 := by omega
        have hr' : r.val ≠ m+i.val := fun h => he (hEq.mpr h)
        simp [hlt,hh,hr']

#print axioms recoverCoordinate_congr_solutions
#print axioms recoverCoordinate_zeroPad
#print axioms fixedCoordinate_solutions
#print axioms fixedCoordinateMatrix_succ
#print axioms fixedCoordinateRhs_succ

end EvenTI.P12Compare
