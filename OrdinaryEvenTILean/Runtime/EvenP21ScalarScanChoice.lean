import EvenP15ScalarKernelProbe

/-! Any physical CRT completion for each feasible prefix suffices to detect
subgroup membership of the whole homogeneous kernel. -/
namespace EvenTI.P21ScalarScan

open scoped Matrix
open Matrix EvenTI.P12Compare EvenTI.P14Recovery

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000

variable {M m n : ℕ} [NeZero M]

def ProbeFeasible (A : Matrix (Fin m) (Fin n) (ZMod M))
    (i : Fin n) (a : ZMod M) (x : Fin n → ZMod M) : Prop :=
  (fixedCoordinateMatrix A (i.val+1)).mulVec x =
    fixedCoordinateRhs (0 : Fin m → ZMod M) (Function.update 0 i a) (i.val+1)

theorem probeFeasible_iff (A : Matrix (Fin m) (Fin n) (ZMod M))
    (i : Fin n) (a : ZMod M) (x : Fin n → ZMod M) :
    ProbeFeasible A i a x ↔
      A.mulVec x=0 ∧ (∀ j : Fin n, j.val < i.val → x j=0) ∧ x i=a := by
  unfold ProbeFeasible
  rw [fixedCoordinate_solutions]
  constructor
  · rintro ⟨h,pre⟩
    refine ⟨h,?_,?_⟩
    · intro j hj
      have hne : j ≠ i := fun eq => (Nat.ne_of_lt hj) (congrArg Fin.val eq)
      simpa [Function.update_of_ne hne] using pre j (by omega)
    · simpa using pre i (by omega)
  · rintro ⟨h,pre,here⟩
    refine ⟨h,?_⟩
    intro j hj
    by_cases he : j=i
    · subst j
      simpa using here
    · have hne : j.val ≠ i.val := fun e => he (Fin.ext e)
      simpa [Function.update_of_ne he] using pre j (by omega)

theorem kernel_of_prefix_choices
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (H : AddSubgroup (Fin n → ZMod M))
    (choices : ∀ (i : Fin n) (a : ZMod M), (∃ x, ProbeFeasible A i a x) →
      ∃ x ∈ H, ProbeFeasible A i a x) :
    ∀ x, A.mulVec x=0 → x ∈ H := by
  intro x hx
  have progress : ∀ k ≤ n, ∃ z ∈ H, A.mulVec z=0 ∧
      ∀ j : Fin n, j.val < k → z j=x j := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨0,H.zero_mem,by simp,fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
    | succ k ih =>
      intro kn
      obtain ⟨z,hz,hzKer,pre⟩ := ih (by omega)
      let i : Fin n := ⟨k,by omega⟩
      let r := x-z
      have hr : A.mulVec r=0 := by simp [r,Matrix.mulVec_sub,hx,hzKer]
      have rPre (j : Fin n) (hj : j.val < i.val) : r j=0 := by
        change x j-z j=0
        rw [pre j hj,sub_self]
      have feasible := (probeFeasible_iff A i (r i) r).mpr ⟨hr,rPre,rfl⟩
      obtain ⟨u,hu,huf⟩ := choices i (r i) ⟨r,feasible⟩
      obtain ⟨hKer,hPre,hHere⟩ := (probeFeasible_iff A i (r i) u).mp huf
      refine ⟨z+u,H.add_mem hz hu,by simp [Matrix.mulVec_add,hzKer,hKer],?_⟩
      intro j hj
      change z j+u j=x j
      by_cases he : j=i
      · subst j
        rw [hHere]
        change z i+(x i-z i)=x i
        abel
      · have hne : j.val ≠ k := fun e => he (Fin.ext e)
        have hjk : j.val < k := by omega
        rw [pre j hjk,hPre j hjk,add_zero]
  obtain ⟨z,hz,_,pre⟩ := progress n (by rfl)
  have he : z=x := funext fun j => pre j j.isLt
  simpa only [he] using hz

#print axioms probeFeasible_iff
#print axioms kernel_of_prefix_choices
end EvenTI.P21ScalarScan

