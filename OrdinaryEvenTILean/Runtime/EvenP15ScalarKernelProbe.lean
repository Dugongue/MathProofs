import EvenP14CRTPositive

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P15Scalar

open Matrix EvenTI.P12Compare EvenTI.P14Recovery

variable {M m n : ℕ} [NeZero M]

/-- Recover one element of the original homogeneous system with prescribed
first nonzero position. An unattainable prescription contributes zero. -/
def recoveryKernelProbe (A : Matrix (Fin m) (Fin n) (ZMod M))
    (i : Fin n) (a : ZMod M) : Fin n → ZMod M :=
  (recoverLinear (fixedCoordinateMatrix A (i.val+1))
    (fixedCoordinateRhs 0 (Function.update 0 i a) (i.val+1))).getD 0

private theorem probePrescription {i j : Fin n} {a : ZMod M} (hj : j.val < i.val) :
    Function.update (0 : Fin n → ZMod M) i a j = 0 := by
  have hne : j ≠ i := fun h => (Nat.ne_of_lt hj) (congrArg Fin.val h)
  simp [Function.update_of_ne hne]

theorem recoveryKernelProbe_sound (A : Matrix (Fin m) (Fin n) (ZMod M))
    (i : Fin n) (a : ZMod M) :
    A.mulVec (recoveryKernelProbe A i a) = 0 ∧
      ∀ j : Fin n, j.val < i.val → recoveryKernelProbe A i a j = 0 := by
  unfold recoveryKernelProbe
  cases hz : recoverLinear (fixedCoordinateMatrix A (i.val+1))
      (fixedCoordinateRhs 0 (Function.update 0 i a) (i.val+1)) with
  | none => simp
  | some z =>
    simp only [Option.getD_some]
    have h := (fixedCoordinate_solutions A 0 (Function.update 0 i a) z (i.val+1)).mp
      (recoverLinear_sound _ _ hz)
    exact ⟨h.1,fun j hj => (h.2 j (by omega)).trans (probePrescription hj)⟩

theorem recoveryKernelProbe_value (A : Matrix (Fin m) (Fin n) (ZMod M))
    (i : Fin n) (y : Fin n → ZMod M) (hy : A.mulVec y = 0)
    (hyPre : ∀ j : Fin n, j.val < i.val → y j = 0) :
    recoveryKernelProbe A i (y i) i = y i := by
  let w := Function.update (0 : Fin n → ZMod M) i (y i)
  let S := fixedCoordinateMatrix A (i.val+1)
  let b := fixedCoordinateRhs (0 : Fin m → ZMod M) w (i.val+1)
  have hSol : S.mulVec y = b := by
    apply (fixedCoordinate_solutions A 0 w y (i.val+1)).mpr
    refine ⟨hy,fun j hj => ?_⟩
    by_cases he : j = i
    · subst j
      simp [w]
    · have hva : j.val≠i.val := fun h => he (Fin.ext h)
      rw [hyPre j (by omega)]
      exact (probePrescription (by omega)).symm
  obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (recoverLinear_complete S b ⟨y,hSol⟩)
  have hzPre := (fixedCoordinate_solutions A 0 w z (i.val+1)).mp (recoverLinear_sound S b hz)
  change ((recoverLinear S b).getD 0) i = _
  rw [hz]
  exact (hzPre.2 i (by omega)).trans (by simp [w])

/-- One representative per feasible prefix coordinate value generates the
kernel. Process coordinates in order and subtract the chosen representative
from the residual until the residual is zero. -/
theorem recoveryKernelProbe_generates (A : Matrix (Fin m) (Fin n) (ZMod M))
    (P : AddSubgroup (Fin n → ZMod M))
    (hProbe : ∀ i a, recoveryKernelProbe A i a ∈ P) :
    ∀ y, A.mulVec y = 0 → y ∈ P := by
  intro y hy
  have matchPrefix : ∀ k ≤ n, ∃ z ∈ P, A.mulVec z = 0 ∧
      ∀ j : Fin n, j.val < k → z j = y j := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨0,P.zero_mem,by simp,fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
    | succ k ih =>
      intro hk
      obtain ⟨z,hz,hzKer,hzPre⟩ := ih (by omega)
      let i : Fin n := ⟨k,by omega⟩
      let r := y-z
      have hR : A.mulVec r = 0 := by
        simp [r,Matrix.mulVec_sub,hy,hzKer]
      have hRpre (j : Fin n) (hj : j.val < i.val) : r j = 0 := by
        change y j-z j=0
        rw [hzPre j hj,sub_self]
      let u := recoveryKernelProbe A i (r i)
      have hUS := recoveryKernelProbe_sound A i (r i)
      have hUI := recoveryKernelProbe_value A i r hR hRpre
      refine ⟨z+u,P.add_mem hz (hProbe i (r i)),by simp [Matrix.mulVec_add,hzKer,u,hUS.1],?_⟩
      intro j hj
      change z j + u j = y j
      by_cases he : j = i
      · subst j
        change z i + recoveryKernelProbe A i (r i) i = y i
        rw [hUI]
        change z i + (y i - z i) = y i
        abel
      · have jn : j.val ≠ k := fun h => he (Fin.ext h)
        have hlt : j.val < k := by omega
        have hu0 : u j = 0 := hUS.2 j hlt
        rw [hzPre j hlt,hu0,add_zero]
  obtain ⟨z,hz,_,hp⟩ := matchPrefix n (le_refl n)
  have he : z = y := funext fun j => hp j j.isLt
  simpa only [he] using hz

def scanRecoveryKernelProbes (A : Matrix (Fin m) (Fin n) (ZMod M))
    (test : (Fin n → ZMod M) → Bool) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange M).all fun a => test (recoveryKernelProbe A i (a.val : ZMod M))

/-- The physical caller can enumerate just n*M probes. Its verdict is the
full-kernel predicate whenever membership on the kernel is a subgroup. -/
theorem scanRecoveryKernelProbes_iff (A : Matrix (Fin m) (Fin n) (ZMod M))
    (test : (Fin n → ZMod M) → Bool) (P : AddSubgroup (Fin n → ZMod M))
    (hTest : ∀ y, A.mulVec y = 0 → (test y = true ↔ y ∈ P)) :
    scanRecoveryKernelProbes A test = true ↔ ∀ y, A.mulVec y = 0 → y ∈ P := by
  simp only [scanRecoveryKernelProbes,List.all_eq_true,List.mem_finRange,true_implies]
  constructor
  · intro h
    apply recoveryKernelProbe_generates A P
    intro i a
    have hv := h i ⟨a.val,ZMod.val_lt a⟩
    change test (recoveryKernelProbe A i (a.val : ZMod M)) = true at hv
    rw [ZMod.natCast_zmod_val] at hv
    exact (hTest _ (recoveryKernelProbe_sound A i a).1).mp hv
  · intro h i a
    have hKer := (recoveryKernelProbe_sound A i (a.val : ZMod M)).1
    exact (hTest _ hKer).mpr (h _ hKer)

#print axioms recoveryKernelProbe_sound
#print axioms recoveryKernelProbe_value
#print axioms recoveryKernelProbe_generates
#print axioms scanRecoveryKernelProbes_iff
end EvenTI.P15Scalar