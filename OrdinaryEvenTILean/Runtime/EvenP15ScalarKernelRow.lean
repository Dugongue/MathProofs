import EvenP12CompareRecoverLinear

set_option autoImplicit false

namespace EvenTI.P15Scalar

open Matrix EvenTI.P12Compare

variable {M m n : ℕ} [NeZero M]

def appendScalarRow (A : Matrix (Fin m) (Fin n) (ZMod M)) (c : Fin n → ZMod M) :
    Matrix (Fin (m+1)) (Fin n) (ZMod M) :=
  fun r j => Fin.lastCases (c j) (fun k => A k j) r

def appendScalarRhs (r : ZMod M) : Fin (m+1) → ZMod M :=
  Fin.lastCases r (fun _ => 0)

theorem appendScalarRow_solutions (A : Matrix (Fin m) (Fin n) (ZMod M))
    (c x : Fin n → ZMod M) (r : ZMod M) :
    (appendScalarRow A c).mulVec x = appendScalarRhs (m:=m) r ↔
      A.mulVec x = 0 ∧ dotProduct c x = r := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_,?_⟩
    · simpa [appendScalarRow,appendScalarRhs,Matrix.mulVec] using congrFun h i.castSucc
    · simpa [appendScalarRow,appendScalarRhs,Matrix.mulVec] using congrFun h (Fin.last m)
  · rintro ⟨hA,hc⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendScalarRow,appendScalarRhs,Matrix.mulVec] using hc
    · simpa [appendScalarRow,appendScalarRhs,Matrix.mulVec] using congrFun hA j

/-- A linear form vanishes on the homogeneous residue kernel exactly when
every nonzero value is infeasible. This uses the same checked CRT driver
and does not require constructing a family of homogeneous transporters. -/
theorem kernelRowVanishes_iff_CRTTests (A : Matrix (Fin m) (Fin n) (ZMod M))
    (c : Fin n → ZMod M) :
    (∀ x, A.mulVec x = 0 → dotProduct c x = 0) ↔
      ∀ r : ZMod M, r ≠ 0 → recoverLinear (appendScalarRow A c) (appendScalarRhs r) = none := by
  constructor
  · intro h r hr
    cases hz : recoverLinear (appendScalarRow A c) (appendScalarRhs r) with
    | none => rfl
    | some x =>
      have hx := (appendScalarRow_solutions A c x r).mp
        (recoverLinear_sound _ _ hz)
      exact False.elim (hr (hx.2.symm.trans (h x hx.1)))
  · intro h x hx
    by_contra hc
    have hs := (appendScalarRow_solutions A c x (dotProduct c x)).mpr ⟨hx,rfl⟩
    have hSome := recoverLinear_complete _ _ ⟨x,hs⟩
    rw [h _ hc] at hSome
    contradiction

#print axioms appendScalarRow_solutions
#print axioms kernelRowVanishes_iff_CRTTests
end EvenTI.P15Scalar