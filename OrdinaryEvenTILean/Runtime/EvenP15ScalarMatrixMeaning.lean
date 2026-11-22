import EvenP15ScalarMatrix
import EvenP12ScalarProbe

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace EvenTI.P15Scalar

open EvenTI.Action EvenTI.Contract
open EvenTI.P12Scalar (rawScalarModes)
open Matrix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n d : ℕ}

/-- The literal field digits of a square matrix test scalarity without
constructing a unit or applying an inverse. -/
theorem rawScalarModeDigits_iff (F : FieldEncoding K) (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) :
    (∀ i j : Fin n, (F (M i j)).val =
      scalarExpected (n+1) (F (M ⟨0,hn⟩ ⟨0,hn⟩)).val (F 0).val (i.val*n+j.val)) ↔
      M = M ⟨0,hn⟩ ⟨0,hn⟩ • (1 : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h
    ext i j
    have hh := h i j
    have hOffset := diagonal_offset_iff n i.val j.val i.isLt j.isLt
    apply F.injective
    apply Fin.ext
    by_cases he : i=j
    · have e : i.val=j.val := congrArg Fin.val he
      simp only [scalarExpected,if_pos (hOffset.mpr e)] at hh
      simpa [Matrix.smul_apply,Matrix.one_apply,he] using hh
    · have e : i.val≠j.val := fun eq => he (Fin.ext eq)
      simp only [scalarExpected,if_neg (fun h => e (hOffset.mp h))] at hh
      simpa [Matrix.smul_apply,Matrix.one_apply,he] using hh
  · intro h i j
    have hh := congrFun (congrFun h i) j
    have hOffset := diagonal_offset_iff n i.val j.val i.isLt j.isLt
    by_cases he : i=j
    · have e : i.val=j.val := congrArg Fin.val he
      rw [scalarExpected,if_pos (hOffset.mpr e)]
      simpa [Matrix.smul_apply,Matrix.one_apply,he] using
        congrArg (fun v : K => (F v).val) hh
    · have e : i.val≠j.val := fun eq => he (Fin.ext eq)
      simpa [scalarExpected,if_neg (fun h => e (hOffset.mp h)),Matrix.smul_apply,Matrix.one_apply,he] using
        congrArg (fun v : K => (F v).val) hh

/-- Interpret a literal row-major slice as the matrix expected by the
self-branch check. Values outside the slice do not affect its verdict. -/
theorem rawScalarBankMode_iff (F : FieldEncoding K) (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) (xs : List ℕ) (base : ℕ)
    (hRows : ∀ i j : Fin n, xs.getD (base+(i.val*n+j.val)) 0 = (F (M i j)).val) :
    (∀ k < n*n, xs.getD (base+k) 0 =
      scalarExpected (n+1) (xs.getD base 0) (F 0).val k) ↔
      M = M ⟨0,hn⟩ ⟨0,hn⟩ • (1 : Matrix (Fin n) (Fin n) K) := by
  have hdiag : xs.getD base 0 = (F (M ⟨0,hn⟩ ⟨0,hn⟩)).val := by
    simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero] using hRows ⟨0,hn⟩ ⟨0,hn⟩
  rw [hdiag,← rawScalarModeDigits_iff F hn M]
  constructor
  · intro h i j
    have hi : i.val*n+j.val < n*n := calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by rw [Nat.succ_mul]
      _ ≤ n*n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
    simpa only [hRows i j] using h _ hi
  · intro h k hk
    let p := (finProdFinEquiv (m := n) (n := n)).symm ⟨k,hk⟩
    have he : p.1.val*n+p.2.val=k := by
      have he' := (finProdFinEquiv (m := n) (n := n)).apply_symm_apply (⟨k,hk⟩ : Fin (n*n))
      have he'' := congrArg Fin.val he'
      change p.2.val+n*p.1.val=k at he''
      rwa [Nat.add_comm,Nat.mul_comm n p.1.val] at he''
    rw [← he,hRows]
    exact h p.1 p.2

theorem rawScalarModes_iff_bankModes (F : FieldEncoding K) (hn : 0 < n)
    (M : Fin d → Matrix (Fin n) (Fin n) K) (xs : List ℕ) (base : Fin d → ℕ)
    (hRows : ∀ (i : Fin d) (j k : Fin n), xs.getD (base i+(j.val*n+k.val)) 0 =
      (F (M i j k)).val) :
    rawScalarModes M = true ↔
      ∀ (i : Fin d) (j : ℕ), j < n*n → xs.getD (base i+j) 0 =
        scalarExpected (n+1) (xs.getD (base i) 0) (F 0).val j := by
  simp only [rawScalarModes,dif_pos hn,List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq]
  exact forall_congr' fun i => (rawScalarBankMode_iff F hn (M i) xs (base i) (hRows i)).symm

#print axioms rawScalarModeDigits_iff
#print axioms rawScalarBankMode_iff
#print axioms rawScalarModes_iff_bankModes
end EvenTI.P15Scalar