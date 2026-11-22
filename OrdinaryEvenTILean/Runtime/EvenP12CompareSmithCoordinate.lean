import EvenP8SmithCharacters
import Mathlib.Data.Nat.ModEq

namespace EvenTI.P12Compare

open scoped BigOperators Matrix
open Mathproof.P15NetworkDefs20261007
open EvenTI.Part8

set_option maxHeartbeats 600000

variable {M m n : ℕ} [NeZero M]

private def scalarDivision (a b : ZMod M) : ZMod M :=
  (((b.val / Nat.gcd a.val M : ℕ) : ℤ) * Nat.gcdA a.val M : ℤ)

private theorem scalarDivision_mul (a b : ZMod M) (h : Nat.gcd a.val M ∣ b.val) :
    a * scalarDivision a b = b := by
  have hg := congrArg (fun z : ℤ => (z : ZMod M)) (Nat.gcd_eq_gcd_ab a.val M)
  push_cast at hg
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] at hg
  calc a * scalarDivision a b =
      ((b.val / Nat.gcd a.val M : ℕ) : ZMod M) * (a * Nat.gcdA a.val M) := by
        simp only [scalarDivision, Int.cast_mul, Int.cast_natCast]
        ring
    _ = b := by rw [← hg, ← Nat.cast_mul, Nat.div_mul_cancel h, ZMod.natCast_zmod_val]

/-- A monomial-diagonal matrix certifies consistency from row moduli alone. -/
private theorem monomialSolve_iff (D : Matrix (Fin m) (Fin n) (ZMod M))
    (hD : IsMonoDiag D) (b : Fin m → ZMod M) :
    (∃ x, D.mulVec x = b) ↔ ∀ i, Nat.gcd (rowEntryZ D i).val M ∣ (b i).val := by
  have hentry (i : Fin m) (j : Fin n) (hij : D i j ≠ 0) : rowEntryZ D i = D i j := by
    unfold rowEntryZ
    exact Finset.sum_eq_single j (fun k _ hk => (hD i j hij).1 k hk) (by simp)
  have hrow (i : Fin m) (j : Fin n) (hij : D i j ≠ 0) (x : Fin n → ZMod M) :
      D.mulVec x i = D i j * x j := by
    change (∑ k, D i k * x k) = D i j * x j
    exact Finset.sum_eq_single j (fun k _ hk => by rw [(hD i j hij).1 k hk,zero_mul]) (by simp)
  constructor
  · rintro ⟨x,rfl⟩ i
    by_cases hv : ∃ j, D i j ≠ 0
    · obtain ⟨j,hj⟩ := hv
      rw [hentry i j hj,hrow i j hj,ZMod.val_mul]
      exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).2
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
    · push Not at hv
      simp [rowEntryZ,Matrix.mulVec,dotProduct,hv]
  · intro h
    let x : Fin n → ZMod M := fun j => ∑ i, if D i j = 0 then 0 else scalarDivision (D i j) (b i)
    refine ⟨x,funext fun i => ?_⟩
    by_cases hv : ∃ j, D i j ≠ 0
    · obtain ⟨j,hj⟩ := hv
      rw [hrow i j hj]
      have hjx : x j = scalarDivision (D i j) (b i) := by
        unfold x
        rw [Finset.sum_eq_single i (fun k _ hk => by simp [(hD i j hj).2 k hk]) (by simp),
          if_neg hj]
      rw [hjx]
      exact scalarDivision_mul _ _ (by simpa only [hentry i j hj] using h i)
    · push Not at hv
      have hd := h i
      simp only [rowEntryZ,hv,Finset.sum_const_zero,ZMod.val_zero,Nat.gcd_zero_left] at hd
      have hz : b i = 0 := (ZMod.val_eq_zero _).mp
        (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt (b i)))
      simp [Matrix.mulVec,dotProduct,hv,hz]

/-- The paid Smith data B,U suffices for a linear consistency test. The two
inverses and the column transform enter the proof of correctness only. -/
theorem solve_iff_of_paid_smith {A : Matrix (Fin m) (Fin n) (ZMod M)}
    {st : ZDiag.State M m n} (h : ZDiag.Valid A st) (hD : IsMonoDiag st.B)
    (b : Fin m → ZMod M) :
    (∃ x, A.mulVec x = b) ↔
      ∀ i, Nat.gcd (rowEntryZ st.B i).val M ∣ (st.U.mulVec b i).val := by
  rw [← monomialSolve_iff st.B hD]
  obtain ⟨hB,_,hU,hV,_⟩ := h
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨st.Vi.mulVec x,?_⟩
    rw [hB, Matrix.mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hx]
  · rintro ⟨x,hx⟩
    refine ⟨st.V.mulVec x,?_⟩
    have hx' := congrArg (fun y => st.Ui.mulVec y) hx
    calc
      A.mulVec (st.V.mulVec x) = (st.Ui * (st.U * A * st.V)).mulVec x := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc st.Ui st.U A, hU, Matrix.one_mul,
          ← Matrix.mulVec_mulVec]
      _ = st.Ui.mulVec (st.B.mulVec x) := by rw [← hB, ← Matrix.mulVec_mulVec]
      _ = st.Ui.mulVec (st.U.mulVec b) := hx'
      _ = b := by rw [Matrix.mulVec_mulVec,hU,Matrix.one_mulVec]

def appendCoordinate (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) :
    Matrix (Fin (m+1)) (Fin n) (ZMod M) :=
  fun r j => Fin.lastCases (if j = i then 1 else 0) (fun k => A k j) r

def appendCoordinateRhs (b : Fin m → ZMod M) (s : ZMod M) :
    Fin (m+1) → ZMod M := Fin.lastCases s b

private theorem appendCoordinate_equiv (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (i : Fin n) (s : ZMod M) (x : Fin n → ZMod M) :
    (appendCoordinate A i).mulVec x = appendCoordinateRhs b s ↔
    A.mulVec x = b ∧ x i = s := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_,?_⟩
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
        using congrFun h j.castSucc
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
        using congrFun h (Fin.last m)
  · rintro ⟨h₁,h₂⟩
    funext j
    refine Fin.lastCases ?_ (fun r => ?_) j
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul] using congrFun h₁ r

private theorem appendCoordinate_affine (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M))
    (b : Fin m → ZMod M) (s : ZMod M) (r : Fin (m+1)) :
    U.mulVec (appendCoordinateRhs b s) r =
      (∑ j : Fin m, U r j.castSucc * b j) + U r (Fin.last m) * s := by
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,appendCoordinateRhs]

/-- Every proposed value of the appended coordinate extends to a solution
exactly when the same installed B,U banks satisfy these unary conditions. -/
theorem appendCoordinate_certificate (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (i : Fin n) {st : ZDiag.State M (m+1) n}
    (h : ZDiag.Valid (appendCoordinate A i) st) (hD : IsMonoDiag st.B) (s : ZMod M) :
    (∃ x, A.mulVec x = b ∧ x i = s) ↔
      ∀ r, Nat.gcd (rowEntryZ st.B r).val M ∣
        (((∑ j : Fin m, st.U r j.castSucc * b j) + st.U r (Fin.last m) * s).val) := by
  have hh := solve_iff_of_paid_smith h hD (appendCoordinateRhs b s)
  rw [show (∃ x, (appendCoordinate A i).mulVec x = appendCoordinateRhs b s) ↔
    (∃ x, A.mulVec x = b ∧ x i = s) from exists_congr (appendCoordinate_equiv A b i s)] at hh
  simpa only [appendCoordinate_affine] using hh

/-- Convert the transpose solves to the exact character-row equation used in
the recovery theorem. -/
theorem characterRows_mul_iff (A : Matrix (Fin m) (Fin n) (ZMod M))
    (h : ℕ) (C : Matrix (Fin n) (Fin m) (ZMod M)) :
    C * A = (h : ZMod M) • (1 : Matrix (Fin n) (Fin n) (ZMod M)) ↔
      ∀ i, A.transpose.mulVec (C i) = fun j => if i = j then (h : ZMod M) else 0 := by
  constructor
  · intro he i
    funext j
    have hh := congrArg (fun D : Matrix (Fin n) (Fin n) (ZMod M) => D i j) he
    simpa [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,mul_ite,mul_comm] using hh
  · intro he
    ext i j
    have hh := congrFun (he i) j
    simpa [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,mul_ite,mul_comm] using hh

/-- Character power evaluation is independent of the chosen character
solutions on a feasible multiplicative right-hand side. -/
theorem characterRows_values_eq {G : Type*} [CommGroup G]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (C C' : Matrix (Fin n) (Fin m) (ZMod M))
    (hC : C * A = C' * A) (x : Fin n → G) (hx : ∀ j, x j ^ M = 1) (y : Fin m → G)
    (hy : matPowZ A x = y) : matPowZ C y = matPowZ C' y := by
  have he := congrArg (fun D : Matrix (Fin n) (Fin n) (ZMod M) => matPowZ D x) hC
  simpa only [matPowZ_mul _ _ _ hx, hy] using he

/-- Each installed Smith row gives an ordinary unary linear congruence in
canonical natural-number representatives. -/
theorem unaryDvd_iff (a s c : ZMod M) {d : ℕ} (hd : d ∣ M) :
    d ∣ (a*s+c).val ↔ a.val*s.val ≡ M-c.val [MOD d] := by
  rw [ZMod.val_add,ZMod.val_mul,Nat.mod_add_mod,Nat.dvd_mod_iff hd,← Nat.modEq_zero_iff_dvd]
  have hc : c.val ≤ M := (ZMod.val_lt c).le
  have hsum : M-c.val+c.val = M := Nat.sub_add_cancel hc
  have hM : M ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hd
  constructor
  · intro h
    apply Nat.ModEq.add_right_cancel' c.val
    rw [hsum]
    exact h.trans hM.symm
  · intro h
    have hh := h.add_right c.val
    rw [hsum] at hh
    exact hh.trans hM

/-- A deterministic merge of two normalized unary congruences. -/
def mergeUnary (a d b e : ℕ) : Option (ℕ × ℕ) :=
  if h : a ≡ b [MOD Nat.gcd d e] then some ((Nat.chineseRemainder' h).val, Nat.lcm d e)
  else none

theorem mergeUnary_correct (a d b e u : ℕ) :
    (∃ w, mergeUnary a d b e = some w ∧ u ≡ w.1 [MOD w.2]) ↔
      u ≡ a [MOD d] ∧ u ≡ b [MOD e] := by
  unfold mergeUnary
  split
  · rename_i h
    let w := Nat.chineseRemainder' h
    constructor
    · rintro ⟨v,hv,hu⟩
      have hve : v = (w.val,Nat.lcm d e) := (Option.some.inj hv).symm
      subst v
      exact ⟨(hu.of_dvd (Nat.dvd_lcm_left _ _)).trans w.property.1,
        (hu.of_dvd (Nat.dvd_lcm_right _ _)).trans w.property.2⟩
    · rintro ⟨h₁,h₂⟩
      exact ⟨(w.val,Nat.lcm d e),rfl,
        Nat.mod_lcm (h₁.trans w.property.1.symm) (h₂.trans w.property.2.symm)⟩
  · rename_i h
    refine ⟨by simp,?_⟩
    rintro ⟨h₁,h₂⟩
    exact False.elim (h ((h₁.of_dvd (Nat.gcd_dvd_left _ _)).symm.trans
      (h₂.of_dvd (Nat.gcd_dvd_right _ _))))

#print axioms appendCoordinate_certificate
#print axioms characterRows_mul_iff
#print axioms characterRows_values_eq
#print axioms unaryDvd_iff
#print axioms mergeUnary_correct

end EvenTI.P12Compare
