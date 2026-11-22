import EvenP12CompareRecoverSmithRun

namespace EvenTI.P12Compare

open scoped BigOperators Matrix
open EvenTI.Part8
open Mathproof.P15NetworkDefs20261007
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithArray20261007
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithMachine20261007 (smithIMP smithCost smithIMP_run)

variable {M m n : ℕ} [NeZero M]

private theorem unitRhs_apply (U : Matrix (Fin n) (Fin n) (ZMod M)) (h : ℕ)
    (i r : Fin n) :
    U.mulVec (fun j => if i=j then (h : ZMod M) else 0) r = U r i * h := by
  simp [Matrix.mulVec,dotProduct,mul_ite,eq_comm]

/-- One paid transposed Smith transform simultaneously decides every
character-row equation h eᵢ. No recovery or field power evaluation is used. -/
theorem characterCap_iff_of_smith
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ) {st : ZDiag.State M n m}
    (hSt : ZDiag.Valid A.transpose st) (hD : IsMonoDiag st.B) :
    (smithPowerRows A h).isSome = true ↔
      ∀ (i r : Fin n), Nat.gcd (rowEntryZ st.B r).val M ∣ (st.U r i * (h : ZMod M)).val := by
  unfold smithPowerRows
  rw [smithLeftSolve_isSome_iff]
  constructor
  · rintro ⟨C,hC⟩ i r
    have hs := (characterRows_mul_iff A h C).mp hC i
    have h₁ := (solve_iff_of_paid_smith hSt hD
      (fun j => if i=j then (h : ZMod M) else 0)).mp ⟨C i,hs⟩ r
    simpa only [unitRhs_apply] using h₁
  · classical
    intro hh
    have hs (i : Fin n) : ∃ v, A.transpose.mulVec v = fun j => if i=j then (h : ZMod M) else 0 := by
      apply (solve_iff_of_paid_smith hSt hD _).mpr
      intro r
      simpa only [unitRhs_apply] using hh i r
    choose C hC using hs
    exact ⟨C,(characterRows_mul_iff A h C).mpr hC⟩

/-- In the fully cleared rectangular Smith form, a row's coefficient is
one diagonal word or zero at a tail row. -/
theorem rowEntryZ_eq_diagonal (B : Matrix (Fin n) (Fin m) (ZMod M))
    (hC : ZDiag.Clr (min n m) B) (r : Fin n) :
    rowEntryZ B r = if hj : r.val < m then B r ⟨r.val,hj⟩ else 0 := by
  unfold rowEntryZ
  split
  · rename_i hj
    refine Finset.sum_eq_single (⟨r.val,hj⟩ : Fin m) ?_ (by simp)
    intro j _ hne
    apply hC r j (Or.inl (lt_min r.isLt hj))
    intro he
    exact hne (Fin.ext he.symm)
  · rename_i hj
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hr := r.isLt
    have hj' := j.isLt
    exact hC r j (Or.inr (lt_min (by omega) hj')) (by omega)

/-- The literal divisibility tests over the two installed Smith output banks. -/
def installedCharacterCap (M m n h : ℕ) (σ : Env) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all fun r =>
      let diagonalRow := if r.val < m then decode M (σ.arrs matrixR) (r.val*m+r.val) else 0
      let ui := decode M (σ.arrs matrixR) (n*m+r.val*n+i.val)
      decide (Nat.gcd diagonalRow.val M ∣ (ui * (h : ZMod M)).val)

/-- The byte-machine subcall required by the exact scalar cap. The remaining
scan visits the n² explicit tests in the returned B and U output banks. -/
theorem paidCharacterCapSmith_run (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ) {W : ℕ}
    {σ : Env} (hW : 2*M*M+M+3 < W) (hLayout : n+m+n*m+n*n+4 < W)
    (hLen : n*m+n*n+m ≤ (σ.arrs matrixR).length)
    (hCanon : Canonical M (σ.arrs matrixR))
    (hm : σ.vars modR = M) (hr : σ.vars rowsR = n) (hn : σ.vars inputColsR = m)
    (hB : ∀ r : Fin n, ∀ j : Fin m, decode M (σ.arrs matrixR) (r.val*m+j.val) = A j r) :
    ∃ τ, Run W smithIMP σ τ (smithCost M n m) ∧
      (τ.arrs matrixR).length = (σ.arrs matrixR).length ∧
      Canonical M (τ.arrs matrixR) ∧
      installedCharacterCap M m n h τ = (smithPowerRows A h).isSome ∧
      Frame smithIMP σ τ := by
  obtain ⟨τ,st,hRun,hℓ,hcan,hbank,hvalid,hclr,hD,_,hFrame⟩ :=
    smithIMP_run A.transpose hW hLayout hLen hCanon hm hr hn hB
  refine ⟨τ,hRun,hℓ,hcan,?_,hFrame⟩
  rw [Bool.eq_iff_iff, characterCap_iff_of_smith A h hvalid hD]
  simp only [installedCharacterCap,List.all_eq_true,List.mem_finRange,forall_true_left,
    decide_eq_true_eq,hbank.2]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro r
  have hEntry : (if r.val < m then decode M (τ.arrs matrixR) (r.val*m+r.val) else 0) =
      rowEntryZ st.B r := by
    rw [rowEntryZ_eq_diagonal st.B hclr r]
    by_cases hlt : r.val < m
    · rw [if_pos hlt,dif_pos hlt]
      exact hbank.1 r ⟨r.val,hlt⟩
    · simp [hlt]
  rw [hEntry]

#print axioms characterCap_iff_of_smith
#print axioms rowEntryZ_eq_diagonal
#print axioms paidCharacterCapSmith_run

end EvenTI.P12Compare
