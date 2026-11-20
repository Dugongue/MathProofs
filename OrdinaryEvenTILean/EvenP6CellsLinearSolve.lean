import EvenP5KernelCore
import EvenP5InvRref

/-! The MathProof P15 augmented-column solver, specialized to the reusable
kernel API. The stored variant shares eager pivot rows. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace EvenTI.CellLinearSolve

open Mathproof.P15RecogOps20261007 Mathproof.P15RecogLinAlg20261007
open EvenTI.KernelDonor EvenTI.Contract
open scoped BigOperators

/-- Unknown indices: `none` is the augmented column. -/
def optIdx (k : ℕ) : List (Option (Fin k)) := none :: (List.finRange k).map some

theorem optIdx_complete (k : ℕ) : ∀ o, o ∈ optIdx k := by
  rintro (_ | c) <;> simp [optIdx]

theorem optIdx_nodup (k : ℕ) : (optIdx k).Nodup := by
  unfold optIdx
  refine List.nodup_cons.2 ⟨by simp, (List.nodup_finRange k).map (fun a b h => Option.some_injective _ h)⟩

section Gen

variable {α : Type} (A : Ops α) {ι : Type} [DecidableEq ι]

/-- Rows of the augmented system. -/
def solveRows (idxR : List ι) (k : ℕ) (cols : Fin k → ι → α) (v : ι → α) :
    List (Option (Fin k) → α) :=
  idxR.map fun i o => match o with
    | none => A.neg (v i)
    | some c => cols c i

/-- A solution of `Σ_j c_j cols_j = v`, if any. -/
def solveF (idxR : List ι) (k : ℕ) (cols : Fin k → ι → α) (v : ι → α) : Option (Fin k → α) :=
  match (kerBasis A (optIdx k) (solveRows A idxR k cols v)).find? (fun w => !A.isZero (w none)) with
  | none => none
  | some w => some fun c => A.mul (A.inv (w none)) (w (some c))

end Gen
section Field

variable {K : Type} [Field K] [DecidableEq K] {ι : Type} [DecidableEq ι] [Fintype ι]
  {idxR : List ι} (hidxR : ∀ i, i ∈ idxR)

local notation "O" => Ops.ofField K

omit [Fintype ι] in
theorem rowKer_solveRows {k : ℕ} [Fintype ι] (cols : Fin k → ι → K) (v : ι → K)
    (w : Option (Fin k) → K) :
    w ∈ rowKer (solveRows O idxR k cols v) ↔
      ∀ i ∈ idxR, ∑ c, w (some c) * cols c i = w none * v i := by
  constructor
  · intro hw i hi
    have := hw _ (List.mem_map.2 ⟨i, hi, rfl⟩)
    simp only [Fintype.sum_option] at this
    simp only [ofField_neg] at this
    rw [← sub_eq_zero, ← this]
    simp only [mul_comm]
    ring
  · intro hw r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    simp only [Fintype.sum_option, ofField_neg]
    have := hw i hi
    rw [← sub_eq_zero] at this
    rw [← this]
    simp only [mul_comm]
    ring

include hidxR

theorem solveF_spec {k : ℕ} (cols : Fin k → ι → K) (v : ι → K) (c : Fin k → K)
    (h : solveF O idxR k cols v = some c) : ∑ j, c j • cols j = v := by
  unfold solveF at h
  obtain ⟨kin, -⟩ := kerBasis_spec (optIdx_complete k) (optIdx_nodup k) (solveRows O idxR k cols v)
  rcases hw : (kerBasis O (optIdx k) (solveRows O idxR k cols v)).find?
      (fun w => !(Ops.ofField K).isZero (w none)) with _ | w
  · rw [hw] at h; simp at h
  rw [hw] at h
  simp only [Option.some.injEq] at h
  subst h
  have hmem := List.mem_of_find?_eq_some hw
  have hne := List.find?_some hw
  simp only [ofField_isZero, Bool.not_eq_true', decide_eq_false_iff_not] at hne
  have hk := (rowKer_solveRows cols v w).1 (kin w hmem)
  funext i
  have hi := hk i (hidxR i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ofField_mul, ofField_inv]
  calc ∑ j, (w none)⁻¹ * w (some j) * cols j i = (w none)⁻¹ * ∑ j, w (some j) * cols j i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = v i := by rw [hi, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem solveF_isSome {k : ℕ} (cols : Fin k → ι → K) (v : ι → K)
    (hv : v ∈ Submodule.span K (Set.range cols)) : (solveF O idxR k cols v).isSome := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  obtain ⟨-, kspan⟩ := kerBasis_spec (optIdx_complete k) (optIdx_nodup k) (solveRows O idxR k cols v)
  unfold solveF
  rcases hw : (kerBasis O (optIdx k) (solveRows O idxR k cols v)).find?
      (fun w => !(Ops.ofField K).isZero (w none)) with _ | w
  · exfalso
    have hall := List.find?_eq_none.1 hw
    -- the witness `(1, a)` lies in the kernel
    let w0 : Option (Fin k) → K := fun o => match o with
      | none => 1
      | some c => a c
    have hw0 : w0 ∈ rowKer (solveRows O idxR k cols v) := by
      rw [rowKer_solveRows]
      intro i _
      simp only [w0, one_mul]
      rw [← ha]
      simp [Finset.sum_apply, mul_comm]
    rw [← kspan] at hw0
    -- the functional `w ↦ w none` vanishes on the span
    let g : (Option (Fin k) → K) →ₗ[K] K := LinearMap.proj none
    have hle : Submodule.span K {w | w ∈ kerBasis O (optIdx k) (solveRows O idxR k cols v)} ≤
        LinearMap.ker g := by
      rw [Submodule.span_le]
      intro w hwm
      have := hall w hwm
      simp only [ofField_isZero, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at this
      simpa [g] using this
    have := hle hw0
    simp [g, w0] at this
  · rw [hw]; rfl

end Field


section Stored

variable {K : Type} [Field K] [DecidableEq K] {ι : Type}
    [DecidableEq ι] [Fintype ι]

/-- Augmented solve with intermediate rows stored eagerly. -/
def solveStored (rows : List ι) {k : ℕ} (cols : Fin k → ι → K) (v : ι → K) :
    Option (Fin k → K) :=
  let O := Ops.ofField K
  match (kerBasisStored O (optIdx k) (solveRows O rows k cols v)).find?
      (fun w => !O.isZero (w none)) with
  | none => none
  | some w => some fun c => O.mul (O.inv (w none)) (w (some c))

theorem solveStored_eq (rows : List ι) {k : ℕ} (cols : Fin k → ι → K) (v : ι → K) :
    solveStored rows cols v = solveF (Ops.ofField K) rows k cols v := by
  simp only [solveStored, solveF, kerBasisStored_eq _ (optIdx_complete k)]

theorem solveStored_correct {rows : List ι} (hr : ∀ i, i ∈ rows)
    {k : ℕ} (cols : Fin k → ι → K) (v : ι → K) (c : Fin k → K)
    (h : solveStored rows cols v = some c) : ∑ j, c j • cols j = v := by
  exact solveF_spec hr cols v c ((solveStored_eq rows cols v).symm ▸ h)

theorem solveStored_total (rows : List ι) (hr : ∀ i, i ∈ rows)
    {k : ℕ} (cols : Fin k → ι → K) (v : ι → K)
    (hv : v ∈ Submodule.span K (Set.range cols)) :
    (solveStored rows cols v).isSome := by
  rw [solveStored_eq]
  exact solveF_isSome hr cols v hv

end Stored

#print axioms solveStored_correct
#print axioms solveStored_total

end EvenTI.CellLinearSolve
