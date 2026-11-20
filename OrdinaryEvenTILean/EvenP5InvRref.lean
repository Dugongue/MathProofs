import EvenP5KernelCore

/-! Materialized evaluation of the checked RREF and row-kernel programs.
Every elimination writes a finite row before the next step reads it. -/

namespace EvenTI.Contract

open Mathproof.P15RecogOps20261007 EvenTI.KernelDonor

variable {α ι : Type} [DecidableEq ι]

private theorem lookup_of_mem (f : ι → α) (d : α) (i : ι) {idx : List ι} (hi : i ∈ idx) :
    (((idx.map fun j => (j, f j)).findSome? fun p => if p.1 = i then some p.2 else none).getD d) = f i := by
  induction idx with
  | nil => simp at hi
  | cons j idx ih =>
    by_cases h : j = i
    · simp [h]
    · simp [h, ih (List.mem_cons.mp hi |>.resolve_left (Ne.symm h))]

/-- Evaluate all entries of a row, with the resulting table shared by its readers. -/
def storeRow (A : Ops α) (idx : List ι) (v : ι → α) : ι → α :=
  let table := idx.map fun i => (i, v i)
  fun i => (table.findSome? fun p => if p.1 = i then some p.2 else none).getD A.zero

theorem storeRow_eq (A : Ops α) {idx : List ι} (hidx : ∀ i, i ∈ idx) (v : ι → α) :
    storeRow A idx v = v := by
  funext i
  exact lookup_of_mem v A.zero i (hidx i)

private def reduceStored (A : Ops α) (idx : List ι)
    (bs : List (ι × (ι → α))) (v : ι → α) : ι → α :=
  bs.foldl (fun u pb => storeRow A idx (axpy A u (u pb.1) pb.2)) v

private theorem reduceStored_eq (A : Ops α) {idx : List ι} (hidx : ∀ i, i ∈ idx)
    (bs : List (ι × (ι → α))) (v : ι → α) : reduceStored A idx bs v = reduceBy A bs v := by
  simp only [reduceStored, reduceBy, storeRow_eq A hidx]

private def insertStored (A : Ops α) (idx : List ι)
    (bs : List (ι × (ι → α))) (v : ι → α) : List (ι × (ι → α)) :=
  let r := reduceStored A idx bs v
  match firstNZ A idx r with
  | none => bs
  | some p =>
    let w := storeRow A idx (smul A (A.inv (r p)) r)
    bs.map (fun pb => (pb.1, storeRow A idx (axpy A pb.2 (pb.2 p) w))) ++ [(p, w)]

private theorem insertStored_eq (A : Ops α) {idx : List ι} (hidx : ∀ i, i ∈ idx)
    (bs : List (ι × (ι → α))) (v : ι → α) : insertStored A idx bs v = insertVec A idx bs v := by
  simp only [insertStored, insertVec, reduceStored_eq A hidx, storeRow_eq A hidx]
  cases firstNZ A idx (reduceBy A bs v) <;> rfl

/-- RREF with a fresh stored row after every elimination. -/
def rrefStored (A : Ops α) (idx : List ι) (rows : List (ι → α)) : List (ι × (ι → α)) :=
  rows.foldl (insertStored A idx) []

theorem rrefStored_eq (A : Ops α) {idx : List ι} (hidx : ∀ i, i ∈ idx) (rows : List (ι → α)) :
    rrefStored A idx rows = rref A idx rows := by
  unfold rrefStored rref
  have h : insertStored A idx = insertVec A idx := by funext bs v; exact insertStored_eq A hidx bs v
  rw [h]

/-- The checked full kernel basis, evaluated with stored elimination rows. -/
def kerBasisStored (A : Ops α) (idx : List ι) (rows : List (ι → α)) : List (ι → α) :=
  let gs := rrefStored A idx rows
  (idx.filter fun c => !(gs.any fun pb => decide (pb.1 = c))).map (kerVec A gs)

theorem kerBasisStored_eq (A : Ops α) {idx : List ι} (hidx : ∀ i, i ∈ idx) (rows : List (ι → α)) :
    kerBasisStored A idx rows = kerBasis A idx rows := by
  simp only [kerBasisStored, kerBasis, Mathproof.P15LinAlgKer20261007.kerBasis,
    Mathproof.P15LinAlgKer20261007.freeCols, rrefStored_eq A hidx]

#print axioms rrefStored_eq
#print axioms kerBasisStored_eq

end EvenTI.Contract
