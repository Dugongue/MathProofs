import Mathproof.Meta.P15LinAlgKer20261007

/-! The row-system kernel adapter reuses the P15 RREF, orthogonal-complement
kernel proof, and free-column independence argument. The relevant original
sources are P15RecogOps20261007, P15RecogLinAlg20261007, P15LinAlgKer20261007,
P15DecideRefOps20261007, and P15GSSKernelBasis20261007. -/

namespace EvenTI.KernelDonor

open Mathproof.P15RecogOps20261007 Mathproof.P15RecogLinAlg20261007
open Mathproof.P15LinAlgKer20261007 (freeCols mem_freeCols kerVec_free_other perp)

variable {K : Type} [Field K] [DecidableEq K] {ι : Type} [DecidableEq ι]

/-- A row-system basis with one vector per free column of the RREF. -/
def kerBasis {α : Type} (A : Ops α) (idx : List ι) (rows : List (ι → α)) :
    List (ι → α) :=
  Mathproof.P15LinAlgKer20261007.kerBasis A idx (rref A idx rows)

/-- Solutions of all the listed homogeneous row equations. -/
def rowKer [Fintype ι] (rows : List (ι → K)) : Submodule K (ι → K) where
  carrier := {c | ∀ r ∈ rows, ∑ i, r i * c i = 0}
  add_mem' := by
    intro x y hx hy r hr
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    rw [hx r hr, hy r hr, add_zero]
  zero_mem' := by intro r _; simp
  smul_mem' := by
    intro a x hx r hr
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [show ∑ i, r i * (a * x i) = a * ∑ i, r i * x i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hx r hr, mul_zero]

private theorem perp_spanL_eq [Fintype ι] (rows : List (ι → K)) :
    perp (spanL rows) = rowKer rows := by
  classical
  ext x
  change (∀ u ∈ spanL rows, ∑ i, u i * x i = 0) ↔
    (∀ u ∈ rows, ∑ i, u i * x i = 0)
  constructor
  · intro h u hu
    exact h u (Submodule.subset_span hu)
  · intro h u hu
    unfold spanL at hu
    induction hu using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => simp
    | add a b _ _ ha hb => simp [add_mul, Finset.sum_add_distrib, ha, hb]
    | smul a b _ hb => simp [mul_assoc, ← Finset.mul_sum, hb]

theorem kerBasis_spec [Fintype ι] {idx : List ι} (hidx : ∀ i, i ∈ idx) (_hnd : idx.Nodup)
    (rows : List (ι → K)) :
    (∀ v ∈ kerBasis (Ops.ofField K) idx rows, v ∈ rowKer rows) ∧
      Submodule.span K {v | v ∈ kerBasis (Ops.ofField K) idx rows} = rowKer rows := by
  obtain ⟨hP, hB⟩ := rref_spec hidx rows
  have hspan : spanL (kerBasis (Ops.ofField K) idx rows) = rowKer rows := by
    unfold kerBasis
    rw [Mathproof.P15LinAlgKer20261007.kerBasis_spec hidx hP, hB, perp_spanL_eq]
  refine ⟨fun v hv => ?_, hspan⟩
  rw [← hspan]
  exact Submodule.subset_span hv

private theorem freeKernel_independent (bs : List (ι × (ι → K))) (fs : List ι)
    (hnd : fs.Nodup) (hfree : ∀ f ∈ fs, ∀ pb ∈ bs, pb.1 ≠ f) :
    LinearIndependent K (fun j : Fin fs.length => kerVec (Ops.ofField K) bs (fs.get j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hi := congrFun hc (fs.get i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa [kerVec_self] using hi
  · intro j _ hji
    have hne : fs.get i ≠ fs.get j := by
      intro h
      have hij : i = j := (List.Nodup.get_inj_iff hnd).1 h
      exact hji hij.symm
    rw [kerVec_free_other (hfree _ (List.get_mem _ _)) hne, mul_zero]
  · simp

theorem rows_kernel_independent (idx : List ι) (rows : List (ι → K)) (hnd : idx.Nodup) :
    LinearIndependent K (fun j : Fin (kerBasis (Ops.ofField K) idx rows).length =>
      (kerBasis (Ops.ofField K) idx rows).get j) := by
  let bs := rref (Ops.ofField K) idx rows
  let fs := freeCols idx bs
  have hfs : fs.Nodup := hnd.filter _
  have hfree : ∀ f ∈ fs, ∀ pb ∈ bs, pb.1 ≠ f := fun f hf => (mem_freeCols.1 hf).2
  have hli := freeKernel_independent bs fs hfs hfree
  let ee : Fin (kerBasis (Ops.ofField K) idx rows).length ≃ Fin fs.length :=
    finCongr (by simp [kerBasis, Mathproof.P15LinAlgKer20261007.kerBasis, fs, bs])
  have hh := hli.comp ee ee.injective
  convert hh using 1
  funext j
  change (List.map (kerVec (Ops.ofField K) bs) fs).get j =
    kerVec (Ops.ofField K) bs (fs.get (ee j))
  exact List.getElem_map (kerVec (Ops.ofField K) bs)

#print axioms kerBasis_spec
#print axioms rows_kernel_independent

end EvenTI.KernelDonor

