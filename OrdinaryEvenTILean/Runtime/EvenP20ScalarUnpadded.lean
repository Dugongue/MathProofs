import EvenP8HomogeneousBase
import EvenP8OrdinaryLift

namespace EvenTI.P20Scalar.Unpadded

open Matrix EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.CellPreparation
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment

set_option maxHeartbeats 300000

section Regular
variable {K : Type} [Field K] {d : ℕ} {width : Fin d → ℕ}
  {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
  (t : ∀ i v, WordTable K (D i v))
  (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
  (hOne : ∀ i v, P i v (t i v).one = 1)
  (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)

include hOne hMul in
theorem liveActionMatrix_scalar (i : Fin d) (c : K) :
    liveActionMatrix t P i (fun v => c • (1 : X i v)) = c • 1 := by
  let T := blockTable (t i)
  let E := blockDecode (P i)
  have h := blockTable_model (t i) (P i) (hOne i) (hMul i)
  letI : WordTable.Laws T := WordTable.laws_of_model _ E h.1 h.2
  have he : E.symm (fun v => c • (1 : X i v)) = c • T.one := by
    apply E.injective
    rw [E.apply_symm_apply, E.map_smul, h.1]
    rfl
  change wordMulMatrix T (E.symm (fun v => c • (1 : X i v))) = _
  rw [he]
  ext r s
  change T.multiply (c • T.one) (Pi.single s 1) r = (c • (1 : Matrix _ _ K)) r s
  rw [WordTable.Laws.smul_mul, WordTable.Laws.one_mul]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

include hOne hMul in
theorem liveActionMatrix_scalar_iff (i : Fin d) (a : ∀ v, X i v) (c : K) :
    liveActionMatrix t P i a = c • 1 ↔ ∀ v, a v = c • (1 : X i v) := by
  rw [← liveActionMatrix_scalar t P hOne hMul i c]
  change liveMatrixHom t P hOne hMul i a =
    liveMatrixHom t P hOne hMul i (fun v => c • (1 : X i v)) ↔ _
  rw [(liveMatrixHom_injective t P hOne hMul i).eq_iff]
  exact ⟨fun h v => congrFun h v, fun h => funext h⟩
end Regular

section Coordinates
variable {K A B : Type} [Field K] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

theorem transport_scalar_iff (e : A ≃ B) (G : (Matrix A A K)ˣ) (c : K) :
    (transportMatrixUnit e G).val = c • 1 ↔ G.val = c • 1 := by
  change (Matrix.reindexAlgEquiv K K e) G.val = c • 1 ↔ _
  rw [← map_one (Matrix.reindexAlgEquiv K K e),
    ← map_smul (Matrix.reindexAlgEquiv K K e) c (1 : Matrix A A K)]
  exact (Matrix.reindexAlgEquiv K K e).injective.eq_iff

theorem conjugate_scalar_iff (U G : (Matrix A A K)ˣ) (c : K) :
    (U * G * U⁻¹).val = c • 1 ↔ G.val = c • 1 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix A A K => U.inv * M * U.val) h
    simpa [mul_assoc] using he
  · intro h
    change U.val * G.val * U.inv = c • 1
    rw [h]
    simp [mul_assoc]
end Coordinates

section Native
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p))
  [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]

local instance localLaws (p) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance localField (p) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

/-- All native blocks are tested in a full mode; unknown chart coefficients cancel.
This does not apply to a nontrivial order-four rectangular crop. -/
theorem recoverTrialSites_scalar_iff (hw : ∀ p, (m p).n = w.width p)
    (U : ModeUnits K (fun i => Fin (ModeSize w m i)))
    (x : BranchAssignment w m) (i : Fin (w.sites + 2)) (c : K) :
    (recoverTrialSites w m h hw U U x i).val = c • 1 ↔
      ∀ v, (branchOccurrenceUnits w m x i v).val = c • 1 := by
  unfold recoverTrialSites
  rw [transport_scalar_iff, conjugate_scalar_iff]
  unfold recoveredChartUnits
  rw [transport_scalar_iff]
  change liveActionMatrix (branchTables w m) (branchDecode w m) i
    (fun v => (branchOccurrenceUnits w m x i v).val) = c • 1 ↔ _
  exact liveActionMatrix_scalar_iff (branchTables w m) (branchDecode w m)
    (fun _ _ => wordDecode_one _) (fun _ _ a b => wordDecode_mul _ a b) i _ c
end Native

section Ordinary
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
  (o : Fin ((l+1)+(l+1)) ≃ Fin ((l+1)+(l+1))) (T S : Dense K l n)

/-- The reciprocal and higher singular recovery only permutes complete matrices. -/
theorem recoverOrdinaryChanges_scalar_iff (G : OrdinarySiteUnits o T S) :
    (∀ j, ∃ c : K, (recoverOrdinaryChanges o T S G j).val = c • 1) ↔
      ∀ i, ∃ c : K, (G i).val = c • 1 := by
  constructor
  · intro h i
    obtain ⟨c,hc⟩ := h (((ordinarySiteOrder l).trans o) i)
    refine ⟨c,?_⟩
    change (G (((ordinarySiteOrder l).trans o).symm (((ordinarySiteOrder l).trans o) i))).val = c • 1 at hc
    have hi := ((ordinarySiteOrder l).trans o).symm_apply_apply i
    exact hi ▸ hc
  · intro h j
    exact h (((ordinarySiteOrder l).trans o).symm j)
end Ordinary

#print axioms liveActionMatrix_scalar_iff
#print axioms recoverTrialSites_scalar_iff
#print axioms recoverOrdinaryChanges_scalar_iff
end EvenTI.P20Scalar.Unpadded
