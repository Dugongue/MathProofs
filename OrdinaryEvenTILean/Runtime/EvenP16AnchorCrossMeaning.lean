import EvenP16AnchorCrossGrid

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P15Execution
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

def contractedCoords (l n : ℕ) : Fin (n^l*n^l) ≃ Coord l n × Coord l n :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (inputCoordOrder n l).symm (inputCoordOrder n l).symm)

private theorem contractedCoords_indices (l n : ℕ) (k : Fin (n^l*n^l)) :
    (inputCoordOrder n l (contractedCoords l n k).1).val = k.val/(n^l) ∧
    (inputCoordOrder n l (contractedCoords l n k).2).val = k.val%(n^l) := by
  simp only [contractedCoords,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,Equiv.apply_symm_apply]
  exact ⟨rfl,rfl⟩

private theorem crossLeftCoord (l n : ℕ) (hn : 0 < n) (p : Fin (n*n)) (k : Fin (n^l*n^l)) :
    crossLeftIndex n (n^l) p.val k.val = (inputCoordOrder n (l+1)
      (retainedMode 0 ((finProdFinEquiv.symm p).1,(contractedCoords l n k).1))).val := by
  rw [inputCoord_retained n l hn]
  have hc := contractedCoords_indices l n k
  have hv : k.val / (n^l) < n^l := Nat.div_lt_of_lt_mul k.isLt
  simp only [Fin.val_zero,Nat.sub_zero,insertWordIndex,hc.1,Nat.div_eq_of_lt hv,Nat.mod_eq_of_lt hv,
    Nat.zero_mul,Nat.zero_add,crossLeftIndex]
  rfl

private theorem crossRightCoord (l n : ℕ) (hn : 0 < n) (m : Fin (l+1))
    (p : Fin (n*n)) (k : Fin (n^l*n^l)) :
    crossRightIndex n (n^l) (n^(l-m.val)) p.val k.val = (inputCoordOrder n (l+1)
      (retainedMode m ((finProdFinEquiv.symm p).2,(contractedCoords l n k).2))).val := by
  rw [inputCoord_retained n l hn,(contractedCoords_indices l n k).2]
  rfl

/-- Interpret an installed cut bank in the exact public coordinate order of
its original tensor. This works both for the cut and its reciprocal. -/
def InstalledCutMatrix (F : FieldPresentation K) (s : Env) (l n base : ℕ)
    (M : Matrix (Coord (l+1) n) (Coord (l+1) n) K) : Prop :=
  ∀ x y, val F canonical qN.WS s (base+((inputCoordOrder n (l+1) x).val*(n*n^l)+(inputCoordOrder n (l+1) y).val)) = M x y

private theorem readFront (F : FieldPresentation K) {l n base : ℕ} {s : Env}
    (hn : 0 < n) (mode : HigherModes l) (p : Fin (n*n)) (k : Fin (n^l*n^l))
    (A : Matrix (Coord (l+1) n) (Coord (l+1) n) K) (h : InstalledCutMatrix F s l n base A) :
    val F canonical qN.WS s (crossFrontIndex mode.1 n (n^l) (n^(l-mode.2.val)) base p.val k.val) =
      reciprocalFront A mode (finProdFinEquiv.symm p) (contractedCoords l n k) := by
  obtain ⟨b,i⟩ := mode
  unfold crossFrontIndex
  rw [crossLeftCoord l n hn,crossRightCoord l n hn]
  cases b <;> apply h

private theorem readBack (F : FieldPresentation K) {l n base : ℕ} {s : Env}
    (hn : 0 < n) (mode : HigherModes l) (p : Fin (n*n)) (k : Fin (n^l*n^l))
    (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K) (h : InstalledCutMatrix F s l n base N) :
    val F canonical qN.WS s (crossBackIndex mode.1 n (n^l) (n^(l-mode.2.val)) base p.val k.val) =
      reciprocalBack N mode (contractedCoords l n k) (finProdFinEquiv.symm p) := by
  obtain ⟨b,i⟩ := mode
  unfold crossBackIndex
  rw [crossLeftCoord l n hn,crossRightCoord l n hn]
  cases b <;> apply h

/-- The numerical dot grid on the two actual installed banks coincides with
the crossed contraction in the reciprocal anchor theorem. -/
theorem crossedSum_eq_panels (F : FieldPresentation K) {l n src inv : ℕ} {s : Env}
    (hn : 0 < n) (mode : HigherModes l) (i j : Fin (n*n))
    (A N : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (hA : InstalledCutMatrix F s l n src A) (hN : InstalledCutMatrix F s l n inv N) :
    (∑ k ∈ Finset.range (n^l*n^l),
      val F canonical qN.WS s (crossFrontIndex mode.1 n (n^l) (n^(l-mode.2.val)) src i.val k) *
      val F canonical qN.WS s (crossBackIndex mode.1 n (n^l) (n^(l-mode.2.val)) inv j.val k)) =
      (reciprocalFront A mode * reciprocalBack N mode) (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) := by
  rw [←Fin.sum_univ_eq_sum_range,Matrix.mul_apply]
  calc
    _ = ∑ k : Fin (n^l*n^l), reciprocalFront A mode (finProdFinEquiv.symm i) (contractedCoords l n k) *
        reciprocalBack N mode (contractedCoords l n k) (finProdFinEquiv.symm j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [readFront F hn mode i k A hA,readBack F hn mode j k N hN]
    _ = _ := (contractedCoords l n).sum_comp (fun k : Coord l n × Coord l n =>
      reciprocalFront A mode (finProdFinEquiv.symm i) k * reciprocalBack N mode k (finProdFinEquiv.symm j))

#print axioms crossedSum_eq_panels
end EvenTI.P16Execution