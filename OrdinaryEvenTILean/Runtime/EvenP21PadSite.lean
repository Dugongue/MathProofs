import EvenP21PadNative
import EvenP8OrderFourHomogeneous

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 20000

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.CellPreparation EvenTI.CellProducer EvenTI.LiveAlgebra EvenTI.P16Recover
open EvenTI.P20Pad
open Mathproof.Problem18IMPMatrixMemory20261001 (index_lt)

section InverseBank

variable {width : ℕ}

def inverseAddress (r c : Fin width) : ℕ := r.val*width+c.val

theorem inverseAddress_lt (r c : Fin width) : inverseAddress r c < width*width := index_lt r c

def inverseRow (hw : 0 < width) (k : Fin (width*width)) : Fin width :=
  ⟨k.val/width,(Nat.div_lt_iff_lt_mul hw).mpr k.isLt⟩

def inverseCol (hw : 0 < width) (k : Fin (width*width)) : Fin width :=
  ⟨k.val%width,Nat.mod_lt _ hw⟩

theorem inverseAddress_indices (hw : 0 < width) (k : Fin (width*width)) :
    inverseAddress (inverseRow hw k) (inverseCol hw k)=k.val := by
  unfold inverseAddress inverseRow inverseCol
  simp only [Nat.mul_comm]
  exact Nat.div_add_mod _ _

theorem inverseAddress_row (hw : 0 < width) (r c : Fin width) :
    inverseRow hw ⟨inverseAddress r c,inverseAddress_lt r c⟩=r := by
  apply Fin.ext
  change (r.val*width+c.val)/width=r.val
  rw [Nat.mul_comm r.val width,Nat.mul_add_div hw,Nat.div_eq_of_lt c.isLt,Nat.add_zero]

theorem inverseAddress_col (r c : Fin width) : inverseAddress r c%width=c.val := by
  have h : r.val*width%width=0 := Nat.mul_mod_left r.val width
  change (r.val*width+c.val)%width=c.val
  rw [Nat.add_mod,h,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt c.isLt]

def inverseBankSite {s n : ℕ} {C : Fin s → Type}
    (hw : 0 < width) (e : (Σ v, C v) ≃ Fin width) (site : Fin s → Fin n)
    (k : Fin (width*width)) : Fin n := site (e.symm (inverseRow hw k)).1

theorem inverseBankSite_words {s n : ℕ} {C : Fin s → Type}
    (hw : 0 < width) (e : (Σ v, C v) ≃ Fin width) (site : Fin s → Fin n)
    (bank : List ℕ) (hBank : ∀ r : Fin width, bank.getD r.val 0=(site (e.symm r).1).val)
    (k : Fin (width*width)) :
    bank.getD (k.val/width) 0=(inverseBankSite hw e site k).val :=
  hBank (inverseRow hw k)

variable {K : Type} [Field K]

def inverseBlockSupported {s : ℕ} {C : Fin s → Type}
    (right : Bool) (cutoff : ℕ) (e : (Σ v, C v) ≃ Fin width)
    (P : Matrix (Fin width) (Fin width) K) (v : Fin s) : Prop :=
  ∃ (r : C v) (c : Fin width), columnKept right cutoff c.val=true ∧ P (e ⟨v,r⟩) c≠0

variable [Fintype K]

/-- The installed label chart can be the inverse gauge itself. The row
length is the padded width, and a row inherits the CRT slot of its
actual numbered native block. -/
theorem inverseBankMask_test {s n M : ℕ} {C : Fin s → Type}
    (hw : 0 < width) (D : FieldEncoding K) (right : Bool) (cutoff : ℕ)
    (e : (Σ v, C v) ≃ Fin width) (P : Matrix (Fin width) (Fin width) K)
    (chart : List ℕ) (site : Fin s → Fin n) (reference : Fin n) (z : Fin n → ZMod M)
    (hChart : ∀ r c, chart.getD (inverseAddress r c) 0=(D (P r c)).val) :
    maskedResidueTest right width cutoff chart (D 0).val (inverseBankSite hw e site) reference z=true ↔
      ∀ v, inverseBlockSupported right cutoff e P v → (z (site v)).val=(z reference).val := by
  simp only [maskedResidueTest,decide_eq_true_eq]
  constructor
  · intro h v hv
    obtain ⟨r,c,hKeep,hEntry⟩ := hv
    let row := e ⟨v,r⟩
    let k : Fin (width*width) := ⟨inverseAddress row c,inverseAddress_lt row c⟩
    have hCol : k.val%width=c.val := inverseAddress_col row c
    have hLabel : chart.getD k.val 0≠(D 0).val := by
      change chart.getD (inverseAddress row c) 0≠_
      rw [hChart]
      exact fun he => hEntry (D.injective (Fin.ext he))
    have hAnswer := h k (by rw [hCol]; exact hKeep) hLabel
    simpa only [inverseBankSite,k,inverseAddress_row,row,Equiv.symm_apply_apply] using hAnswer
  · intro h k hKeep hNZ
    let r := inverseRow hw k
    let c := inverseCol hw k
    have hLabel : chart.getD k.val 0=(D (P r c)).val := by
      rw [←inverseAddress_indices hw k]
      exact hChart r c
    have hEntry : P r c≠0 := by
      intro he
      exact hNZ (by rwa [he] at hLabel)
    have hBlock : inverseBlockSupported right cutoff e P (e.symm r).1 :=
      ⟨(e.symm r).2,c,hKeep,by simpa only [Sigma.eta,Equiv.apply_symm_apply] using hEntry⟩
    exact h _ hBlock

end InverseBank

section ActualPadding

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

theorem inverseBlockSupported_iff {s : ℕ} {C : Fin s → ℕ}
    (ell rho : Coord 2 n → K) (i : Fin (2+2))
    (e : (Σ v, Fin (C v)) ≃ Fin (fourRecoveryWidth ell rho i))
    (V : Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)
    (v : Fin s) :
    (∃ (r : Fin (C v)) (j : Fin n),
      ((V*sourcePadNumeric ell rho i).submatrix e id) ⟨v,r⟩ j≠0) ↔
    inverseBlockSupported (fourSiteOrder i).2 (siteCutoff ell rho i) e V v := by
  let X : Matrix (Fin (C v)) (Fin (fourRecoveryWidth ell rho i)) K :=
    V.submatrix (fun r => e ⟨v,r⟩) id
  have hM : X*sourcePadNumeric ell rho i =
      (V*sourcePadNumeric ell rho i).submatrix (fun r => e ⟨v,r⟩) id :=
    Matrix.submatrix_mul_equiv V (sourcePadNumeric ell rho i)
      (fun r => e ⟨v,r⟩) (Equiv.refl _) id
  have hN : (∃ (r : Fin (C v)) (j : Fin n),
      ((V*sourcePadNumeric ell rho i).submatrix e id) ⟨v,r⟩ j≠0) ↔
      X*sourcePadNumeric ell rho i≠0 := by
    rw [hM]
    constructor
    · intro hh hZero
      obtain ⟨r,j,hr⟩ := hh
      exact hr (congrFun (congrFun hZero r) j)
    · intro hNonzero
      by_contra! hz
      apply hNonzero
      ext r j
      exact hz r j
  exact hN.trans (sourcePadNumeric_nonzero_iff ell rho i X)

theorem exists_supportedInverseEntry
    (ell rho : Coord 2 n → K) (i : Fin (2+2)) (hn : 0 < n)
    (U : (Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin (fourRecoveryWidth ell rho i)) K)ˣ) :
    ∃ (r c : Fin (fourRecoveryWidth ell rho i)),
      columnKept (fourSiteOrder i).2 (siteCutoff ell rho i) c.val=true ∧ U.inv r c≠0 := by
  apply (sourcePadNumeric_nonzero_iff ell rho i U.inv).mp
  intro hZero
  let P := sourcePadNumeric ell rho i
  have hp : P=0 := by
    have h := congrArg (fun M => U.val*M) hZero
    change U.val*(U.inv*P)=U.val*0 at h
    rwa [←Matrix.mul_assoc,U.val_inv,Matrix.one_mul,Matrix.mul_zero] at h
  have hLeft := targetCropNumeric_sourcePad_left ell rho i
  change targetCropNumeric ell rho ell rho rfl rfl i * P = 1 at hLeft
  rw [hp,Matrix.mul_zero] at hLeft
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact zero_ne_one hLeft

end ActualPadding

#print axioms inverseBankMask_test
#print axioms inverseBlockSupported_iff
#print axioms exists_supportedInverseEntry
end EvenTI.P21Pad
