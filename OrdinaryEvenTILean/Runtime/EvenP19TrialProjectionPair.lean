import EvenP19TrialProjectionCall
import EvenP16TrialNativeProjectionMeaning
import EvenP16TrialContractionProducts
import EvenP16AnchorCrossGrid

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 18000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16TrialNative EvenTI.P16Execution
open EvenTI.TrialProducer EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (Written)

def projectionLeftFormWord : String := "even.pair.form.left-to"
def projectionRightFormWord : String := "even.pair.form.right-to"

def projectionLeftWords : ProjectionWords :=
  ⟨crossN,crossStride,contractionTensorWidth,projectionLeftFormWord,contractionLeftBase⟩

def projectionRightWords : ProjectionWords :=
  ⟨crossN,crossStride,contractionTensorWidth,projectionRightFormWord,contractionRightBase⟩

variable {K : Type} [Field K] [Fintype K]

noncomputable def nativeProjectionPair (F : FieldPresentation K) : Com :=
  .seq (nativeProjectionCall F projectionLeftWords) (nativeProjectionCall F projectionRightWords)

private noncomputable def sampleField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem projectionArgumentsSurvive (F : FieldPresentation K) :
    ∀ r ∈ projectionRightWords.regs ++ [dT,dU,dZ],
        r ∉ scalarWrites (nativeProjectionCall F projectionLeftWords) := by
  change ∀ r ∈ projectionRightWords.regs ++ [dT,dU,dZ],
        r ∉ scalarWrites (nativeProjectionCall sampleField projectionLeftWords)
  decide

private theorem width_split {d n : ℕ} (i : Fin (d+1)) :
    (n^i.val*n)*n^(d-i.val)=n^(d+1) := by
  rw [← pow_succ, ← pow_add]
  congr 1
  omega

private theorem pairProjectionRead {d n : ℕ}
    (i : Fin (d+1)) (hn : 0<n) (ell : Coord (d+1) n → K) (read out : ℕ → K)
    (hRead : ∀ (x : Fin (n^(d+1))), read x.val = ell ((inputCoordOrder n (d+1)).symm x))
    (hOut : ∀ x < n*n, ∀ y < n^(d+1), out (x*n^(d+1)+y) =
      if x/n=y/n^(d-i.val)%n then read (changedDigit n (n^(d-i.val)) y (x%n)) else 0) :
    ∀ (u : Fin (n*n)) (x : Fin (n^(d+1))), out (u.val*n^(d+1)+x.val) =
      projectionCoefficients (rawRetainedProjection i ell) (finProdFinEquiv.symm u)
        ((inputCoordOrder n (d+1)).symm x) := by
  intro u x
  let uv := finProdFinEquiv.symm u
  have hu : uv.1.val*n+uv.2.val=u.val := by
    simpa [uv,finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply u)
  have hm := nativeProjectionGrid_meaning i hn ell read out
    (fun w => (hRead _).trans (congrArg ell ((inputCoordOrder n (d+1)).symm_apply_apply w))) hOut
    uv.1 uv.2 ((inputCoordOrder n (d+1)).symm x)
  rwa [hu,(inputCoordOrder n (d+1)).apply_symm_apply] at hm

/-- Materialize the left and right projection coefficient banks consecutively
from the original-coordinate form banks. Both installed matrices are
available in the same final state and the raw banks below them are preserved. -/
theorem nativeProjectionPair_run (F : FieldPresentation K)
    {d n z a b ls rs tt uu S B : ℕ} {σ : Env} (i : Fin (d+1))
    (ell rho : Coord (d+1) n → K) (hn : 0<n) (hWide : 2*n<B)
    (hRows : n*n+1<B) (hCols : n^(d+1)+1<B)
    (hLeft : ls+n^(d+1)≤a) (hRight : rs+n^(d+1)≤a)
    (hAB : a+(n*n)*n^(d+1)≤b) (hBT : b+(n*n)*n^(d+1)≤tt) (hBU : b+(n*n)*n^(d+1)≤uu)
    (ht : tt<S) (hu : uu<S) (htu : tt≠uu) (hz : z+1<a)
    (hS : Slots F canonical qN.WS S B σ)
    (hzv : val F canonical qN.WS σ z=0) (hov : val F canonical qN.WS σ (z+1)=1)
    (hT : σ.vars dT=tt) (hU : σ.vars dU=uu) (hZ : σ.vars dZ=z)
    (hWidth : σ.vars crossN=n) (hStride : σ.vars crossStride=n^(d-i.val))
    (hColumns : σ.vars contractionTensorWidth=n^(d+1)) (hL : σ.vars contractionLeftBase=a)
    (hR : σ.vars contractionRightBase=b) (hLs : σ.vars projectionLeftFormWord=ls)
    (hRs : σ.vars projectionRightFormWord=rs)
    (hReadL : ∀ x : Fin (n^(d+1)), val F canonical qN.WS σ (ls+x.val)=ell ((inputCoordOrder n (d+1)).symm x))
    (hReadR : ∀ x : Fin (n^(d+1)), val F canonical qN.WS σ (rs+x.val)=rho ((inputCoordOrder n (d+1)).symm x)) :
    ∃ τ, Run B (nativeProjectionPair F) σ τ
      (2*(17+nativeProjectionGridCost F n (n^(d-i.val)) (n^i.val))) ∧
      Slots F canonical qN.WS S B τ ∧
      (∀ (u : Fin (n*n)) (x : Fin (n^(d+1))),
        val F canonical qN.WS τ (a+(u.val*n^(d+1)+x.val))=projectionCoefficients (rawRetainedProjection i ell)
          (finProdFinEquiv.symm u) ((inputCoordOrder n (d+1)).symm x)) ∧
      (∀ (u : Fin (n*n)) (x : Fin (n^(d+1))),
        val F canonical qN.WS τ (b+(u.val*n^(d+1)+x.val))=projectionCoefficients (rawRetainedProjection i rho)
          (finProdFinEquiv.symm u) ((inputCoordOrder n (d+1)).symm x)) ∧
      (∀ k < a, val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
  let s := n^(d-i.val)
  let p := n^i.val
  have hWidthEq : (p*n)*s=(n^(d+1)) := width_split i
  have hM : (n^(d+1))+1<B := hCols
  have hSp : 0<s := pow_pos hn _
  have hPp : 0<p := pow_pos hn _
  have keepLow {x t : ℕ} (hk : x < a) (ha : a≤t) : ¬ Written t (n*n) (n^(d+1)) tt uu x := by
    unfold Written
    omega
  obtain ⟨μ,rL,hμ,vL,fL,_,_,iL,oL⟩ := nativeProjectionCall_run F projectionLeftWords
    (p:=p) (by decide) hn hSp hPp hWide hRows
    (by rw [hWidthEq]; exact hM) (by rw [hWidthEq]; exact hLeft)
    (by rw [hWidthEq]; omega) ht hu htu (by rw [hWidthEq]; omega) (by rw [hWidthEq]; omega)
    (by omega) (by rw [hWidthEq]; exact keepLow (by omega) (le_refl _))
    (by rw [hWidthEq]; exact keepLow hz (le_refl _))
    hS hzv hov hT hU hZ hWidth hStride (hColumns.trans hWidthEq.symm) hLs hL
  rw [hWidthEq] at vL fL
  have μKeep (k : ℕ) (hk : k<a) : val F canonical qN.WS μ k=val F canonical qN.WS σ k :=
    fL k (by omega) (keepLow hk (le_refl _))
  have keepArg {r : String} {v : ℕ} (h : σ.vars r=v)
      (hr : r ∈ projectionRightWords.regs ++ [dT,dU,dZ]) : μ.vars r=v :=
    ((Frame.of_run rL).vars r (projectionArgumentsSurvive F r hr)).trans h
  obtain ⟨τ,rR,hτ,vR,fR,_,_,iR,oR⟩ := nativeProjectionCall_run F projectionRightWords
    (p:=p) (by decide) hn hSp hPp hWide hRows
    (by rw [hWidthEq]; exact hM) (by rw [hWidthEq]; omega)
    (by rw [hWidthEq]; omega) ht hu htu (by rw [hWidthEq]; exact hBT) (by rw [hWidthEq]; exact hBU)
    (by omega) (by rw [hWidthEq]; exact keepLow (by omega) (by omega))
    (by rw [hWidthEq]; exact keepLow hz (by omega))
    hμ ((μKeep _ (by omega)).trans hzv) ((μKeep _ hz).trans hov)
    (keepArg hT (by decide)) (keepArg hU (by decide)) (keepArg hZ (by decide))
    (keepArg hWidth (by decide)) (keepArg hStride (by decide))
    ((keepArg hColumns (by decide)).trans hWidthEq.symm) (keepArg hRs (by decide)) (keepArg hR (by decide))
  rw [hWidthEq] at vR fR
  have hL' := pairProjectionRead i hn ell (fun k => val F canonical qN.WS σ (ls+k))
    (fun k => val F canonical qN.WS μ (a+k)) hReadL vL
  have hR' := pairProjectionRead i hn rho (fun k => val F canonical qN.WS μ (rs+k))
    (fun k => val F canonical qN.WS τ (b+k))
    (fun x => (μKeep _ (by have := x.isLt; omega)).trans (hReadR x)) vR
  refine ⟨τ,(by simpa only [two_mul,s,p,nativeProjectionPair] using rL.seq rR),hτ,?_,hR',?_,iR.trans iL,oR.trans oL⟩
  · intro u x
    have hRow : u.val*(n^(d+1))+x.val < (n*n)*(n^(d+1)) := by
      have h := Nat.mul_le_mul_right (n^(d+1)) (show u.val+1≤n*n by have := u.isLt; omega)
      simp only [Nat.add_mul,one_mul] at h
      have := x.isLt
      omega
    rw [fR _ (by omega) (by unfold Written; omega)]
    exact hL' u x
  · intro k hk
    exact (fR _ (by omega) (keepLow hk (by omega))).trans (μKeep k hk)

theorem nativeProjectionGridCost_fixed (F : FieldPresentation K) {d n : ℕ} (i : Fin (d+1)) :
    nativeProjectionGridCost F n (n^(d-i.val)) (n^i.val) =
      nativeProjectionGridCost F n (n^d) 1 := by
  unfold nativeProjectionGridCost
  rw [width_split i,one_mul,←pow_succ']

#print axioms nativeProjectionPair_run
end EvenTI.P19Trial
