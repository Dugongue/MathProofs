import EvenP15ScalarLoadedMatrix
import Mathproof.Meta.Problem18P36BoundaryRoutedController20261003

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace EvenTI.P17Scalar

open EvenTI.P15Scalar
open EvenTI.Contract EvenTI.P15Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)
open Mathproof.Problem18P34AssemblyMatrixMemory20261003 (matrix_congr)
open Mathproof.Problem18P36BoundaryRoutedController20261003
  (renameCom renameEnv renameEnv_vars renameEnv_arrs renameEnv_symm rename_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def scalarScratchBank : String := "even.scalar.scratch"

def scalarScratchSwap : String ≃ String := Equiv.swap "data" scalarScratchBank

private theorem scalarScratchSwap_data : scalarScratchSwap "data" = scalarScratchBank := by
  simp [scalarScratchSwap]

private theorem scalarScratchSwap_mem : scalarScratchSwap canonical.mem = canonical.mem := by decide
private theorem scalarScratchSwap_scratch : scalarScratchSwap canonical.scratch = canonical.scratch := by decide

private theorem scalarScratchSlots {F : FieldPresentation K} {ws : String} {S B : ℕ} {s : Env}
    (h : Slots F canonical ws S B s) :
    Slots F canonical ws S B (renameEnv scalarScratchSwap.symm s) := by
  let u := renameEnv scalarScratchSwap.symm s
  have hm : u.arrs canonical.mem = s.arrs canonical.mem := by
    change s.arrs (scalarScratchSwap canonical.mem) = _
    rw [scalarScratchSwap_mem]
  have hs : u.arrs canonical.scratch = s.arrs canonical.scratch := by
    change s.arrs (scalarScratchSwap canonical.scratch) = _
    rw [scalarScratchSwap_scratch]
  obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩,hws,hfit,ha,hc,hsw⟩ := h
  refine ⟨⟨h1,h2,h3,h4,h5,?_,?_,?_,?_,?_,h11,h12⟩,hws,?_,ha,?_,hsw⟩
  · rw [hm]; exact h6
  · rw [hs]; exact h7
  · rw [hs]; exact h8
  · rw [hm]; exact h9
  · intro j
    rw [hm]
    exact h10 j
  · rw [hm]
    exact hfit
  · intro p hp j
    change (u.arrs canonical.mem).getD (s.vars ws+p*F.e+j.val) 0 < F.p
    rw [hm]
    exact hc p hp j

noncomputable def routedLoadedMatrixScalar (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) : Com :=
  renameCom scalarScratchSwap (loadedMatrixScalar D F ws)

/-- The checked scalar consumer can occupy separate scratch memory while
the raw prepared request stays in its original data bank. Array renaming
is a compile-time operation and preserves the exact run cost. -/
theorem routedLoadedMatrixScalar_run (D : FieldEncoding K) (F : FieldPresentation K)
    {ws : String} {W S a n : ℕ} {s : Env} (M : Matrix (Fin n) (Fin n) K)
    (hS : Slots F canonical ws S W s)
    (hWS : labelAddress ≠ ws ∧ scalarLabelDest ≠ ws ∧ scalarCopyIndex ≠ ws)
    (hn : 0 < n) (hQ : Fintype.card K ≤ W) (hP : F.p < W)
    (hA : s.vars scalarCopySource = a) (hD : s.vars scalarCopyTarget = 0)
    (hM : s.vars scalarCopyLength = n*n) (hN : s.vars scalarLoadedDim=n)
    (hRead : a+n*n ≤ S) (hMat : matrix F s (s.vars ws+a*F.e) n n = M)
    (hLen : (s.arrs scalarScratchBank).length = n*n+1) (hW : n*n+1 < W)
    (hSent : (s.arrs scalarScratchBank).getD (n*n) 0 = 0) :
    ∃ t, Run W (routedLoadedMatrixScalar D F ws) s t
      (installScalarLabelsCost F (n*n)+60*(n*n)+30) ∧
      (t.vars "good" = 1 ↔ M = M ⟨0,hn⟩ ⟨0,hn⟩ • (1 : Matrix (Fin n) (Fin n) K)) ∧
      t.vars "good" < W ∧
      (∀ k, k ≠ scalarScratchBank → t.arrs k=s.arrs k) ∧ t.inp=s.inp ∧ t.out=s.out := by
  let u := renameEnv scalarScratchSwap.symm s
  have hData : u.arrs "data" = s.arrs scalarScratchBank := by
    change s.arrs (scalarScratchSwap "data") = _
    rw [scalarScratchSwap_data]
  have ruMat : matrix F u (u.vars ws+a*F.e) n n = M := by
    calc
      matrix F u (u.vars ws+a*F.e) n n = matrix F s (s.vars ws+a*F.e) n n := by
        apply matrix_congr F s u
        intro j hj
        change (s.arrs (scalarScratchSwap canonical.mem)).getD _ 0 =
          (s.arrs canonical.mem).getD _ 0
        rw [scalarScratchSwap_mem]
      _ = M := hMat
  obtain ⟨v,r,hScalar,hGood,hArr,hIn,hOut⟩ := loadedMatrixScalar_run D F (s:=u) M
    (scalarScratchSlots hS) hWS hn hQ hP hA hD hM hN hRead ruMat
    (by rwa [hData]) hW (by rwa [hData])
  let t := renameEnv scalarScratchSwap v
  have hBack : renameEnv scalarScratchSwap u = s := renameEnv_symm scalarScratchSwap.symm s
  have rr : Run W (routedLoadedMatrixScalar D F ws) s t
      (installScalarLabelsCost F (n*n)+60*(n*n)+30) := by
    have hr := rename_run scalarScratchSwap r
    simpa only [hBack,t,routedLoadedMatrixScalar] using hr
  exact ⟨t,rr,hScalar,hGood,fun k hk => by
    have hNot : scalarScratchSwap.symm k ≠ "data" := by
      intro h
      apply hk
      exact (scalarScratchSwap.apply_symm_apply k).symm.trans
        ((congrArg scalarScratchSwap h).trans scalarScratchSwap_data)
    change v.arrs (scalarScratchSwap.symm k) = s.arrs k
    rw [hArr _ hNot]
    simp only [u,renameEnv_arrs,Equiv.symm_symm,Equiv.apply_symm_apply],
    hIn,hOut⟩

#print axioms routedLoadedMatrixScalar_run
end EvenTI.P17Scalar