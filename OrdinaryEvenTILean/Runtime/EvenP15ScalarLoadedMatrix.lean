import EvenP15ScalarLabelVector
import EvenP15ScalarMatrixMeaning
import EvenP15ScalarModeLoop
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 5000000

namespace EvenTI.P15Scalar

open EvenTI.Contract
open EvenTI.P12CountPre (sentinelWords)
open EvenTI.P15Trial (labelAddress)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix index_lt)
open Mathproof.Problem18P34AssemblyMatrixMemory20261003 (matrix_slot)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def scalarLoadedDim : String := "even.scalar.loaded.n"

local macro "loadedScalarGoodBound" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP15ScalarModeLoop `EvenTI.P15Scalar.probeGoodBound))

private def scalarSetup : List (String × Expr) := [
  ("index",.lit 0), ("base",.lit 0),
  ("count",.mul (.var scalarLoadedDim) (.var scalarLoadedDim)),
  ("stride",.add (.var scalarLoadedDim) (.lit 1)),
  ("diag",.get "data" (.lit 0)), ("good",.lit 1)]

noncomputable def loadedMatrixScalar (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) : Com :=
  .seq (installScalarLabels D F ws) (.seq (commands scalarSetup) (scalarMatrixScan (D 0).val))

-- The sentinel is kept outside the writable digit slice.
private theorem recoverSentinel (xs : List ℕ) (m : ℕ)
    (hlen : xs.length = m+1) (hz : xs.getD m 0 = 0) :
    xs = sentinelWords (xs.take m) := by
  obtain ⟨v,hv⟩ := List.length_eq_one_iff.mp (show (xs.drop m).length = 1 by simp [hlen])
  have hHead : (xs.drop m).getD 0 0 = 0 := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_drop,Nat.add_zero] using hz
  have hv0 : v = 0 := by simpa [hv] using hHead
  rw [hv0] at hv
  exact (List.take_append_drop m xs).symm.trans (congrArg (xs.take m ++ ·) hv)

private theorem take_getD_lt (xs : List ℕ) {i m : ℕ} (hi : i < m) :
    (xs.take m).getD i 0 = xs.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hi]

/-- Verify scalarity directly on a square witness matrix installed in the
shared canonical field workspace. This is the consumer of a dechart
operation; it makes no binary serialization or additional matrix copy. -/
theorem loadedMatrixScalar_run (D : FieldEncoding K) (F : FieldPresentation K)
    {ws : String} {W S a n : ℕ} {s : Env} (M : Matrix (Fin n) (Fin n) K)
    (hS : Slots F canonical ws S W s)
    (hWS : labelAddress ≠ ws ∧ scalarLabelDest ≠ ws ∧ scalarCopyIndex ≠ ws)
    (hn : 0 < n) (hQ : Fintype.card K ≤ W) (hP : F.p < W)
    (hA : s.vars scalarCopySource = a) (hD : s.vars scalarCopyTarget = 0)
    (hM : s.vars scalarCopyLength = n*n) (hN : s.vars scalarLoadedDim=n)
    (hRead : a+n*n ≤ S) (hMat : matrix F s (s.vars ws+a*F.e) n n = M)
    (hLen : (s.arrs "data").length = n*n+1) (hW : n*n+1 < W)
    (hSent : (s.arrs "data").getD (n*n) 0 = 0) :
    ∃ t, Run W (loadedMatrixScalar D F ws) s t
      (installScalarLabelsCost F (n*n)+60*(n*n)+30) ∧
      (t.vars "good" = 1 ↔ M = M ⟨0,hn⟩ ⟨0,hn⟩ • (1 : Matrix (Fin n) (Fin n) K)) ∧
      t.vars "good" < W ∧ (∀ k, k ≠ "data" → t.arrs k=s.arrs k) ∧ t.inp=s.inp ∧ t.out=s.out := by
  have h1 : 1 < W := by omega
  have hpos : 0 < n*n := Nat.mul_pos hn hn
  have hn2 : n ≤ n*n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n (show 1 ≤ n from hn)
  have hnW : n < W := by omega
  obtain ⟨u,r0,_,hSeg,hUlen,hArr,hIn,hOut,hKeep⟩ :=
    installScalarLabels_run D F hS hWS hQ hP h1 hA hD hM (by omega) (by omega) (by omega)
  have hLenU := hUlen.trans hLen
  have hTail : (u.arrs "data").getD (n*n) 0=0 :=
    (hSeg.outside (n*n) (Or.inr (by omega))).trans hSent
  let xs := (u.arrs "data").take (n*n)
  have hxlen : xs.length = n*n := by
    apply List.length_take_of_le
    omega
  have hxRead (i : ℕ) (hi : i < n*n) :
      xs.getD i 0 = (D (val F canonical ws s (a+i))).val := by
    rw [take_getD_lt _ hi]
    simpa only [Nat.zero_add] using hSeg.inside i hi
  have hData : u.arrs "data" = sentinelWords xs := recoverSentinel _ _ hLenU hTail
  have hDigits : ∀ q ∈ xs, q < W := by
    intro q hq
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
    have h'i : i < n*n := by omega
    have hh := hxRead i h'i
    rw [List.getD_eq_getElem _ _ hi,he] at hh
    rw [hh]
    exact (D _).isLt.trans_le hQ
  let dg := xs.getD 0 0
  have hdigit : dg < W := by
    rw [show dg = (D (val F canonical ws s a)).val by simpa [dg] using hxRead 0 hpos]
    exact (D _).isLt.trans_le hQ
  have huN : u.vars scalarLoadedDim = n := (hKeep _ (by decide) (by decide) (by decide)).trans hN
  have en : (Expr.var scalarLoadedDim).evalB W u = some n :=
    evalB_var_iff.mpr ⟨huN.symm,huN ▸ hnW⟩
  have ez : 0 < W := by omega
  have eDiag : (Expr.get "data" (.lit 0)).evalB W u = some dg := by
    apply evalB_get (evalB_lit ez) _ hdigit
    change (u.arrs "data")[0]? = some (xs.getD 0 0)
    rw [hData,sentinelWords,List.getElem?_append_left (show 0<xs.length by omega),
      List.getD_eq_getElem _ _ (show 0<xs.length by omega),List.getElem?_eq_getElem (show 0<xs.length by omega)]
  let vals := [0,0,n*n,n+1,dg,1]
  have ev : List.Forall₂ (fun v w => v.2.evalB W u = some w) scalarSetup vals := by
    simp only [scalarSetup,vals,List.forall₂_cons]
    exact ⟨evalB_lit ez, evalB_lit ez,
      evalB_bin (op:=.mul) en en (by change n*n < W; omega),
      evalB_bin (op:=.add) en (evalB_lit h1) (by change n+1 < W; omega),
      eDiag,evalB_lit h1,List.Forall₂.nil⟩
  let inputs := List.zip (scalarSetup.map Prod.fst) vals
  let v := install inputs u
  have r1 : Run W (commands scalarSetup) u v 18 := by
    exact commands_run scalarSetup vals u rfl ev (by
      intro p hp r hr
      simp only [scalarSetup,List.mem_cons,List.not_mem_nil,or_false] at hp hr
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [NoVar,scalarLoadedDim])
  have f := installed_arrays inputs u
  obtain ⟨t,r2,hA',hI',hO',hBit⟩ := scalarMatrixScan_run (σ:=v) xs (D 0).val n 0 dg h1
    (by omega) (by omega) ((D 0).isLt.trans_le hQ) hdigit hDigits (by omega)
    (by simp [v,inputs,scalarSetup,vals,install]) (by simp [v,inputs,scalarSetup,vals,install])
    (by simp [v,inputs,scalarSetup,vals,install]) (by simp [v,inputs,scalarSetup,vals,install])
    (by simp [v,inputs,scalarSetup,vals,install]) (by simp [v,inputs,scalarSetup,vals,install])
    (by rw [f.1,hData])
  have rr : Run W (loadedMatrixScalar D F ws) s t
      (installScalarLabelsCost F (n*n)+60*(n*n)+30) :=
    (r0.seq (r1.seq r2)).mono (by omega)
  have goodWord : t.vars "good" < W := loadedScalarGoodBound r2 (by
    simpa [v,inputs,scalarSetup,vals,install] using h1)
  refine ⟨t,rr,?_,goodWord,fun k hk => ?_,hI'.trans (f.2.1.trans hIn),hO'.trans (f.2.2.trans hOut)⟩
  · rw [hBit]
    apply Iff.trans _ (rawScalarBankMode_iff D hn M xs 0 _)
    · rfl
    · intro i j
      have h := hxRead (i.val*n+j.val) (index_lt i j)
      rw [←hMat,matrix_slot]
      simpa [Nat.add_assoc] using h
  · rw [hA',f.1]
    exact hArr k hk

#print axioms loadedMatrixScalar_run
end EvenTI.P15Scalar