import EvenP16TrialContractionProducts
import EvenP16TrialContractionMeaning
import EvenP17ReciprocalVisit

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 17000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P17Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames NoVar)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU dI dO)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut gU gV Written)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots installed_scalar installed_arrays)
open scoped Matrix

variable {K : Type} [Field K] [Fintype K]

private theorem literalProduct_cells {I : Type} [Fintype I] [DecidableEq I] {m n : ℕ}
    (A : Matrix I I K) (P Q : (I → K) →ₗ[K] Matrix (Fin n) (Fin n) K) (e : Fin m ≃ I)
    (a p q out : ℕ → K)
    (ha : ∀ x y : Fin m, a (x.val*m+y.val)=A (e x) (e y))
    (hp : ∀ (i : Fin (n*n)) (x : Fin m),
      p (i.val*m+x.val)=projectionCoefficients P (finProdFinEquiv.symm i) (e x))
    (hq : ∀ (j : Fin (n*n)) (y : Fin m),
      q (j.val*m+y.val)=projectionCoefficients Q (finProdFinEquiv.symm j) (e y))
    (hOut : ∀ i < n*n, ∀ j < n*n, out (i*(n*n)+j)=
      ∑ x ∈ Finset.range m, p (i*m+x) * (∑ y ∈ Finset.range m, a (x*m+y)*q (j*m+y))) :
    ∀ i j : Fin (n*n), out (i.val*(n*n)+j.val)=literalProjectionProduct A P Q e e i j := by
  intro i j
  rw [hOut i.val i.isLt j.val j.isLt]
  unfold literalProjectionProduct
  simp only [Matrix.mul_apply,Matrix.submatrix_apply,Matrix.transpose_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x _
  rw [hp]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro y _
  rw [ha,hq]

private def higherCrossArgs : List (String × Expr) :=
  [(gRows,.mul (.var crossN) (.var crossN)),(gCols,.mul (.var crossN) (.var crossN)),
   (dL,.lit 1),(gOut,.var anchorCrossWord)]

def resetHigherCrossArgs : Com := commands higherCrossArgs

theorem resetHigherCrossArgs_run (F : FieldPresentation K)
    {B S n cross : ℕ} {s : Env} (hs : Slots F canonical qN.WS S B s)
    (hn : s.vars crossN=n) (hc : s.vars anchorCrossWord=cross)
    (hnB : n < B) (hcB : cross < B) (hnn : n*n < B) (hOneB : 1 < B) :
    ∃ t, Run B resetHigherCrossArgs s t 13 ∧ Slots F canonical qN.WS S B t ∧
      t.vars gRows=n*n ∧ t.vars gCols=n*n ∧ t.vars dL=1 ∧ t.vars gOut=cross ∧
      (∀ r, r ∉ [gRows,gCols,dL,gOut] → t.vars r=s.vars r) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  let vals := [n*n,n*n,1,cross]
  let pairs := List.zip (higherCrossArgs.map Prod.fst) vals
  let t := install pairs s
  have ev (r : String) (v : ℕ) (h : s.vars r=v) (hv : v<B) :
      (Expr.var r).evalB B s=some v :=
    evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩
  have en := ev _ _ hn hnB
  have en2 := evalB_bin (op:=.mul) en en hnn
  have hb : List.Forall₂ (fun p v => p.2.evalB B s=some v) higherCrossArgs vals :=
    .cons en2 (.cons en2 (.cons (evalB_lit hOneB) (.cons (ev _ _ hc hcB) .nil)))
  have hSafe : ∀ r ∈ [gRows,gCols,dL,gOut], canonical.e ≠ r ∧ canonical.p ≠ r ∧
      canonical.modBase ≠ r ∧ canonical.exp ≠ r ∧ qN.WS ≠ r := by decide
  have hRoster (p : String × ℕ) (hp : p ∈ pairs) : p.1 ∈ [gRows,gCols,dL,gOut] := by
    have h : p.1 ∈ pairs.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
    exact h
  have hr0 : Run B resetHigherCrossArgs s t 13 := commands_run higherCrossArgs vals s rfl hb (by
    simp [higherCrossArgs,NoVar,gRows,gCols,dL,gOut,crossN,anchorCrossWord])
  refine ⟨t,hr0,installed_slots F pairs s hs (fun p hp => hSafe _ (hRoster p hp)),
    ?_,?_,?_,?_,?_,installed_arrays pairs s⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r h
    exact installed_scalar pairs s r (fun p hp he => h (he ▸ hRoster p hp))

noncomputable def higherContraction (F : FieldPresentation K) : Com :=
  .seq (contractionProducts F) (.seq resetHigherCrossArgs (crossShuffle F))

noncomputable def higherContractionCost (F : FieldPresentation K) (m n : ℕ) : ℕ :=
  contractionProductsCost F m (n*n) (n*n)+(13+crossShuffleCost F n n)

structure ContractionOffsets where
  tensor : ℕ
  left : ℕ
  right : ℕ
  tmp : ℕ
  product : ℕ
  cross : ℕ
  zero : ℕ
  one : ℕ
  tt : ℕ
  uu : ℕ

structure ContractionRegisters (s : Env) (m n : ℕ) (b : ContractionOffsets) : Prop where
  width : s.vars contractionTensorWidth=m
  rows : s.vars contractionLeftWidth=n*n
  cols : s.vars contractionRightWidth=n*n
  tensor : s.vars contractionTensorBase=b.tensor
  left : s.vars contractionLeftBase=b.left
  right : s.vars contractionRightBase=b.right
  tmp : s.vars contractionTempBase=b.tmp
  product : s.vars contractionOutBase=b.product
  target : s.vars anchorCrossWord=b.cross
  sleft : s.vars crossShuffleLeft=n
  sright : s.vars crossShuffleRight=n
  sfrom : s.vars crossShuffleSource=b.product
  sone : s.vars crossShuffleOne=b.one
  radix : s.vars crossN=n
  zero : s.vars dZ=b.zero
  tt : s.vars dT=b.tt
  uu : s.vars dU=b.uu

/-- Compute and cross-shuffle the native contraction for one retained mode
from its two coefficient banks and the raw tensor flattening. -/
theorem higherContraction_run (F : FieldPresentation K) {I : Type} [DecidableEq I] [Fintype I]
    {B S m n : ℕ} {s : Env} (b : ContractionOffsets)
    (A : Matrix I I K) (P Q : (I → K) →ₗ[K] Matrix (Fin n) (Fin n) K) (e : Fin m ≃ I)
    (hS : Slots F canonical qN.WS S B s) (hn : 0 < n)
    (hS₁ : m+1<B) (hS₂ : n*n+1<B) (hR : ContractionRegisters s m n b)
    (hT : b.tensor+m*m ≤ b.tmp) (hL : b.left+(n*n)*m ≤ b.tmp) (hQ : b.right+(n*n)*m ≤ b.tmp)
    (hTmp : b.tmp+m*(n*n) ≤ b.product) (hProd : b.product+(n*n)*(n*n) ≤ b.cross)
    (hCross : b.cross+(n*n)*(n*n) ≤ S)
    (ht : b.tt<b.tensor ∧ b.tt<b.right ∧ b.tt<b.left)
    (hu : b.uu<b.tensor ∧ b.uu<b.right ∧ b.uu<b.left) (htu : b.tt≠b.uu)
    (hz : b.zero<b.tmp ∧ b.zero≠b.tt ∧ b.zero≠b.uu)
    (hOne : b.one<b.tmp ∧ b.one≠b.tt ∧ b.one≠b.uu)
    (hzv : val F canonical qN.WS s b.zero=0) (hov : val F canonical qN.WS s b.one=1)
    (hReadA : ∀ x y : Fin m, val F canonical qN.WS s (b.tensor+(x.val*m+y.val))=A (e x) (e y))
    (hReadL : ∀ (i : Fin (n*n)) (x : Fin m),
      val F canonical qN.WS s (b.left+(i.val*m+x.val))=projectionCoefficients P
        (finProdFinEquiv.symm i) (e x))
    (hReadR : ∀ (j : Fin (n*n)) (y : Fin m),
      val F canonical qN.WS s (b.right+(j.val*m+y.val))=projectionCoefficients Q
        (finProdFinEquiv.symm j) (e y)) :
    ∃ t, Run B (higherContraction F) s t (higherContractionCost F m n) ∧
      Slots F canonical qN.WS S B t ∧ t.vars gRows=n*n ∧ t.vars gCols=n*n ∧
      (∀ p q : Fin n × Fin n, val F canonical qN.WS t
        (b.cross+(pairWordIndex p*(n*n)+pairWordIndex q))=coordinateProjection P Q A p q) ∧
      (∀ k < b.tmp, k≠b.tt → k≠b.uu → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hSB := hS.slots_word
  obtain ⟨α,ra,hα,hOut,hKeep,hVars,hi,ho⟩ := contractionProducts_run F hS
    hTmp (hProd.trans (by omega)) hT hQ hL ht hu htu
    ⟨hz.1,by omega,hz.2.1,hz.2.2⟩ hzv ⟨hS₁,hS₂,hS₂⟩
    hR.width hR.rows hR.cols hR.tensor hR.left hR.right hR.tmp hR.product hR.zero hR.tt hR.uu
  have hExact := literalProduct_cells A P Q e
    (fun i => val F canonical qN.WS s (b.tensor+i))
    (fun i => val F canonical qN.WS s (b.left+i))
    (fun i => val F canonical qN.WS s (b.right+i))
    (fun i => val F canonical qN.WS α (b.product+i)) hReadA hReadL hReadR hOut
  have hαLow (k : ℕ) (hk : k<b.tmp) (ht : k≠b.tt) (hu : k≠b.uu) :
      val F canonical qN.WS α k=val F canonical qN.WS s k :=
    hKeep k (by omega) (by unfold Written;omega) (by unfold Written;omega)
  have regα {r : String} {v : ℕ} (hr : s.vars r=v)
      (h₁ : r∉rectangularTargets) (h₂ : r∉regNames canonical) (h₃ : r≠dI)
      (h₄ : r≠gU) (h₅ : r≠gV) (h₆ : r≠dO) : α.vars r=v :=
    (hVars r h₁ h₂ h₃ h₄ h₅ h₆).trans hr
  have hNB : n<B := (Nat.le_mul_of_pos_right n hn).trans_lt (by omega)
  obtain ⟨β,rb,hβ,hRows,hCols,hIn,hGo,hRegβ,hArrβ,hiβ,hoβ⟩ :=
    resetHigherCrossArgs_run F hα
      (regα hR.radix (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (regα hR.target (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hNB (by omega) (by omega) (by omega)
  have hβMem (k : ℕ) : val F canonical qN.WS β k=val F canonical qN.WS α k := by
    unfold val slice
    rw [hRegβ _ (by decide),hArrβ]
  have regβ {r : String} {v : ℕ} (h : α.vars r=v) (hf : r∉[gRows,gCols,dL,gOut]) :
      β.vars r=v := (hRegβ r hf).trans h
  have crossKeep (k : ℕ) (hk : k<b.cross) (ht : k≠b.tt) (hu : k≠b.uu) :
      ¬ Written b.cross (n*n) (n*n) b.tt b.uu k := by unfold Written; omega
  obtain ⟨t,rc,htS,hShuffle,hKeepₜ,hVarsₜ,hiₜ,hoₜ⟩ :=
    crossShuffle_run F hn hn hS₂ hProd hCross (by omega) (by omega) htu
      (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (crossKeep b.zero (by omega) hz.2.1 hz.2.2) (by omega)
      (crossKeep b.one (by omega) hOne.2.1 hOne.2.2)
      hβ ((hβMem _).trans ((hαLow _ hz.1 hz.2.1 hz.2.2).trans hzv))
      ((hβMem _).trans ((hαLow _ hOne.1 hOne.2.1 hOne.2.2).trans hov)) hIn
      (regβ (regα hR.tt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      (regβ (regα hR.uu (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      (regβ (regα hR.zero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      hRows hCols hGo
      (regβ (regα hR.sleft (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      (regβ (regα hR.sright (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      (regβ (regα hR.sfrom (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
      (regβ (regα hR.sone (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
  refine ⟨t,ra.seq (rb.seq rc),htS,
    (hVarsₜ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hRows,
    (hVarsₜ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCols,?_,?_,
    hiₜ.trans (hiβ.trans hi),hoₜ.trans (hoβ.trans ho)⟩
  · intro p q
    exact nativeProjectionContraction_meaning A P Q e e
      (fun k => val F canonical qN.WS α (b.product+k))
      (fun k => val F canonical qN.WS t (b.cross+k))
      hExact (fun i hi j hj => (hShuffle i hi j hj).trans (by
        rw [hβMem]
        simp only [crossShuffleIndex,Nat.zero_add])) p.1 q.1 p.2 q.2
  · intro k hk ht hu
    exact (hKeepₜ k (by omega) (crossKeep k (by omega) ht hu)).trans
      ((hβMem k).trans (hαLow k hk ht hu))

#print axioms resetHigherCrossArgs_run
#print axioms higherContraction_run
end EvenTI.P19Trial
