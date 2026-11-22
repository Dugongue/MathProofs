import EvenP16RecoverFrobeniusRoot
import EvenP15RecoverPrefixCRT
import Mathproof.Meta.P15RecogIMPRank20261007
import Mathproof.Meta.P15DecideIMPEGens20261007
import Mathproof.Meta.P15DecideIMPMatPow20261007

set_option autoImplicit false
set_option maxRecDepth 28000
set_option maxHeartbeats 2900000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPIntertwinerScan20261001 (blockSize)
open Mathproof.P15RecogIMPRank20261007 (KQ kernelFramed_run)
open Mathproof.Problem18ClaudeIMPUniformBanks20261002 (uw)
open Mathproof.Problem18IMPKernelWitness20261001 (decoded)
open Mathproof.Problem18IMPUniformKernelFromMatrix20261002 (program budget)

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K] [Field A] [Algebra K A] {n m : ℕ}

def frobeniusRootRectMatrix (C : A ≃ₗ[K] (Fin n → K)) (R : A →ₗ[K] (Fin m → K))
    (u : Aˣ) : Matrix (Fin m) (Fin n) K :=
  LinearMap.toMatrix' (R.comp (C.symm.toLinearMap.comp (frobeniusRootDifference C u)))

theorem frobeniusRootRectMatrix_entry (C : A ≃ₗ[K] (Fin n → K)) (R : A →ₗ[K] (Fin m → K))
    (u : Aˣ) (i : Fin m) (j : Fin n) :
    frobeniusRootRectMatrix C R u i j =
      R ((C.symm (Pi.single j 1))^Fintype.card K - (u : A)*C.symm (Pi.single j 1)) i := by
  rw [frobeniusRootRectMatrix,LinearMap.toMatrix'_apply]
  change R (C.symm (C ((C.symm (Pi.single j 1))^Fintype.card K -
    (u : A)*C.symm (Pi.single j 1)))) i = _
  rw [C.symm_apply_apply]

/-- An injective ambient matrix encoding gives the same kernel without pulling
columns back into the extension basis. -/
theorem frobeniusRootRect_kernel_iff (C : A ≃ₗ[K] (Fin n → K)) (R : A →ₗ[K] (Fin m → K))
    (hR : Function.Injective R) (u : Aˣ) (x : Fin n → K) :
    (frobeniusRootRectMatrix C R u).mulVec x = 0 ↔
      (C.symm x)^Fintype.card K = (u : A)*C.symm x := by
  rw [← Matrix.toLin'_apply,frobeniusRootRectMatrix,Matrix.toLin'_toMatrix']
  change R (C.symm (C ((C.symm x)^Fintype.card K - (u : A)*C.symm x))) = 0 ↔ _
  rw [C.symm_apply_apply,← R.map_zero,hR.eq_iff,sub_eq_zero]

/-- The same paid kernel returns an exact root from a rectangular operator
matrix, preserving the input operator banks above the framed work area. -/
theorem frobeniusRootRect_run (F : FieldPresentation K) (C : A ≃ₗ[K] (Fin n → K))
    (R : A →ₗ[K] (Fin m → K)) (hR : Function.Injective R) (u : Aˣ)
    {B S : ℕ} {s : Env}
    (hS : Slots F canonical KQ.WS S B s)
    (hRows : s.vars uw.nR=m) (hCols : s.vars uw.mR=n)
    (hCap : (n+1)*blockSize m n ≤ S)
    (hData : ∀ (i : Fin m) (j : Fin n), val F canonical KQ.WS s (5+j.val*m+i.val) =
      frobeniusRootRectMatrix C R u i j) :
    ∃ t, Run B program s t (budget F m n) ∧ Slots F canonical KQ.WS S B t ∧
      (decoded F m n t = none ↔ ¬ ∃ a : Aˣ, a^(Fintype.card K-1)=u) ∧
      (∀ x, decoded F m n t = some x →
        ∃ hx : C.symm x ≠ 0, Units.mk0 (C.symm x) hx ^ (Fintype.card K-1) = u) ∧
      (∀ j < S, (n+1)*blockSize m n ≤ j → val F canonical KQ.WS t j = val F canonical KQ.WS s j) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,hr,ht,hnone,hsome,hKeep,hI,hO⟩ :=
    kernelFramed_run F (frobeniusRootRectMatrix C R u) hS hRows hCols hCap hData
  have nonzero (x : Fin n → K) (hx : x ≠ 0) : C.symm x ≠ 0 := by
    intro h
    exact hx (C.symm.injective (h.trans C.symm.map_zero.symm))
  refine ⟨t,hr,ht,?_,?_,hKeep,hI,hO⟩
  · rw [hnone]
    constructor
    · rintro h ⟨a,ha⟩
      have he : Units.mk0 (a:A) a.ne_zero = a := Units.ext rfl
      have hh := (frobeniusRoot_eq_unitPower (K:=K) u (a:A) a.ne_zero).mpr (by rwa [he])
      have hv := (frobeniusRootRect_kernel_iff C R hR u (C (a:A))).mpr
        (by simpa only [C.symm_apply_apply] using hh)
      exact a.ne_zero (C.injective ((h _ hv).trans C.map_zero.symm))
    · intro h x hx
      by_contra hn
      have hn' := nonzero x hn
      exact h ⟨Units.mk0 (C.symm x) hn', (frobeniusRoot_eq_unitPower (K:=K) u _ hn').mp
        ((frobeniusRootRect_kernel_iff C R hR u x).mp hx)⟩
  · intro x hx
    obtain ⟨hn,hk⟩ := hsome x hx
    exact ⟨nonzero x hn, (frobeniusRoot_eq_unitPower (K:=K) u _ (nonzero x hn)).mp
      ((frobeniusRootRect_kernel_iff C R hR u x).mp hk)⟩

#print axioms frobeniusRootRectMatrix_entry
#print axioms frobeniusRootRect_kernel_iff
#print axioms frobeniusRootRect_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open EvenTI.Part8 EvenTI.CellPreparation EvenTI.P15Recover EvenOrdinaryTI.LiveRows
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →ₐ[K] Y j)

local notation "V" => VarCount s t d
local notation "J" => RowCount t d
local notation "U" => ∀ v : Fin V, (physicalVarField X Y v)ˣ
local notation "H" => Fintype.card K - 1
local notation "eval" => (prefixEvaluation X Y orig emb)

/-- Any set of verified roots for the projected powers can be passed to the
physical CRT replacement. Its success no longer depends on which roots were chosen. -/
theorem correctResidualCRT_of_powers (enum : Fin (Fintype.card K) ≃ K)
    (views : ∀ r : Fin J, DenseFieldView (K := K) (physicalRowField Y r))
    (c : ∀ j, (Y j)ˣ) (u x : U) (hx : eval x = physicalRHS Y c)
    (hu : ∀ v, u v ^ H = x v ^ H) :
    ∃ a, correctResidualCRT X Y orig emb enum views c u = some a ∧ eval a = physicalRHS Y c := by
  obtain ⟨a,ha,_⟩ := correctBaseResidual_of_powers X Y orig emb enum views c u x hx hu
  have hav := correctResidualCRT_available X Y orig emb enum views c u
  rw [ha] at hav
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hav
  exact ⟨b,hb,correctResidualCRT_sound X Y orig emb enum views c u b hb⟩

#print axioms correctResidualCRT_of_powers
end EvenTI.P16Recover

set_option autoImplicit false
set_option maxRecDepth 28000
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots NoVar val regNames slot_call val_setVar addr)
open Mathproof.Problem18ClaudeFieldMacros20261001 (call)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (call_regs_all call_val)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (F : FieldPresentation K)

def rootPowerBase : String := "even.recovery.root.column.power"
def rootMultiplyBase : String := "even.recovery.root.column.multiply"
def rootKernelBase : String := "even.recovery.root.column.kernel"
def rootColumnLength : String := "even.recovery.root.column.length"
def rootColumnIndex : String := "even.recovery.root.column.index"

private def colAddr (base : String) : Expr := .add (.var base) (.var rootColumnIndex)
private def colGuard : Cond := .lt (.var rootColumnIndex) (.var rootColumnLength)
private def colNext : Com := .assign rootColumnIndex (.add (.var rootColumnIndex) (.lit 1))
private noncomputable def colWrite : Com :=
  call canonical (addr canonical qN.WS (colAddr rootPowerBase))
    (addr canonical qN.WS (colAddr rootMultiplyBase))
    (addr canonical qN.WS (colAddr rootKernelBase)) (fieldMacros F).sub

noncomputable def installRootColumn : Com :=
  .seq (.assign rootColumnIndex (.lit 0)) (.while colGuard (.seq (colWrite F) colNext))

noncomputable def installRootColumnCost (m : ℕ) : ℕ :=
  (32+(fieldMacros F).costPoint)*m+6

private structure ColumnState (initial : Env) (B S L R D m : ℕ) (s : Env) : Prop where
  slots : Slots F canonical qN.WS S B s
  bound : s.vars rootColumnIndex ≤ m
  leftBase : s.vars rootPowerBase = L
  rightBase : s.vars rootMultiplyBase = R
  outBase : s.vars rootKernelBase = D
  length : s.vars rootColumnLength = m
  written : ∀ i < s.vars rootColumnIndex,
    val F canonical qN.WS s (D+i) = val F canonical qN.WS initial (L+i) - val F canonical qN.WS initial (R+i)
  frame : ∀ i < S, (i < D ∨ D+s.vars rootColumnIndex ≤ i) →
    val F canonical qN.WS s i = val F canonical qN.WS initial i
  tapeIn : s.inp = initial.inp
  tapeOut : s.out = initial.out

/-- Subtract the two paid operator blocks into a contiguous kernel column,
while retaining every other field slot and the physical input/output tape. -/
theorem installRootColumn_run {B S L R D m : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) (hB : 1 < B)
    (hL : s.vars rootPowerBase=L) (hR : s.vars rootMultiplyBase=R)
    (hD : s.vars rootKernelBase=D) (hM : s.vars rootColumnLength=m)
    (hLF : L+m ≤ S) (hRF : R+m ≤ S) (hDF : D+m ≤ S)
    (hLSep : L+m ≤ D ∨ D+m ≤ L) (hRSep : R+m ≤ D ∨ D+m ≤ R) :
    ∃ t, Run B (installRootColumn F) s t (installRootColumnCost F m) ∧ Slots F canonical qN.WS S B t ∧
      (∀ i < m, val F canonical qN.WS t (D+i) =
        val F canonical qN.WS s (L+i) - val F canonical qN.WS s (R+i)) ∧
      (∀ i < S, (i < D ∨ D+m ≤ i) → val F canonical qN.WS t i = val F canonical qN.WS s i) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let I := ColumnState F s B S L R D m
  let P (s : Env) := m-s.vars rootColumnIndex
  have hMWord : m < B := by have := hS.slots_word; omega
  let u := s.setVar rootColumnIndex 0
  have r₀ : Run B (.assign rootColumnIndex (.lit 0)) s u 2 := Run.assign (evalB_lit (by omega))
  have hU : u.vars rootColumnIndex=0 := by simp [u]
  have hI : I u := by
    refine ⟨Slots.setVar F canonical hS (by decide) (by decide) _, by simp [hU],hL,hR,hD,hM,?_,?_,rfl,rfl⟩
    · intro i hi; rw [hU] at hi; omega
    · intro i _ _; exact val_setVar F canonical (by decide) s 0 i
  have hg (v : Env) (h : I v) : colGuard.evalB B v = some (decide (v.vars rootColumnIndex < m)) :=
    evalB_condLt (ev_var rfl (h.bound.trans_lt hMWord)) (ev_var h.length hMWord)
  have step (v : Env) (h : I v) (hg' : colGuard.evalB B v=some true) :
      ∃ t, Run B (.seq (colWrite F) colNext) v t (28+(fieldMacros F).costPoint) ∧ I t ∧ P t < P v := by
    rw [hg v h] at hg'
    let j := v.vars rootColumnIndex
    have hj : j < m := of_decide_eq_true (Option.some.inj hg')
    have hJ : j < B := hj.trans hMWord
    have hFit : S < B := h.slots.slots_word
    have e (base : String) (k : ℕ) (hr : v.vars base=k) (hk : k+m ≤ S) :
        (colAddr base).evalB B v = some (k+j) :=
      ev_add (ev_var hr (by omega)) (ev_var rfl hJ) (by omega)
    have hDL : D+j ≠ L+j := by rcases hLSep with hSep|hSep <;> omega
    have hDR : D+j ≠ R+j := by rcases hRSep with hSep|hSep <;> omega
    obtain ⟨w,r₁,hValue,hFrame⟩ := slot_call F canonical (fieldMacros F).sub_spec h.slots
      (colAddr rootPowerBase) (colAddr rootMultiplyBase) (colAddr rootKernelBase)
      (e _ _ h.leftBase hLF) (e _ _ h.rightBase hRF) (e _ _ h.outBase hDF)
      (by simp [NoVar,colAddr,canonical,rootMultiplyBase,rootColumnIndex])
      (by simp [NoVar,colAddr,canonical,rootKernelBase,rootColumnIndex])
      (by simp [NoVar,colAddr,canonical,rootKernelBase,rootColumnIndex])
      (by omega) (by omega) (by omega) hDL hDR
    have hReg (x : String) (hx : x ∉ regNames canonical) : w.vars x = v.vars x :=
      call_regs_all hFrame x hx
    have hjW : w.vars rootColumnIndex=j := hReg _ (by decide)
    let t := w.setVar rootColumnIndex (j+1)
    have hT : t.vars rootColumnIndex=j+1 := by simp [t]
    have r₂ : Run B colNext w t 4 := Run.assign
      (ev_add (ev_var hjW hJ) (evalB_lit hB) (by omega))
    have hStable (i : ℕ) : val F canonical qN.WS t i = val F canonical qN.WS w i :=
      val_setVar F canonical (by decide) w _ i
    have hPrev : ∀ i < S, i ≠ D+j → val F canonical qN.WS t i = val F canonical qN.WS v i :=
      fun i hi he => (hStable i).trans (call_val hFrame hi he)
    have hLV : val F canonical qN.WS v (L+j) = val F canonical qN.WS s (L+j) :=
      h.frame _ (by omega) (by rcases hLSep with hSep|hSep <;> change j < m at hj <;> omega)
    have hRV : val F canonical qN.WS v (R+j) = val F canonical qN.WS s (R+j) :=
      h.frame _ (by omega) (by rcases hRSep with hSep|hSep <;> change j < m at hj <;> omega)
    rw [hLV,hRV] at hValue
    have hRun : Run B (.seq (colWrite F) colNext) v t (28+(fieldMacros F).costPoint) := by
      unfold colWrite
      exact (r₁.seq r₂).mono (by simp [colAddr,Expr.size] <;> omega)
    refine ⟨t,hRun,⟨Slots.setVar F canonical hFrame.slots (by decide) (by decide) _, by rw [hT]; omega,
      (hReg _ (by decide)).trans h.leftBase,(hReg _ (by decide)).trans h.rightBase,
      (hReg _ (by decide)).trans h.outBase,(hReg _ (by decide)).trans h.length,?_,?_,
      hFrame.inp.trans h.tapeIn,hFrame.out.trans h.tapeOut⟩,?_⟩
    · intro i hi
      rw [hT] at hi
      by_cases hi' : i = j
      · subst i
        exact (hStable _).trans hValue
      · exact (hPrev _ (by omega) (by omega)).trans (h.written i (by change i < j; omega))
    · intro i hi he
      rw [hT] at he
      exact (hPrev _ hi (by rcases he with hOut | hOut <;> omega)).trans
        (h.frame _ hi (by
          rcases he with hOut | hOut
          · exact Or.inl hOut
          · exact Or.inr (by change D+j ≤ i; omega)))
    · dsimp only [P]
      rw [hT]
      omega
  obtain ⟨t,rt,hT,hStop⟩ := Run.while_count I P (28+(fieldMacros F).costPoint)
    (fun v hv => ⟨_,hg v hv⟩) step hI
  have hEnd : t.vars rootColumnIndex=m := by
    rw [hg t hT] at hStop
    have hGe : ¬ t.vars rootColumnIndex < m := by simpa using hStop
    have := hT.bound
    omega
  refine ⟨t,(r₀.seq rt).mono ?_,hT.slots,?_,?_,hT.tapeIn,hT.tapeOut⟩
  · have hs : 4+(28+(fieldMacros F).costPoint)=32+(fieldMacros F).costPoint := by omega
    simp [installRootColumnCost,colGuard,Cond.size,Expr.size,P,hU,hs] <;> omega
  · intro i hi; exact hT.written i (by rwa [hEnd])
  · intro i hi he; exact hT.frame i hi (by rwa [hEnd])

#print axioms installRootColumn_run
end EvenTI.P16Recover

set_option autoImplicit false
set_option maxRecDepth 28000
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Matrix
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPMatPow20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (F : FieldPresentation K)

def rootUnitOperator : String := "even.recovery.root.column.unit"

noncomputable def rootOperatorColumn : Com :=
  .seq (mulInto rootUnitOperator mpP rootMultiplyBase) (.seq mpProg (installRootColumn F))

noncomputable def rootOperatorColumnCost (n : ℕ) : ℕ :=
  mulCost F n + (mpCost F n (Fintype.card K) + installRootColumnCost F (n*n))

structure RootOperatorLayout (B S n dst tmp pow basis product unit zero : ℕ) (s : Env) : Prop where
  slots : Slots F canonical qN.WS S B s
  row : s.vars mpN=n
  square : s.vars mpNN=n*n
  exp : s.vars mpE=Fintype.card K
  result : s.vars mpR=pow
  basisReg : s.vars mpP=basis
  temp : s.vars mpT=tmp
  unitReg : s.vars rootUnitOperator=unit
  powerReg : s.vars rootPowerBase=pow
  productReg : s.vars rootMultiplyBase=product
  destination : s.vars rootKernelBase=dst
  lengthReg : s.vars rootColumnLength=n*n
  zeroReg : s.vars dZ=zero
  oneReg : s.vars rOs=zero+1
  tempA : s.vars dT=zero+2
  tempB : s.vars dU=zero+3
  zeroVal : val F canonical qN.WS s zero=0
  oneVal : val F canonical qN.WS s (zero+1)=1
  dst_le : dst+n*n ≤ tmp
  tmp_le : tmp+n*n ≤ pow
  pow_le : pow+n*n ≤ basis
  basis_le : basis+n*n ≤ product
  product_le : product+n*n ≤ unit
  unit_le : unit+n*n ≤ zero
  zero_le : zero+4 ≤ S
  word : S+10 < B
  qWord : Fintype.card K+2 < B

/-- Materialize a kernel column by two concrete linear-algebra machine calls
and the paid slot subtraction loop. Input units and basis elements are stored
as faithful multiplication operators over the fixed base field. -/
theorem rootOperatorColumn_run {B S n dst tmp pow basis product unit zero : ℕ} {s : Env}
    (A U : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (h : RootOperatorLayout F B S n dst tmp pow basis product unit zero s)
    (hA : MatBlock F s basis A) (hU : MatBlock F s unit U) :
    ∃ t, Run B (rootOperatorColumn F) s t (rootOperatorColumnCost F n) ∧
      Slots F canonical qN.WS S B t ∧
      MatBlock F t dst (A^Fintype.card K-U*A) ∧ t.inp=s.inp ∧ t.out=s.out := by
  have hnames : ∀ x ∈ [rootUnitOperator,mpP,rootMultiplyBase], x ∉ regNames canonical ∧
      x ≠ mmA ∧ x ≠ mmB ∧ x ≠ gRows ∧ x ≠ gCols ∧ x ≠ dL ∧ x ≠ gOut ∧
      x ≠ dI ∧ x ≠ gU ∧ x ≠ gV ∧ x ≠ dO ∧ x ≠ qN.WS := by decide
  have key1 := h.dst_le
  have key2 := h.tmp_le
  have key3 := h.pow_le
  have key4 := h.basis_le
  have key5 := h.product_le
  have key6 := h.unit_le
  have key7 := h.zero_le
  have hidx (i j : Fin n) : i.val*n+j.val < n*n := by
    have h := (finProdFinEquiv (i,j)).isLt
    rw [finProdFinEquiv_apply_val] at h
    calc i.val*n + j.val = j.val+n*i.val := by ring
      _ < n*n := h
  obtain ⟨v,r₀,hsV,hProduct,hFrameV,hRegV,hInV,hOutV⟩ :=
    mulInto_run F rootUnitOperator mpP rootMultiplyBase hnames U A hn h.slots
      h.row h.square h.temp h.unitReg h.basisReg h.productReg h.zeroReg h.oneReg h.tempA h.tempB
      hU hA h.zeroVal h.oneVal (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) key7 h.word
  have hKeptBasis : MatBlock F v basis A := by
    intro i j
    have hI := hidx i j
    rw [hFrameV _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (by omega) (by omega)]
    exact hA i j
  have hZ : val F canonical qN.WS v zero=0 := by
    rw [hFrameV _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)]
    exact h.zeroVal
  have hOne : val F canonical qN.WS v (zero+1)=1 := by
    rw [hFrameV _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)]
    exact h.oneVal
  obtain ⟨w,r₁,hsW,hPower,hFrameW,hRegW,hInW,hOutW⟩ := mp_run F A hn hsV
    ((hRegV _ (by decide)).trans h.row) ((hRegV _ (by decide)).trans h.square)
    ((hRegV _ (by decide)).trans h.exp) ((hRegV _ (by decide)).trans h.result)
    ((hRegV _ (by decide)).trans h.basisReg) ((hRegV _ (by decide)).trans h.temp)
    ((hRegV _ (by decide)).trans h.zeroReg) ((hRegV _ (by decide)).trans h.oneReg)
    ((hRegV _ (by decide)).trans h.tempA) ((hRegV _ (by decide)).trans h.tempB)
    hKeptBasis hZ hOne key2 key3 (by omega) key7 h.word h.qWord
  have keep (x : String) (hv : x ∉ scalarWrites (mulInto rootUnitOperator mpP rootMultiplyBase))
      (hw : x ∉ scalarWrites mpProg) : w.vars x = s.vars x :=
    (hRegW x hw).trans (hRegV x hv)
  have hKeptProduct : MatBlock F w product (U*A) := by
    intro i j
    have hI := hidx i j
    rw [hFrameW _ (by omega) (Or.inr (by omega)) (by omega) (by omega)]
    exact hProduct i j
  have hWide := h.word
  obtain ⟨t,r₂,hsT,hCol,_,hInT,hOutT⟩ := installRootColumn_run F hsW (by omega)
    ((keep _ (by decide) (by decide)).trans h.powerReg)
    ((keep _ (by decide) (by decide)).trans h.productReg)
    ((keep _ (by decide) (by decide)).trans h.destination)
    ((keep _ (by decide) (by decide)).trans h.lengthReg)
    (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨t,r₀.seq (r₁.seq r₂),hsT,?_,hInT.trans (hInW.trans hInV),hOutT.trans (hOutW.trans hOutV)⟩
  intro i j
  rw [hCol _ (hidx i j),hPower i j,hKeptProduct i j]
  rfl

#print axioms rootOperatorColumn_run
end EvenTI.P16Recover

set_option autoImplicit false
set_option maxRecDepth 28000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPRank20261007 (KQ)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

variable {K : Type} [Field K] [Fintype K] (F : FieldPresentation K)

def installKernelWorkspace : Com := .assign KQ.WS (.var qN.WS)

/-- Point the kernel at the very same field slots used for operator arithmetic.
The physical compiler copies one address and never copies the matrices. -/
theorem installKernelWorkspace_run {B S : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) :
    ∃ t, Run B installKernelWorkspace s t 2 ∧ Slots F canonical KQ.WS S B t ∧
      (∀ j, val F canonical KQ.WS t j=val F canonical qN.WS s j) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  let t := s.setVar KQ.WS (s.vars qN.WS)
  have hBound : s.vars qN.WS < B := by
    have := hS.fit
    have := hS.base.memory_word
    omega
  have hr : Run B installKernelWorkspace s t 2 := Run.assign (ev_var rfl hBound)
  have hq : Slots F canonical qN.WS S B t :=
    Slots.setVar F canonical hS (by decide) (by decide) _
  have he : t.vars KQ.WS=t.vars qN.WS := by
    simp [t,vars_setVar,show qN.WS ≠ KQ.WS by decide]
  have hK : Slots F canonical KQ.WS S B t := by
    refine ⟨hq.base,by decide,?_,?_,?_,hq.slots_word⟩
    · rw [he]; exact hq.fit
    · rw [he]; exact hq.modulus_apart
    · rw [he]; exact hq.canon
  refine ⟨t,hr,hK,?_,rfl,rfl,rfl⟩
  intro i
  calc
    val F canonical KQ.WS t i = val F canonical qN.WS t i := by simp only [val,he]
    _ = val F canonical qN.WS s i := val_setVar F canonical (by decide) s _ _

#print axioms installKernelWorkspace_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPRank20261007 (KQ)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18IMPIntertwinerScan20261001 (blockSize)
open Mathproof.Problem18ClaudeIMPUniformBanks20261002 (uw)
open Mathproof.Problem18IMPKernelWitness20261001 (decoded)
open Mathproof.Problem18IMPUniformKernelFromMatrix20261002 (program budget)

noncomputable def sharedRootKernel : Com := .seq installKernelWorkspace program

/-- Run the exact root extractor directly on the operator arithmetic bank. -/
theorem sharedRootKernel_run {K A : Type} [Field K] [Fintype K] [DecidableEq K]
    [Field A] [Algebra K A] {n m B S : ℕ} {s : Env}
    (F : FieldPresentation K) (C : A ≃ₗ[K] (Fin n → K))
    (R : A →ₗ[K] (Fin m → K)) (hR : Function.Injective R) (u : Aˣ)
    (hS : Slots F canonical qN.WS S B s)
    (hRows : s.vars uw.nR=m) (hCols : s.vars uw.mR=n)
    (hCap : (n+1)*blockSize m n ≤ S)
    (hData : ∀ (i : Fin m) (j : Fin n), val F canonical qN.WS s (5+j.val*m+i.val) =
      frobeniusRootRectMatrix C R u i j) :
    ∃ t, Run B sharedRootKernel s t (2+budget F m n) ∧ Slots F canonical KQ.WS S B t ∧
      (decoded F m n t = none ↔ ¬ ∃ a : Aˣ, a^(Fintype.card K-1)=u) ∧
      (∀ x, decoded F m n t = some x →
        ∃ hx : C.symm x ≠ 0, Units.mk0 (C.symm x) hx ^ (Fintype.card K-1) = u) ∧
      (∀ j < S, (n+1)*blockSize m n ≤ j → val F canonical KQ.WS t j = val F canonical qN.WS s j) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨v,hr,hV,hVal,_,hIn,hOut⟩ := installKernelWorkspace_run F hS
  have hf := Frame.of_run hr
  obtain ⟨t,ht,hT,hNone,hSome,hKeep,hIt,hOt⟩ := frobeniusRootRect_run F C R hR u hV
    ((hf.vars _ (by decide)).trans hRows) ((hf.vars _ (by decide)).trans hCols) hCap
    (fun i j => (hVal _).trans (hData i j))
  exact ⟨t,hr.seq ht,hT,hNone,hSome,fun j hj hsep => (hKeep j hj hsep).trans (hVal j),
    hIt.trans hIn,hOt.trans hOut⟩

#print axioms sharedRootKernel_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Matrix
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)

/-- If the installed field data use faithful multiplication operators, the
physical output is literally one column of the rectangular root system. -/
theorem rootOperatorColumn_installs {K A : Type} [Field K] [Fintype K] [DecidableEq K]
    [Field A] [Algebra K A] {d n : ℕ} (F : FieldPresentation K)
    (C : A ≃ₗ[K] (Fin d → K)) (R : A →ₗ[K] (Fin (n*n) → K))
    (rho : A →ₐ[K] Matrix (Fin n) (Fin n) K)
    (hRead : ∀ x (i : Fin (n*n)),
      R x i = rho x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    (u : Aˣ) (col : Fin d) (hn : 0 < n)
    {B S dst tmp pow basis product unit zero : ℕ} {s : Env}
    (h : RootOperatorLayout F B S n dst tmp pow basis product unit zero s)
    (hA : MatBlock F s basis (rho (C.symm (Pi.single col 1))))
    (hU : MatBlock F s unit (rho (u:A))) :
    ∃ t, Run B (rootOperatorColumn F) s t (rootOperatorColumnCost F n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i : Fin (n*n), val F canonical qN.WS t (dst+i.val)=frobeniusRootRectMatrix C R u i col) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨t,ht,hs,hM,hi,ho⟩ := rootOperatorColumn_run F _ _ hn h hA hU
  refine ⟨t,ht,hs,?_,hi,ho⟩
  intro i
  let ij : Fin n × Fin n := finProdFinEquiv.symm i
  have hI : ij.1.val*n+ij.2.val = i.val := by
    have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
    change (finProdFinEquiv ij).val=i.val at h
    rw [finProdFinEquiv_apply_val] at h
    calc ij.1.val*n + ij.2.val = ij.2.val+n*ij.1.val := by ring
      _ = i.val := h
  rw [frobeniusRootRectMatrix_entry,hRead,map_sub,map_pow,map_mul,←hI]
  exact hM ij.1 ij.2

#print axioms rootOperatorColumn_installs
end EvenTI.P16Recover
