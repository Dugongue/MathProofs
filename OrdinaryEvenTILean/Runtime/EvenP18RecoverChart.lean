import EvenP6PrimaryBlocks
import EvenP6AlignGauge
import Mathproof.Meta.P15DecideIMPSolve20261007

/-! Exact coordinates of the selected anchor restricted to its live primary
basis. The solve routine reads the computed kernel columns themselves. -/
namespace EvenTI.P18Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial
open EvenTI.Contract EvenTI.PrimaryAlignment
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT KBLay XBs)
open Mathproof.P15DecideIMPRowKer20261007 (tRB)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC svLB svW svY svOK solveProg solveCost solve_run)

set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K : Type} [Field K] [Fintype K] {n w : ℕ}

theorem primaryChartColumn_unique (S : Matrix (Fin n) (Fin n) K) (f : K[X])
    (xs : Fin w → (Fin n → K)) (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval S f).mulVecLin)
    (j : Fin w) :
    ∃! y : Fin w → K, ∑ i, y i • xs i = S.mulVec (xs j) := by
  have hc : Commute (aeval S f) (aeval S (X : K[X])) :=
    (Commute.all _ _).map (aeval S)
  rw [aeval_X] at hc
  have hk : xs j ∈ (aeval S f).mulVecLin.ker := by
    rw [← hSpan]
    exact Submodule.subset_span ⟨j,rfl⟩
  have hz : (aeval S f).mulVec (xs j) = 0 := LinearMap.mem_ker.mp hk
  have hv : S.mulVec (xs j) ∈ (aeval S f).mulVecLin.ker := by
    apply LinearMap.mem_ker.mpr
    change (aeval S f).mulVec (S.mulVec (xs j)) = 0
    rw [Matrix.mulVec_mulVec,hc.eq,← Matrix.mulVec_mulVec,hz,Matrix.mulVec_zero]
  let L := frameFromVectors ((aeval S f).mulVecLin) xs hInd hSpan
  obtain ⟨y,hy⟩ := L.surjective ⟨S.mulVec (xs j),hv⟩
  have hy' : ∑ i, y i • xs i = S.mulVec (xs j) :=
    (frameFromVectors_apply _ _ hInd hSpan y).symm.trans (congrArg Subtype.val hy)
  refine ⟨y,hy',?_⟩
  intro z hz'
  apply L.injective
  apply Subtype.ext
  exact (frameFromVectors_apply _ _ hInd hSpan z).trans
    (hz'.trans (hy'.symm.trans (frameFromVectors_apply _ _ hInd hSpan y).symm))

/-- Compute the physical ambient Krylov columns from the original anchor and
the first installed primary column. This avoids a restriction and a basis
inversion on simple factors. -/
theorem ambientKrylovColumns (A : Matrix (Fin n) (Fin n) K)
    (S : Matrix (Fin w) (Fin w) K) (C : Matrix (Fin n) (Fin w) K)
    (h : C*S=A*C) (i : Fin n) (j : Fin w) :
    (C*krylovMatrix S) i j = ((A^j.val).mulVec (C.mulVec (firstVector w))) i := by
  have step (t : ℕ) : C*S^t=A^t*C := by
    induction t with
    | zero => simp
    | succ t ih =>
      simp only [pow_succ]
      calc
        C * (S^t*S) = (C*S^t)*S := (Matrix.mul_assoc C _ S).symm
        _ = (A^t*C)*S := by rw [ih]
        _ = A^t*(C*S) := Matrix.mul_assoc _ C S
        _ = A^t*(A*C) := by rw [h]
        _ = (A^t*A)*C := (Matrix.mul_assoc _ A C).symm
  change (C.mulVec ((S^j.val).mulVec (firstVector w))) i = _
  rw [Matrix.mulVec_mulVec,step,← Matrix.mulVec_mulVec]

structure ChartPorts (σ : Env) (w n CB RB AM OUT LB W YB Z : ℕ) : Prop where
  m : σ.vars svM = w
  dim : σ.vars svL = n
  cb : σ.vars svC = CB
  rb : σ.vars tRB = RB
  am : σ.vars kAM = AM
  out : σ.vars kOUT = OUT
  lb : σ.vars svLB = LB
  work : σ.vars svW = W
  y : σ.vars svY = YB
  z : σ.vars dZ = Z
  one : σ.vars rOs = Z+1
  first : σ.vars dT = Z+2
  second : σ.vars dU = Z+3

structure ChartGeometry (w n CB RB AM OUT LB W YB Z Sn B : ℕ) : Prop where
  kernel : KBLay n (w+1) AM OUT Z Sn B
  start : (w+1+1)*XBs n (w+1) ≤ CB
  columns : CB+(w+1)*n ≤ RB
  transpose : RB+n*(w+1) ≤ AM
  out : OUT+(w+1)*(w+1) ≤ LB
  labels : LB+w+2 ≤ W
  work : W+2 ≤ YB
  y : YB+w ≤ Z

variable [DecidableEq K]

/-- The paid solve succeeds on the live primary columns and a single
multiplication column. Its output is the unique chart column in this basis. -/
theorem primaryChartColumn_run (F : FieldPresentation K) (S : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (xs : Fin w → Fin n → K) (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs) = LinearMap.ker (aeval S f).mulVecLin)
    (j : Fin w) {CB RB AM OUT LB W YB Z Sn B : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS Sn B σ) (P : ChartPorts σ w n CB RB AM OUT LB W YB Z)
    (G : ChartGeometry w n CB RB AM OUT LB W YB Z Sn B)
    (hw : σ.vars qN.WS = F.e+1)
    (hCols : ∀ i : Fin w, ∀ k : Fin n, val F canonical qN.WS σ (CB+(i.val*n+k.val)) = xs i k)
    (hRhs : ∀ k : Fin n, val F canonical qN.WS σ (CB+(w*n+k.val)) = S.mulVec (xs j) k)
    (hz : val F canonical qN.WS σ Z = 0)
    (ho : val F canonical qN.WS σ (Z+1) = 1) :
    ∃ τ, Run B solveProg σ τ (solveCost F w n) ∧ Slots F canonical qN.WS Sn B τ ∧
      τ.vars svOK = 1 ∧
      ∑ i : Fin w, val F canonical qN.WS τ (YB+i.val) • xs i = S.mulVec (xs j) ∧
      (∀ y : Fin w → K, (∑ i, y i • xs i = S.mulVec (xs j)) →
        ∀ i, y i = val F canonical qN.WS τ (YB+i.val)) ∧
      Frame solveProg σ τ := by
  let C : Fin (w+1) → Fin n → K := Fin.lastCases (S.mulVec (xs j)) xs
  have data : ∀ (i : Fin (w+1)) (k : Fin n),
      val F canonical qN.WS σ (CB+(i.val*n+k.val)) = C i k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro k
      simpa [C] using hRhs k
    · intro k
      simpa [C] using hCols j k
  obtain ⟨τ,r,s,result,_,_,_,_⟩ := solve_run F G.kernel C hS
    P.m P.dim P.cb P.rb P.am P.out P.lb P.work P.y P.z P.one P.first P.second
    hw data hz ho G.start G.columns G.transpose G.out G.labels G.work G.y
  obtain ⟨y,hy,uniq⟩ := primaryChartColumn_unique S f xs hInd hSpan j
  rcases result with ⟨ok,answer⟩ | ⟨_,none⟩
  · have hAnswer : ∑ i : Fin w, val F canonical qN.WS τ (YB+i.val) • xs i = S.mulVec (xs j) := by
      simpa [C] using answer
    refine ⟨τ,r,s,ok,hAnswer,?_,Frame.of_run r⟩
    intro z hz' i
    exact congrFun ((uniq z hz').trans (uniq _ hAnswer).symm) i
  · exact (none ⟨y,by simpa [C] using hy⟩).elim

#print axioms ambientKrylovColumns
#print axioms primaryChartColumn_unique
#print axioms primaryChartColumn_run
end EvenTI.P18Recover

