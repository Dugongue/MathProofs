import EvenP19ScalarInstalledProbe


set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 25000

namespace EvenTI.P21ScalarScan

open EvenTI.P15Scalar
open EvenTI.P18Scalar (runScalarProbeWith)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

private def usableProbe : Cond := .eq (.var crtActive) (.lit 1)

/-- Feed the recovered modular assignment to the live consumer. Infeasible
probes contribute the identity. Each successful probe carries a feasible
prefix and exposes exactly the consumer's bit about that assignment. -/
theorem runScalarProbeWithStable_run {M W m n C : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M) (consume : Com) (answer : String)
    (test : (Fin n → ZMod M) → Bool) (hId : test 0 = true)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCap : (s.arrs constraintMatrix).length < W) (hRhs : (s.arrs crtRhsBank).length = m+n)
    (hIndex : s.vars probeIndex = i.val) (hValue : s.vars probeValue = a.val)
    (hNone : ∀ u, RecoveryLayout M m n u → RecoveryLayout M m n (u.setVar answer 1))
    (hUse : ∀ (u : Env) (x : Fin n → ZMod M),
      Run W runScalarKernelProbe s u (runScalarKernelProbeCost M m n) →
      Frame runScalarKernelProbe s u →
      RecoveryLayout M m n u → Canonical M (u.arrs constraintMatrix) →
      u.vars crtActive = 1 →
      (∀ j, (u.arrs coordinateBank).getD j.val 0 = (x j).val) →
      ∃ v, Run W consume u v C ∧ v.vars answer ≤ 1 ∧
        (v.vars answer = 1 ↔ test x = true) ∧
        RecoveryLayout M m n v ∧ Canonical M (v.arrs constraintMatrix)) :
    let A := incidenceMatrix M src
    let B := fixedCoordinateMatrix A (i.val+1)
    let b := fixedCoordinateRhs (0 : Fin m → ZMod M) (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W (runScalarProbeWith consume answer) s t
      (runScalarKernelProbeCost M m n+C+6) ∧
      Frame (runScalarProbeWith consume answer) s t ∧
      RecoveryLayout M m n t ∧ Canonical M (t.arrs constraintMatrix) ∧
      t.vars answer ≤ 1 ∧ (t.vars answer = 1 ↔ test (selection.getD 0) = true) ∧
      (selection.isSome = true ↔ ∃ x, B.mulVec x = b) ∧
      (∀ x, selection = some x → B.mulVec x = b) := by
  obtain ⟨u,r0,f0,hu,hCan,hActive,hExact,hPayload⟩ := runScalarKernelProbe_run
    src i a hW hRows hL hs hSrc hCanonical hCap hRhs hIndex hValue
  have h1 : 1 < W := by omega
  by_cases h : u.vars crtActive = 1
  · obtain ⟨x,hSol,hWords⟩ := hPayload h
    obtain ⟨v,r1,hBit,hVerdict,hStable,hStillCan⟩ := hUse u x r0 f0 hu hCan h hWords
    have hEval : usableProbe.evalB W u = some true :=
      evalB_condEq (ev_var h h1) (evalB_lit h1)
    have rr : Run W (runScalarProbeWith consume answer) s v
        (runScalarKernelProbeCost M m n+C+6) :=
      (r0.seq (Run.ite_true (d:=.assign answer (.lit 1)) hEval r1)).mono (by
        simp [usableProbe,Cond.size,Expr.size] <;> omega)
    refine ⟨v,some x,rr,Frame.of_run rr,hStable,hStillCan,hBit,hVerdict,⟨fun _ => ⟨x,hSol⟩,fun _ => rfl⟩,?_⟩
    intro y hy
    exact (Option.some.inj hy) ▸ hSol
  · have hZ : u.vars crtActive = 0 := by omega
    have hEval : usableProbe.evalB W u = some false :=
      evalB_condEq (ev_var hZ (by omega)) (evalB_lit (n:=1) h1)
    let v := u.setVar answer 1
    have r1 : Run W (.assign answer (.lit 1)) u v 2 := Run.assign (evalB_lit h1)
    have rr : Run W (runScalarProbeWith consume answer) s v
        (runScalarKernelProbeCost M m n+C+6) :=
      (r0.seq (Run.ite_false (c:=consume) hEval r1)).mono (by
        simp [usableProbe,Cond.size,Expr.size] <;> omega)
    refine ⟨v,none,rr,Frame.of_run rr,hNone u hu,hCan,by simp [v],by simp [v,hId],?_,?_⟩
    · constructor
      · simp
      · intro hSolution
        exact False.elim (h (hExact.mpr hSolution))
    · intro x hx
      cases hx

#print axioms runScalarProbeWithStable_run
end EvenTI.P21ScalarScan
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000

namespace EvenTI.P21ScalarScan

open EvenTI.P18Scalar (arrayWords_of_run)
open EvenTI.P19Scalar.InstalledProbe (chartResidueTest runInstalledChartProbe runInstalledChartProbeCost)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P19Scalar.PrefixStencilScan (checkInstalledChartResidues checkInstalledChartResidues_run)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

local macro "keepLayout" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.RecoveryLayout.fromFrame))

/-- The complete paid homogeneous prefix probe now recovers actual CRT
coordinates, constructs the installed chart stencil, and evaluates exact
residue equalities in that bank. There is no action-matrix callback premise. -/
theorem runInstalledChartProbeStable_run
    {M W m n L columns zero : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (chart sites : List ℕ) (site : Fin L → Fin n) (reference : Fin n)
    (hSiteIndex : ∀ k : Fin L, sites.getD (k.val/columns) 0=(site k).val)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCapacity : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length=m+n)
    (hIndex : s.vars probeIndex=i.val) (hValue : s.vars probeValue=a.val)
    (hL : L < W) (hColumns : columns < W) (hZero : zero < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hTarget : L ≤ (s.arrs activeSlotBank).length)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hZ : s.vars stencilZero=zero) (hRef : s.vars stencilReference=reference.val)
    (hCoordLength : (s.arrs coordinateBank).length < W)
    (hCoordWords : ∀ v ∈ s.arrs coordinateBank, v < W) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M)
      (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W runInstalledChartProbe s t
      (runInstalledChartProbeCost M m n L) ∧
      Frame runInstalledChartProbe s t ∧
      RecoveryLayout M m n t ∧ Canonical M (t.arrs constraintMatrix) ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        chartResidueTest chart zero site reference (selection.getD 0)=true) ∧
      (selection.isSome=true ↔ ∃ x, C.mulVec x=rhs) ∧
      (∀ x, selection=some x → C.mulVec x=rhs) := by
  have hOne : 1 < W := by omega
  let test := chartResidueTest (M:=M) chart zero site reference
  have hIdentity : test 0=true := by simp [test,chartResidueTest]
  have hUse (u : Env) (x : Fin n → ZMod M)
      (r0 : Run W runScalarKernelProbe s u (runScalarKernelProbeCost M m n))
      (f : Frame runScalarKernelProbe s u)
      (hu : RecoveryLayout M m n u) (hc : Canonical M (u.arrs constraintMatrix))
      (ha : u.vars crtActive=1)
      (hx : ∀ j, (u.arrs coordinateBank).getD j.val 0=(x j).val) :
      ∃ v, Run W checkInstalledChartResidues u v (70*L+70) ∧
        v.vars activeWordAnswer ≤ 1 ∧
        (v.vars activeWordAnswer=1 ↔ test x=true) ∧
        RecoveryLayout M m n v ∧ Canonical M (v.arrs constraintMatrix) := by
    let coords := u.arrs coordinateBank
    have hCoordsWord : coords.length < W := (f.len coordinateBank).trans_lt hCoordLength
    have hCoordsValues : ∀ v ∈ coords, v < W := arrayWords_of_run r0 coordinateBank hCoordWords
    have hReference : reference.val < coords.length := reference.isLt.trans_le hu.destLen
    have hIndices (k : ℕ) (hk : k < L) :
        sites.getD (k/columns) 0 < coords.length := by
      rw [hSiteIndex ⟨k,hk⟩]
      exact (site ⟨k,hk⟩).isLt.trans_le hu.destLen
    obtain ⟨v,rv,hBit,hVerdict,hOther,hInput,hOutput⟩ :=
      checkInstalledChartResidues_run chart sites coords hOne hL hColumns hZero
        hChartFit hSiteFit hChartWords hSiteWords
        ((f.arrs _ (by decide)).trans hChart)
        ((f.arrs _ (by decide)).trans hSites)
        (by rw [f.len]; exact hTarget)
        ((f.vars _ (by decide)).trans hLimit)
        ((f.vars _ (by decide)).trans hCols)
        ((f.vars _ (by decide)).trans hZ)
        ((f.vars _ (by decide)).trans hRef)
        rfl hCoordsWord hCoordsValues hReference hIndices
    have he :
        (∀ k < L, chart.getD k 0 ≠ zero →
          coords.getD (sites.getD (k/columns) 0) 0=coords.getD reference.val 0) ↔ test x=true := by
      simp only [test,chartResidueTest,decide_eq_true_eq]
      constructor
      · intro h k hk
        have hh := h k.val k.isLt hk
        rw [hSiteIndex k,hx,hx] at hh
        exact hh
      · intro h k hk hz
        rw [hSiteIndex ⟨k,hk⟩,hx,hx]
        exact h ⟨k,hk⟩ hz
    have frame := Frame.of_run rv
    have restored : RecoveryLayout M m n v := keepLayout hu frame
      (by decide) (by decide) (by decide) (by decide)
      (by rw [frame.arrs _ (by decide)]; exact hu.workCanon)
    have canon : Canonical M (v.arrs constraintMatrix) := by
      rw [frame.arrs _ (by decide)]
      exact hc
    exact ⟨v,rv,hBit,hVerdict.trans he,restored,canon⟩
  have hNone (u : Env) (hu : RecoveryLayout M m n u) :
      RecoveryLayout M m n (u.setVar activeWordAnswer 1) := by
    have rn : Run W (.assign activeWordAnswer (.lit 1)) u (u.setVar activeWordAnswer 1) 2 :=
      Run.assign (evalB_lit hOne)
    exact keepLayout hu (Frame.of_run rn) (by decide) (by decide) (by decide) (by decide) hu.workCanon
  obtain ⟨t,selection,hr,hf,hRecover,hCan,hBit,hVerdict,hSome,hSolution⟩ :=
    runScalarProbeWithStable_run src i a checkInstalledChartResidues activeWordAnswer test hIdentity
      hW hRows hLayoutSize hLayout hSrc hCanonical hCapacity hRhs hIndex hValue hNone hUse
  refine ⟨t,selection,hr.mono ?_,hf,hRecover,hCan,hBit,hVerdict,hSome,hSolution⟩
  unfold runInstalledChartProbeCost
  omega

#print axioms runInstalledChartProbeStable_run
end EvenTI.P21ScalarScan
