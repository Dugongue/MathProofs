import EvenP21ScalarScanState
import EvenP21ScalarScanChoice
import EvenP18ScalarProbeSubgroup

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000

namespace EvenTI.P21ScalarScan

open scoped Matrix
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open EvenTI.P15Scalar (probeIndex probeValue)
open EvenTI.P17Scalar (scalarProbeCursor scalarProbeLimit scalarProbeLoop scalarProbeLoop_run probeCursorInput activeWordAnswer)
open EvenTI.P18Scalar (chartResidueSubgroup chartResidueTest_iff_mem)
open EvenTI.P19Scalar.InstalledProbe (chartResidueTest runInstalledChartProbe runInstalledChartProbeCost)
open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithCoefficients20261007 (modR)

/-- A single row-major coordinate/residue visit, followed by its conjunction. -/
def scanProbeVisit : Com := .seq runInstalledChartProbe andProbeAnswer

def scanInstalledMode : Com :=
  .seq (.assign scanAnswer (.lit 1)) (scalarProbeLoop scanProbeVisit)

def scanInstalledModeCost (M m n L : ℕ) : ℕ :=
  (runInstalledChartProbeCost M m n L+24)*(n*M)+8

def probeKey {M n : ℕ} (i : Fin n) (a : ZMod M) : ℕ := M*i.val+a.val

private theorem probeKey_lt {M n : ℕ} [NeZero M] (i : Fin n) (a : ZMod M) :
    probeKey i a < n*M := by
  calc
    probeKey i a < M*(i.val+1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left (ZMod.val_lt a) _
    _ ≤ M*n := Nat.mul_le_mul_left _ i.isLt
    _ = n*M := Nat.mul_comm _ _

private theorem probeKey_parts {M n k : ℕ} [NeZero M] {i : Fin n} {a : ZMod M}
    (h : probeKey i a = k) : i.val = k/M ∧ a.val = k%M := by
  rw [←h]
  unfold probeKey
  rw [Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne M)),Nat.div_eq_of_lt (ZMod.val_lt a),
    Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt (ZMod.val_lt a)]
  exact ⟨rfl,rfl⟩

/-- Exhaustively run the paid CRT prefix probes in a single installed mode.
The boolean output equals scalarity on the entire incidence kernel. The
coordinate, chart, incidence and CRT scratch banks remain reusable. -/
theorem scanInstalledMode_run {M W m n L columns zero : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n)
    (chart sites : List ℕ) (site : Fin L → Fin n) (reference : Fin n)
    (hSiteIndex : ∀ k : Fin L, sites.getD (k.val/columns) 0 = (site k).val)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hL : L < W) (hColumns : columns < W) (hZero : zero < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hLimit : s.vars scalarProbeLimit = n*M) (hNM : n*M < W)
    (hs : ScanInput M W L columns zero src chart sites reference s) :
    ∃ t, Run W scanInstalledMode s t (scanInstalledModeCost M m n L) ∧
      Frame scanInstalledMode s t ∧
      ScanInput M W L columns zero src chart sites reference t ∧
      t.vars scanAnswer ≤ 1 ∧
      (t.vars scanAnswer = 1 ↔ ∀ x, (incidenceMatrix M src).mulVec x = 0 →
        x ∈ chartResidueSubgroup chart zero site reference) := by
  let A := incidenceMatrix M src
  let H := chartResidueSubgroup (M:=M) chart zero site reference
  let good := ∀ x, A.mulVec x = 0 → x ∈ H
  let I (k : ℕ) (u : Env) :=
    ScanInput M W L columns zero src chart sites reference u ∧
    u.vars scanAnswer ≤ 1 ∧ (good → u.vars scanAnswer = 1) ∧
    (u.vars scanAnswer = 1 → ∀ (i : Fin n) (a : ZMod M), probeKey i a < k →
      (∃ x, ProbeFeasible A i a x) → ∃ x ∈ H, ProbeFeasible A i a x)
  have hTest (x : Fin n → ZMod M) :
      chartResidueTest chart zero site reference x = true ↔ x ∈ H :=
    chartResidueTest_iff_mem chart zero site reference x
  have hOne : 1 < W := by omega
  have hMW : M < W := by omega
  let s₁ := s.setVar scanAnswer 1
  have r0 : Run W (.assign scanAnswer (.lit 1)) s s₁ 2 := Run.assign (evalB_lit hOne)
  have hInit : I 0 (s₁.setVar scalarProbeCursor 0) := by
    refine ⟨(hs.setVar scanAnswer 1 (by decide)).setVar scalarProbeCursor 0 (by decide),
      by simp [s₁,show scanAnswer ≠ scalarProbeCursor by decide],
      fun _ => by simp [s₁,show scanAnswer ≠ scalarProbeCursor by decide],?_⟩
    exact fun _ _ _ hk => False.elim (Nat.not_lt_zero _ hk)
  have step : ∀ k < n*M, ∀ u, I k u → u.vars scalarProbeCursor = k →
      u.vars scalarProbeLimit = n*M → u.vars modR = M →
      ∃ v, Run W scanProbeVisit (probeCursorInput u M k) v
        (runInstalledChartProbeCost M m n L+6) ∧
        v.vars scalarProbeCursor = k ∧ v.vars scalarProbeLimit = n*M ∧ v.vars modR = M ∧
        I (k+1) (v.setVar scalarProbeCursor (k+1)) := by
    intro k hk u hu hCur hLim hMod
    let w := probeCursorInput u M k
    let i : Fin n := ⟨k/M,(Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne M))).mpr hk⟩
    let a : ZMod M := ((k%M : ℕ) : ZMod M)
    have av : a.val = k%M := by
      rw [show a = ((k%M : ℕ) : ZMod M) by rfl,ZMod.val_natCast,
        Nat.mod_mod]
    have wi : w.vars probeIndex = i.val := by
      simp [w,probeCursorInput,i,show probeIndex ≠ probeValue by decide]
    have wa : w.vars probeValue = a.val := by simp [w,probeCursorInput,av]
    have hw : ScanInput M W L columns zero src chart sites reference w :=
      (hu.1.setVar probeIndex (k/M) (by decide)).setVar probeValue (k%M) (by decide)
    obtain ⟨v,choice,rp,fp,hl,hc,hBit,hVerdict,hSome,hSound⟩ :=
      runInstalledChartProbeStable_run src i a chart sites site reference hSiteIndex
        hW hRows hLayoutSize hw.recovery hw.incidence hw.canonical hw.capacity hw.rhs wi wa
        hL hColumns hZero hChartFit hSiteFit hChartWords hSiteWords hw.chartEq hw.sitesEq hw.target
        hw.limit hw.cols hw.zeroWord hw.referenceWord hw.coordLength hw.coordWords
    let z := if v.vars activeWordAnswer = 1 then v else v.setVar scanAnswer 0
    obtain ⟨rz,hzBound,hzYes⟩ := andProbeAnswer_run hOne hBit
    have hv := hw.afterProbe rp fp hl hc
    have hNextInput : ScanInput M W L columns zero src chart sites reference z := by
      by_cases h : v.vars activeWordAnswer = 1
      · simpa [z,h] using hv
      · simpa [z,h] using hv.setVar scanAnswer 0 (by decide)
    have hR : Run W scanProbeVisit w z (runInstalledChartProbeCost M m n L+6) :=
      rp.seq rz
    have f := Frame.of_run hR
    have readScan : v.vars scanAnswer = u.vars scanAnswer := by
      rw [fp.vars _ (by decide)]
      simp [w,probeCursorInput,show scanAnswer ≠ probeIndex by decide,
        show scanAnswer ≠ probeValue by decide]
    have stepVerdict : z.vars scanAnswer = 1 ↔
        u.vars scanAnswer = 1 ∧ choice.getD 0 ∈ H := by
      rw [hzYes,readScan,hVerdict,hTest]
    have zg (r : String) (hP : r ∉ Mathproof.Problem18IMPFieldLayout20261001.scalarWrites scanProbeVisit)
        (hI : r ≠ probeIndex) (hV : r ≠ probeValue) : z.vars r = u.vars r := by
      rw [f.vars _ hP]
      simp [w,probeCursorInput,hI,hV]
    refine ⟨z,hR,(zg _ (by decide) (by decide) (by decide)).trans hCur,
      (zg _ (by decide) (by decide) (by decide)).trans hLim,hNextInput.recovery.modWord,?_⟩
    have zreg : (z.setVar scalarProbeCursor (k+1)).vars scanAnswer = z.vars scanAnswer := by
      simp [show scanAnswer ≠ scalarProbeCursor by decide]
    refine ⟨hNextInput.setVar scalarProbeCursor (k+1) (by decide),?_,?_,?_⟩
    · rw [zreg]
      exact hzBound.trans (by rw [readScan]; exact hu.2.1)
    · intro hg
      rw [zreg,stepVerdict]
      refine ⟨hu.2.2.1 hg,?_⟩
      cases h : choice with
      | none => simpa [h] using H.zero_mem
      | some x =>
        have hf : ProbeFeasible A i a x := hSound x h
        simpa [h] using hg x ((probeFeasible_iff A i a x).mp hf).1
    · intro hy j b hKey hFeasible
      rw [zreg,stepVerdict] at hy
      by_cases hOld : probeKey j b < k
      · exact hu.2.2.2 hy.1 j b hOld hFeasible
      · have hNew : probeKey j b = k := by omega
        obtain ⟨hji,hba⟩ := probeKey_parts hNew
        have hj : j = i := Fin.ext hji
        have hb : b = a := ZMod.val_injective M (hba.trans av.symm)
        subst j
        subst b
        have hSome' : choice.isSome = true := hSome.mpr hFeasible
        obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hSome'
        refine ⟨x,?_,hSound x hx⟩
        simpa [hx] using hy.2
  have hLim₁ : s₁.vars scalarProbeLimit = n*M := by
    simpa [s₁,show scalarProbeLimit ≠ scanAnswer by decide] using hLimit
  have hM₁ : s₁.vars modR = M := by
    simpa [s₁,show modR ≠ scanAnswer by decide] using hs.recovery.modWord
  obtain ⟨t,rt,ht,_,_,_⟩ := scalarProbeLoop_run scanProbeVisit I hNM hMW hOne
    hLim₁ hM₁ hInit step
  have rr : Run W scanInstalledMode s t (scanInstalledModeCost M m n L) := by
    have hCost : runInstalledChartProbeCost M m n L+6+18 = runInstalledChartProbeCost M m n L+24 := by omega
    exact (r0.seq rt).mono (by unfold scanInstalledModeCost; rw [hCost]; omega)
  refine ⟨t,rr,Frame.of_run rr,ht.1,ht.2.1,?_,ht.2.2.1⟩
  intro hy
  exact kernel_of_prefix_choices A H (fun i a => ht.2.2.2 hy i a (probeKey_lt i a))

#print axioms scanInstalledMode_run
end EvenTI.P21ScalarScan
