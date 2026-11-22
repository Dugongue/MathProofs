import EvenP21ScalarScanLoop
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1500000

namespace EvenTI.P21ScalarScan

open scoped Matrix
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open EvenTI.P17Scalar (scalarProbeLimit)
open EvenTI.P18Scalar (chartResidueSubgroup)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

def scanModeCursor : String := "even.p21.scalar.scan.mode"
def scanModeCount : String := "even.p21.scalar.scan.mode_count"
def scanAllAnswer : String := "even.p21.scalar.scan.all_answer"

structure ScanModeInput (W n : ℕ) where
  L : ℕ
  columns : ℕ
  zero : ℕ
  chart : List ℕ
  sites : List ℕ
  site : Fin L → Fin n
  reference : Fin n
  index : ∀ k : Fin L, sites.getD (k.val/columns) 0 = (site k).val
  wordL : L < W
  wordColumns : columns < W
  wordZero : zero < W
  fitChart : L ≤ chart.length
  fitSites : ∀ k < L, k/columns < sites.length
  wordChart : ∀ a ∈ chart, a < W
  wordSites : ∀ a ∈ sites, a < W

def ScanModeInput.installed {M W m n : ℕ} (P : ScanModeInput W n)
    (src : Fin m → Fin 3 → Fin n) (s : Env) : Prop :=
  ScanInput M W P.L P.columns P.zero src P.chart P.sites P.reference s ∧
  s.vars scalarProbeLimit = n*M

def ScanModeInput.scalar {M W m n : ℕ} (P : ScanModeInput W n)
    (src : Fin m → Fin 3 → Fin n) : Prop :=
  ∀ x, (incidenceMatrix M src).mulVec x = 0 →
    x ∈ chartResidueSubgroup P.chart P.zero P.site P.reference

def andModeAnswer : Com :=
  .ite (.eq (.var scanAnswer) (.lit 1)) .skip (.assign scanAllAnswer (.lit 0))

theorem andModeAnswer_run {s : Env} {W : ℕ} (hW : 1 < W)
    (hBit : s.vars scanAnswer ≤ 1) :
    let t := if s.vars scanAnswer = 1 then s else s.setVar scanAllAnswer 0
    Run W andModeAnswer s t 6 ∧
      t.vars scanAllAnswer ≤ s.vars scanAllAnswer ∧
      (t.vars scanAllAnswer = 1 ↔ s.vars scanAllAnswer = 1 ∧ s.vars scanAnswer = 1) := by
  let test : Cond := .eq (.var scanAnswer) (.lit 1)
  by_cases hy : s.vars scanAnswer = 1
  · have e : test.evalB W s = some true := evalB_condEq (ev_var hy hW) (evalB_lit hW)
    have rr : Run W andModeAnswer s s 6 :=
      (Run.ite_true (d:=.assign scanAllAnswer (.lit 0)) e Run.skip).mono (by decide)
    simp [hy,rr]
  · have hz : s.vars scanAnswer = 0 := by omega
    have e : test.evalB W s = some false :=
      evalB_condEq (ev_var hz (by omega)) (evalB_lit (n:=1) hW)
    have rr : Run W andModeAnswer s (s.setVar scanAllAnswer 0) 6 :=
      (Run.ite_false (c:=.skip) e (Run.assign (evalB_lit (by omega)))).mono (by decide)
    simp [hy,rr]

def scanModeVisit (prepare : Com) : Com :=
  .seq prepare (.seq scanInstalledMode andModeAnswer)

def scanAcrossModes (prepare : Com) : Com :=
  .seq (.assign scanAllAnswer (.lit 1))
    (forLoop scanModeCursor scanModeCount (scanModeVisit prepare))

/-- Execute the actual selector and homogeneous probes for every mode. A
single reusable scratch area suffices. The installed mode proof is the physical
selector interface, and the only scalar test executed is the paid CRT scan. -/
theorem scanAcrossModes_run {M W m n modes pCost cCost : ℕ} [NeZero M]
    {s : Env} (src : Fin m → Fin 3 → Fin n) (plan : Fin modes → ScanModeInput W n)
    (prepare : Com) (Ready : Env → Prop)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hNM : n*M < W) (hModes : modes < W) (hCount : s.vars scanModeCount = modes)
    (hCost : ∀ i, scanInstalledModeCost M m n (plan i).L ≤ cCost)
    (hReady : Ready s)
    (hIndex : ∀ u k, Ready u → Ready (u.setVar scanModeCursor k))
    (hAnswer : ∀ u k, Ready u → Ready (u.setVar scanAllAnswer k))
    (hAfter : ∀ (i : Fin modes) u v, Ready u → Frame scanInstalledMode u v →
      (plan i).installed (M:=M) src v → Ready v)
    (hPrepCursor : scanModeCursor ∉ scalarWrites prepare)
    (hPrepCount : scanModeCount ∉ scalarWrites prepare)
    (hPrepAnswer : scanAllAnswer ∉ scalarWrites prepare)
    (hPrepare : ∀ (i : Fin modes) (u : Env), Ready u → u.vars scanModeCursor = i.val →
      ∃ v, Run W prepare u v pCost ∧ (plan i).installed (M:=M) src v ∧ Ready v) :
    ∃ t, Run W (scanAcrossModes prepare) s t ((pCost+cCost+14)*modes+8) ∧
      Frame (scanAcrossModes prepare) s t ∧ Ready t ∧ t.vars scanAllAnswer ≤ 1 ∧
      (t.vars scanAllAnswer = 1 ↔ ∀ i, (plan i).scalar (M:=M) src) := by
  let I (k : ℕ) (u : Env) := Ready u ∧ u.vars scanAllAnswer ≤ 1 ∧
    (u.vars scanAllAnswer = 1 ↔ ∀ i : Fin modes, i.val < k → (plan i).scalar (M:=M) src)
  let s₁ := s.setVar scanAllAnswer 1
  have hOne : 1 < W := by omega
  have r0 : Run W (.assign scanAllAnswer (.lit 1)) s s₁ 2 := Run.assign (evalB_lit hOne)
  have hi : I 0 (s₁.setVar scanModeCursor 0) := by
    refine ⟨hIndex _ _ (hAnswer _ _ hReady),?_,?_⟩ <;>
      simp [s₁,show scanAllAnswer ≠ scanModeCursor by decide]
  have step : ∀ k < modes, ∀ u, I k u → u.vars scanModeCursor = k →
      u.vars scanModeCount = modes →
      ∃ v, Run W (scanModeVisit prepare) u v (pCost+cCost+6) ∧
        v.vars scanModeCursor = k ∧ v.vars scanModeCount = modes ∧
        I (k+1) (v.setVar scanModeCursor (k+1)) := by
    intro k hk u hu hc hcnt
    let i : Fin modes := ⟨k,hk⟩
    let P := plan i
    obtain ⟨v,rp,inst,hv⟩ := hPrepare i u hu.1 hc
    obtain ⟨z,rs,fs,hScan,hBit,hSc⟩ := scanInstalledMode_run src P.chart P.sites P.site P.reference
      P.index hW hRows hLayoutSize P.wordL P.wordColumns P.wordZero P.fitChart P.fitSites
      P.wordChart P.wordSites inst.2 hNM inst.1
    let a := if z.vars scanAnswer = 1 then z else z.setVar scanAllAnswer 0
    obtain ⟨ra,hMono,hAnd⟩ := andModeAnswer_run hOne hBit
    have fa : Frame andModeAnswer z a := Frame.of_run ra
    have fp := Frame.of_run rp
    have rr : Run W (scanModeVisit prepare) u a (pCost+cCost+6) :=
      rp.seq ((rs.mono (hCost i)).seq ra)
    have hSame : z.vars scanAllAnswer = u.vars scanAllAnswer :=
      (fs.vars _ (by decide)).trans (fp.vars _ hPrepAnswer)
    have hNext : Ready a := by
      have rz := hAfter i v z hv fs ⟨hScan, (fs.vars _ (by decide)).trans inst.2⟩
      by_cases ha : z.vars scanAnswer = 1
      · simpa [a,ha] using rz
      · simpa [a,ha] using hAnswer z 0 rz
    have idx := (fa.vars scanModeCursor (by decide)).trans
      ((fs.vars _ (by decide)).trans ((fp.vars _ hPrepCursor).trans hc))
    have cnt := (fa.vars scanModeCount (by decide)).trans
      ((fs.vars _ (by decide)).trans ((fp.vars _ hPrepCount).trans hcnt))
    refine ⟨a,rr,idx,cnt,hIndex _ _ hNext,?_,?_⟩
    · simp only [vars_setVar, show scanAllAnswer ≠ scanModeCursor by decide, if_false]
      exact hMono.trans (by rw [hSame]; exact hu.2.1)
    · simp only [vars_setVar, show scanAllAnswer ≠ scanModeCursor by decide, if_false]
      rw [hAnd,hSame,hu.2.2,hSc]
      change ((∀ j : Fin modes, j.val < k → (plan j).scalar (M:=M) src) ∧
          P.scalar (M:=M) src) ↔ ∀ j : Fin modes, j.val < k+1 →
            (plan j).scalar (M:=M) src
      constructor
      · rintro ⟨prev,now⟩ j hj
        by_cases hOld : j.val < k
        · exact prev j hOld
        · have he : j = i := by
            apply Fin.ext
            change j.val = k
            omega
          exact he.symm ▸ now
      · intro all
        exact ⟨fun j hj => all j (by omega), all i (by exact Nat.lt_succ_self k)⟩
  have hCount₁ : s₁.vars scanModeCount = modes := by
    simpa [s₁,show scanModeCount ≠ scanAllAnswer by decide] using hCount
  obtain ⟨t,rt,ht,_⟩ := forLoop_run scanModeCursor scanModeCount (scanModeVisit prepare)
    (by decide) I hCount₁ hModes hi step
  have hBodyCost : pCost+cCost+6+8 = pCost+cCost+14 := by omega
  have rr : Run W (scanAcrossModes prepare) s t ((pCost+cCost+14)*modes+8) :=
    (r0.seq rt).mono (by rw [hBodyCost]; omega)
  refine ⟨t,rr,Frame.of_run rr,ht.1,ht.2.1,?_⟩
  rw [ht.2.2]
  exact ⟨fun h i => h i i.isLt,fun h i _ => h i⟩

#print axioms scanAcrossModes_run
end EvenTI.P21ScalarScan
