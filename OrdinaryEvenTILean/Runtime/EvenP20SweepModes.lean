import EvenP20SweepPrepared
import EvenP17RecoverAnchorLoad

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 45000

namespace EvenTI.P20Sweep

open scoped Polynomial
open UniqueFactorizationMonoid
open EvenTI.P19Recover EvenTI.P17Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_mul ev_var)
open Mathproof.Problem17Primary48RawArchive (Output)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Use one fixed-capacity factor range per mode. Unused factor rows do not
change the next mode's address. -/
def installModeOffset (capacity : String) : Com :=
  .assign savedOffset (.mul (.var anchorWanted) (.var capacity))

theorem installModeOffset_run (F : FieldPresentation K) {capacity : String} {B Sn k cap : ℕ} {s : Env}
    (h : Slots F canonical qN.WS Sn B s) (hk : s.vars anchorWanted=k)
    (hc : s.vars capacity=cap) (hkB : k<B) (hcB : cap<B) (hSize : k*cap<B) :
    ∃ t, Run B (installModeOffset capacity) s t 4 ∧ Slots F canonical qN.WS Sn B t ∧
      t.vars savedOffset=k*cap ∧
      (∀ a, val F canonical qN.WS t a=val F canonical qN.WS s a) ∧
      t.arrs=s.arrs ∧ Frame (installModeOffset capacity) s t := by
  let t := s.setVar savedOffset (k*cap)
  have r : Run B (installModeOffset capacity) s t 4 :=
    Run.assign (ev_mul (ev_var hk hkB) (ev_var hc hcB) hSize)
  exact ⟨t,r,Slots.setVar F canonical h (by decide) (by decide) _,
    by simp [t], fun a => val_setVar F canonical (by decide) s _ a,rfl,Frame.of_run r⟩

theorem earlierModeBeforeOffset {i j cap rows : ℕ} (h : i < j) (hRows : rows ≤ cap) :
    i*cap+rows≤j*cap :=
  (Nat.add_le_add_left hRows _).trans (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr h))


noncomputable def recoverAllModes (prepare : Com) (count : String) (O : Output) (address : String) : Com :=
  forLoop anchorWanted count (.seq prepare (recoverArchiveFactors O address))

/-- The mode loop accepts the archive order chosen by its actual preparation
program. Its certificate records the complete factor list for every mode. -/
theorem recoverAllModes_of_prepare (F : FieldPresentation K) {B modes pc fc : ℕ}
    (O : Output) (address count : String) (hc : anchorWanted≠count)
    (names : SweepNames O address) (prepare : Com)
    (n : ℕ → ℕ) (A : (m : ℕ) → Matrix (Fin (n m)) (Fin (n m)) K) (U : ℕ → SweepLayout)
    (bounds : ∀ m < modes, ∀ l ≤ (U m).N, SweepBounds F (n m) l B (U m))
    (order : ∀ j < modes, ∀ m < modes, j < m →
      (U j).base=(U m).base ∧ (U j).lane=(U m).lane ∧ (U j).offset+(U j).N≤(U m).offset)
    (clock : ∀ m < modes, (maxModeRowTime F (U m).N (n m)+8)*(U m).N+6≤fc)
    (keepCursor : anchorWanted ∉ scalarWrites (.seq prepare (recoverArchiveFactors O address)))
    (keepCount : count ∉ scalarWrites (.seq prepare (recoverArchiveFactors O address)))
    (Ready : Env → Prop) {s : Env} (hReady : Ready s) (hModes : s.vars count=modes) (hModesB : modes<B)
    (readyIndex : ∀ u i, Ready u → Ready (u.setVar anchorWanted i))
    (prepareMode : ∀ m < modes, ∀ u, Ready u → u.vars anchorWanted=m →
      ∃ v L, Run B prepare u v pc ∧ L.length≤(U m).N ∧
        PreparedMode F (A m) L O address (U m) B v ∧ DurablePrefix F (U m) u v ∧ Ready v)
    (afterMode : ∀ m < modes, ∀ (L : List (Polynomial K)) u v, Ready u →
      PreparedMode F (A m) L O address (U m) B v →
      Run B (recoverArchiveFactors O address) u v ((maxModeRowTime F (U m).N (n m)+8)*L.length+6) →
      Ready v) :
    ∃ t, Run B (recoverAllModes prepare count O address) s t ((pc+fc+8)*modes+6) ∧
      Ready t ∧ t.vars anchorWanted=modes ∧
      ∀ m < modes, ∃ L : List (Polynomial K), L.length≤(U m).N ∧
        (L : Multiset (Polynomial K))=(normalizedFactors (A m).charpoly).dedup ∧
        ∀ i < L.length, SavedChart F (A m) (factorAt (A m) L i) ((U m).offset+i)
          (rowBasis (U m).base (U m).lane ((U m).offset+i))
          (rowChart (U m).base (U m).lane ((U m).offset+i)) t := by
  let Row (m : ℕ) (L : List (Polynomial K)) (i : ℕ) (v : Env) : Prop :=
    SavedChart F (A m) (factorAt (A m) L i) ((U m).offset+i)
      (rowBasis (U m).base (U m).lane ((U m).offset+i))
      (rowChart (U m).base (U m).lane ((U m).offset+i)) v
  let Done (m : ℕ) (v : Env) : Prop :=
    ∃ L : List (Polynomial K), L.length≤(U m).N ∧
      (L : Multiset (Polynomial K))=(normalizedFactors (A m).charpoly).dedup ∧
      ∀ i < L.length, Row m L i v
  let Inv (i : ℕ) (v : Env) : Prop := Ready v ∧ ∀ m < i, Done m v
  let body := Com.seq prepare (recoverArchiveFactors O address)
  have p₀ : Inv 0 (s.setVar anchorWanted 0) := ⟨readyIndex _ _ hReady,by simp⟩
  have step : ∀ m < modes, ∀ u, Inv m u → u.vars anchorWanted=m → u.vars count=modes →
      ∃ v, Run B body u v (pc+fc) ∧ v.vars anchorWanted=m ∧ v.vars count=modes ∧
        Inv (m+1) (v.setVar anchorWanted (m+1)) := by
    intro m hm u hU hu huCnt
    obtain ⟨w,L,rw,hLen,hw,oldW,hrW⟩ := prepareMode m hm u hU.1 hu
    obtain ⟨v,rv,hv,_,oldV,hRows⟩ := recoverPreparedMode_run F names (bounds m hm L.length hLen) hw
    have hStepCost := (Nat.add_le_add_right (Nat.mul_le_mul_left _ hLen) 6).trans (clock m hm)
    have r : Run B body u v (pc+fc) := rw.seq (rv.mono hStepCost)
    have frame := Frame.of_run r
    have hReadyV := afterMode m hm L w v hrW hv rv
    have old := oldW.trans F oldV
    refine ⟨v,r,(frame.vars _ keepCursor).trans hu,(frame.vars _ keepCount).trans huCnt,
      readyIndex _ _ hReadyV,?_⟩
    intro j hj
    by_cases eq : j=m
    · subst j
      exact ⟨L,hLen,hw.installed.list,fun i hi => (hRows i hi).setVar F (by decide) _⟩
    · have earlier : j < m := by omega
      have jm : j < modes := earlier.trans hm
      obtain ⟨G,hGL,hList,rows⟩ := hU.2 j earlier
      refine ⟨G,hGL,hList,?_⟩
      intro i hi
      obtain ⟨basis,lane,offset⟩ := order j jm m hm earlier
      have row : (U j).offset+i < (U m).offset := by omega
      have cap := (bounds j jm G.length hGL).matrixLane
      have hTop := rowChart_end_le_next (U m).base (U m).lane row
      have hBasis (k : ℕ) (hk : k < (n j)*(n j)) :
          (U m).base ≤ rowBasis (U j).base (U j).lane ((U j).offset+i)+k ∧
          rowBasis (U j).base (U j).lane ((U j).offset+i)+k <
            rowBasis (U m).base (U m).lane (U m).offset := by
        rw [basis,lane]
        rw [rowChart] at hTop
        rw [lane] at cap
        constructor
        · exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
        · omega
      have hChart (k : ℕ) (hk : k < (n j)*(n j)) :
          (U m).base ≤ rowChart (U j).base (U j).lane ((U j).offset+i)+k ∧
          rowChart (U j).base (U j).lane ((U j).offset+i)+k <
            rowBasis (U m).base (U m).lane (U m).offset := by
        rw [basis,lane]
        rw [lane] at cap
        constructor
        · unfold rowChart rowBasis
          omega
        · omega
      have hOld := (rows i hi).frame F (old.2 _ row)
        (fun k hk => old.1 _ (hBasis k hk).1 (hBasis k hk).2)
        (fun k hk => old.1 _ (hChart k hk).1 (hChart k hk).2)
      exact hOld.setVar F (by decide) _
  obtain ⟨t,r,hEnd,hIdx⟩ := forLoop_run anchorWanted count body hc Inv hModes hModesB p₀ step
  exact ⟨t,r,hEnd.1,hIdx,hEnd.2⟩

#print axioms recoverAllModes_of_prepare
end EvenTI.P20Sweep

