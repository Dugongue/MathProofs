import Mathproof.MinimumGenerationPhysicalGreedyHeaderInstall

namespace Mathproof.MinimumGeneration.PhysicalGreedyHeaderSums

open SearchTransducer PhysicalGreedyHeader PhysicalGreedyHeaderInstall

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

abbrev P := TapeAddition.machine

def accumulator (i : Fin 3) : Bank := ⟨13+i.val,by omega⟩

def baseIndex (i : Fin 3) : Fin 8 := ⟨5+i.val,by omega⟩

private theorem accumulator_ne (i : Fin 3) (j : Bank) (hj : j.val ≤ 12 ∨ j.val = 16) :
    accumulator i ≠ j := fun e => by
  have v := congrArg (fun x : Bank => x.val) e
  change 13+i.val = j.val at v
  have := i.isLt
  omega

def additionBanks (i : Fin 3) : Fin P.workTapes ↪ Bank where
  toFun j := if j = 0 then accumulator i else if j = 1 then 12 else if j = 2 then 16 else 3
  inj' j k eq := by
    change Fin 4 at j k
    have a : accumulator i ≠ (12 : Bank) := accumulator_ne i 12 (by decide)
    have b : accumulator i ≠ (16 : Bank) := accumulator_ne i 16 (by decide)
    have c : accumulator i ≠ (3 : Bank) := accumulator_ne i 3 (by decide)
    fin_cases j <;> fin_cases k <;> first | rfl | simp_all

private def advance (i : Fin 3) : Option (Fin 3) :=
  if h : i.val+1 < 3 then some ⟨i.val+1,h⟩ else none

abbrev stages : Stages 3 P.states 17 where
  first := 0
  entry _ := P.initialState
  transition i := (P.relocateBanks (additionBanks i)).transition
  next i _ := advance i

abbrev machine := stages.machine

def inputConfig (i : Fin 3) (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    (stages.component i).Config :=
  ⟨P.initialState,input,fun _ => 0,cells,prior⟩

def start (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    machine.Config := stages.tag 0 (inputConfig 0 input cells prior)

def write (n value : Nat) (i : Fin 3) (cells : Bank → Int → Option Bool) : Bank → Int → Option Bool :=
  Function.update cells (accumulator i) (wordAt (width n) value)

def finalCells (n id x : Nat) (old : Bank → Int → Option Bool) : Bank → Int → Option Bool :=
  write n (fixed n id 7 + x) 2 (write n (fixed n id 6 + x) 1
    (write n (fixed n id 5 + x) 0 old))

theorem finalFrame {n id x : Nat} (old : Bank → Int → Option Bool)
    (j : Bank) (hj : j.val ≤ 12 ∨ j.val = 16) :
    finalCells n id x old j = old j := by
  simp [finalCells, write, (accumulator_ne 0 j hj).symm,
    (accumulator_ne 1 j hj).symm, (accumulator_ne 2 j hj).symm]

theorem finalMarkers {n id x : Nat} (old : Bank → Int → Option Bool) :
    finalCells n id x old 13 = wordAt (width n) (markers n id x 3) ∧
    finalCells n id x old 14 = wordAt (width n) (markers n id x 4) ∧
    finalCells n id x old 15 = wordAt (width n) (header n id x + 1) := by
  obtain ⟨e0,e1,e2⟩ := after_add n id x
  refine ⟨?_,?_,?_⟩ <;> simp [finalCells, write, accumulator, e0,e1,e2]

private theorem configEq {M : SearchTransducer} (c d : M.Config)
    (hq : c.state = d.state) (hi : c.inputHead = d.inputHead)
    (hh : c.workHead = d.workHead) (hc : c.workCell = d.workCell)
    (ho : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem addOnce (i : Fin 3) {raw prior : List Bool} {input : Int}
    {n base x : Nat} {cells : Bank → Int → Option Bool}
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length)
    (fit : x < 2 ^ width n)
    (acc : cells (accumulator i) = wordAt (width n) base)
    (arg : cells 12 = wordAt (width n) x)
    (count : cells 16 = wordAt (width n) 0)
    (zero : cells 3 = wordAt (width n) 0) :
    ∃ d : (stages.component i).Config,
      (stages.component i).BoundedSegment raw (width n+1) (inputConfig i input cells prior) d
        (TapeAddition.additionSteps (width n) x) ∧
      (stages.component i).step raw d = none ∧
      d.inputHead = input ∧ d.workHead = (fun _ => 0) ∧
      d.workCell = write n (base+x) i cells ∧ d.outputReversed = prior := by
  let w := width n
  let e := additionBanks i
  let a := TapeAddition.startConfig w base x 0 input prior
  let b := TapeAddition.stopConfig w (base+x) x input prior
  obtain ⟨run,halt⟩ := TapeAddition.executeAddition raw prior input w base x 0 hin fit
  let aa := P.bankConfig e a (fun _ => 0) cells
  let bb := P.bankConfig e b (fun _ => 0) cells
  have ha := P.relocateBanks_segment e run (heads := fun _ => 0) (cells := cells) (by simp)
  have hq : aa.state = (inputConfig i input cells prior).state := rfl
  have hh (c : P.Config) (hc : c.workHead = (fun _ => 0)) :
      (P.bankConfig e c (fun _ => 0) cells).workHead = fun _ => 0 := by
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨k,rfl⟩ := hj
      exact (P.bankConfig_head_image e c _ _ k).trans (congrFun hc k)
    · exact (P.bankConfig_frame e c _ _ hj).1
  have hAcells : aa.workCell = cells := by
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨k,rfl⟩ := hj
      rw [show aa.workCell (e k) = a.workCell k from P.bankConfig_cell_image e a _ _ k]
      change Fin 4 at k
      fin_cases k
      · exact (register_work _ _).trans acc.symm
      · exact (register_work _ _).trans arg.symm
      · exact (register_work _ _).trans count.symm
      · exact (register_work _ _).trans zero.symm
    · exact (P.bankConfig_frame e a _ _ hj).2
  have hBcells : bb.workCell = write n (base+x) i cells := by
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨k,rfl⟩ := hj
      rw [show bb.workCell (e k) = b.workCell k from P.bankConfig_cell_image e b _ _ k]
      change Fin 4 at k
      fin_cases k
      · change TapeAddition.register w (base+x) = write n (base+x) i cells (accumulator i)
        simp [write, register_work, wordAt, w]
      · change TapeAddition.register w x = write n (base+x) i cells 12
        simpa [write, (accumulator_ne i 12 (by decide)).symm, wordAt, register_work, w] using arg.symm
      · change TapeAddition.register w 0 = write n (base+x) i cells 16
        simpa [write, (accumulator_ne i 16 (by decide)).symm, wordAt, register_work, w] using count.symm
      · change TapeAddition.register w 0 = write n (base+x) i cells 3
        simpa [write, (accumulator_ne i 3 (by decide)).symm, wordAt, register_work, w] using zero.symm
    · rw [(P.bankConfig_frame e b _ _ hj).2]
      have ne : j ≠ accumulator i := fun he => hj ⟨0, show accumulator i = j from he.symm⟩
      simp [write, ne]
  have same : aa = inputConfig i input cells prior :=
    configEq _ _ hq rfl (hh a rfl) hAcells rfl
  change (stages.component i).BoundedSegment raw (w+1) aa bb _ at ha
  rw [same] at ha
  have hStop : (stages.component i).step raw bb = none := by
    change (P.relocateBanks e).step raw (P.bankConfig e b (fun _ => 0) cells) = none
    rw [P.relocateBanks_step,halt]
    rfl
  exact ⟨bb,ha,hStop,rfl,hh b rfl,hBcells,rfl⟩

private theorem jump {i j : Fin 3} (d : (stages.component i).Config)
    (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool)
    (hi : d.inputHead = input) (hh : d.workHead = (fun _ => 0))
    (hc : d.workCell = cells) (ho : d.outputReversed = prior) :
    stages.enter j d = inputConfig j input cells prior :=
  configEq _ _ rfl hi hh hc ho

/-- Add the live widened candidate to each of the three reset bases. The single
finite controller preserves every other marker and workspace bank. -/
theorem execute {n id x : Nat} {raw prior : List Bool} {input : Int}
    {old : Bank → Int → Option Bool} (R : Ready n id x old)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) (fit : x < 2 ^ TableIO.width n) :
    ∃ (ticks : Nat) (d : machine.Config),
      machine.BoundedSegment raw (width n+1) (start input (afterCopy n old) prior) d ticks ∧
      machine.step raw d = none ∧ d.inputHead = input ∧ d.workHead = (fun _ => 0) ∧
      d.workCell = finalCells n id x (afterCopy n old) ∧ d.outputReversed = prior := by
  let F := afterCopy n old
  let G := write n (fixed n id 5 + x) 0 F
  let H := write n (fixed n id 6 + x) 1 G
  have f0 : x < 2 ^ width n := fit.trans_le (Nat.pow_le_pow_right (by decide) (by unfold width; omega))
  have hX : F 12 = wordAt (width n) x := addend_ready R fit
  have hC : F 16 = wordAt (width n) 0 := countdown_ready R
  have hZ : F 3 = wordAt (width n) 0 := (afterCopy_sources n old 3 (by decide)).trans (R.constants 0)
  obtain ⟨a,ra,sa,ia,ha,ca,oa⟩  := addOnce (prior := prior) (cells := F) (base := fixed n id 5) 0 hin f0
    (accumulator_ready R 0) hX hC hZ
  obtain ⟨b,rb,sb,ib,hb,cb,ob⟩  := addOnce (prior := prior) (cells := G) (base := fixed n id 6) 1 hin f0
    (by simpa [G, write, accumulator] using accumulator_ready R 1)
    (by simpa [G, write, accumulator] using hX)
    (by simpa [G, write, accumulator] using hC)
    (by simpa [G, write, accumulator] using hZ)
  obtain ⟨c,rc,sc,ic,hc,cc,oc⟩  := addOnce (prior := prior) (cells := H) (base := fixed n id 7) 2 hin f0
    (by simpa [H, G, write, accumulator] using accumulator_ready R 2)
    (by simpa [H, G, write, accumulator] using hX)
    (by simpa [H, G, write, accumulator] using hC)
    (by simpa [H, G, write, accumulator] using hZ)
  let ticks := TapeAddition.additionSteps (width n) x
  have route : stages.Routed raw (width n+1) 0 (inputConfig 0 input F prior) 2 c
      (ticks+1+(ticks+1+ticks)) := by
    refine .call ra sa (show stages.next 0 a.state = some 1 by rfl) ?_
    rw [jump a input G prior ia ha ca oa]
    refine .call rb sb (show stages.next 1 b.state = some 2 by rfl) ?_
    rw [jump b input H prior ib hb cb ob]
    exact .finish rc
  obtain ⟨hRun,hHalt⟩ := stages.routed_stop route sc (by rfl)
  exact ⟨_,stages.tag 2 c,hRun,hHalt,ic,hc,cc,oc⟩

end Mathproof.MinimumGeneration.PhysicalGreedyHeaderSums
