import Mathproof.MinimumGenerationBipartiteCayley
import Mathproof.MinimumGenerationPrefixDifference
import Mathproof.MinimumGenerationVirtualMarkerScan

namespace Mathproof.MinimumGeneration.CayleyQueryDispatch

open SearchTransducer
open InputPosition (work)
open Lax51Proofs.RamToTM (subBits)

set_option backward.isDefEq.respectTransparency false

private abbrev sub := RankPhysicalSubtract.machine
private abbrev done := RankPhysicalSubtract.done

def orderBank : Fin 5 := 0
def rowBank : Fin 5 := 1
def colBank : Fin 5 := 2
def rowTrial : Fin 5 := 3
def colTrial : Fin 5 := 4

private def pair (j : Fin 5) (hne : j ≠ orderBank) : Fin 2 ↪ Fin 5 where
  toFun i := if i = 0 then orderBank else j
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

private def rowPair : Fin 2 ↪ Fin 5 := pair rowTrial (by decide)
private def colPair : Fin 2 ↪ Fin 5 := pair colTrial (by decide)
private def bankPair (i : Fin 3) : Fin 2 ↪ Fin 5 := if i = 0 then rowPair else colPair

private def colStage (b : Bool) : Fin 3 := if b then 1 else 2

/-- The row borrowing flag selects the literal finite stage used for the
column subtraction. -/
abbrev stages : Stages 3 7 5 where
  first := 0
  entry := fun _ => 0
  transition i := (sub.relocateBanks (bankPair i)).transition
  next i q := if i = 0 then some (colStage (decide (q = done true))) else none

abbrev machine := stages.machine

def rowIsLeft (c : machine.Config) : Bool :=
  decide ((finProdFinEquiv.symm c.state).1 = (1 : Fin 3))

def colIsLeft (c : machine.Config) : Bool :=
  decide ((finProdFinEquiv.symm c.state).2 = done true)

def rowLabelBank (c : machine.Config) : Fin 5 := if rowIsLeft c then rowBank else rowTrial

def colLabelBank (c : machine.Config) : Fin 5 := if colIsLeft c then colBank else colTrial

/-- Return the live endpoint banks in left-to-right order; same-side cells
are zero and require no group operation. -/
def crossBanks (c : machine.Config) : Option (Fin 5 × Fin 5) :=
  if rowIsLeft c = colIsLeft c then none
  else if rowIsLeft c then some (rowLabelBank c, colLabelBank c)
  else some (colLabelBank c, rowLabelBank c)

private def zeroHeads : Fin 5 → Int := fun _ => 0

private def initCells (w n x y : ℕ) (i : Fin 5) : Int → Option Bool :=
  if i = orderBank then work (encodeLabel w n)
  else if i = rowBank ∨ i = rowTrial then work (encodeLabel w x) else work (encodeLabel w y)

private def diffWords (w x n : ℕ) := subBits (encodeLabel w x) (encodeLabel w n) false

private def rowEntry (w n x y : ℕ) (parked : Int) (out : List Bool) :
    (stages.component 0).Config :=
  sub.bankConfig (bankPair 0)
    (RankPhysicalSubtract.cfg 0 0 (encodeLabel w x) (encodeLabel w n) out parked)
    zeroHeads (initCells w n x y)

private def rowExit (w n x y : ℕ) (parked : Int) (out : List Bool) :
    (stages.component 0).Config :=
  sub.bankConfig (bankPair 0)
    (RankPhysicalSubtract.cfg (done (decide (x < n))) 0 (diffWords w x n) (encodeLabel w n) out parked)
    zeroHeads (initCells w n x y)

private def colEntry (i : Fin 3) (w n y : ℕ) (r : (stages.component 0).Config) :
    (stages.component i).Config :=
  sub.bankConfig (bankPair i)
    (RankPhysicalSubtract.cfg 0 0 (encodeLabel w y) (encodeLabel w n) r.outputReversed r.inputHead)
    r.workHead r.workCell

private def colExit (i : Fin 3) (w n y : ℕ) (r : (stages.component 0).Config) :
    (stages.component i).Config :=
  sub.bankConfig (bankPair i)
    (RankPhysicalSubtract.cfg (done (decide (y < n))) 0 (diffWords w y n) (encodeLabel w n)
      r.outputReversed r.inputHead)
    r.workHead r.workCell

def start (w n x y : ℕ) (parked : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (rowEntry w n x y parked out)

def finish (w n x y : ℕ) (parked : Int) (out : List Bool) : machine.Config :=
  let i := colStage (decide (x < n))
  stages.tag i (colExit i w n y (rowExit w n x y parked out))

private theorem bankHeads (e : Fin 2 ↪ Fin 5) (q : Fin 7)
    (t s o : List Bool) (p : Int) (heads : Fin 5 → Int) (cells : Fin 5 → Int → Option Bool)
    (h : ∀ j, heads j = 0) :
    ∀ j, (sub.bankConfig e (RankPhysicalSubtract.cfg q 0 t s o p) heads cells).workHead j = 0 := by
  intro j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    exact bankConfig_head_image sub e _ heads cells k
  · exact ((bankConfig_frame sub e _ heads cells hj).1).trans (h j)

private theorem rowHead (w n x y : ℕ) (parked : Int) (out : List Bool) :
    ∀ j, (rowExit w n x y parked out).workHead j = 0 :=
  bankHeads _ _ _ _ _ _ _ _ (fun _ => rfl)

private theorem sameConfig {M : SearchTransducer} (a b : M.Config)
    (state : a.state = b.state) (input : a.inputHead = b.inputHead)
    (heads : a.workHead = b.workHead) (cells : a.workCell = b.workCell)
    (output : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem colStage_ne_zero (b : Bool) : colStage b ≠ 0 := by cases b <;> decide

private theorem colPair_eq (b : Bool) : bankPair (colStage b) = colPair := by
  exact if_neg (colStage_ne_zero b)

private theorem colGraft (w n x y : ℕ) (parked : Int) (out : List Bool) :
    let r := rowExit w n x y parked out
    let i := colStage (decide (x < n))
    stages.enter i r = colEntry i w n y r := by
  intro r i
  have hpair : bankPair i = colPair := colPair_eq _
  apply sameConfig
  · rfl
  · rfl
  · funext j
    exact (rowHead w n x y parked out j).trans
      (bankHeads _ _ _ _ _ _ _ _ (rowHead w n x y parked out) j).symm
  · funext j
    by_cases hj : j ∈ Set.range (bankPair i)
    · obtain ⟨k, rfl⟩ := hj
      change r.workCell (bankPair i k) =
        (sub.bankConfig (bankPair i) _ r.workHead r.workCell).workCell (bankPair i k)
      rw [bankConfig_cell_image]
      fin_cases k
      · change r.workCell (bankPair i 0) = work (encodeLabel w n)
        rw [hpair]
        change r.workCell (bankPair 0 0) = _
        exact bankConfig_cell_image sub (bankPair 0) _ zeroHeads _ 0
      · change r.workCell (bankPair i 1) = work (encodeLabel w y)
        rw [hpair]
        change (sub.bankConfig (bankPair 0) _ zeroHeads _).workCell colTrial = _
        have hn : colTrial ∉ Set.range (bankPair 0) := by
          rintro ⟨q,h⟩
          fin_cases q <;> contradiction
        exact (bankConfig_frame sub (bankPair 0) _ zeroHeads _ hn).2
    · exact (bankConfig_frame sub (bankPair i) _ r.workHead r.workCell hj).2.symm
  · rfl

/-- Two actual calls to the framed physical subtractor classify both sides,
produce normalized endpoint candidates, and restore the complete head layout. -/
theorem execute (word out : List Bool) (parked : Int) (w n x y : ℕ)
    (bounds : (-1 : Int) ≤ parked ∧ parked ≤ word.length)
    (hn : n < 2^w) (hx : x < 2^w) (hy : y < 2^w) :
    machine.BoundedSegment word (w+1) (start w n x y parked out)
      (finish w n x y parked out) (2*w+3+1+(2*w+3)) ∧
    machine.step word (finish w n x y parked out) = none := by
  let r := rowExit w n x y parked out
  let i := colStage (decide (x < n))
  obtain ⟨rowRun, rowStop⟩ := RankPhysicalSubtract.execute_encoded word out parked w x n bounds hx hn
  obtain ⟨colRun, colStop⟩ := RankPhysicalSubtract.execute_encoded word out parked w y n bounds hy hn
  have first : (stages.component 0).BoundedSegment word (w+1) (rowEntry w n x y parked out)
      r (2*w+3) :=
    relocateBanks_segment sub (bankPair 0) (heads := zeroHeads) (cells := initCells w n x y)
      rowRun (by simp [zeroHeads])
  have hRowStop : (stages.component 0).step word r = none := by
    have eq := relocateBanks_step sub (bankPair 0) word
      (RankPhysicalSubtract.cfg (done (decide (x < n))) 0 (diffWords w x n) (encodeLabel w n) out parked)
      zeroHeads (initCells w n x y)
    exact eq.trans (congrArg _ rowStop)
  have second : (stages.component i).BoundedSegment word (w+1) (colEntry i w n y r)
      (colExit i w n y r) (2*w+3) :=
    relocateBanks_segment sub (bankPair i) (heads := r.workHead) (cells := r.workCell)
      colRun (fun j _ => by
        have h : r.workHead j = 0 := rowHead w n x y parked out j
        rw [h]
        simp)
  have hColStop : (stages.component i).step word (colExit i w n y r) = none := by
    have eq := relocateBanks_step sub (bankPair i) word
      (RankPhysicalSubtract.cfg (done (decide (y < n))) 0 (diffWords w y n) (encodeLabel w n)
        out parked) r.workHead r.workCell
    exact eq.trans (congrArg _ colStop)
  have next : stages.next 0 r.state = some i := by
    by_cases h : x < n <;>
      simp [stages, r, i, rowExit, bankConfig, RankPhysicalSubtract.cfg, h, RankPhysicalSubtract.done]
  have jump := stages.segment_handoff hRowStop next (first.2 _ le_rfl _ first.1)
  change stages.machine.BoundedSegment word _ _ (stages.tag i (stages.enter i r)) 1 at jump
  rw [show stages.enter i r = colEntry i w n y r from colGraft w n x y parked out] at jump
  constructor
  · exact BoundedSegment.append _ (BoundedSegment.append _ (stages.segment_component 0 first) jump)
      (stages.segment_component i second)
  · change stages.machine.step word (stages.tag i (colExit i w n y r)) = none
    rw [stages.step_halt i hColStop]
    have hh : stages.next i (colExit i w n y r).state = none := by
      change (if i = 0 then _ else _) = none
      exact if_neg (colStage_ne_zero _)
    rw [hh]
    rfl

private theorem notInPair (e : Fin 2 ↪ Fin 5) {j : Fin 5}
    (a : j ≠ e 0) (b : j ≠ e 1) : j ∉ Set.range e := by
  rintro ⟨i,h⟩
  fin_cases i
  · exact a h.symm
  · exact b h.symm

private theorem cell_row {w n x y : ℕ} {parked : Int} {out : List Bool} :
    (finish w n x y parked out).workCell rowBank = work (encodeLabel w x) := by
  let r := rowExit w n x y parked out
  let i := colStage (decide (x < n))
  have hPair := colPair_eq (decide (x < n))
  have hn : rowBank ∉ Set.range (bankPair i) := by
    exact notInPair _ (by rw [hPair]; decide) (by rw [hPair]; decide)
  change (sub.bankConfig (bankPair i) _ r.workHead r.workCell).workCell rowBank = _
  rw [(bankConfig_frame _ _ _ _ _ hn).2]
  have hm : rowBank ∉ Set.range (bankPair 0) := notInPair _ (by decide) (by decide)
  change (sub.bankConfig (bankPair 0) _ zeroHeads (initCells w n x y)).workCell rowBank = _
  exact (bankConfig_frame _ _ _ _ _ hm).2

private theorem cell_col {w n x y : ℕ} {parked : Int} {out : List Bool} :
    (finish w n x y parked out).workCell colBank = work (encodeLabel w y) := by
  let r := rowExit w n x y parked out
  let i := colStage (decide (x < n))
  have hPair := colPair_eq (decide (x < n))
  have hn : colBank ∉ Set.range (bankPair i) := by
    exact notInPair _ (by rw [hPair]; decide) (by rw [hPair]; decide)
  change (sub.bankConfig (bankPair i) _ r.workHead r.workCell).workCell colBank = _
  rw [(bankConfig_frame _ _ _ _ _ hn).2]
  have hm : colBank ∉ Set.range (bankPair 0) := notInPair _ (by decide) (by decide)
  change (sub.bankConfig (bankPair 0) _ zeroHeads (initCells w n x y)).workCell colBank = _
  exact (bankConfig_frame _ _ _ _ _ hm).2

private theorem cell_rowTrial {w n x y : ℕ} {parked : Int} {out : List Bool} :
    (finish w n x y parked out).workCell rowTrial = work (diffWords w x n) := by
  let r := rowExit w n x y parked out
  let i := colStage (decide (x < n))
  have hPair := colPair_eq (decide (x < n))
  have hn : rowTrial ∉ Set.range (bankPair i) :=
    notInPair _ (by rw [hPair]; decide) (by rw [hPair]; decide)
  change (sub.bankConfig (bankPair i) _ r.workHead r.workCell).workCell rowTrial = _
  rw [(bankConfig_frame _ _ _ _ _ hn).2]
  change (sub.bankConfig (bankPair 0) _ zeroHeads (initCells w n x y)).workCell (bankPair 0 1) = _
  exact bankConfig_cell_image _ _ _ _ _ 1

private theorem cell_colTrial {w n x y : ℕ} {parked : Int} {out : List Bool} :
    (finish w n x y parked out).workCell colTrial = work (diffWords w y n) := by
  let r := rowExit w n x y parked out
  let i := colStage (decide (x < n))
  have hi : bankPair i 1 = colTrial := by rw [colPair_eq]; rfl
  change (sub.bankConfig (bankPair i) _ r.workHead r.workCell).workCell colTrial = _
  rw [← hi]
  exact bankConfig_cell_image _ _ _ _ _ 1

private theorem subtractWord (w x n : ℕ) (fit : x < 2 ^ w) (rightSide : n ≤ x) :
    diffWords w x n = encodeLabel w (x - n) := by
  unfold diffWords
  rw [← RankPhysicalSubtract.fixedBits_eq_encodeLabel w x fit,
    ← RankPhysicalSubtract.fixedBits_eq_encodeLabel w n (rightSide.trans_lt fit),
    ← Lax51Proofs.RamToTM.fixedBits_sub_of_le w rightSide,
    RankPhysicalSubtract.fixedBits_eq_encodeLabel w (x - n) ((Nat.sub_le _ _).trans_lt fit)]

/-- The side flags, live registers, and restored frame at the literal halt. -/
theorem finishSpec (w n x y : ℕ) (parked : Int) (out : List Bool)
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    let d := finish w n x y parked out
    d.inputHead = parked ∧ d.outputReversed = out ∧ (∀ j, d.workHead j = 0) ∧
    rowIsLeft d = decide (x < n) ∧ colIsLeft d = decide (y < n) ∧
    d.workCell (rowLabelBank d) = work (encodeLabel w (if x < n then x else x - n)) ∧
    d.workCell (colLabelBank d) = work (encodeLabel w (if y < n then y else y - n)) := by
  have hRow : rowIsLeft (finish w n x y parked out) = decide (x < n) := by
    by_cases h : x < n <;> simp [rowIsLeft, finish, colStage, Stages.tag, h]
  have hCol : colIsLeft (finish w n x y parked out) = decide (y < n) := by
    by_cases h : y < n <;> simp [colIsLeft, finish, Stages.tag, colExit, bankConfig,
      RankPhysicalSubtract.cfg, RankPhysicalSubtract.done, h]
  have hHeads : ∀ j, (finish w n x y parked out).workHead j = 0 := by
    intro j
    let r := rowExit w n x y parked out
    exact bankHeads (bankPair (colStage (decide (x < n)))) (done (decide (y < n)))
      (diffWords w y n) (encodeLabel w n) out parked r.workHead r.workCell
      (rowHead w n x y parked out) j
  refine ⟨rfl, rfl, hHeads, hRow, hCol, ?_, ?_⟩
  · unfold rowLabelBank
    rw [hRow]
    by_cases h : x < n
    · simpa only [h, decide_true, if_true] using
        (cell_row (w := w) (n := n) (x := x) (y := y) (parked := parked) (out := out))
    · rw [if_neg h]
      simpa only [h, decide_false, Bool.false_eq_true, if_false, subtractWord w x n hx (Nat.le_of_not_gt h)] using
        (cell_rowTrial (w := w) (n := n) (x := x) (y := y) (parked := parked) (out := out))
  · unfold colLabelBank
    rw [hCol]
    by_cases h : y < n
    · simpa only [h, decide_true, if_true] using
        (cell_col (w := w) (n := n) (x := x) (y := y) (parked := parked) (out := out))
    · rw [if_neg h]
      simpa only [h, decide_false, Bool.false_eq_true, if_false, subtractWord w y n hy (Nat.le_of_not_gt h)] using
        (cell_colTrial (w := w) (n := n) (x := x) (y := y) (parked := parked) (out := out))

/-- Finite control selects the literal left and right endpoint banks, in the
same orientation used by the bipartite adjacency theorem. -/
theorem crossBanksSpec {n : ℕ} (row col : Fin (n+n)) (w : ℕ)
    (cap : n+n ≤ 2 ^ w) (parked : Int) (out : List Bool) :
    let d := finish w n row.val col.val parked out
    match BipartiteCayley.endpoints row col with
    | none => crossBanks d = none
    | some (x,y) => ∃ a b, crossBanks d = some (a,b) ∧
        d.workCell a = work (encodeLabel w x.val) ∧
        d.workCell b = work (encodeLabel w y.val) := by
  let d := finish w n row.val col.val parked out
  obtain ⟨_, _, _, left, right, rowWord, colWord⟩ :=
    finishSpec w n row.val col.val parked out (row.isLt.trans_le cap) (col.isLt.trans_le cap)
  have hl : rowIsLeft d = decide (row.val < n) := left
  have hr : colIsLeft d = decide (col.val < n) := right
  change match BipartiteCayley.endpoints row col with
    | none => crossBanks d = none
    | some (x,y) => ∃ a b, crossBanks d = some (a,b) ∧ _ ∧ _
  unfold BipartiteCayley.endpoints BipartiteCayley.split
  by_cases x : row.val < n <;> by_cases y : col.val < n
  · simp [x, y, crossBanks, hl, hr]
  · simp only [dif_pos x, dif_neg y]
    refine ⟨rowLabelBank d, colLabelBank d, ?_, ?_, ?_⟩
    · simp [x, y, crossBanks, hl, hr]
    · simpa only [if_pos x] using rowWord
    · simpa only [if_neg y] using colWord
  · simp only [dif_neg x, dif_pos y]
    refine ⟨colLabelBank d, rowLabelBank d, ?_, ?_, ?_⟩
    · simp [x, y, crossBanks, hl, hr]
    · simpa only [if_pos y] using colWord
    · simpa only [if_neg x] using rowWord
  · simp [x, y, crossBanks, hl, hr]


end Mathproof.MinimumGeneration.CayleyQueryDispatch
