import Mathproof.MinimumGenerationCayleyReaderCandidate
import Mathproof.MinimumGenerationPhysicalGreedyReaderSetup

namespace Mathproof.MinimumGeneration.CayleyReaderRetarget

open SearchTransducer
open PhysicalGreedyTemplateCompose (Run lift liftRun Memory)
open CayleyReaderCandidate (W headerView readerView source clock)
open CayleyQueryPrefixModel (width)
open BipartiteCayley (left)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev H := PhysicalGreedyHeaderDriver.machine
abbrev C := CayleyReaderCandidate.machine
def headerBanks : Fin H.workTapes ↪ Fin W where
  toFun := CayleyReaderCandidate.header
  inj' := fun _ _ e => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin W => i.val) e))

def same : Fin C.workTapes ↪ Fin W := Function.Embedding.refl _
abbrev machine := (lift H headerBanks).follow (lift C same)

def staged {n : Nat} (G : Group (Fin n)) (y : Fin n) (m : Memory W) : Memory W :=
  fun j => if h : 74 ≤ j.val ∧ j.val < 91 then
    PhysicalGreedyHeaderDriver.final n G.toOne.one.val y.val (headerView m)
      ⟨j.val-74,by omega⟩
    else m j

def installed {n : Nat} (G : Group (Fin n)) (y : Fin n) (m : Memory W) (ticks : List Bool) :
    Memory W := TapeInstall.installed source (staged G y m) ticks.length

private theorem staged_header {n : Nat} (G : Group (Fin n)) (y : Fin n) (m : Memory W) (j : Fin H.workTapes) :
    staged G y m (headerBanks j) =
      PhysicalGreedyHeaderDriver.final n G.toOne.one.val y.val (headerView m) j := by
  have h : 74 ≤ (headerBanks j).val ∧ (headerBanks j).val < 91 := by
    change 74 ≤ 74+j.val ∧ 74+j.val < 91
    have jlt := j.isLt
    change j.val < 17 at jlt
    omega
  rw [staged,dif_pos h]
  congr 1
  exact Fin.ext (by change 74+j.val-74=j.val; omega)

private theorem staged_frame {n : Nat} (G : Group (Fin n)) (y : Fin n) (m : Memory W) (j : Fin W)
    (hj : j ∉ Set.range headerBanks) : staged G y m j = m j := by
  apply dif_neg
  intro h
  exact hj ⟨⟨j.val-74,by change j.val-74 < 17; omega⟩,
    Fin.ext (by change 74+(j.val-74)=j.val; omega)⟩

private theorem reader_staged {n : Nat} (G : Group (Fin n)) (y : Fin n) (m : Memory W) :
    readerView (staged G y m) = readerView m := by
  funext i
  apply staged_frame
  rintro ⟨j,e⟩
  have q := congrArg (fun a : Fin W => a.val) e
  change 74+j.val=i.val at q
  have := i.isLt
  omega

/-- Install the live candidate from the ordinal tape into the preserved Cayley
query reader, using the existing header machine followed by the copy sweep. -/
theorem execute {n : Nat} (G : Group (Fin n)) (cut p : Nat) (x y : Fin n)
    (ticks prior : List Bool) (input : Int) (m : Memory W)
    (R : CayleyReaderCycle.Ready G cut (left G.toOne.one) (left x) p ticks (readerView m))
    (H0 : PhysicalGreedyHeaderInstall.Ready n G.toOne.one.val y.val (headerView m))
    (hi : (-1 : Int) ≤ input ∧ input ≤ (@encodeCayley n G.toMul).length) :
    Run machine (@encodeCayley n G.toMul) (ticks.length+1) input prior m (installed G y m ticks) ∧
    CayleyReaderCycle.Ready G y.val (left G.toOne.one) (left y) 1 ticks
      (readerView (installed G y m ticks)) ∧
    headerView (installed G y m ticks) =
      PhysicalGreedyHeaderDriver.final n G.toOne.one.val y.val (headerView m) := by
  let raw := @encodeCayley n G.toMul
  let a := PhysicalGreedyHeaderDriver.start input (headerView m) prior
  obtain ⟨k,d,r,s,hin,heads,cells,out,live⟩ := PhysicalGreedyHeaderDriver.execute
    (raw := raw) (prior := prior) H0 hi (y.isLt.trans Nat.lt_log2_self)
  let h := PhysicalGreedyHeaderInstall.start input (headerView m) prior
  obtain ⟨asIn,ah,az,ao⟩ := PhysicalGreedyHeaderInstall.start_layout input (headerView m) prior
  have aIn : a.inputHead = input := asIn
  have aOut : a.outputReversed = prior := ao
  have aHead : a.workHead = fun _ => 0 := by
    funext i
    exact (PhysicalGreedyHeaderInstall.machine.bankConfig_head_image
      PhysicalGreedyHeaderDriver.banks h (fun _ => 0) (headerView m) i).trans (congrFun ah i)
  have aCell (i : Fin H.workTapes) : a.workCell i = m (headerBanks i) := by
    exact (PhysicalGreedyHeaderInstall.machine.bankConfig_cell_image
      PhysicalGreedyHeaderDriver.banks h (fun _ => 0) (headerView m) i).trans (congrFun az i)
  have hspace := (CayleyQueryPrefixModel.width_le G).trans R.body.clockEnough
  have first : Run (lift H headerBanks) raw (ticks.length+1) input prior m (staged G y m) :=
    liftRun H headerBanks (PhysicalEntry.segment_mono r (hspace.trans (Nat.le_succ _)))
      s rfl aIn hin aHead heads aOut out aCell
      (fun i => (congrFun cells i).trans (staged_header G y m i).symm)
      (fun i no => (staged_frame G y m i no).symm)
  have layout : headerView (staged G y m) =
      PhysicalGreedyHeaderDriver.final n G.toOne.one.val y.val (headerView m) := by
    funext i
    exact staged_header G y m i
  have L : PhysicalGreedyHeaderDriver.Live n G.toOne.one.val y.val (headerView (staged G y m)) := by
    rw [layout, ← cells]
    exact live
  have R' : CayleyReaderCycle.Ready G cut (left G.toOne.one) (left x) p ticks
      (readerView (staged G y m)) := by
    rw [reader_staged]
    exact R
  obtain ⟨cr,cs,ci,ch,co,cframe,ready⟩ := CayleyReaderCandidate.execute
    G cut p x y ticks prior input (staged G y m) R' L hi
  have second : Run (lift C same) raw (ticks.length+1) input prior (staged G y m) (installed G y m ticks) :=
    liftRun C same cr cs rfl rfl ci rfl ch rfl co (fun _ => rfl) (fun _ => rfl)
      (fun i no => (no ⟨i,rfl⟩).elim)
  exact ⟨first.follow second, ready, cframe.trans layout⟩

end Mathproof.MinimumGeneration.CayleyReaderRetarget
