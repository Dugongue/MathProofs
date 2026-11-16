import Mathproof.MinimumGenerationPhysicalGreedyHeaderSums

namespace Mathproof.MinimumGeneration.PhysicalGreedyHeaderDriver

open SearchTransducer PhysicalGreedyHeader
open PhysicalGreedyHeaderInstall (Bank Ready wordAt afterCopy constBank)

set_option backward.isDefEq.respectTransparency false

abbrev I := PhysicalGreedyHeaderInstall.machine
abbrev A := PhysicalGreedyHeaderSums.machine

def banks : Bank ↪ Bank := Function.Embedding.refl _

abbrev machine := thenMachine I A banks banks

def start (h : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) : machine.Config :=
  thenLeft I A banks banks
    (I.bankConfig banks (PhysicalGreedyHeaderInstall.start h cells prior) (fun _ => 0) cells)

def final (n id x : Nat) (cells : Bank → Int → Option Bool) : Bank → Int → Option Bool :=
  PhysicalGreedyHeaderSums.finalCells n id x (afterCopy n cells)

def markerBank (i : Fin 5) : Bank :=
  if i = 0 then 3 else if i = 1 then 6 else if i = 2 then 7 else if i = 3 then 13 else 14

/-- The physical reader ABI of the filled banks. The cutoff remains the
original candidate; initialization touches neither that bank nor the identity. -/
structure Live (n id x : Nat) (cells : Bank → Int → Option Bool) : Prop where
  order : cells 0 = wordAt (TableIO.width n) n
  cut : cells 1 = wordAt (TableIO.width n) x
  identity : cells 2 = wordAt (TableIO.width n) id
  matrixOrder : cells 5 = wordAt (width n) (graphOrder n)
  shiftedAddress : cells 11 = wordAt (width n) 1
  headerPlusOne : cells 15 = wordAt (width n) (header n id x + 1)
  marked : ∀ i, cells (markerBank i) = wordAt (width n) (markers n id x i)

theorem untouched {n id x : Nat} {cells : Bank → Int → Option Bool} (j : Bank) (hj : j.val < 11) :
    final n id x cells j = cells j :=
  (PhysicalGreedyHeaderSums.finalFrame _ j (.inl (by omega))).trans
    (PhysicalGreedyHeaderInstall.afterCopy_sources _ _ _ hj)

theorem final_layout {n id x : Nat} {cells : Bank → Int → Option Bool} (R : Ready n id x cells) :
    Live n id x (final n id x cells) := by
  obtain ⟨h3,h4,hH⟩ := PhysicalGreedyHeaderSums.finalMarkers (n := n) (id := id) (x := x)
    (afterCopy n cells)
  refine ⟨(untouched 0 (by decide)).trans R.rawOrder,
    (untouched 1 (by decide)).trans R.rawCandidate,
    (untouched 2 (by decide)).trans R.rawIdentity,
    (untouched 5 (by decide)).trans (R.constants 2),
    (PhysicalGreedyHeaderSums.finalFrame _ 11 (.inl (by decide))).trans
      (PhysicalGreedyHeaderInstall.address_ready R), hH, ?_⟩
  intro i
  fin_cases i
  · exact (untouched 3 (by decide)).trans (R.constants 0)
  · exact (untouched 6 (by decide)).trans (R.constants 3)
  · exact (untouched 7 (by decide)).trans (R.constants 4)
  · exact h3
  · exact h4

theorem raw_bound {n : Nat} (G : Group (Fin n)) :
    width n+1 ≤ 5*(Nat.log2 ((@encodeCayley n G.toMul).length + 1)+1) := by
  let raw := @encodeCayley n G.toMul
  have len : n ≤ raw.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have hl : n.log2 ≤ (raw.length+1).log2 := by
    by_cases hn : n = 0
    · simp [hn]
    · apply (Nat.le_log2 (by omega)).2
      exact (Nat.log2_self_le (by omega)).trans (by omega)
  unfold width TableIO.width
  change 4*(n.log2+1)+1 ≤ 5*((raw.length+1).log2+1)
  omega

private theorem head (P : SearchTransducer) (e : Fin P.workTapes ↪ Fin P.workTapes)
    (he : ∀ j, e j = j) (c : P.Config) (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig e c (fun _ => 0) m).workHead = c.workHead := by
  funext i
  simpa only [he] using P.bankConfig_head_image e c _ m i

private theorem cell (P : SearchTransducer) (e : Fin P.workTapes ↪ Fin P.workTapes)
    (he : ∀ j, e j = j) (c : P.Config) (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig e c (fun _ => 0) m).workCell = c.workCell := by
  funext i
  simpa only [he] using P.bankConfig_cell_image e c _ m i

private theorem configEq {M : SearchTransducer} (c d : M.Config)
    (hq : c.state = d.state) (hi : c.inputHead = d.inputHead)
    (hh : c.workHead = d.workHead) (hc : c.workCell = d.workCell)
    (ho : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

/-- Finite, physical initialization of the marker and endpoint banks for one
live prefix query. Each call starts from the current candidate bank, leaving
raw label and all reusable templates intact. -/
theorem execute {n id x : Nat} {raw prior : List Bool} {input : Int}
    {cells : Bank → Int → Option Bool} (R : Ready n id x cells)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) (fits : x < 2 ^ TableIO.width n) :
    ∃ (k : Nat) (d : machine.Config),
      machine.BoundedSegment raw (width n+1) (start input cells prior) d k ∧
      machine.step raw d = none ∧ d.inputHead = input ∧ d.workHead = (fun _ => 0) ∧
      d.workCell = final n id x cells ∧ d.outputReversed = prior ∧ Live n id x d.workCell := by
  let i := PhysicalGreedyHeaderInstall.stop n input cells prior
  let a := PhysicalGreedyHeaderSums.start input (afterCopy n cells) prior
  obtain ⟨k,ir,is⟩ := PhysicalGreedyHeaderInstall.execute
    (raw := raw) (prior := prior) R hin
  obtain ⟨l,d,ar,as,ih,wh,mc,out⟩ := PhysicalGreedyHeaderSums.execute
    (raw := raw) (prior := prior) R hin fits
  have it := I.relocateBanks_segment banks ir (heads := fun _ => 0) (cells := cells) (by simp)
  have tail := A.relocateBanks_segment banks ar (heads := fun _ => 0) (cells := cells) (by simp)
  let ii := I.bankConfig banks i (fun _ => 0) cells
  let aa := A.bankConfig banks a (fun _ => 0) cells
  let dd := A.bankConfig banks d (fun _ => 0) cells
  have hIs : (I.relocateBanks banks).step raw ii = none := by
    unfold ii
    rw [relocateBanks_step,is]
    rfl
  have hAs : (A.relocateBanks banks).step raw dd = none := by
    unfold dd
    rw [relocateBanks_step,as]
    rfl
  obtain ⟨il,im,ic,io⟩ := PhysicalGreedyHeaderInstall.stop_layout n input cells prior
  have eq : thenEntry I A banks banks ii = aa := by
    apply configEq
    · rfl
    · exact il
    · exact ((head I banks (fun _ => rfl) i cells).trans im).trans
        (head A banks (fun _ => rfl) a cells).symm
    · exact ((cell I banks (fun _ => rfl) i cells).trans ic).trans
        (cell A banks (fun _ => rfl) a cells).symm
    · exact io
  change (A.relocateBanks banks).BoundedSegment raw (width n+1) aa dd l at tail
  rw [← eq] at tail
  let z := thenRight I A banks banks dd
  have hCell : z.workCell = final n id x cells :=
    (cell A banks (fun _ => rfl) d cells).trans mc
  refine ⟨_,z,thenSegment I A banks banks it hIs tail,?_,ih,
    (head A banks (fun _ => rfl) d cells).trans wh,hCell,out,?_⟩
  · change machine.step raw (thenRight I A banks banks dd) = none
    rw [thenStep_right,hAs]
    rfl
  · rw [hCell]
    exact final_layout R

end Mathproof.MinimumGeneration.PhysicalGreedyHeaderDriver
