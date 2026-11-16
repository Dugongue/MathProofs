import Mathproof.MinimumGenerationPhysicalGreedyCycleInvariant
import Mathproof.MinimumGenerationPhysicalGreedyReaderInstall
import Mathproof.MinimumGenerationPhysicalGreedyReaderFromRaw

namespace Mathproof.MinimumGeneration.PhysicalGreedyOrdinalSetup

open SearchTransducer
open PhysicalGreedyReaderInstall (copied copyRun)
open PhysicalGreedyTemplateCompose (configEq)
open PhysicalGreedyHeaderInstall (wordAt outside_word)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev Bank (N : Nat) := Fin (95+N)

def embed (N : Nat) : Fin 93 ↪ Bank N :=
  ⟨Fin.castLE (by omega),fun _ _ h => Fin.ext (congrArg (fun j : Bank N => j.val) h)⟩

def reader (N : Nat) (i : Fin 74) : Bank N := embed N (PhysicalGreedyReaderSetup.reader i)
def header (N : Nat) (i : Fin 18) : Bank N := embed N (PhysicalGreedyReaderSetup.header i)
def native (N : Nat) (i : Fin N) : Bank N := Fin.natAdd 95 i

def order (N : Nat) : Bank N := header N 0
def label (N : Nat) : Bank N := header N 1
def ordinal (N : Nat) : Bank N := ⟨93,by omega⟩
def zero (N : Nat) : Bank N := ⟨94,by omega⟩

def source (N : Nat) : Bank N → Option (Bank N) :=
  fun i => if i=ordinal N ∨ i=zero N then some (label N) else none

abbrev A := PhysicalGreedyReaderFromRaw.machine
abbrev C (N : Nat) := TapeInstall.machine (order N) (source N)

private def identity (N : Nat) : Bank N ↪ Bank N := Function.Embedding.refl _

abbrev machine (N : Nat) := thenMachine A (C N) (embed N) (identity N)

def memory (N n id : Nat) (j : Bank N) : Int → Option Bool :=
  if h : j.val < 93 then PhysicalGreedyReaderSetup.outputData n id ⟨j.val,h⟩
  else fun _ => none

def prepared (N n id : Nat) : Bank N → Int → Option Bool :=
  copied (source N) (memory N n id)

theorem memory_image (N n id : Nat) (j : Fin 93) :
    memory N n id (embed N j) = PhysicalGreedyReaderSetup.outputData n id j := by
  unfold memory
  rw [dif_pos (show (embed N j).val < 93 from j.isLt)]
  rfl

theorem prepared_image (N n id : Nat) (j : Fin 93) :
    prepared N n id (embed N j) = PhysicalGreedyReaderSetup.outputData n id j := by
  have a : embed N j ≠ ordinal N := fun h => by
    have d := congrArg Fin.val h
    change j.val=93 at d
    exact (Nat.ne_of_lt j.isLt) d
  have b : embed N j ≠ zero N := fun h => by
    have d := congrArg Fin.val h
    change j.val=94 at d
    have := j.isLt
    omega
  rw [show prepared N n id (embed N j) = memory N n id (embed N j) from by
    simp [prepared,copied,source,a,b]]
  exact memory_image N n id j

theorem headInitialized_label (N n id : Nat) :
    prepared N n id (label N) = wordAt (TableIO.width n) 0 :=
  (prepared_image N n id (PhysicalGreedyReaderSetup.header 1)).trans
    (PhysicalGreedyReaderSetup.header_preserved n id 1)

theorem headInitialized_order (N n id : Nat) :
    prepared N n id (order N) = wordAt (TableIO.width n) n :=
  (prepared_image N n id (PhysicalGreedyReaderSetup.header 0)).trans
    (PhysicalGreedyReaderSetup.header_preserved n id 0)

private theorem labelMemory (N n id : Nat) :
    memory N n id (label N) = wordAt (TableIO.width n) 0 :=
  (memory_image N n id (PhysicalGreedyReaderSetup.header 1)).trans
    (PhysicalGreedyReaderSetup.header_preserved n id 1)

private theorem orderMemory (N n id : Nat) :
    memory N n id (order N) = wordAt (TableIO.width n) n :=
  (memory_image N n id (PhysicalGreedyReaderSetup.header 0)).trans
    (PhysicalGreedyReaderSetup.header_preserved n id 0)

theorem ordinalPrepared (N n id : Nat) :
    prepared N n id (ordinal N) = wordAt (TableIO.width n) 0 := by
  simpa [prepared,copied,source] using labelMemory N n id

theorem zeroPrepared (N n id : Nat) :
    prepared N n id (zero N) = wordAt (TableIO.width n) 0 := by
  simpa [prepared,copied,source] using labelMemory N n id

theorem nativePrepared (N n id : Nat) (i : Fin N) :
    prepared N n id (native N i) = fun _ => none := by
  have low : 95 ≤ (native N i).val := by change 95 ≤ 95+i.val; omega
  have neq (j : Bank N) (hj : j.val < 95) : native N i ≠ j := fun h => by
    have eq := congrArg Fin.val h
    omega
  have a := neq (ordinal N) (by change 93<95; decide)
  have b := neq (zero N) (by change 94<95; decide)
  dsimp only [prepared,copied,source,memory]
  rw [if_neg (by simp [a,b]), Option.elim_none, dif_neg (by omega)]

theorem stateInitialized {n : Nat} (G : Group (Fin n)) (N B : Nat) :
    PhysicalGreedyCycleInvariant.Ready G (CayleyReaderClock.bits n) B (reader N) (native N)
      (prepared N n G.toOne.one.val) := by
  apply PhysicalGreedyCycleInvariant.initialized
  · intro i
    exact prepared_image N n G.toOne.one.val (PhysicalGreedyReaderSetup.reader i)
  · intro i p hp
    rw [nativePrepared]

private def parked (N : Nat) : Bank N → Int := fun _ => 0
private def empty (N : Nat) : Bank N → Int → Option Bool := fun _ _ => none

private theorem allHead {N : Nat} (c : (C N).Config) :
    ((C N).bankConfig (identity N) c (parked N) (empty N)).workHead = c.workHead := by
  funext j
  exact (C N).bankConfig_head_image (identity N) c _ _ j

private theorem allCell {N : Nat} (c : (C N).Config) :
    ((C N).bankConfig (identity N) c (parked N) (empty N)).workCell = c.workCell := by
  funext j
  exact (C N).bankConfig_cell_image (identity N) c _ _ j

/-- Start from blank tapes and the actual Cayley word, initialize the reader,
and physically install both dedicated raw-width ordinal words. Native work
tapes remain fully blank and every head is parked. -/
theorem execute {n : Nat} (G : Group (Fin n)) (N : Nat) :
    let raw := @encodeCayley n G.toMul
    let B := 17*(Nat.log2 (raw.length+1)+1)
    ∃ (k : Nat) (d : (machine N).Config),
      (machine N).BoundedSegment raw B (machine N).initial d k ∧ (machine N).step raw d = none ∧
      (machine N).logarithmicWorkspace 17 raw ∧ d.workHead=(fun _ => 0) ∧
      d.outputReversed=[] ∧ d.workCell = prepared N n G.toOne.one.val := by
  let raw := @encodeCayley n G.toMul
  let B := 17*(Nat.log2 (raw.length+1)+1)
  let id := G.toOne.one.val
  let w := TableIO.width n
  let old := memory N n id
  obtain ⟨k,a,run,done,_,heads,out,words,_,_⟩ := PhysicalGreedyReaderFromRaw.execute G
  have localBound := run.2 k le_rfl a run.1
  have legal : (-1 : Int) ≤ a.inputHead ∧ a.inputHead ≤ raw.length := ⟨localBound.1,localBound.2.1⟩
  have hClock : source N (order N) = none := by
    unfold source
    apply if_neg
    rintro (h|h)
    · have z := congrArg Fin.val h
      change 74=93 at z
      omega
    · have z := congrArg Fin.val h
      change 74=94 at z
      omega
  obtain ⟨copy,copyStop⟩ := TapeInstall.execute (order N) (source N) hClock raw
    (encodeLabel w n) [] a.inputHead old (orderMemory N n id) legal
  rw [length_encodeLabel] at copy copyStop
  let aa := A.bankConfig (embed N) a (parked N) (empty N)
  let c := TapeInstall.start (order N) (source N) a.inputHead old []
  let d := TapeInstall.stop (order N) (source N) a.inputHead old [] w
  let cc := (C N).bankConfig (identity N) c (parked N) (empty N)
  let dd := (C N).bankConfig (identity N) d (parked N) (empty N)
  have pad := A.relocateBanks_segment (embed N) run (heads := parked N) (cells := empty N) (by simp [parked])
  have fit : w+1 ≤ B := by
    have h := PhysicalGreedyHeaderDriver.raw_bound G
    change PhysicalGreedyHeader.width n+1 ≤ 5*((raw.length+1).log2+1) at h
    unfold PhysicalGreedyHeader.width at h
    dsimp [w,B]
    omega
  have next := (C N).relocateBanks_segment (identity N) (PhysicalEntry.segment_mono copy fit)
    (heads := parked N) (cells := empty N) (by simp [parked])
  have stopA : (A.relocateBanks (embed N)).step raw aa = none := by
    unfold aa
    rw [relocateBanks_step,done]
    rfl
  have stopC : ((C N).relocateBanks (identity N)).step raw dd = none := by
    unfold dd d
    rw [relocateBanks_step,copyStop]
    rfl
  have aaHead : aa.workHead = parked N := by
    funext j
    by_cases h : j ∈ Set.range (embed N)
    · obtain ⟨i,rfl⟩ := h
      exact (A.bankConfig_head_image (embed N) a (parked N) (empty N) i).trans (congrFun heads i)
    · exact (A.bankConfig_frame (embed N) a (parked N) (empty N) h).1
  have aaCell : aa.workCell = old := by
    funext j
    by_cases h : j ∈ Set.range (embed N)
    · obtain ⟨i,rfl⟩ := h
      exact (A.bankConfig_cell_image (embed N) a (parked N) (empty N) i).trans
        ((congrFun words i).trans (memory_image N n id i).symm)
    · have large : ¬ j.val<93 := fun g => h ⟨⟨j.val,g⟩,Fin.ext rfl⟩
      exact (A.bankConfig_frame (embed N) a (parked N) (empty N) h).2.trans (by
        change (fun _ => (none : Option Bool)) = memory N n id j
        rw [memory,dif_neg large])
  have put : thenEntry A (C N) (embed N) (identity N) aa = cc := by
    apply configEq
    · rfl
    · rfl
    · exact aaHead.trans (allHead c).symm
    · exact aaCell.trans (allCell c).symm
    · exact out
  change ((C N).relocateBanks (identity N)).BoundedSegment raw B cc dd _ at next
  rw [← put] at next
  have whole := thenSegment A (C N) (embed N) (identity N) pad stopA next
  have starter : (machine N).initial =
      thenLeft A (C N) (embed N) (identity N) (A.bankConfig (embed N) A.initial (parked N) (empty N)) := by
    apply configEq
    · rfl
    · rfl
    · funext j
      by_cases h : j ∈ Set.range (embed N)
      · obtain ⟨i,rfl⟩ := h
        exact (A.bankConfig_head_image (embed N) A.initial (parked N) (empty N) i).symm
      · exact (A.bankConfig_frame (embed N) A.initial (parked N) (empty N) h).1.symm
    · funext j
      by_cases h : j ∈ Set.range (embed N)
      · obtain ⟨i,rfl⟩ := h
        exact (A.bankConfig_cell_image (embed N) A.initial (parked N) (empty N) i).symm
      · exact (A.bankConfig_frame (embed N) A.initial (parked N) (empty N) h).2.symm
    · rfl
  rw [← starter] at whole
  let d' := thenRight A (C N) (embed N) (identity N) dd
  have stop : (machine N).step raw d' = none := by
    change (machine N).step raw (thenRight A (C N) (embed N) (identity N) dd) = none
    rw [thenStep_right,stopC]
    rfl
  have installed : d.workCell = prepared N n id := by
    funext j
    cases map : source N j with
    | none => exact (TapeInstall.installed_source _ _ _ _ map).trans (by simp [prepared,copied,map])
    | some src =>
      have chose : j=ordinal N ∨ j=zero N := by
        by_contra! h
        simp [source,h] at map
      have eq : src = label N := by
        have ans : some (label N) = some src := by simpa [source,chose] using map
        exact (Option.some.inj ans).symm
      subst src
      exact (TapeInstall.installed_exact _ _ _ _ _ map (by
        intro p hp
        rcases chose with rfl|rfl <;>
          exact (congrFun (labelMemory N n id) p ▸ outside_word w 0 p hp).symm)).trans
        (by simp [prepared,copied,map])
  refine ⟨_,d',whole,stop,(BoundedSegment.logspaceOutput _ whole stop).1,
    allHead d,rfl,(allCell d).trans installed⟩

end Mathproof.MinimumGeneration.PhysicalGreedyOrdinalSetup
