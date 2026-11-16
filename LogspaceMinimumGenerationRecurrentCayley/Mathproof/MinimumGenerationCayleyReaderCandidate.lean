import Mathproof.MinimumGenerationCayleyReaderCycle
import Mathproof.MinimumGenerationPhysicalGreedyHeaderDriver

namespace Mathproof.MinimumGeneration.CayleyReaderCandidate

open SearchTransducer
open InputPosition (work)
open PhysicalGreedyHeaderInstall (Bank)
open CayleyReaderCycle

set_option backward.isDefEq.respectTransparency false

abbrev W := 93

def reader (i : Fin 74) : Fin W := Fin.castAdd 19 i

def header (i : Bank) : Fin W := ⟨74 + i.val, by change 74 + i.val < 93; have := i.isLt; omega⟩

def source (i : Fin W) : Option (Fin W) :=
  if i = 27 then some (header 1)
  else if i = 31 then some (header 13)
  else if i = 32 then some (header 14)
  else if i = 33 then some (header 11)
  else if i = 34 then some (header 15)
  else none

def clock : Fin W := 70

abbrev machine := TapeInstall.machine clock source

def readerView (old : Fin W → Int → Option Bool) : Fin 74 → Int → Option Bool :=
  fun j => old (reader j)

def headerView (old : Fin W → Int → Option Bool) : Bank → Int → Option Bool :=
  fun j => old (header j)


private theorem source_unchanged {j : Fin W} (h : 35 ≤ j.val) :
    source j = none := by
  unfold source
  split <;> try (rename_i e; subst j; contradiction)
  split <;> try (rename_i e; subst j; contradiction)
  split <;> try (rename_i e; subst j; contradiction)
  split <;> try (rename_i e; subst j; contradiction)
  split <;> try (rename_i e; subst j; contradiction)
  rfl

private theorem blankBeyond (bits : List Bool) {j : Int}
    (pos : j < 1 ∨ (bits.length : Int) < j) : work bits j = none := by
  by_cases q : j ≤ 0
  · simp [work,q]
  · simp only [work, if_neg q]
    exact List.getElem?_eq_none (by omega)

private theorem wordExterior {a b w : Nat} (h : a ≤ w) {z : Int}
    (hz : z < 1 ∨ (w : Int) < z) : work (encodeLabel a b) z = none := by
  apply blankBeyond
  rw [length_encodeLabel]
  omega

open CayleyQueryPrefixModel (cells keep width rawSpace)
open BipartiteCayley (left)

private theorem restore_index (i : Fin 35) :
    reader (restoreBanks (CayleyReaderRestore.readerBanks i)) = Fin.castAdd 58 i := by
  apply Fin.ext
  change (if i.val < 35 then i.val else i.val + 35) = i.val
  exact if_pos i.isLt

private theorem sourceKind (i : Fin 35) :
    source (Fin.castAdd 58 i) = none ∨
    (i = 27 ∧ source (Fin.castAdd 58 i) = some (header 1)) ∨
    (i = 31 ∧ source (Fin.castAdd 58 i) = some (header 13)) ∨
    (i = 32 ∧ source (Fin.castAdd 58 i) = some (header 14)) ∨
    (i = 33 ∧ source (Fin.castAdd 58 i) = some (header 11)) ∨
    (i = 34 ∧ source (Fin.castAdd 58 i) = some (header 15)) := by
  fin_cases i <;> decide

private theorem changedIndex (i : Fin 35) (j : Fin W)
    (h : source (Fin.castAdd 58 i) = some j) :
    (i = 27 ∧ j = header 1) ∨ (i = 31 ∧ j = header 13) ∨
    (i = 32 ∧ j = header 14) ∨ (i = 33 ∧ j = header 11) ∨
    (i = 34 ∧ j = header 15) := by
  rcases sourceKind i with a | ⟨rfl,a⟩ | ⟨rfl,a⟩ | ⟨rfl,a⟩ | ⟨rfl,a⟩ | ⟨rfl,a⟩
  · rw [a] at h
    contradiction
  all_goals
    have e := Option.some.inj (h.symm.trans a)
    subst j
    decide

private theorem changed_support {n : Nat} (G : Group (Fin n)) (cut p : Nat)
    (id x : Fin n) (i : Fin 35) (j : Fin W) {z : Int}
    (hz : z < 1 ∨ (width n : Int) < z) (h : source (Fin.castAdd 58 i) = some j) :
    cells G cut (left id) (left x) p i z = none := by
  rcases changedIndex i j h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact wordExterior (a := TableIO.width n) (by unfold width; omega) hz
  all_goals exact wordExterior (a := width n) le_rfl hz

private theorem changed_value {n : Nat} (G : Group (Fin n)) (x : Fin n)
    (old : Fin W → Int → Option Bool)
    (L : PhysicalGreedyHeaderDriver.Live n G.toOne.one.val x.val (headerView old))
    (i : Fin 35) (j : Fin W) (h : source (Fin.castAdd 58 i) = some j) :
    old j = cells G x.val (left G.toOne.one) (left x) 1 i := by
  rcases changedIndex i j h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact L.cut
  · exact L.marked (3 : Fin 5)
  · exact L.marked (4 : Fin 5)
  · exact L.shiftedAddress
  · exact L.headerPlusOne
private theorem stableIndex (i : Fin 35) :
    (21 ≤ i.val ∧ i.val ≠ 22 ∧ i.val ≠ 25) →
    source (Fin.castAdd 58 i) = none →
    i = 21 ∨ i = 23 ∨ i = 24 ∨ i = 26 ∨ i = 28 ∨ i = 29 ∨ i = 30 := by
  fin_cases i <;> decide

private theorem stable_value {n : Nat} (G : Group (Fin n)) (cut p : Nat)
    (x y : Fin n) (i : Fin 35) (hi : i ∈ keep)
    (h : source (Fin.castAdd 58 i) = none) :
    cells G cut (left G.toOne.one) (left x) p i =
      cells G y.val (left G.toOne.one) (left y) 1 i := by
  rcases stableIndex i hi h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem prepared {n : Nat} (G : Group (Fin n)) (cut p : Nat) (x y : Fin n)
    (ticks : List Bool) (old : Fin W → Int → Option Bool)
    (R : Ready G cut (left G.toOne.one) (left x) p ticks (readerView old))
    (L : PhysicalGreedyHeaderDriver.Live n G.toOne.one.val y.val (headerView old)) :
    Ready G y.val (left G.toOne.one) (left y) 1 ticks
      (readerView (TapeInstall.installed source old ticks.length)) := by
  let new := TapeInstall.installed source old ticks.length
  change Ready G y.val (left G.toOne.one) (left y) 1 ticks (readerView new)
  have short := CayleyQueryPrefixModel.width_le G
  have tickWide : width n ≤ ticks.length := (Nat.le_succ _).trans (short.trans R.body.clockEnough)
  have readOrig (i : Fin 35) : readerView old (restoreBanks (CayleyReaderRestore.readerBanks i)) =
      old (Fin.castAdd 58 i) := congrArg old (restore_index i)
  have newOrig (i : Fin 35) : readerView new (restoreBanks (CayleyReaderRestore.readerBanks i)) =
      new (Fin.castAdd 58 i) := congrArg new (restore_index i)
  have keepBig (j : Fin W) (hj : 35 ≤ j.val) : new j = old j :=
    TapeInstall.installed_source source old ticks.length j (source_unchanged hj)
  have result (i : Fin 35) (hi : i ∈ keep) :
      new (Fin.castAdd 58 i) = cells G y.val (left G.toOne.one) (left y) 1 i := by
    cases hs : source (Fin.castAdd 58 i) with
    | none =>
      rw [show new (Fin.castAdd 58 i) = old (Fin.castAdd 58 i) from
        TapeInstall.installed_source source old ticks.length _ hs, ← readOrig]
      exact (R.body.live i hi).trans (stable_value G cut p x y i hi hs)
    | some j =>
      have target := changed_value G y old L i j hs
      have exactCells : new (Fin.castAdd 58 i) = old j := by
        apply TapeInstall.installed_exact source old ticks.length _ j hs
        intro z hz
        have hw : z < 1 ∨ (width n : Int) < z := by omega
        rw [← readOrig, R.body.live i hi, target]
        exact (changed_support G cut p G.toOne.one x i j hw hs).trans
          (changed_support G y.val 1 G.toOne.one y i j hw hs).symm
      exact exactCells.trans target

  refine ⟨⟨?_,R.body.clockEnough,?_,?_,?_,?_,?_⟩,?_⟩
  · exact (keepBig _ (by decide)).trans R.body.clockWord
  · exact (keepBig _ (by decide)).trans R.body.cardinality
  · exact (keepBig _ (by decide)).trans R.body.order
  · exact (keepBig _ (by decide)).trans R.body.clean
  · intro i hi
    rw [newOrig]
    exact result i hi
  · intro i z hz
    rw [newOrig]
    cases hs : source (Fin.castAdd 58 i) with
    | none =>
      rw [show new (Fin.castAdd 58 i) = old (Fin.castAdd 58 i) from
        TapeInstall.installed_source source old ticks.length _ hs, ← readOrig]
      exact R.body.outside i z hz
    | some j =>
      have hi : i ∈ keep := by
        rcases changedIndex i j hs with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
          (change 21 ≤ (_ : Fin 35).val ∧ (_ : Fin 35).val ≠ 22 ∧ (_ : Fin 35).val ≠ 25; decide)
      rw [result i hi]
      have wraw : width n ≤ rawSpace (@encodeCayley n G.toMul) := (Nat.le_succ _).trans short
      have hout : z < 1 ∨ (width n : Int) < z := by omega
      exact changed_support G y.val 1 G.toOne.one y i j hout hs
  · intro i
    exact (keepBig _ (by change 35 ≤ 35+i.val; omega)).trans (R.shadows i)

/-- Reload the live candidate header into the recurrent Cayley reader by a
single bounded parallel copy, leaving the saved header banks intact. -/
theorem execute {n : Nat} (G : Group (Fin n)) (cut p : Nat) (x y : Fin n)
    (ticks prior : List Bool) (input : Int) (old : Fin W → Int → Option Bool)
    (R : Ready G cut (left G.toOne.one) (left x) p ticks (readerView old))
    (L : PhysicalGreedyHeaderDriver.Live n G.toOne.one.val y.val (headerView old))
    (hi : (-1 : Int) ≤ input ∧ input ≤ (@encodeCayley n G.toMul).length) :
    let d := TapeInstall.stop clock source input old prior ticks.length
    machine.BoundedSegment (@encodeCayley n G.toMul) (ticks.length+1)
      (TapeInstall.start clock source input old prior) d (2*ticks.length+3) ∧
    machine.step (@encodeCayley n G.toMul) d = none ∧ d.inputHead = input ∧
    d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧ headerView d.workCell = headerView old ∧
    Ready G y.val (left G.toOne.one) (left y) 1 ticks (readerView d.workCell) := by
  obtain ⟨run,stop⟩ := TapeInstall.execute clock source (by decide)
    (@encodeCayley n G.toMul) ticks prior input old R.body.clockWord hi
  have eq : 2 * ticks.length + 3 = ticks.length + 2 + ticks.length + 1 := by omega
  refine ⟨eq ▸ run,stop,rfl,rfl,rfl,?_,prepared G cut p x y ticks old R L⟩
  funext j
  exact TapeInstall.installed_source source old ticks.length _ (source_unchanged
    (by change 35 ≤ 74+j.val; omega))

end Mathproof.MinimumGeneration.CayleyReaderCandidate
