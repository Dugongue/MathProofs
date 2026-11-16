import Mathproof.MinimumGenerationCayleyQueryPrefix

namespace Mathproof.MinimumGeneration.CayleyReaderFrame

open SearchTransducer
open InputPosition (work)
open CayleyQueryPrefixModel (rawSpace width keep)

set_option backward.isDefEq.respectTransparency false

/-- A local transition can write only at the work head's previous position. -/
theorem stepOutside {P : SearchTransducer} {word : List Bool} {c d : P.Config}
    (s : P.step word c = some d) (bank : Fin P.workTapes) (pos : Int)
    (away : pos ≠ c.workHead bank) :
    d.workCell bank pos = c.workCell bank pos := by
  unfold SearchTransducer.step at s
  cases e : P.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [e] at s
  | some a =>
    obtain ⟨q,m,w,o⟩ := a
    simp only [e,Option.map_some,Option.some.injEq] at s
    subst d
    exact if_neg away

/-- Every prefix of a bounded execution leaves all cells outside its
physical head interval unchanged. -/
theorem segmentOutside {P : SearchTransducer} {word : List Bool} {B k : ℕ} {c d : P.Config}
    (seg : P.BoundedSegment word B c d k) (j : ℕ) (hj : j ≤ k) {e : P.Config}
    (run : P.runFrom word c j = some e) (bank : Fin P.workTapes) (pos : Int)
    (away : B < pos.natAbs) :
    e.workCell bank pos = c.workCell bank pos := by
  induction j generalizing e with
  | zero =>
    have eq : c = e := Option.some.inj run
    subst e
    rfl
  | succ j ih =>
    obtain ⟨mid,priorRun,step⟩ := Option.bind_eq_some_iff.mp run
    have le : j ≤ k := Nat.le_trans (Nat.le_succ _) hj
    have head := (seg.2 j le mid priorRun).2.2 bank
    have ne : pos ≠ mid.workHead bank := by
      intro h
      rw [h] at away
      omega
    exact (stepOutside step bank pos ne).trans (ih le priorRun)

theorem workOutside {xs : List Bool} {B : ℕ} (hlen : xs.length ≤ B)
    (pos : Int) (outside : B < pos.natAbs) :
    work xs pos = none := by
  unfold work
  by_cases h : pos ≤ 0
  · exact if_pos h
  · rw [if_neg h]
    apply List.getElem?_eq_none
    omega

private theorem encodedOutside {w x B : ℕ} (h : w ≤ B) (pos : Int) (outside : B < pos.natAbs) :
    work (encodeLabel w x) pos = none := by
  exact workOutside (by simpa [encodeLabel] using h) pos outside

private theorem coordsOutside {n p B : ℕ} (h : width n ≤ B) (i : Fin 10)
    (pos : Int) (outside : B < pos.natAbs) :
    CayleyQueryCoordinates.entryCells (width n) n p i pos = none := by
  unfold CayleyQueryCoordinates.entryCells
  split
  · unfold CayleyQueryDispatch.OffsetInstall.live
    split
    · exact encodedOutside h _ outside
    split
    · exact encodedOutside h _ outside
    split
    · exact encodedOutside h _ outside
    · rfl
  · unfold CayleyQueryCoordinates.seed
    split
    · exact encodedOutside h _ outside
    · rfl

private theorem templateOutside {n id cut B : ℕ} (h : width n ≤ B) (i : Fin 18)
    (pos : Int) (outside : B < pos.natAbs) :
    CayleyPrefixLeaf.template n 0 0 id cut i pos = none := by
  have wide : 2*TableIO.width n ≤ B := by unfold width at h; omega
  have small : TableIO.width n ≤ B := by omega
  fin_cases i <;> first | rfl | exact encodedOutside wide _ outside | exact encodedOutside small _ outside

/-- The literal 35-bank preparation is blank outside the reader's head cap. -/
theorem entryOutside {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n))
    (p : ℕ) (bank : Fin 35) (pos : Int)
    (outside : rawSpace (@encodeCayley n G.toMul) < pos.natAbs) :
    CayleyQueryPrefixModel.cells G cut s t p bank pos = none := by
  have widthFit : width n ≤ rawSpace (@encodeCayley n G.toMul) :=
    (Nat.le_succ _).trans (CayleyQueryPrefixModel.width_le G)
  unfold CayleyQueryPrefixModel.cells
  split
  · exact coordsOutside widthFit _ _ outside
  split
  · exact templateOutside widthFit _ _ outside
  split
  · exact encodedOutside widthFit _ outside
  split <;> exact encodedOutside widthFit _ outside

/-- Exact raw reader execution, including the closure of its finite work
interval for every prefix and scratch bank. -/
theorem execute {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (hCut : cut ≤ n)
    (s t : Fin (n+n)) (p : ℕ) (prior : List Bool)
    (legal : p ≤ Connectivity.ustconHeaderLength s t + (n+n)*(n+n) + 1) :
    let raw := @encodeCayley n G.toMul
    let B := rawSpace raw
    let first := CayleyQueryRouter.start CayleyQueryPrefixModel.addressBank
      CayleyQueryPrefixModel.markerBank CayleyQueryPrefixModel.guardBanks
      CayleyQueryPrefixModel.coordBanks CayleyQueryPrefix.cross CayleyQueryPrefix.fit
      (↑(n+1 : ℕ) : Int) (CayleyQueryPrefixModel.cells G cut s t p) prior
    ∃ k last, CayleyQueryPrefix.machine.BoundedSegment raw B first last k ∧
      CayleyQueryPrefix.machine.step raw last = none ∧
      CayleyQueryPrefix.callback.returnCell last.state =
        Connectivity.ustconCell (BipartiteCayley.bits G (fun _ => true) cut) s t ((p : Int)-1) ∧
      last.outputReversed = prior ∧
      (∀ j ∈ keep, last.workHead j = 0 ∧ last.workCell j = CayleyQueryPrefixModel.cells G cut s t p j) ∧
      CayleyQueryPrefix.machine.Bounded raw B last ∧
      ∀ j ≤ k, ∀ c, CayleyQueryPrefix.machine.runFrom raw first j = some c →
        ∀ bank pos, B < pos.natAbs → c.workCell bank pos = none := by
  obtain ⟨k,last,run,halt,answer,printed,frame⟩ := CayleyQueryPrefix.execute G cut hCut s t p prior legal
  refine ⟨k,last,run,halt,answer,printed,frame,run.2 _ le_rfl _ run.1,?_⟩
  intro j hj c observed bank pos outside
  rw [segmentOutside run j hj observed bank pos outside]
  let A := CayleyQueryGuard.machine CayleyQueryPrefixModel.addressBank
    CayleyQueryPrefixModel.markerBank CayleyQueryPrefixModel.guardBanks
  let old := CayleyQueryPrefixModel.cells G cut s t p
  let d := CayleyQueryGuard.start CayleyQueryPrefixModel.addressBank
    CayleyQueryPrefixModel.markerBank CayleyQueryPrefixModel.guardBanks
      (↑(n+1 : ℕ) : Int) old prior
  have image := A.bankConfig_cell_image (Function.Embedding.refl _) d d.workHead d.workCell bank
  change (A.bankConfig (Function.Embedding.refl _) d d.workHead d.workCell).workCell bank pos = none
  rw [show (A.bankConfig (Function.Embedding.refl _) d d.workHead d.workCell).workCell bank =
    d.workCell bank from image]
  exact entryOutside G cut s t p bank pos outside

end Mathproof.MinimumGeneration.CayleyReaderFrame
