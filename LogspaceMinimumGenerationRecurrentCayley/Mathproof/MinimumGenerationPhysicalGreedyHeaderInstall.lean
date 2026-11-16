import Mathproof.MinimumGenerationPhysicalGreedyHeader

namespace Mathproof.MinimumGeneration.PhysicalGreedyHeaderInstall

open SearchTransducer
open InputPosition (work)
open PhysicalGreedyHeader

set_option backward.isDefEq.respectTransparency false

abbrev Bank := Fin 17

def wordAt (w x : Nat) : Int → Option Bool := work (encodeLabel w x)

def outside (w : Nat) (cell : Int → Option Bool) : Prop :=
  ∀ p, p < 1 ∨ (w : Int) < p → cell p = none

theorem outside_word (w x : Nat) : outside w (wordAt w x) := by
  intro p hp
  rcases hp with hp | hp
  · simp [wordAt, work, show p ≤ 0 by omega]
  · have h0 : ¬ p ≤ 0 := by omega
    have len : (encodeLabel w x).length ≤ (p-1).toNat := by
      rw [length_encodeLabel]
      omega
    simp only [wordAt, work, if_neg h0, List.getElem?_eq_none len]

def constBank (i : Fin 8) : Bank :=
  ⟨3+i.val,by omega⟩

/-- Banks below 11 are immutable templates. Only the wide registers from
bank 11 onward need to start blank outside their marked word windows. -/
structure Ready (n id x : Nat) (cells : Bank → Int → Option Bool) : Prop where
  rawOrder : cells 0 = wordAt (TableIO.width n) n
  rawCandidate : cells 1 = wordAt (TableIO.width n) x
  rawIdentity : cells 2 = wordAt (TableIO.width n) id
  constants : ∀ i, cells (constBank i) = wordAt (width n) (fixed n id i)
  scratch : ∀ i, 11 ≤ i.val → outside (width n) (cells i)

def reset : Bank → Option Bank :=
  fun j => if j = 11 then some 4 else if j = 12 then some 3
    else if j = 13 then some 8 else if j = 14 then some 9
    else if j = 15 then some 10 else if j = 16 then some 3 else none

def copyLow : Bank → Option Bank := fun j => if j = 12 then some 1 else none

abbrev A := TapeInstall.machine (3 : Bank) reset
abbrev C := TapeInstall.machine (0 : Bank) copyLow

def embedding : Bank ↪ Bank := Function.Embedding.refl _

abbrev machine := thenMachine A C embedding embedding

def afterReset (n : Nat) (cells : Bank → Int → Option Bool) :=
  TapeInstall.installed reset cells (width n)

def afterCopy (n : Nat) (cells : Bank → Int → Option Bool) :=
  TapeInstall.installed copyLow (afterReset n cells) (TableIO.width n)

private theorem untouchedReset (j : Bank) (lt : j.val < 11) :
    reset j = none := by
  have neq (k : Bank) (h : 11 ≤ k.val) : j ≠ k := fun e => by
    rw [← e] at h
    omega
  simp [reset, neq 11 (by decide), neq 12 (by decide), neq 13 (by decide),
    neq 14 (by decide), neq 15 (by decide), neq 16 (by decide)]

theorem afterCopy_sources (n : Nat) (cells : Bank → Int → Option Bool)
    (j : Bank) (lt : j.val < 11) : afterCopy n cells j = cells j := by
  have no : j ≠ 12 := fun e => by rw [e] at lt; contradiction
  exact (TapeInstall.installed_source _ _ _ _ (if_neg no)).trans
    (TapeInstall.installed_source _ _ _ _ (untouchedReset j lt))

theorem resetBank {n id x : Nat} {cells : Bank → Int → Option Bool}
    (R : Ready n id x cells) (dst : Bank) (src : Fin 8)
    (isDest : 11 ≤ dst.val) (select : reset dst = some (constBank src)) :
    afterReset n cells dst = wordAt (width n) (fixed n id src) := by
  refine (TapeInstall.installed_exact reset cells (width n) dst (constBank src) select ?_).trans
    (R.constants src)
  intro p hp
  rw [R.scratch dst isDest p hp, R.constants src, outside_word _ _ p hp]

theorem address_ready {n id x : Nat} {cells : Bank → Int → Option Bool}
    (R : Ready n id x cells) : afterCopy n cells 11 = wordAt (width n) 1 :=
  (TapeInstall.installed_source _ _ _ _ rfl).trans (resetBank R 11 1 (by decide) rfl)

theorem addend_ready {n id x : Nat} {cells : Bank → Int → Option Bool}
    (R : Ready n id x cells) (fit : x < 2^TableIO.width n) :
    afterCopy n cells 12 = wordAt (width n) x := by
  apply installLow fit 12 1 copyLow rfl
  · exact (TapeInstall.installed_source _ _ _ _ (by decide)).trans R.rawCandidate
  · exact resetBank R 12 0 (by decide) rfl

theorem accumulator_ready {n id x : Nat} {cells : Bank → Int → Option Bool}
    (R : Ready n id x cells) (j : Fin 3) :
    afterCopy n cells ⟨13+j.val,by omega⟩ =
      wordAt (width n) (fixed n id ⟨5+j.val,by omega⟩) := by
  fin_cases j
  · exact (TapeInstall.installed_source _ _ _ _ rfl).trans (resetBank R 13 5 (by decide) rfl)
  · exact (TapeInstall.installed_source _ _ _ _ rfl).trans (resetBank R 14 6 (by decide) rfl)
  · exact (TapeInstall.installed_source _ _ _ _ rfl).trans (resetBank R 15 7 (by decide) rfl)

theorem countdown_ready {n id x : Nat} {cells : Bank → Int → Option Bool}
    (R : Ready n id x cells) : afterCopy n cells 16 = wordAt (width n) 0 :=
  (TapeInstall.installed_source _ _ _ _ rfl).trans (resetBank R 16 0 (by decide) rfl)

def start (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    machine.Config :=
  thenLeft A C embedding embedding
    (A.bankConfig embedding (TapeInstall.start 3 reset input cells prior) (fun _ => 0) cells)

def stop (n : Nat) (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    machine.Config :=
  thenRight A C embedding embedding
    (C.bankConfig embedding
      (TapeInstall.stop 0 copyLow input (afterReset n cells) prior (TableIO.width n))
      (fun _ => 0) cells)

private theorem sameHead (P : SearchTransducer) (e : Fin P.workTapes ↪ Fin P.workTapes)
    (he : ∀ i, e i = i) (c : P.Config) (h : Fin P.workTapes → Int)
    (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig e c h m).workHead = c.workHead := by
  funext i
  simpa only [he] using P.bankConfig_head_image e c h m i

private theorem sameCell (P : SearchTransducer) (e : Fin P.workTapes ↪ Fin P.workTapes)
    (he : ∀ i, e i = i) (c : P.Config) (h : Fin P.workTapes → Int)
    (m : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig e c h m).workCell = c.workCell := by
  funext i
  simpa only [he] using P.bankConfig_cell_image e c h m i

theorem start_layout (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    (start input cells prior).inputHead = input ∧
    (start input cells prior).workHead = (fun _ => 0) ∧
    (start input cells prior).workCell = cells ∧
    (start input cells prior).outputReversed = prior :=
  ⟨rfl, sameHead A embedding (fun _ => rfl) _ (fun _ => 0) cells, sameCell A embedding (fun _ => rfl) _ (fun _ => 0) cells, rfl⟩

theorem stop_layout (n : Nat) (input : Int) (cells : Bank → Int → Option Bool) (prior : List Bool) :
    (stop n input cells prior).inputHead = input ∧
    (stop n input cells prior).workHead = (fun _ => 0) ∧
    (stop n input cells prior).workCell = afterCopy n cells ∧
    (stop n input cells prior).outputReversed = prior :=
  ⟨rfl, sameHead C embedding (fun _ => rfl) _ (fun _ => 0) cells, sameCell C embedding (fun _ => rfl) _ (fun _ => 0) cells, rfl⟩

/-- Two real tape sweeps install the start address and reusable accumulator
bases and copy the live candidate into a reset, wider addend register. -/
theorem execute {n id x : Nat} {cells : Bank → Int → Option Bool} {raw prior : List Bool} {input : Int}
    (R : Ready n id x cells) (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    ∃ ticks, machine.BoundedSegment raw (width n+1) (start input cells prior)
      (stop n input cells prior) ticks ∧ machine.step raw (stop n input cells prior) = none := by
  let w := width n
  let wr := TableIO.width n
  obtain ⟨runA, stopA⟩ :=
    TapeInstall.execute 3 reset (by decide) raw (encodeLabel w 0) prior input cells (R.constants 0) hin
  have la : (encodeLabel w 0).length = w := length_encodeLabel _ _
  rw [la] at runA stopA
  have ordered : afterReset n cells 0 = work (encodeLabel wr n) :=
    (TapeInstall.installed_source _ _ _ _ (by decide)).trans R.rawOrder
  obtain ⟨runC, stopC⟩ :=
    TapeInstall.execute 0 copyLow (by decide) raw (encodeLabel wr n) prior input
      (afterReset n cells) ordered hin
  have lc : (encodeLabel wr n).length = wr := length_encodeLabel _ _
  rw [lc] at runC stopC
  let s := A.bankConfig embedding (TapeInstall.stop 3 reset input cells prior w) (fun _ => 0) cells
  let c := C.bankConfig embedding (TapeInstall.start 0 copyLow input (afterReset n cells) prior)
    (fun _ => 0) cells
  have ha := A.relocateBanks_segment embedding runA (heads := fun _ => 0) (cells := cells) (by simp)
  have hb₀ := PhysicalEntry.segment_mono runC (show wr+1 ≤ w+1 by dsimp [w, wr, width]; omega)
  have hb := C.relocateBanks_segment embedding hb₀ (heads := fun _ => 0) (cells := cells) (by simp)
  change (C.relocateBanks embedding).BoundedSegment raw (w+1) c _ _ at hb
  have eq : thenEntry A C embedding embedding s = c := by
    have hh₁ : s.workHead = (fun _ => 0) := sameHead A embedding (fun _ => rfl) _ (fun _ => 0) cells
    have hh₂ : c.workHead = (fun _ => 0) := sameHead C embedding (fun _ => rfl) _ (fun _ => 0) cells
    have hc₁ : s.workCell = afterReset n cells := sameCell A embedding (fun _ => rfl) _ (fun _ => 0) cells
    have hc₂ : c.workCell = afterReset n cells := sameCell C embedding (fun _ => rfl) _ (fun _ => 0) cells
    let m : Fin 4 → Int → (Bank → Int) → (Bank → Int → Option Bool) → List Bool →
        (C.relocateBanks embedding).Config := fun q i h m o => ⟨q,i,h,m,o⟩
    have e₁ : thenEntry A C embedding embedding s = m 0 input (fun _ => 0) (afterReset n cells) prior := by
      change m 0 input s.workHead s.workCell prior = _
      rw [hh₁,hc₁]
    have e₂ : c = m 0 input (fun _ => 0) (afterReset n cells) prior := by
      have hs : c.state = 0 := rfl
      have hi : c.inputHead = input := rfl
      have ho : c.outputReversed = prior := rfl
      generalize c = k at hs hi hh₂ hc₂ ho ⊢
      cases k
      simp_all [m]
    exact e₁.trans e₂.symm
  rw [← eq] at hb
  have hA : (A.relocateBanks embedding).step raw s = none := by
    unfold s
    rw [relocateBanks_step,stopA]
    rfl
  refine ⟨_, thenSegment A C embedding embedding ha hA hb, ?_⟩
  unfold stop
  rw [thenStep_right, relocateBanks_step, stopC]
  rfl

end Mathproof.MinimumGeneration.PhysicalGreedyHeaderInstall
