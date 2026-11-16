import Mathproof.MinimumGenerationCayleyReaderFrame
import Mathproof.MinimumGenerationCayleyReaderReset

namespace Mathproof.MinimumGeneration.CayleyReaderRestore

open SearchTransducer
open InputPosition (work)
open CayleyQueryPrefixModel (width rawSpace keep cells width_le)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The original machine's 35 tapes retain their original bank numbers. -/
def readerBanks : Fin 35 ↪ Fin 39 :=
  ⟨Fin.castAdd 4, fun _ _ h => Fin.ext (congrArg (fun i : Fin 39 => i.val) h)⟩

def clock : Fin 39 := 35
def savedCard : Fin 39 := 36
def savedOrder : Fin 39 := 37
def blank : Fin 39 := 38

/-- Restore all disposable regions. The virtual pointer is read from the
preserved address tape, which may have been updated by the native controller. -/
def source (j : Fin 39) : Option (Fin 39) :=
  if j = 0 then some savedCard
  else if j = 3 then some 28
  else if j = 4 then some 33
  else if j = 5 then some savedOrder
  else if j = 22 then some 21
  else if j = 25 then some 24
  else if j.val < 21 then some blank
  else none

abbrev machine := CayleyReaderReset.machine clock source

/-- Persistent layout needed to reproduce the exact 35 tapes for a call. -/
structure Ready {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (ticks : List Bool) (old : Fin 39 → Int → Option Bool) : Prop where
  clockWord : old clock = work ticks
  clockEnough : rawSpace (@encodeCayley n G.toMul) ≤ ticks.length
  cardinality : old savedCard = work (encodeLabel (width n) (n+n))
  order : old savedOrder = work (encodeLabel (width n) n)
  clean : old blank = fun _ => none
  live : ∀ j ∈ keep, old (readerBanks j) = cells G cut s t p j
  outside : ∀ (j : Fin 35) (z : Int), rawSpace (@encodeCayley n G.toMul) < z.natAbs →
    old (readerBanks j) z = none

private theorem rangeReader (j : Fin 39) (h : j.val < 35) :
    readerBanks ⟨j.val,h⟩ = j := Fin.ext rfl

private theorem sourceKinds {i j : Fin 39} (map : source i = some j) :
    i.val < 35 ∧ (j = savedCard ∨ j = savedOrder ∨ j = blank ∨
      j = 21 ∨ j = 24 ∨ j = 28 ∨ j = 33) := by
  unfold source at map
  split at map
  · rename_i h
    subst i
    exact ⟨by decide, .inl (Option.some.inj map).symm⟩
  · split at map
    · rename_i h
      subst i
      exact ⟨by decide, .inr (.inr (.inr (.inr (.inr (.inl (Option.some.inj map).symm)))))⟩
    · split at map
      · rename_i h
        subst i
        exact ⟨by decide, .inr (.inr (.inr (.inr (.inr (.inr (Option.some.inj map).symm)))))⟩
      · split at map
        · rename_i h
          subst i
          exact ⟨by decide, .inr (.inl (Option.some.inj map).symm)⟩
        · split at map
          · rename_i h
            subst i
            exact ⟨by decide, .inr (.inr (.inr (.inl (Option.some.inj map).symm)))⟩
          · split at map
            · rename_i h
              subst i
              exact ⟨by decide, .inr (.inr (.inr (.inr (.inl (Option.some.inj map).symm))))⟩
            · split at map
              · rename_i h
                exact ⟨h.trans (by decide), .inr (.inr (.inl (Option.some.inj map).symm))⟩
              · cases map

private theorem sourceReady {n : ℕ} {G : Group (Fin n)} {cut : ℕ} {s t : Fin (n+n)}
    {p : ℕ} {ticks : List Bool} {old : Fin 39 → Int → Option Bool}
    (prepared : Ready G cut s t p ticks old)
    (i j : Fin 39) (map : source i = some j) :
    source j = none ∧ j ≠ clock ∧ ∀ z, ticks.length < z.natAbs → old i z = old j z := by
  obtain ⟨ib,kinds⟩ := sourceKinds map
  have oldBlank (z : Int) (hz : ticks.length < z.natAbs) (a : Fin 39) (hb : a.val < 35) :
      old a z = none :=
    rangeReader a hb ▸ prepared.outside ⟨a.val,hb⟩ z (prepared.clockEnough.trans_lt hz)
  have numBound : width n ≤ ticks.length :=
    ((Nat.le_succ _).trans (width_le G)).trans prepared.clockEnough
  rcases kinds with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans ?_⟩
    rw [prepared.cardinality]
    exact (CayleyReaderFrame.workOutside (by simpa [encodeLabel] using numBound) z hz).symm
  · refine ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans ?_⟩
    rw [prepared.order]
    exact (CayleyReaderFrame.workOutside (by simpa [encodeLabel] using numBound) z hz).symm
  · exact ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans (congrFun prepared.clean z).symm⟩
  · exact ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans (oldBlank z hz 21 (by decide)).symm⟩
  · exact ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans (oldBlank z hz 24 (by decide)).symm⟩
  · exact ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans (oldBlank z hz 28 (by decide)).symm⟩
  · exact ⟨by decide,by decide,fun z hz => (oldBlank z hz i ib).trans (oldBlank z hz 33 (by decide)).symm⟩

private theorem restored {n : ℕ} {G : Group (Fin n)} {cut : ℕ} {s t : Fin (n+n)}
    {p : ℕ} {ticks : List Bool} {old : Fin 39 → Int → Option Bool}
    (prepared : Ready G cut s t p ticks old) (j : Fin 35) :
    (source (readerBanks j)).elim (old (readerBanks j)) (fun i => old i) = cells G cut s t p j := by
  have zeroWide := prepared.live 28 (by change 21 ≤ 28 ∧ 28 ≠ 22 ∧ 28 ≠ 25; decide)
  have pointer := prepared.live 33 (by change 21 ≤ 33 ∧ 33 ≠ 22 ∧ 33 ≠ 25; decide)
  have zeroRow := prepared.live 21 (by change 21 ≤ 21 ∧ 21 ≠ 22 ∧ 21 ≠ 25; decide)
  have zeroTarget := prepared.live 24 (by change 21 ≤ 24 ∧ 24 ≠ 22 ∧ 24 ≠ 25; decide)
  fin_cases j <;> first
    | exact prepared.cardinality
    | exact prepared.order
    | exact prepared.clean
    | exact zeroWide
    | exact pointer
    | exact zeroRow
    | exact zeroTarget
    | exact prepared.live _ (by change 21 ≤ (_ : ℕ) ∧ _ ≠ 22 ∧ _ ≠ 25; decide)

/-- Restore the exact 35-bank reader entry from the post-call physical frame
with its current live virtual pointer and immutable templates. -/
theorem execute {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (input : Int) (prior ticks : List Bool) (old : Fin 39 → Int → Option Bool)
    (prepared : Ready G cut s t p ticks old)
    (inputLegal : (-1 : Int) ≤ input ∧ input ≤ (@encodeCayley n G.toMul).length) :
    let raw := @encodeCayley n G.toMul
    ∃ k last,
      machine.BoundedSegment raw (ticks.length+1)
        (CayleyReaderReset.start clock source input prior old) last k ∧
      machine.step raw last = none ∧ last.inputHead = input ∧ last.outputReversed = prior ∧
      (∀ i, last.workHead i = 0) ∧
      (∀ j : Fin 35, last.workCell (readerBanks j) = cells G cut s t p j) ∧
      (∀ j : Fin 39, 35 ≤ j.val → last.workCell j = old j) := by
  obtain ⟨k,run,halt,inp,out,heads,cells⟩ := CayleyReaderReset.execute clock source
    (@encodeCayley n G.toMul) prior ticks input old (by decide) prepared.clockWord inputLegal
    (sourceReady prepared)
  refine ⟨k,_,run,halt,inp,out,heads,?_,?_⟩
  · intro j
    exact (cells (readerBanks j)).trans (restored prepared j)
  · intro j high
    have fixed : source j = none := by
      cases m : source j with
      | none => rfl
      | some a =>
        have h := (sourceKinds m).1
        omega
    exact (cells j).trans (by rw [fixed];rfl)

/-- Two widenings of the reader's four-label clock suffice for the common
scratch window, including the smallest Cayley tables. -/
theorem resetClockEnough {n : ℕ} (G : Group (Fin n)) :
    rawSpace (@encodeCayley n G.toMul) ≤ 16 * TableIO.width n := by
  let raw := @encodeCayley n G.toMul
  let v := TableIO.width n
  let q := (2 : ℕ)^v
  have vpos : 0 < v := by unfold v TableIO.width; omega
  have hfit : n < q := Nat.lt_log2_self
  have twice : 2*v ≤ q := by
    have low : v-1 < 2^(v-1) := Nat.lt_two_pow_self
    have split : q = 2^(v-1)*2 := by
      change 2^v = _
      rw [← pow_succ]
      congr 1
    rw [split]
    omega
  have qpos : 0 < q := by omega
  have qsq : 4 ≤ q*q := Nat.mul_le_mul (by omega : 2≤q) (by omega : 2≤q)
  have front : 2*(n+2) ≤ q*q*q := by
    have first : 2*(n+2) ≤ 4*q := by omega
    exact first.trans (Nat.mul_le_mul_right q qsq)
  have nsq : n*n < q*q := by
    have p := Nat.mul_le_mul_right n hfit.le
    have t := Nat.mul_lt_mul_of_pos_left hfit qpos
    exact p.trans_lt t
  have body : 2*(n*n*v) < q*q*q := calc
    2*(n*n*v) = (n*n)*(2*v) := by ring
    _ ≤ (n*n)*q := Nat.mul_le_mul_left _ twice
    _ < _ := Nat.mul_lt_mul_of_pos_right nsq qpos
  have size : raw.length+1 < q*q*q := by
    change (@encodeCayley n G.toMul).length+1 < _
    rw [@length_encodeCayley n G.toMul]
    change n+1+n*n*v+1 < _
    omega
  have pow : q*q*q = 2^(3*v) := by
    change (2:ℕ)^v * 2^v * 2^v = _
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have lg : (raw.length+1).log2 < 3*v := (Nat.log2_lt (by omega)).2 (size.trans_eq pow)
  change rawSpace raw ≤ 16*v
  unfold rawSpace
  omega


end Mathproof.MinimumGeneration.CayleyReaderRestore
