import Mathproof.MinimumGenerationRankEntry
import Mathproof.MinimumGenerationMacroDispatch
import Init.Data.List.FinRange

namespace Mathproof.MinimumGeneration.RankLiveEntry

open SearchTransducer

/-- Enter a row by reading the first source entry, then read the second entry,
update the weighted accumulator, and repeat. On exhaustion scale the answer. -/
structure Operations (S W : Nat) where
  entry : Fin 4 → Fin S
  transition : Fin 4 → MacroTransition S W
  rowAvailable : Fin S → Bool

def Operations.stages {S W : Nat} (P : Operations S W) : Stages 4 S W where
  first := 0
  entry := P.entry
  transition := P.transition
  next i q :=
    if i = 0 then some (if P.rowAvailable q then 1 else 3)
    else if i = 1 then some 2
    else if i = 2 then some 0
    else none

namespace Operations

variable {S W : Nat} (P : Operations S W)

abbrev Cfg (i : Fin 4) := (P.stages.component i).Config

/-- Each certified macro keeps the specified data banks and prior output. -/
def Preserves (keep : Set (Fin W)) {i j : Fin 4} (c : P.Cfg i) (d : P.Cfg j) : Prop :=
  d.outputReversed = c.outputReversed ∧
    ∀ b ∈ keep, d.workHead b = c.workHead b ∧ d.workCell b = c.workCell b

theorem Preserves.trans {keep : Set (Fin W)} {i j k : Fin 4}
    {a : P.Cfg i} {b : P.Cfg j} {c : P.Cfg k}
    (hab : P.Preserves keep a b) (hbc : P.Preserves keep b c) : P.Preserves keep a c :=
  ⟨hbc.1.trans hab.1, fun t ht => ⟨(hbc.2 t ht).1.trans (hab.2 t ht).1,
    (hbc.2 t ht).2.trans (hab.2 t ht).2⟩⟩

theorem preserves_enter {keep : Set (Fin W)} {i : Fin 4} (j : Fin 4) (c : P.Cfg i) :
    P.Preserves keep c (P.stages.enter j c) :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

variable {K : Type*} [CommRing K] {m n : Nat}

def foldRow (read : Fin m → Fin n → K) (a : Fin m → K) (i j : Fin n)
    (acc : K) (r : Fin m) : K :=
  acc + (read r i * a r) * read r j

/-- Bank assertions for the four finite-control phases. Values in these
predicates are proof parameters. The machine computes from its live banks. -/
structure Layout (K : Type*) (m : Nat) where
  cursor : List (Fin m) → K → P.Cfg 0 → Prop
  left : List (Fin m) → K → K → P.Cfg 1 → Prop
  pair : List (Fin m) → K → K → K → P.Cfg 2 → Prop
  finish : K → P.Cfg 3 → Prop
  output : K → P.Cfg 3 → Prop

/-- Local specifications of the four actual physical segments. The row list is
a logical description of the cursor; the driver allocates no tape for it. -/
structure Contract (word : List Bool) (B : Nat) (keep : Set (Fin W))
    (read : Fin m → Fin n → K) (a : Fin m → K) (b : Fin n → K) (i j : Fin n)
    (L : P.Layout K m) : Prop where
  readLeft : ∀ r rs acc c, L.cursor (r :: rs) acc c →
    ∃ k d, (P.stages.component 0).BoundedSegment word B c d k ∧
      (P.stages.component 0).step word d = none ∧ P.rowAvailable d.state = true ∧
      L.left (r :: rs) acc (read r i) (P.stages.enter 1 d) ∧ P.Preserves keep c d
  exhausted : ∀ acc c, L.cursor [] acc c →
    ∃ k d, (P.stages.component 0).BoundedSegment word B c d k ∧
      (P.stages.component 0).step word d = none ∧ P.rowAvailable d.state = false ∧
      L.finish acc (P.stages.enter 3 d) ∧ P.Preserves keep c d
  readRight : ∀ r rs acc x c, L.left (r :: rs) acc x c →
    ∃ k d, (P.stages.component 1).BoundedSegment word B c d k ∧
      (P.stages.component 1).step word d = none ∧
      L.pair (r :: rs) acc x (read r j) (P.stages.enter 2 d) ∧ P.Preserves keep c d
  accumulate : ∀ r rs acc x y c, L.pair (r :: rs) acc x y c →
    ∃ k d, (P.stages.component 2).BoundedSegment word B c d k ∧
      (P.stages.component 2).step word d = none ∧
      L.cursor rs (acc + (x * a r) * y) (P.stages.enter 0 d) ∧ P.Preserves keep c d
  scale : ∀ acc c, L.finish acc c →
    ∃ k d, (P.stages.component 3).BoundedSegment word B c d k ∧
      (P.stages.component 3).step word d = none ∧ L.output (b i * acc) d ∧
      P.Preserves keep c d

private theorem routeRows {word : List Bool} {B : Nat} {keep : Set (Fin W)}
    {read : Fin m → Fin n → K} {a : Fin m → K} {b : Fin n → K} {i j : Fin n}
    {L : P.Layout K m} (h : P.Contract word B keep read a b i j L)
    (rows : List (Fin m)) (acc : K) (c : P.Cfg 0) (hc : L.cursor rows acc c) :
    ∃ k d, P.stages.Routed word B 0 c 3 d k ∧
      (P.stages.component 3).step word d = none ∧
      L.output (b i * rows.foldl (foldRow read a i j) acc) d ∧ P.Preserves keep c d := by
  induction rows generalizing acc c with
  | nil =>
    obtain ⟨k, d, he, hs, hz, hFinish, hd⟩ := h.exhausted acc c hc
    obtain ⟨l, e, he', hs', hAnswer, heFrame⟩ := h.scale acc _ hFinish
    have route : P.stages.next 0 d.state = some 3 := by simp [stages, hz]
    exact ⟨k + 1 + l, e, .call he hs route (.finish he'), hs', hAnswer,
      Preserves.trans P hd (Preserves.trans P (P.preserves_enter 3 d) heFrame)⟩
  | cons r rs ih =>
    obtain ⟨k, d, hl, hlStop, hm, hRight, hd⟩ := h.readLeft r rs acc c hc
    obtain ⟨l, e, hr, hrStop, hPair, he⟩ := h.readRight r rs acc (read r i) _ hRight
    obtain ⟨p, f, ha, haStop, hRest, hf⟩ :=
      h.accumulate r rs acc (read r i) (read r j) _ hPair
    obtain ⟨q, z, hTail, hStop, hAnswer, hz⟩ := ih _ _ hRest
    have routeLeft : P.stages.next 0 d.state = some 1 := by simp [stages, hm]
    have routeRight : P.stages.next 1 e.state = some 2 := rfl
    have routeAccum : P.stages.next 2 f.state = some 0 := rfl
    have keepLeft := Preserves.trans P hd (P.preserves_enter 1 d)
    have keepRight := Preserves.trans P he (P.preserves_enter 2 e)
    have keepAccum := Preserves.trans P hf (P.preserves_enter 0 f)
    exact ⟨k + 1 + (l + 1 + (p + 1 + q)), z,
      .call hl hlStop routeLeft (.call hr hrStop routeRight (.call ha haStop routeAccum hTail)),
      hStop, hAnswer, Preserves.trans P keepLeft
        (Preserves.trans P keepRight (Preserves.trans P keepAccum hz))⟩

/-- One binary controller executes the complete weighted entry loop on the
same input. It returns the exact Gram entry while spending one common
head bound throughout all row callbacks and arithmetic segments. -/
theorem executeGramEntry {word : List Bool} {B : Nat} {keep : Set (Fin W)}
    (A : Matrix (Fin m) (Fin n) K) (a : Fin m → K) (b : Fin n → K) (i j : Fin n)
    (L : P.Layout K m) (h : P.Contract word B keep A a b i j L)
    (c : P.Cfg 0) (hc : L.cursor (List.finRange m) 0 c) :
    ∃ (k : Nat) (d : P.Cfg 3),
      P.stages.machine.BoundedSegment word B (P.stages.tag 0 c) (P.stages.tag 3 d) k ∧
      P.stages.machine.step word (P.stages.tag 3 d) = none ∧
      L.output (RankMinors.weightedGram A a b i j) d ∧ P.Preserves keep c d := by
  obtain ⟨k, d, hRoute, hStop, hOut, hKeep⟩ := P.routeRows h _ _ _ hc
  obtain ⟨hRun, hHalt⟩ := P.stages.routed_stop hRoute hStop (by rfl)
  have hGram := RankMinors.streamWeightedGramEntry_eq A a b i j
  unfold RankMinors.streamWeightedGramEntry at hGram
  rw [Fin.foldl_eq_finRange_foldl] at hGram
  exact ⟨k, d, hRun, hHalt, hGram ▸ hOut, hKeep⟩

end Operations
end Mathproof.MinimumGeneration.RankLiveEntry
