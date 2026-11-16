import Mathproof.Computability.MultitapeLocality20261014
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup

namespace Mathproof.MinimumGeneration

open Mathproof.Multitape
open Mathproof.Multitape.Locality (moveOffset)

inductive InputCell
  | leftEnd
  | data (bit : Bool)
  | rightEnd

/-- The output symbol is supplied by the transition. The transition can read only
the input tape and the work tapes. The finite control types are fixed globally. -/
structure SearchTransducer where
  states : ℕ
  workTapes : ℕ
  initialState : Fin states
  transition : Fin states → InputCell → (Fin workTapes → Option Bool) →
    Option (Fin states × Move × (Fin workTapes → Action (Option Bool)) × Option Bool)

namespace SearchTransducer

structure Config (M : SearchTransducer) where
  state : Fin M.states
  inputHead : Int
  workHead : Fin M.workTapes → Int
  workCell : Fin M.workTapes → Int → Option Bool
  outputReversed : List Bool

def initial (M : SearchTransducer) : M.Config :=
  ⟨M.initialState, 0, fun _ => 0, fun _ _ => none, []⟩

def readInput (word : List Bool) (head : Int) : InputCell :=
  if head < 0 then .leftEnd
  else (word[head.toNat]?).elim .rightEnd InputCell.data

/-- One local transition. The immutable input and the write-only output are
separate from the work tapes. -/
def step (M : SearchTransducer) (word : List Bool) (c : M.Config) : Option M.Config :=
  (M.transition c.state (readInput word c.inputHead) (fun i => c.workCell i (c.workHead i))).map
    fun (state, inputMove, workAction, outputBit) =>
      { state := state
        inputHead := c.inputHead + moveOffset inputMove
        workHead := fun i => c.workHead i + moveOffset (workAction i).move
        workCell := fun i j =>
          if j = c.workHead i then (workAction i).write.getD (c.workCell i j)
          else c.workCell i j
        outputReversed := outputBit.elim c.outputReversed (fun bit => bit :: c.outputReversed) }

/-- Exactly the requested number of transitions, with failure when a transition
is requested past halt. -/
def after (M : SearchTransducer) (word : List Bool) : ℕ → Option M.Config
  | 0 => some M.initial
  | k + 1 => (M.after word k).bind (M.step word)

def logarithmicWorkspace (M : SearchTransducer) (C : ℕ) (word : List Bool) : Prop :=
  ∀ (k : ℕ) (c : M.Config), M.after word k = some c →
    (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (word.length : Int) ∧
      ∀ i, (c.workHead i).natAbs ≤ C * (Nat.log2 (word.length + 1) + 1)

def outputs (M : SearchTransducer) (word result : List Bool) : Prop :=
  ∃ (k : ℕ) (c : M.Config), M.after word k = some c ∧ M.step word c = none ∧
    c.outputReversed.reverse = result

/-- Output emitted by this transducer is append-only, measured in forward order. -/
theorem step_output_prefix {M : SearchTransducer} {word : List Bool}
    {c c' : M.Config} (h : M.step word c = some c') :
    ∃ suffix : List Bool, c'.outputReversed.reverse = c.outputReversed.reverse ++ suffix := by
  unfold step at h
  cases ht : M.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [ht] at h
  | some p =>
    rcases p with ⟨state, inputMove, workAction, outputBit⟩
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst c'
    cases outputBit with
    | none => exact ⟨[], by simp⟩
    | some bit => exact ⟨[bit], by simp⟩

end SearchTransducer

def encodeLabel (width value : ℕ) : List Bool :=
  (List.range width).map (Nat.testBit value)

/-- Unary order header followed by a fixed-width binary multiplication table. -/
def encodeCayley (n : ℕ) [Mul (Fin n)] : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun x =>
      (List.finRange n).flatMap (fun y => encodeLabel (Nat.log2 n + 1) (x * y).val))

/-- Write the chosen element labels using the same width as the input table. -/
def encodeGenerators (n : ℕ) (gs : List (Fin n)) : List Bool :=
  gs.flatMap (fun g => encodeLabel (Nat.log2 n + 1) g.val)

def Generates {G : Type*} [Group G] (gs : List G) : Prop :=
  Subgroup.closure {g | g ∈ gs} = ⊤

def MinimumGenerators {G : Type*} [Group G] (gs : List G) : Prop :=
  Generates gs ∧ ∀ hs : List G, Generates hs → gs.length ≤ hs.length

/-- Exact unrestricted search statement for Question 8.1 in a read-only-input,
write-only-output deterministic multitape model. -/
def CayleyMinimumGeneratorSearch : Prop :=
  ∃ (M : SearchTransducer) (C : ℕ), ∀ (n : ℕ) (G : Group (Fin n)),
    let word := @encodeCayley n G.toMul
    M.logarithmicWorkspace C word ∧
      ∃ gs : List (Fin n), @MinimumGenerators (Fin n) G gs ∧
        M.outputs word (encodeGenerators n gs)


/-- Every finite group has a generating list of least length. -/
theorem exists_minimumGenerators {G : Type*} [Group G] [Fintype G] :
    ∃ gs : List G, MinimumGenerators gs := by
  classical
  let Attained : ℕ → Prop := fun k => ∃ gs : List G, Generates gs ∧ gs.length = k
  have h : ∃ k, Attained k := by
    let gs := (Finset.univ : Finset G).toList
    refine ⟨gs.length, gs, ?_, rfl⟩
    have hset : {g | g ∈ gs} = (Set.univ : Set G) := by
      ext g
      simp [gs]
    rw [Generates, hset, Subgroup.closure_univ]
  obtain ⟨gs, hgs, hs⟩ := Nat.find_spec h
  refine ⟨gs, hgs, ?_⟩
  intro ys hy
  rw [hs]
  exact Nat.find_min' h ⟨ys, hy, rfl⟩

/-- A surjection sends a generating list to a generating list of the same length. -/
theorem generates_map_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (gs : List G) (hg : Generates gs) :
    Generates (gs.map f) := by
  have himage : {y | y ∈ gs.map f} = f '' {x | x ∈ gs} := by
    ext y
    simp
  rw [Generates, himage, ← MonoidHom.map_closure]
  rw [Generates] at hg
  rw [hg, Subgroup.map_top_of_surjective _ hf]



/-- The minimum-length output list has no repeated elements. -/
theorem minimumGenerators_nodup {G : Type*} [Group G]
    {gs : List G} (h : MinimumGenerators gs) : gs.Nodup := by
  classical
  have he : {x : G | x ∈ gs.dedup} = {x : G | x ∈ gs} := by
    ext x
    simp
  have hgen : Generates gs.dedup := by simpa only [Generates, he] using h.1
  have hs := List.dedup_sublist gs
  exact List.dedup_eq_self.mp (hs.eq_of_length (le_antisymm hs.length_le (h.2 _ hgen)))

private theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β)
    (m : ℕ) (hf : ∀ a ∈ xs, (f a).length = m) :
    (xs.flatMap f).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun b hb => hf b (by simp [hb])), List.length_cons, Nat.succ_mul, add_comm]

@[simp] theorem length_encodeLabel (w x : ℕ) : (encodeLabel w x).length = w := by
  simp [encodeLabel]

/-- Exact input length of the binary representation used in the target. -/
theorem length_encodeCayley (n : ℕ) [Mul (Fin n)] :
    (encodeCayley n).length = n + 1 + n * n * (Nat.log2 n + 1) := by
  have inner (x : Fin n) :
      ((List.finRange n).flatMap (fun y => encodeLabel (Nat.log2 n + 1)
        (x * y).val)).length = n * (Nat.log2 n + 1) := by
    rw [length_flatMap_constant _ _ (Nat.log2 n + 1) (by simp)]
    simp
  unfold encodeCayley
  rw [List.length_append, List.length_append, List.length_replicate, List.length_singleton,
    length_flatMap_constant _ _ (n * (Nat.log2 n + 1)) (fun x _ => inner x)]
  simp [Nat.mul_assoc, Nat.add_assoc]

end Mathproof.MinimumGeneration
