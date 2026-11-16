import Mathproof.MinimumGenerationReingoldLiveInput

namespace Mathproof.MinimumGeneration.BipartiteCayley

open SimpleGraph

variable {G : Type*} [Group G]

/-- Each label has a left and right copy. A cross-copy edge uses one oriented
quotient of the original labels, and the two copies of each label are joined. -/
def graph (S : Set G) : SimpleGraph (G ⊕ G) where
  Adj
    | .inl x, .inr y => x = y ∨ x⁻¹ * y ∈ S
    | .inr y, .inl x => x = y ∨ x⁻¹ * y ∈ S
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x h; cases x <;> exact h⟩

private def forget : G ⊕ G → G
  | .inl x | .inr x => x

private theorem projectEdge (S : Set G) {a b : G ⊕ G} (h : (graph S).Adj a b) :
    (mulCayley S).Reachable (forget a) (forget b) := by
  cases a with
  | inl x =>
    cases b with
    | inl y => exact False.elim h
    | inr y =>
      change x = y ∨ x⁻¹ * y ∈ S at h
      obtain rfl | hs := h
      · exact Reachable.rfl
      · by_cases e : x = y
        · subst y
          exact Reachable.rfl
        · exact Adj.reachable ((mulCayley_adj S x y).2 ⟨e, Or.inl hs⟩)
  | inr y =>
    cases b with
    | inr x => exact False.elim h
    | inl x =>
      change x = y ∨ x⁻¹ * y ∈ S at h
      obtain rfl | hs := h
      · exact Reachable.rfl
      · by_cases e : x = y
        · subst y
          exact Reachable.rfl
        · exact (Adj.reachable ((mulCayley_adj S x y).2 ⟨e, Or.inl hs⟩)).symm

private theorem liftEdge (S : Set G) {x y : G} (h : (mulCayley S).Adj x y) :
    (graph S).Reachable (.inl x) (.inl y) := by
  obtain ⟨_, hs | hs⟩ := (mulCayley_adj S x y).1 h
  · exact (Adj.reachable (G := graph S) (u := .inl x) (v := .inr y)
      (Or.inr hs)).trans (Adj.reachable (G := graph S) (Or.inl rfl))
  · exact (Adj.reachable (G := graph S) (u := .inl x) (v := .inr x)
      (Or.inl rfl)).trans (Adj.reachable (G := graph S) (Or.inr hs))

theorem reachable_iff (S : Set G) (x y : G) :
    (graph S).Reachable (.inl x) (.inl y) ↔ (mulCayley S).Reachable x y := by
  constructor
  · intro hr
    change (mulCayley S).Reachable (forget (.inl x)) (forget (.inl y))
    rw [reachable_iff_reflTransGen] at hr
    generalize (Sum.inl x : G ⊕ G) = a at hr ⊢
    generalize (Sum.inl y : G ⊕ G) = b at hr ⊢
    induction hr with
    | refl => exact Reachable.rfl
    | tail _ e ih => exact ih.trans (projectEdge S e)
  · intro hr
    rw [reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact Reachable.rfl
    | tail _ e ih => exact ih.trans (liftEdge S e)

theorem reachable_iff_mem_closure (S : Set G) (x : G) :
    (graph S).Reachable (.inl 1) (.inl x) ↔ x ∈ Subgroup.closure S :=
  (reachable_iff S 1 x).trans (cayley_reachable_iff_mem_closure S x)

/-- The first n virtual addresses belong to the left copy. -/
def split {n : Nat} (i : Fin (n+n)) : Fin n ⊕ Fin n :=
  if h : i.val < n then .inl ⟨i.val, h⟩ else .inr ⟨i.val - n, by omega⟩

def left {n : Nat} (x : Fin n) : Fin (n+n) := ⟨x.val, by omega⟩

def right {n : Nat} (x : Fin n) : Fin (n+n) := ⟨n + x.val, by omega⟩

@[simp] theorem split_left {n : Nat} (x : Fin n) : split (left x) = .inl x := by
  unfold split left
  rw [dif_pos x.isLt]

@[simp] theorem split_right {n : Nat} (x : Fin n) : split (right x) = .inr x := by
  unfold split right
  rw [dif_neg (show ¬ n + x.val < n by omega)]
  congr 2
  exact Nat.add_sub_cancel_left n x.val

theorem split_surjective {n : Nat} : Function.Surjective (@split n) := by
  intro x
  cases x with
  | inl x => exact ⟨left x, split_left x⟩
  | inr x => exact ⟨right x, split_right x⟩

/-- Typed coordinates returned for a cross-side matrix query. Same-side
queries have no edge. A cross-side query always reads the left-to-right quotient. -/
def endpoints {n : Nat} (row col : Fin (n+n)) : Option (Fin n × Fin n) :=
  match split row, split col with
  | .inl x, .inr y | .inr y, .inl x => some (x,y)
  | _, _ => none

@[simp] theorem endpoints_left_right {n : Nat} (x y : Fin n) :
    endpoints (left x) (right y) = some (x,y) := by simp [endpoints]

@[simp] theorem endpoints_right_left {n : Nat} (x y : Fin n) :
    endpoints (right y) (left x) = some (x,y) := by simp [endpoints]

@[simp] theorem endpoints_left_left {n : Nat} (x y : Fin n) :
    endpoints (left x) (left y) = none := by simp [endpoints]

@[simp] theorem endpoints_right_right {n : Nat} (x y : Fin n) :
    endpoints (right x) (right y) = none := by simp [endpoints]

def bits {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat)
    (row col : Fin (n+n)) : Bool :=
  match endpoints row col with
  | none => false
  | some (x,y) =>
    decide (x = y) || (eligible (ReingoldLiveInput.difference G x y) &&
      decide ((ReingoldLiveInput.difference G x y).val < cut))

theorem bits_correct {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat)
    (row col : Fin (n+n)) :
    bits G eligible cut row col = true ↔
      (@graph (Fin n) G {z | eligible z = true ∧ z.val < cut}).Adj (split row) (split col) := by
  unfold bits endpoints
  cases hrow : split row <;> cases hcol : split col <;>
    simp only [graph, Bool.false_eq_true,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Set.mem_ofPred_eq] <;>
    rfl

/-- The raw two-copy adjacency evaluates at most one table quotient per address. -/
def rawBits {n : Nat} (word : List Bool) (identity : Fin n)
    (eligible : Fin n → Bool) (cut : Nat) (row col : Fin (n+n)) : Bool :=
  match endpoints row col with
  | none => false
  | some (x,y) =>
    if x = y then true else
      match TableIO.rawDifference word n identity.val x y with
      | none => false
      | some z => eligible z && decide (z.val < cut)

theorem rawBits_correct {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool)
    (cut : Nat) (row col : Fin (n+n)) :
    rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut row col =
      bits G eligible cut row col := by
  unfold rawBits bits
  cases h : endpoints row col with
  | none => rfl
  | some e =>
    obtain ⟨x,y⟩ := e
    dsimp only
    rw [ReingoldLiveInput.rawDifference_eq_difference n G x y]
    by_cases he : x = y <;> simp [he]

end Mathproof.MinimumGeneration.BipartiteCayley
