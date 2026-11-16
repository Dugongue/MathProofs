import Mathproof.MinimumGenerationGreedyGenerator
import Mathproof.MinimumGenerationReingoldNative

namespace Mathproof.MinimumGeneration.RawGreedyMembership

/-- A subgroup membership query computed by the native addressed Reingold
reader on the virtual graph of the physical Cayley input. -/
def query {n : Nat} (word : List Bool) (identity : Fin n)
    (seed : Fin n → Bool) (x : Fin n) : Bool :=
  ReingoldNative.decider n (ReingoldLiveInput.rawAdj word n identity.val seed .full) identity x

theorem query_correct {n : Nat} (G : Group (Fin n)) :
    @ChiefExecution.CorrectMembership n G (query (@encodeCayley n G.toMul) G.toOne.one) := by
  intro seed x
  rw [query, ReingoldNative.raw_cayley_query n G seed .full G.toOne.one x]
  exact @cayley_reachable_iff_mem_closure (Fin n) G {a | seed a = true} x

def next {n : Nat} (word : List Bool) (identity : Fin n)
    (eligible : Fin n → Bool) (start : Nat) : Option (Fin n) :=
  GreedyGenerator.next (query word identity) eligible start

theorem next_spec {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool)
    (start : Nat) (x : Fin n) :
    next (@encodeCayley n G.toMul) G.toOne.one eligible start = some x ↔
      start ≤ x.val ∧
      (eligible x = true ∧ x ∉ @Subgroup.closure (Fin n) G {y | eligible y = true ∧ y.val < x.val}) ∧
      ∀ y : Fin n, start ≤ y.val → y.val < x.val →
        (eligible y = true → y ∈ @Subgroup.closure (Fin n) G {z | eligible z = true ∧ z.val < y.val}) :=
  @GreedyGenerator.next_spec n G _ (query_correct G) eligible start x

theorem closure_accept_prefix {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) :
    @Subgroup.closure (Fin n) G
      {x | GreedyGenerator.accept (query (@encodeCayley n G.toMul) G.toOne.one) eligible x = true ∧
        x.val < cut} =
      @Subgroup.closure (Fin n) G {x | eligible x = true ∧ x.val < cut} :=
  @GreedyGenerator.closure_accept_prefix n G _ (query_correct G) eligible cut

end Mathproof.MinimumGeneration.RawGreedyMembership
