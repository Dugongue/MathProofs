import Mathproof.MinimumGenerationBipartiteCayley
import Mathproof.MinimumGenerationRawGreedyMembership

namespace Mathproof.MinimumGeneration.BipartiteCayley

open SimpleGraph

private def sumAddress {n : Nat} : Fin n ⊕ Fin n → Fin (n+n)
  | .inl x => left x
  | .inr x => right x

private theorem split_sumAddress {n : Nat} (a : Fin n ⊕ Fin n) :
    split (sumAddress a) = a := by
  cases a <;> simp [sumAddress]

private theorem reachable_comap_left {n : Nat} (G : SimpleGraph (Fin n ⊕ Fin n))
    (x y : Fin n) :
    (G.comap split).Reachable (left x) (left y) ↔ G.Reachable (.inl x) (.inl y) := by
  constructor
  · intro h
    simpa only [Hom.comap_apply, split_left] using h.map (Hom.comap split G)
  · intro h
    let f : G →g G.comap split := ⟨sumAddress, by
      intro a b hab
      change G.Adj (split (sumAddress a)) (split (sumAddress b))
      simpa only [split_sumAddress] using hab⟩
    exact h.map f

/-- The existing native Reingold evaluator can consume the one-quotient
two-copy matrix. The computation returns exact eligible-prefix membership. -/
def rawPrefixQuery {n : Nat} (word : List Bool) (identity : Fin n)
    (eligible : Fin n → Bool) (cut : Nat) (x : Fin n) : Bool :=
  ReingoldNative.decider (n+n) (rawBits word identity eligible cut) (left identity) (left x)

theorem rawPrefixQuery_correct {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool)
    (cut : Nat) (x : Fin n) :
    rawPrefixQuery (@encodeCayley n G.toMul) G.toOne.one eligible cut x = true ↔
      x ∈ @Subgroup.closure (Fin n) G {z | eligible z = true ∧ z.val < cut} := by
  let S : Set (Fin n) := {z | eligible z = true ∧ z.val < cut}
  let H := @graph (Fin n) G S
  rw [rawPrefixQuery]
  exact (ReingoldNative.decider_correct (n+n) (H.comap split) _ (by
    intro a b
    rw [rawBits_correct]
    exact bits_correct G eligible cut a b) (left G.toOne.one) (left x)).trans
      ((reachable_comap_left H G.toOne.one x).trans
        (@reachable_iff_mem_closure (Fin n) G S x))

theorem rawPrefixQuery_eq_ordinary {n : Nat} (G : Group (Fin n)) (eligible : Fin n → Bool)
    (cut : Nat) (x : Fin n) :
    rawPrefixQuery (@encodeCayley n G.toMul) G.toOne.one eligible cut x =
      RawGreedyMembership.query (@encodeCayley n G.toMul) G.toOne.one
        (fun z => eligible z && decide (z.val < cut)) x := by
  apply Bool.eq_iff_iff.mpr
  rw [rawPrefixQuery_correct]
  exact Iff.trans (by simp [Bool.and_eq_true])
    ((RawGreedyMembership.query_correct G _ x).symm)

end Mathproof.MinimumGeneration.BipartiteCayley
