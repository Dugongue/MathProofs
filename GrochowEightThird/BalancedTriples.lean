import Mathlib.Tactic

open Finset

namespace BalancedTriples

def triples : Finset (Finset (Fin 6)) :=
  (univ : Finset (Fin 6)).powersetCard 3

def distinguished : Finset (Fin 6) := {0, 1, 2}

def family : Finset (Finset (Fin 6)) :=
  triples.filter fun T => 2 ≤ (T ∩ distinguished).card

def complement (T : Finset (Fin 6)) : Finset (Fin 6) := univ \ T

theorem balancedTriplesCounterexample :
    family.card = 10 ∧
    (triples.filter fun T => decide (T ∈ family) == decide (complement T ∈ family)) = ∅ ∧
    (∀ i : Fin 6, (family.filter fun T => i ∈ T).Nonempty) ∧
    (∀ i : Fin 6, (family.filter fun T => i ∉ T).Nonempty) := by
  decide

#print axioms balancedTriplesCounterexample

end BalancedTriples
