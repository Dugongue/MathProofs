import Mathproof.Meta.TISLPermutationKill20260908

namespace BlindAssembly

open Mathproof.Meta.TISteppingStones20260904
open Mathproof.Meta.TISLModeAsymmetry20260908
open Mathproof.Meta.TISLPermutationKill20260908

theorem separate_slab_families {K : Type} [Field K] {n : ℕ}
    {i₀ i₁ : Fin n} (hne : i₁ ≠ i₀) (j : Fin n)
    (N M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M.det) :
    ¬ GLRel (swap23 (slab3 i₀ N)) (slab j M) := by
  apply not_glRel_of_mode2_mismatch _ (slab_not_mode2Def hM)
  apply mode3Def_swap23
  change Mode3Def (slab3 i₀ N)
  exact slab3_mode3Def hne N

end BlindAssembly
