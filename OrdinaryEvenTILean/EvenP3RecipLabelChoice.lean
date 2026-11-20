import EvenNextRecipLabels

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped Matrix
open Matrix Module
open Mathproof.Problem17TracePairing

noncomputable section

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private theorem representative_exists (S : Submodule K (Matrix I I K))
    (c : Module.Dual K S) : ∃ P : Matrix I I K,
      (tracePairing P).comp S.subtype = c := by
  obtain ⟨C, hc⟩ := LinearMap.exists_extend c
  obtain ⟨P, hp⟩ := ((tracePairing (K := K) (ι := I)).toDual tracePairing_nondegenerate).surjective C
  change tracePairing P = C at hp
  exact ⟨P, by rw [hp]; exact hc⟩

/-- Count each character of a trace slice via one actual matrix label.
Distinct restricted characters can never share a representative. -/
def matrixLabelChoice (S : Submodule K (Matrix I I K)) :
    Module.Dual K S ↪ Matrix I I K where
  toFun c := Classical.choose (representative_exists S c)
  inj' := by
    intro c d h
    calc
      c = (tracePairing (Classical.choose (representative_exists S c))).comp S.subtype :=
        (Classical.choose_spec (representative_exists S c)).symm
      _ = (tracePairing (Classical.choose (representative_exists S d))).comp S.subtype :=
        congrArg (fun P => (tracePairing P).comp S.subtype) h
      _ = d := Classical.choose_spec (representative_exists S d)

theorem matrixLabelChoice_spec (S : Submodule K (Matrix I I K)) (c : Module.Dual K S) :
    (tracePairing (matrixLabelChoice S c)).comp S.subtype = c :=
  Classical.choose_spec (representative_exists S c)

#print axioms matrixLabelChoice_spec

end
end Mathproof.EvenTI.Reciprocal.Coverage
