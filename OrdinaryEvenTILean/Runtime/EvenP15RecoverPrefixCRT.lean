import EvenP15RecoverResidualSemantics

namespace EvenTI.P15Recover

open EvenTI.Part8 EvenTI.CellPreparation EvenOrdinaryTI.LiveRows EvenOrdinaryTI.LCMProjection
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option maxHeartbeats 4500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →ₐ[K] Y j)
variable (enum : Fin (Fintype.card K) ≃ K) (FP : FieldPresentation K)
variable (A : ∀ v, DenseFieldView (K := K) (X v)) (B : ∀ j, DenseFieldView (K := K) (Y j))
variable (c : ∀ j, (Y j)ˣ) (bank : PreparedPrefix) (hBank : PrefixBankExact X Y orig bank)

local notation "V" => VarCount s t d
local notation "U" => ∀ v : Fin V, (physicalVarField X Y v)ˣ
local notation "VV" => (affinePrefixVarView (d := d) X Y A B)
local notation "RV" => (affinePrefixRowView (d := d) Y B)

private def chooseRoot (v : Fin V) (x : (physicalVarField X Y v)ˣ) :
    Option (physicalVarField X Y v)ˣ :=
  letI : Fintype (physicalVarField X Y v) := selectedPrefixFintype X Y (.inl v)
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  boundedUnitRoot enum (VV v).coordinates x

def recoverFeasiblePrefixCRT : Option U :=
  (recoverProjectedPower X Y orig emb enum A B c bank hBank).bind fun powered =>
    (collectSites fun v => chooseRoot X Y enum A B v (powered v)).bind fun roots =>
      correctResidualCRT X Y orig emb enum RV c roots

/-- CRT may choose a different assignment, with the same complete success predicate. -/
theorem recoverFeasiblePrefixCRT_available :
    (recoverFeasiblePrefixCRT X Y orig emb enum A B c bank hBank).isSome =
      (recoverFeasibleLivePrefix X Y orig emb enum A B c bank hBank).isSome := by
  unfold recoverFeasiblePrefixCRT recoverFeasibleLivePrefix
  cases hp : recoverProjectedPower X Y orig emb enum A B c bank hBank with
  | none => rfl
  | some powered =>
    simp only [Option.bind_some]
    change ((collectSites fun v => chooseRoot X Y enum A B v (powered v)).bind _).isSome =
      ((collectSites fun v => chooseRoot X Y enum A B v (powered v)).bind _).isSome
    cases hR : collectSites (fun v => chooseRoot X Y enum A B v (powered v)) with
    | none => rfl
    | some roots =>
      simpa only [Option.bind_some] using correctResidualCRT_available X Y orig emb enum RV c roots

theorem recoverFeasiblePrefixCRT_sound {z : U}
    (hz : recoverFeasiblePrefixCRT X Y orig emb enum A B c bank hBank = some z) :
    prefixEvaluation X Y orig emb z = physicalRHS Y c := by
  unfold recoverFeasiblePrefixCRT at hz
  obtain ⟨p,_,hp⟩ := Option.bind_eq_some_iff.mp hz
  obtain ⟨r,_,hr⟩ := Option.bind_eq_some_iff.mp hp
  exact correctResidualCRT_sound X Y orig emb enum RV c r z hr

noncomputable def recoverLivePrefixCRT : Option U :=
  if decideLivePrefix X Y orig emb enum FP A B c bank hBank then
    recoverFeasiblePrefixCRT X Y orig emb enum A B c bank hBank else none

theorem recoverLivePrefixCRT_available :
    (recoverLivePrefixCRT X Y orig emb enum FP A B c bank hBank).isSome =
      (recoverLivePrefix X Y orig emb enum FP A B c bank hBank).isSome := by
  unfold recoverLivePrefixCRT recoverLivePrefix
  by_cases hb : decideLivePrefix X Y orig emb enum FP A B c bank hBank = true
  · simp only [if_pos hb]
    exact recoverFeasiblePrefixCRT_available X Y orig emb enum A B c bank hBank
  · simp only [if_neg hb]

theorem recoverLivePrefixCRT_sound {z : U}
    (hz : recoverLivePrefixCRT X Y orig emb enum FP A B c bank hBank = some z) :
    prefixEvaluation X Y orig emb z = physicalRHS Y c := by
  unfold recoverLivePrefixCRT at hz
  split at hz
  · exact recoverFeasiblePrefixCRT_sound X Y orig emb enum A B c bank hBank hz
  · contradiction

#print axioms recoverLivePrefixCRT_available
#print axioms recoverLivePrefixCRT_sound

end EvenTI.P15Recover
