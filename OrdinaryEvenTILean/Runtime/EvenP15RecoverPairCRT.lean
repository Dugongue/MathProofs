import EvenP15RecoverNativeBranch
import EvenP11PaidSmithVerdict
import EvenP15AlternativeAttempt

namespace EvenTI.P15Recover

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.Comparison EvenTI.Part8 EvenTI.CellPreparation
open Mathproof.EvenTI.GlobalCoverage
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option maxHeartbeats 5000000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}
variable (F : FieldEncoding K) (FP : FieldPresentation K)
variable (T S : Dense K l n) (P Q : PreparedTrial K l n)
variable (out : BankedTrial F) (ho : compileTrialBanks F T S P Q = some out)

noncomputable def recoverCompiledBranchCRT (b : {b // b ∈ out.branches}) :
    Option {g : Changes K ((l+1)+(l+1)) n // act g T = S} :=
  letI := out.models
  (recoverNativeBranchCRT F out.words out.modes out.layout out.capacities FP b.val
    (actualCompiledBranch F T S P Q out ho b.val b.property)).bind fun x =>
    recoverOriginalTransporter F T S P Q out ho b.val.left b.val.right x

noncomputable def recoverCompiledTrialCRT :
    Option {g : Changes K ((l+1)+(l+1)) n // act g T = S} :=
  out.branches.attach.findSome? (recoverCompiledBranchCRT F FP T S P Q out ho)

private theorem recoverCompiledBranchCRT_covers (b : {b // b ∈ out.branches})
    (hS : scalarAccepted S)
    (hs : (recoverCompiledBranch F FP T S P Q out ho b).isSome = true) :
    (recoverCompiledBranchCRT F FP T S P Q out ho b).isSome = true := by
  letI := out.models
  let hActual := actualCompiledBranch F T S P Q out ho b.val b.property
  let old := recoverNativeBranch F out.words out.modes out.layout out.capacities FP b.val hActual
  let new := recoverNativeBranchCRT F out.words out.modes out.layout out.capacities FP b.val hActual
  have hOld : old.isSome = true := by
    unfold recoverCompiledBranch at hs
    change (old.bind _).isSome = true at hs
    cases h : old with
    | none => simp [h] at hs
    | some x => rfl
  have hNew : new.isSome = true := (recoverNativeBranchCRT_available F out.words out.modes
    out.layout out.capacities FP b.val hActual).trans hOld
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hNew
  have hAction := recoverNativeBranchCRT_sound F out.words out.modes out.layout out.capacities
    FP b.val hActual hx
  obtain ⟨g,hg⟩ := recoverOriginalTransporter_complete F T S P Q out ho b.val.left b.val.right x hS hAction
  unfold recoverCompiledBranchCRT
  change (new.bind _).isSome = true
  simp [hx,hg]

theorem recoverCompiledTrialCRT_covers (hS : scalarAccepted S)
    (hs : (recoverCompiledTrial F FP T S P Q out ho).isSome = true) :
    (recoverCompiledTrialCRT F FP T S P Q out ho).isSome = true := by
  unfold recoverCompiledTrial at hs
  unfold recoverCompiledTrialCRT
  rw [List.findSome?_isSome_iff] at hs ⊢
  obtain ⟨b,hb,hOld⟩ := hs
  exact ⟨b,hb,recoverCompiledBranchCRT_covers F FP T S P Q out ho b hS hOld⟩

noncomputable def recoveringPairAttemptCRT (D : FieldEncoding K) (F : FieldPresentation K) : PairAttempt K :=
  fun T S P Q =>
    match h : compileTrialBanks D T S P Q with
    | none => none
    | some o => (recoverCompiledTrialCRT D F T S P Q o h).map Subtype.val

theorem recoveringPairAttemptCRT_sound
    (g : Changes K ((l+1)+(l+1)) n) (hg : recoveringPairAttemptCRT F FP T S P Q = some g) :
    act g T = S := by
  unfold recoveringPairAttemptCRT at hg
  split at hg
  · contradiction
  · obtain ⟨u,_,rfl⟩ := Option.map_eq_some_iff.mp hg
    exact u.property

theorem recoveringPairAttemptCRT_covers (hT : sourceAccepted T)
    (g : Changes K ((l+1)+(l+1)) n)
    (hg : recoveringPairAttempt F FP T S P Q = some g) :
    (recoveringPairAttemptCRT F FP T S P Q).isSome = true := by
  have hAct := recoveringPairAttempt_sound F FP T S P Q g hg
  have hS : scalarAccepted S := hAct ▸ ((scalarAccepted_act T g).mpr hT.2)
  unfold recoveringPairAttempt at hg
  split at hg
  · contradiction
  · rename_i o ho
    obtain ⟨u,hu,_⟩ := Option.map_eq_some_iff.mp hg
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp
      (recoverCompiledTrialCRT_covers F FP T S P Q o ho hS (by simp [hu]))
    unfold recoveringPairAttemptCRT
    split
    · rename_i hn
      rw [ho] at hn
      contradiction
    · rename_i o' ho'
      have he := Option.some.inj (ho.symm.trans ho')
      subst o'
      simp [hv]

#print axioms recoveringPairAttemptCRT_sound
#print axioms recoveringPairAttemptCRT_covers


theorem recoveringPairAttemptCRT_refines (D : FieldEncoding K) (F : FieldPresentation K) :
    EvenTI.P15Execution.RecoveryRefines D F (recoveringPairAttemptCRT D F) := by
  constructor
  · intro l n T S P Q g h
    exact recoveringPairAttemptCRT_sound D F T S P Q g h
  · intro l n T S P Q g hs h
    exact recoveringPairAttemptCRT_covers D F T S P Q hs g h

#print axioms recoveringPairAttemptCRT_refines

end EvenTI.P15Recover
