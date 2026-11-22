import EvenP16RecoverRootChoice
import EvenP8Attempt
import EvenP11PaidSmithVerdict
import EvenP15AlternativeAttempt

namespace EvenTI.P16Recover

open EvenTI.Part8 EvenTI.CellPreparation EvenTI.P15Recover EvenOrdinaryTI.LiveRows EvenOrdinaryTI.LCMProjection
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

private def chooseFrobenius (v : Fin V) (x : (physicalVarField X Y v)ˣ) :
    Option (physicalVarField X Y v)ˣ :=
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  frobeniusRootChoice (VV v).coordinates x

private theorem oldRootSound (v : Fin V) (a b : (physicalVarField X Y v)ˣ)
    (h : chooseRoot X Y enum A B v a=some b) : b^(Fintype.card K-1)=a := by
  letI : Fintype (physicalVarField X Y v) := selectedPrefixFintype X Y (.inl v)
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  exact boundedUnitRoot_sound enum (VV v).coordinates h

private theorem oldRootComplete (v : Fin V) (a : (physicalVarField X Y v)ˣ)
    (h : ∃ b : (physicalVarField X Y v)ˣ, b^(Fintype.card K-1)=a) :
    (chooseRoot X Y enum A B v a).isSome=true := by
  letI : Fintype (physicalVarField X Y v) := selectedPrefixFintype X Y (.inl v)
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  exact boundedUnitRoot_complete enum (VV v).coordinates h

private theorem frobRootSound (v : Fin V) (a b : (physicalVarField X Y v)ˣ)
    (h : chooseFrobenius X Y A B v a=some b) : b^(Fintype.card K-1)=a := by
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  exact frobeniusRootChoice_sound (VV v).coordinates a b h

private theorem frobRootComplete (v : Fin V) (a : (physicalVarField X Y v)ˣ)
    (h : ∃ b : (physicalVarField X Y v)ˣ, b^(Fintype.card K-1)=a) :
    (chooseFrobenius X Y A B v a).isSome=true := by
  letI : DecidableEq (physicalVarField X Y v) := fieldViewDecEq (VV v)
  exact frobeniusRootChoice_complete (VV v).coordinates a h

def recoverFeasiblePrefixFrobenius : Option U :=
  (recoverProjectedPower X Y orig emb enum A B c bank hBank).bind fun powered =>
    finishChoosingRoots X Y orig emb enum RV c (fun v => chooseFrobenius X Y A B v (powered v))

theorem recoverFeasiblePrefixFrobenius_available :
    (recoverFeasiblePrefixFrobenius X Y orig emb enum A B c bank hBank).isSome =
      (recoverFeasibleLivePrefix X Y orig emb enum A B c bank hBank).isSome := by
  rw [← recoverFeasiblePrefixCRT_available X Y orig emb enum A B c bank hBank]
  unfold recoverFeasiblePrefixFrobenius recoverFeasiblePrefixCRT
  cases recoverProjectedPower X Y orig emb enum A B c bank hBank with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    let old := fun v => chooseRoot X Y enum A B v (p v)
    let new := fun v => chooseFrobenius X Y A B v (p v)
    change (finishChoosingRoots X Y orig emb enum RV c new).isSome =
      (finishChoosingRoots X Y orig emb enum RV c old).isSome
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact finishChoosingRoots_covers X Y orig emb enum RV c p new old
        (fun v b => frobRootSound X Y A B v (p v) b)
        (fun v b => oldRootSound X Y enum A B v (p v) b)
        (fun v => oldRootComplete X Y enum A B v (p v))
    · exact finishChoosingRoots_covers X Y orig emb enum RV c p old new
        (fun v b => oldRootSound X Y enum A B v (p v) b)
        (fun v b => frobRootSound X Y A B v (p v) b)
        (fun v => frobRootComplete X Y A B v (p v))
theorem recoverFeasiblePrefixFrobenius_sound {z : U}
    (hz : recoverFeasiblePrefixFrobenius X Y orig emb enum A B c bank hBank = some z) :
    prefixEvaluation X Y orig emb z = physicalRHS Y c := by
  unfold recoverFeasiblePrefixFrobenius at hz
  obtain ⟨_,_,hp⟩ := Option.bind_eq_some_iff.mp hz
  exact finishChoosingRoots_sound X Y orig emb enum RV c _ z hp

noncomputable def recoverLivePrefixFrobenius : Option U :=
  if decideLivePrefix X Y orig emb enum FP A B c bank hBank then
    recoverFeasiblePrefixFrobenius X Y orig emb enum A B c bank hBank else none

theorem recoverLivePrefixFrobenius_available :
    (recoverLivePrefixFrobenius X Y orig emb enum FP A B c bank hBank).isSome =
      (recoverLivePrefix X Y orig emb enum FP A B c bank hBank).isSome := by
  unfold recoverLivePrefixFrobenius recoverLivePrefix
  by_cases hb : decideLivePrefix X Y orig emb enum FP A B c bank hBank = true
  · simp only [if_pos hb]
    exact recoverFeasiblePrefixFrobenius_available X Y orig emb enum A B c bank hBank
  · simp only [if_neg hb]

theorem recoverLivePrefixFrobenius_sound {z : U}
    (hz : recoverLivePrefixFrobenius X Y orig emb enum FP A B c bank hBank = some z) :
    prefixEvaluation X Y orig emb z = physicalRHS Y c := by
  unfold recoverLivePrefixFrobenius at hz
  split at hz
  · exact recoverFeasiblePrefixFrobenius_sound X Y orig emb enum A B c bank hBank hz
  · contradiction

#print axioms recoverLivePrefixFrobenius_available
#print axioms recoverLivePrefixFrobenius_sound

end EvenTI.P16Recover

namespace EvenTI.P16Recover

open scoped BigOperators
open EvenTI.Part8 EvenTI.Action EvenTI.Contract EvenTI.LiveAlgebra
open EvenTI.PrimaryAlignment EvenTI.CellProducer EvenTI.CellPreparation EvenOrdinaryTI.LiveRows
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

set_option maxHeartbeats 4500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  (F : FieldEncoding K) (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
  (h : ∀ p, ModeLayout (m p)) (hw : ∀ p, (m p).n = w.width p)
  [∀ p i, Fact (((m p).blocks.get i).HasFieldModel)]
  (FP : FieldPresentation K) (b : BankedBranch F w m h hw)

local instance recoveryWords (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordTable.Laws (numberedTable (m p) v) := numberedWordLaws (m p) v
local instance recoveryFields (p : Fin w.modeCount) (v : Fin (CodeWidth w m p)) :
    WordFieldCertificate (numberedTable (m p) v) := numberedFieldCertificate (m p) v

local notation "BT" => (branchTables w m)
local notation "BE" => (branchJointOrder w m h)
local notation "AC" => (liveCoordinates BT BE)
local notation "WS" => (SharedField (CodeField w m))

local instance recoveryJointWords : WordTable.Laws (liveJointTable BT) :=
  liveJoint_laws BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)
local instance recoveryReduced : IsReduced (LiveJoint BT) :=
  liveJoint_isReduced BT (branchDecode w m) (fun _ _ => wordDecode_one _)
    (fun _ _ x y => wordDecode_mul _ x y)
local instance recoveryCompact :
    ∀ j : Fin (rawCells F.symm AC).length, CellFieldCertificate AC ((rawCells F.symm AC).get j) :=
  liveCellCertificate BT F.symm BE

local notation "Coef" => (sourceCoefficients w m hw b.left)
local notation "Target" => (targetCoefficients w m hw b.right)
local notation "AF" => (LiveActiveField BT F.symm BE Coef)
local notation "Operand" => (liveOperand BT BE Coef)
local notation "Mode" => (liveMode BT (branchDecode w m) (fun _ _ => wordDecode_one _) (fun _ _ => wordDecode_mul _))
local notation "Key" => (commonKey w.mode (branchIsFree w m))
local notation "Neg" => (fun i _ => w.minus i)
local notation "Link" => (sharedLink (K := K) (CodeField w m) w.mode (branchIsFree w m))
local notation "O" => (joinedOrigin F.symm AC Mode Key Operand)
local notation "N" => (joinedNegative F.symm AC Mode Neg Operand)
local notation "E" => (joinedEmbedding F.symm AC Mode WS Key Link Operand)

local notation "SX" => (NativeSignedSources w m)
local notation "SY" => (NativeSignedTargets F w m h hw b.left)
local notation "ORIG" => (nativeSignedOrigins F w m h hw b.left)
local notation "INC" => (nativeSignedIncidence F w m h hw b.left)
local notation "SRC" => (nativeSignedSourceView w m)
local notation "DST" => (nativeSignedTargetView F w m h hw b.left)
local notation "C" => (nativeSignedRatios F w m h hw b.left b.output)

noncomputable def recoverNativeBranchFrobenius (ho : ActualBankedBranch F w m h hw b) :
    Option (BranchAssignment w m) :=
  (recoverLivePrefixFrobenius SX SY ORIG INC F.symm FP SRC DST C b.output.2
    (nativePrefixBanksExact F w m h hw b.left b.right b.output ho)).map
      (recoverSignedVariables (d := w.sites) WS AF)

theorem recoverNativeBranchFrobenius_available (ho : ActualBankedBranch F w m h hw b) :
    (recoverNativeBranchFrobenius F w m h hw FP b ho).isSome =
      (recoverNativeBranch F w m h hw FP b ho).isSome := by
  simpa only [recoverNativeBranchFrobenius,recoverNativeBranch,Option.isSome_map] using
    recoverLivePrefixFrobenius_available SX SY ORIG INC F.symm FP SRC DST C b.output.2
      (nativePrefixBanksExact F w m h hw b.left b.right b.output ho)

private theorem actual_ratios (ho : ActualBankedBranch F w m h hw b) :
    rawRatios F.symm AC Operand (liveOperand BT BE Target) = some b.output.1 := by
  unfold ActualBankedBranch compileModeBanks compileRawPrefix at ho
  obtain ⟨ratios,hr,hout⟩ := Option.map_eq_some_iff.mp ho
  exact hr.trans (congrArg some (congrArg Prod.fst hout))

theorem recoverNativeBranchFrobenius_sound (ho : ActualBankedBranch F w m h hw b)
    {x : BranchAssignment w m} (hx : recoverNativeBranchFrobenius F w m h hw FP b ho = some x) :
    branchSignedAction w m h Coef x = Target := by
  unfold recoverNativeBranchFrobenius at hx
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp hx
  apply (liveSignedCells_iff BT F.symm BE (branchDecode w m)
    (fun _ _ => wordDecode_one _) (fun _ _ => wordDecode_mul _) WS Key Link Neg Coef Target _).mpr
  refine ⟨b.output.1,actual_ratios F w m h hw b ho,?_⟩
  exact recoverSignedVariables_exact WS AF O E N z b.output.1
    (recoverLivePrefixFrobenius_sound SX SY ORIG INC F.symm FP SRC DST C b.output.2
      (nativePrefixBanksExact F w m h hw b.left b.right b.output ho) hz)

#print axioms recoverNativeBranchFrobenius_available
#print axioms recoverNativeBranchFrobenius_sound

end EvenTI.P16Recover

namespace EvenTI.P16Recover

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

noncomputable def recoverCompiledBranchFrobenius (b : {b // b ∈ out.branches}) :
    Option {g : Changes K ((l+1)+(l+1)) n // act g T = S} :=
  letI := out.models
  (recoverNativeBranchFrobenius F out.words out.modes out.layout out.capacities FP b.val
    (actualCompiledBranch F T S P Q out ho b.val b.property)).bind fun x =>
    recoverOriginalTransporter F T S P Q out ho b.val.left b.val.right x

noncomputable def recoverCompiledTrialFrobenius :
    Option {g : Changes K ((l+1)+(l+1)) n // act g T = S} :=
  out.branches.attach.findSome? (recoverCompiledBranchFrobenius F FP T S P Q out ho)

private theorem recoverCompiledBranchFrobenius_covers (b : {b // b ∈ out.branches})
    (hS : scalarAccepted S)
    (hs : (recoverCompiledBranch F FP T S P Q out ho b).isSome = true) :
    (recoverCompiledBranchFrobenius F FP T S P Q out ho b).isSome = true := by
  letI := out.models
  let hActual := actualCompiledBranch F T S P Q out ho b.val b.property
  let old := recoverNativeBranch F out.words out.modes out.layout out.capacities FP b.val hActual
  let new := recoverNativeBranchFrobenius F out.words out.modes out.layout out.capacities FP b.val hActual
  have hOld : old.isSome = true := by
    unfold recoverCompiledBranch at hs
    change (old.bind _).isSome = true at hs
    cases h : old with
    | none => simp [h] at hs
    | some x => rfl
  have hNew : new.isSome = true := (recoverNativeBranchFrobenius_available F out.words out.modes
    out.layout out.capacities FP b.val hActual).trans hOld
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hNew
  have hAction := recoverNativeBranchFrobenius_sound F out.words out.modes out.layout out.capacities
    FP b.val hActual hx
  obtain ⟨g,hg⟩ := recoverOriginalTransporter_complete F T S P Q out ho b.val.left b.val.right x hS hAction
  unfold recoverCompiledBranchFrobenius
  change (new.bind _).isSome = true
  simp [hx,hg]

theorem recoverCompiledTrialFrobenius_covers (hS : scalarAccepted S)
    (hs : (recoverCompiledTrial F FP T S P Q out ho).isSome = true) :
    (recoverCompiledTrialFrobenius F FP T S P Q out ho).isSome = true := by
  unfold recoverCompiledTrial at hs
  unfold recoverCompiledTrialFrobenius
  rw [List.findSome?_isSome_iff] at hs ⊢
  obtain ⟨b,hb,hOld⟩ := hs
  exact ⟨b,hb,recoverCompiledBranchFrobenius_covers F FP T S P Q out ho b hS hOld⟩

noncomputable def recoveringPairAttemptFrobenius (D : FieldEncoding K) (F : FieldPresentation K) : PairAttempt K :=
  fun T S P Q =>
    match h : compileTrialBanks D T S P Q with
    | none => none
    | some o => (recoverCompiledTrialFrobenius D F T S P Q o h).map Subtype.val

theorem recoveringPairAttemptFrobenius_sound
    (g : Changes K ((l+1)+(l+1)) n) (hg : recoveringPairAttemptFrobenius F FP T S P Q = some g) :
    act g T = S := by
  unfold recoveringPairAttemptFrobenius at hg
  split at hg
  · contradiction
  · obtain ⟨u,_,rfl⟩ := Option.map_eq_some_iff.mp hg
    exact u.property

theorem recoveringPairAttemptFrobenius_covers (hT : sourceAccepted T)
    (g : Changes K ((l+1)+(l+1)) n)
    (hg : recoveringPairAttempt F FP T S P Q = some g) :
    (recoveringPairAttemptFrobenius F FP T S P Q).isSome = true := by
  have hAct := recoveringPairAttempt_sound F FP T S P Q g hg
  have hS : scalarAccepted S := hAct ▸ ((scalarAccepted_act T g).mpr hT.2)
  unfold recoveringPairAttempt at hg
  split at hg
  · contradiction
  · rename_i o ho
    obtain ⟨u,hu,_⟩ := Option.map_eq_some_iff.mp hg
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp
      (recoverCompiledTrialFrobenius_covers F FP T S P Q o ho hS (by simp [hu]))
    unfold recoveringPairAttemptFrobenius
    split
    · rename_i hn
      rw [ho] at hn
      contradiction
    · rename_i o' ho'
      have he := Option.some.inj (ho.symm.trans ho')
      subst o'
      simp [hv]

#print axioms recoveringPairAttemptFrobenius_sound
#print axioms recoveringPairAttemptFrobenius_covers


theorem recoveringPairAttemptFrobenius_refines (D : FieldEncoding K) (F : FieldPresentation K) :
    EvenTI.P15Execution.RecoveryRefines D F (recoveringPairAttemptFrobenius D F) := by
  constructor
  · intro l n T S P Q g h
    exact recoveringPairAttemptFrobenius_sound D F T S P Q g h
  · intro l n T S P Q g hs h
    exact recoveringPairAttemptFrobenius_covers D F T S P Q hs g h

#print axioms recoveringPairAttemptFrobenius_refines

end EvenTI.P16Recover
