import EvenP18RawReciprocal
import EvenP18RawRecipWord
import EvenP18ReciprocalCost
import EvenP15Totalizer

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep EvenTI.P12Compare EvenTI.P10Scan
open EvenTI.P15Execution EvenTI.P16Execution EvenTI.P17Execution
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34Machine20261002Layout
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax51.TuringPolytime
open Lax51.BinaryWordEncoding Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem rawReciprocalTrial_originalBits (D : FieldEncoding K) (F : FieldPresentation K) (target : Bool) :
    ∃ p : Polynomial ℕ,
      ∀ {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n), 2 ≤ n →
        let w := comparisonInput D T U
        rawReciprocalTrialCost F target l n w.length ≤ p.eval (bitSize w) := by
  obtain ⟨p,hp⟩ := produceReciprocalTrial_originalBits D F
  refine ⟨p+C (74+3*F.e+reciprocalRawSetupCost target)+
    C (44+encodedBankLoadStepCost F contiguousAddress)*X,?_⟩
  intro l n T U hn
  dsimp only
  let w := comparisonInput D T U
  let L := bitSize w
  have hLen : w.length ≤ L := Lax51Proofs.Encoding.length_le_bitSize w
  have hSize : w.length=2+n^((l+1)+(l+1))+n^((l+1)+(l+1)) := by
    simp [w,comparisonInput,tensorWords_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
  have hArea : n^((l+1)+(l+1)) ≤ L := by omega
  have hLoad := Nat.mul_le_mul_left (encodedBankLoadStepCost F contiguousAddress+4) hArea
  have hRun := hp T U hn
  simp only [rawReciprocalTrialCost,encodedBankLoadCost,eval_add,eval_mul,eval_C,eval_X]
  change (40*(w.length+1)+3*F.e+25)+(reciprocalRawSetupCost target+
    (((encodedBankLoadStepCost F contiguousAddress+4)*n^((l+1)+(l+1))+6)+
      (3+produceReciprocalTrialCost F l n))) ≤
    p.eval L+(74+3*F.e+reciprocalRawSetupCost target)+(44+encodedBankLoadStepCost F contiguousAddress)*L
  have hScale : (encodedBankLoadStepCost F contiguousAddress+4)*L+40*L =
      (44+encodedBankLoadStepCost F contiguousAddress)*L := by ring
  change produceReciprocalTrialCost F l n ≤ p.eval L at hRun
  omega

private def reciprocalValid (D : FieldEncoding K) (target : Bool) (w : List ℕ) : Prop :=
  ∃ (l n : ℕ) (T U : Tensor K ((l+1)+(l+1)) n),
    1≤l ∧ 2≤n ∧ IsUnit (flatten (if target then U else T)) ∧ w=comparisonInput D T U

private noncomputable def reciprocalExtension (F : FieldPresentation K) (w : List ℕ) : String → ℕ :=
  comparisonInitExt F (reciprocalRawSlots ((w[1]?.getD 0)^((w.headD 0)/2))) w.length (fun _ => 0)

private theorem reciprocalExtension_eq (D : FieldEncoding K) (F : FieldPresentation K) {l n : ℕ}
    (T U : Tensor K ((l+1)+(l+1)) n) :
    reciprocalExtension F (comparisonInput D T U) =
      comparisonInitExt F (reciprocalRawSlots (n*n^l)) (comparisonInput D T U).length (fun _ => 0) := by
  simp [reciprocalExtension,comparisonInput,show ((l+1)+(l+1))/2=l+1 by omega,pow_succ']

private def rawReciprocalRun (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) (p : Polynomial ℕ) (w : List ℕ) (t : Env) : Prop :=
  Run (2^((rawReciprocalWordExponent F).eval (bitSize w)+bitSize w+1)) (rawReciprocalTrialProgram D F target)
    (initEnv (reciprocalExtension F w) (w.length::w)) t (p.eval (bitSize w))

private noncomputable def rawReciprocalReference (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) (p : Polynomial ℕ) (w : List ℕ) : List ℕ := by
  classical
  exact if h : ∃ t, rawReciprocalRun D F target p w t then h.choose.out else []
#print axioms rawReciprocalTrial_originalBits
private theorem rawReciprocalReference_eq {D : FieldEncoding K} {F : FieldPresentation K}
    {target : Bool} {p : Polynomial ℕ} {w : List ℕ} {t : Env} (h : rawReciprocalRun D F target p w t) :
    rawReciprocalReference D F target p w=t.out := by
  classical
  have ex : ∃ t, rawReciprocalRun D F target p w t := ⟨t,h⟩
  unfold rawReciprocalReference
  rw [dif_pos ex]
  obtain ⟨_,_,h₁⟩ := Run.bigStep (Classical.choose_spec ex)
  obtain ⟨_,_,h₂⟩ := Run.bigStep h
  exact congrArg Env.out (BigStep.unique h₁ h₂).1

open Mathproof.Problem18IMPPartialCompiler20261001 (ramPolytimeOn_of_bounded_imp)

/-- A total polynomial-time program computes the exact full reciprocal record
on every original raw input with a nonsingular selected cut. -/
theorem rawReciprocalTrial_binary (D : FieldEncoding K) (F : FieldPresentation K) (target : Bool) :
    ∃ g, TuringPolytime g ∧
      ∀ {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n), 1≤l → 2≤n →
        let V := if target then U else T
        IsUnit (flatten V) →
        g (comparisonInput D T U)=preparedTrialWords D (.reciprocal (rawReciprocalAnchor V (flatten V)⁻¹)) := by
  obtain ⟨p,hp⟩ := rawReciprocalTrial_originalBits D F target
  let c := rawReciprocalTrialProgram D F target
  have ready {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n) (hl : 1≤l) (hn : 2≤n)
      (h : IsUnit (flatten (if target then U else T))) :
      let V := if target then U else T
      ∃ t, rawReciprocalRun D F target p (comparisonInput D T U) t ∧
        t.out=preparedTrialWords D (.reciprocal (rawReciprocalAnchor V (flatten V)⁻¹)) := by
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂⟩ := rawReciprocalWord_bounds D F T U hl hn
    obtain ⟨t,r,_,ho⟩ := rawReciprocalTrialProgram_run D F T U target (fun _ => 0) hl hn h
      h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
    refine ⟨t,?_,ho⟩
    unfold rawReciprocalRun
    rw [reciprocalExtension_eq D F T U]
    exact r.mono (hp T U hn)
  obtain ⟨g,hg,he⟩ := totalBinary_of_ramOn
    (ramPolytimeOn_of_bounded_imp (reciprocalValid D target) (layout c) c
      (rawReciprocalReference D F target p) (rawReciprocalWordExponent F) p (layout_ok c) (by
    intro w hw
    obtain ⟨l,n,T,U,hl,hn,h,rfl⟩ := hw
    obtain ⟨t,hr,_⟩ := ready T U hl hn h
    exact ⟨reciprocalExtension F _,t,hr,(rawReciprocalReference_eq hr).symm⟩))
  refine ⟨g,hg,?_⟩
  intro l n T U hl hn V h
  obtain ⟨t,hr,ho⟩ := ready T U hl hn h
  exact (he _ ⟨l,n,T,U,hl,hn,h,rfl⟩).trans ((rawReciprocalReference_eq hr).trans ho)

#print axioms rawReciprocalTrial_binary
end EvenTI.P18Execution






