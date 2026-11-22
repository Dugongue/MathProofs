import EvenP15TrialFrame
import EvenP15Totalizer

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P15Trial

open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding Lax51.TuringPolytime
open Mathproof.Problem18IMPPartialCompiler20261001 (ramPolytimeOn_of_bounded_imp)
open Mathproof.Problem18P34Machine20261002Layout (layout layout_ok)
open Polynomial

def trialBinaryProgram : Com :=
  .seq (.read "length") <|
    .seq inputLoadLoop (.seq trialFrameProgram trialCartesian)

def serializedTrialRequests (x : List ℕ) : List ℕ :=
  let p := unpairW x
  let q := unpairW p.2
  requestWords p.1 (unlistW q.1) (unlistW q.2)

@[simp] theorem serializedTrialRequests_input (raw : List ℕ) (xs ys : List (List ℕ)) :
    serializedTrialRequests (trialInputFrame raw xs ys) = requestWords raw xs ys := by
  simp [serializedTrialRequests,trialInputFrame]

theorem trialBinaryProgram_run (raw : List ℕ) (xs ys : List (List ℕ)) {B : ℕ}
    (hB : 2 < B) (hLen : (trialInputFrame raw xs ys).length+1 < B)
    (hWords : ∀ v ∈ trialInputFrame raw xs ys, v+1 < B) :
    let z := trialInputFrame raw xs ys
    ∃ τ, Run B trialBinaryProgram (initEnv (fun _ => z.length+1) (z.length::z)) τ
      (13*z.length+106+trialCartesianBound z xs ys) ∧
      τ.out=requestWords raw xs ys := by
  let z := trialInputFrame raw xs ys
  let s := initEnv (fun _ => z.length+1) (z.length::z)
  let s₁ := {s.setVar "length" z.length with inp := z}
  have r₀ : Run B (.read "length") s s₁ 1 := Run.read rfl
  have hLen' : z.length+1 < B := hLen
  have hWords' : ∀ v∈z, v < B := fun v hv => (Nat.lt_succ_self v).trans (hWords v hv)
  obtain ⟨ρ,r₁,hl,hb,ho,_⟩ := inputLoad_run z (σ := s₁) (by simp [s₁])
    (by simp [s₁,s,initEnv]) rfl (by simp [s₁,s,initEnv,inputBuffer_zero])
    (by omega) (by omega) hWords'
  obtain ⟨η,a,A,b,C,j,J,r₂,hData,_,hOut,hCtx,hS,hE,hRaw,hXs,hYs,hBounds,hTarget⟩ :=
    trialFrameProgram_run raw xs ys hLen hB hWords' (hb.trans (inputBuffer_full z)) hl
  obtain ⟨τ,r₃,out,_,_⟩ := trialCartesian_run z xs ys hCtx hS hE hXs hBounds hYs hTarget
    hLen hB hWords hData
  have hR : Run B trialBinaryProgram s τ (1+((13*z.length+5)+(100+trialCartesianBound z xs ys))) :=
    r₀.seq (r₁.seq (r₂.seq r₃))
  have hC : 1+((13*z.length+5)+(100+trialCartesianBound z xs ys)) =
      13*z.length+106+trialCartesianBound z xs ys := by omega
  refine ⟨τ,?_,?_⟩
  · change Run B trialBinaryProgram s τ (13*z.length+106+trialCartesianBound z xs ys)
    rw [← hC]
    exact hR
  · rw [out,hRaw,hOut,ho] <;> rfl

private theorem blockCount_le (xs : List (List ℕ)) : xs.length ≤ (xs.flatMap blockW).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons,List.flatMap_cons,List.length_append,blockW] at *
    omega

theorem trialCartesianBound_le (raw : List ℕ) (xs ys : List (List ℕ)) (L : ℕ)
    (h : (trialInputFrame raw xs ys).length ≤ L) :
    trialCartesianBound (trialInputFrame raw xs ys) xs ys ≤ 
      ((45*L+59)*L+21)*L+6 := by
  let z := trialInputFrame raw xs ys
  have hxx := blockCount_le xs
  have hyy := blockCount_le ys
  have hL : z.length = raw.length + (xs.flatMap blockW).length + (ys.flatMap blockW).length+4 := by
    simp [z,trialInputFrame,pairW,listW] <;> omega
  have hx : xs.length ≤ L := by change z.length ≤ L at h; omega
  have hy : ys.length ≤ L := by change z.length ≤ L at h; omega
  have hR : trialRecordBound z+15 ≤ 45*L+59 := by
    change z.length ≤ L at h
    unfold trialRecordBound
    omega
  have ha := Nat.mul_le_mul hR hy
  have hb : trialTargetBound z ys+15 ≤ (45*L+59)*L+21 := by
    unfold trialTargetBound
    omega
  exact Nat.add_le_add_right (Nat.mul_le_mul hb hx) 6

def serializedTrialShape (x : List ℕ) : Prop :=
  ∃ raw xs ys, x=trialInputFrame raw xs ys

noncomputable def trialWordClock : Polynomial ℕ :=
  ((C 45*X+C 59)*X+C 21)*X+C 13*X+C 112

/-- One unconditional binary implementation of the serializer, with exact
output on every proper nested payload frame. A clock totalizes other tapes. -/
theorem serializedTrialRequests_binary :
    ∃ g, TuringPolytime g ∧ ∀ raw xs ys, g (trialInputFrame raw xs ys)=requestWords raw xs ys := by
  have hp : ∃ g, TuringPolytime g ∧
      ∀ z, serializedTrialShape z → g z=serializedTrialRequests z := by
    apply EvenTI.P15Execution.totalBinary_of_ramOn
    apply ramPolytimeOn_of_bounded_imp serializedTrialShape (layout trialBinaryProgram) trialBinaryProgram
      serializedTrialRequests (C 2) trialWordClock (layout_ok trialBinaryProgram)
    intro z hz
    obtain ⟨raw,xs,ys,rfl⟩ := hz
    let z := trialInputFrame raw xs ys
    let L := bitSize z
    let B := 2^(2+L+1)
    have hs : 2^(L+1) < B := Nat.pow_lt_pow_right (by decide) (by omega)
    have hL : z.length+1 < B :=
      (Nat.succ_le_of_lt (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one z)).trans_lt hs
    have hB : 2 < B := (show 2 < 2^3 by decide).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
    have hW : ∀ v ∈ z, v+1 < B := fun v hv =>
      (Nat.succ_le_of_lt (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hv)).trans_lt hs
    obtain ⟨τ,r,hOut⟩ := trialBinaryProgram_run raw xs ys hB hL hW
    refine ⟨fun _ => z.length+1,τ,?_,by simpa only [serializedTrialRequests_input] using hOut⟩
    simp only [Polynomial.eval_C]
    apply r.mono
    have hlen : z.length ≤ L := Lax51Proofs.Encoding.length_le_bitSize z
    have hclock := trialCartesianBound_le raw xs ys L hlen
    simp only [trialWordClock,eval_add,eval_mul,eval_C,eval_X]
    change 13*z.length+106+trialCartesianBound z xs ys ≤ 
      ((45*L+59)*L+21)*L+13*L+112
    change trialCartesianBound z xs ys ≤ _ at hclock
    omega
  obtain ⟨g,hg,hOn⟩ := hp
  exact ⟨g,hg,fun raw xs ys => (hOn _ ⟨raw,xs,ys,rfl⟩).trans (serializedTrialRequests_input raw xs ys)⟩

#print axioms serializedTrialRequests_binary
end EvenTI.P15Trial
