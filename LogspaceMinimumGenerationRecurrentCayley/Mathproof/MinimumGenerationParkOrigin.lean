import Mathproof.MinimumGenerationTapeCompose
import Mathlib.Algebra.BigOperators.Fin

namespace Mathproof.MinimumGeneration.ParkOrigin

open Mathproof.Multitape SearchTransducer
open Mathproof.Multitape.Locality (moveOffset)

set_option backward.isDefEq.respectTransparency false

variable (M : SearchTransducer)

/-- An immutable marker on the companion tape identifies the origin. -/
def origin (p : Int) : Option Bool := if p = 0 then some true else none

private abbrev Sides := Fin M.workTapes → Fin 2

private def banks {α : Type} (f g : Fin M.workTapes → α) :
    Fin (M.workTapes + M.workTapes) → α :=
  Sum.elim f g ∘ finSumFinEquiv.symm

@[simp] private theorem banks_left {α : Type} (f g : Fin M.workTapes → α) (i : Fin M.workTapes) :
    banks M f g (Fin.castAdd M.workTapes i) = f i := by
  simp [banks, finSumFinEquiv_symm_apply_castAdd]

@[simp] private theorem banks_right {α : Type} (f g : Fin M.workTapes → α) (i : Fin M.workTapes) :
    banks M f g (Fin.natAdd M.workTapes i) = g i := by
  change Sum.elim f g (finSumFinEquiv.symm (Fin.natAdd M.workTapes i)) = g i
  simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

private def controls : ((Fin 2 × Fin M.states) × Sides M) ≃
    Fin ((2 * M.states) * (2 ^ M.workTapes)) :=
  (Equiv.prodCongr finProdFinEquiv finFunctionFinEquiv).trans finProdFinEquiv

def tag (mode : Fin 2) (q : Fin M.states) (side : Sides M) :
    Fin ((2 * M.states) * (2 ^ M.workTapes)) := controls M ((mode,q),side)

private def advance (mark : Option Bool) (motion : Move) (side : Fin 2) : Fin 2 :=
  if mark = some true then if motion = .left then 1 else 0 else side

private def toward (mark : Option Bool) (side : Fin 2) : Move :=
  if mark = some true then .stay else if side = 1 then .right else .left

/-- Copy head motions to a marked companion tape. After the source halts,
use the marker and a side bit to park each pair without touching its data. -/
def machine : SearchTransducer where
  states := (2 * M.states) * (2 ^ M.workTapes)
  workTapes := M.workTapes + M.workTapes
  initialState := tag M 0 M.initialState (fun _ => 0)
  transition state inp read :=
    let ((mode,q),side) := (controls M).symm state
    let mark := fun i : Fin M.workTapes => read (Fin.natAdd M.workTapes i)
    if mode = 0 then
      match M.transition q inp (fun i => read (Fin.castAdd M.workTapes i)) with
      | none => some (tag M 1 q side, .stay, fun _ => ⟨none,.stay⟩, none)
      | some (nxt, m, act, bit) => some
          (tag M 0 nxt (fun i => advance (mark i) (act i).move (side i)), m,
            banks M act (fun i => ⟨none,(act i).move⟩), bit)
    else
      if ∀ i, mark i = some true then none
      else
        let motion := fun i => (⟨none,toward (mark i) (side i)⟩ : Action (Option Bool))
        some (tag M 1 q side, .stay, banks M motion motion, none)

/-- The companion tracks are read-only, with the same head positions. -/
def lift (mode : Fin 2) (c : M.Config) (side : Sides M) : (machine M).Config :=
  ⟨tag M mode c.state side, c.inputHead, banks M c.workHead c.workHead,
    banks M c.workCell (fun _ => origin), c.outputReversed⟩

def valid (c : M.Config) (side : Sides M) : Prop :=
  ∀ i, c.workHead i ≠ 0 → (side i = 1 ↔ c.workHead i < 0)

@[simp] private theorem control_tag (mode : Fin 2) (q : Fin M.states) (side : Sides M) :
    (controls M).symm (tag M mode q side) = ((mode,q),side) :=
  Equiv.symm_apply_apply _ _

@[simp] private theorem origin_true (p : Int) : origin p = some true ↔ p = 0 := by
  by_cases h : p = 0 <;> simp [origin,h]

private theorem nextSide (p : Int) (side : Fin 2) (m : Move)
    (good : p ≠ 0 → (side = 1 ↔ p < 0))
    (away : p + moveOffset m ≠ 0) :
    advance (origin p) m side = 1 ↔ p + moveOffset m < 0 := by
  by_cases h : p = 0
  · subst p
    cases m <;> simp [advance,origin,moveOffset]
  · rw [advance, if_neg (fun e => h ((origin_true p).mp e)), good h]
    cases m <;> simp only [moveOffset] at away ⊢ <;> omega

private theorem bank_ext {P : SearchTransducer} (c d : P.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead) (h : c.workHead = d.workHead)
    (t : c.workCell = d.workCell) (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem liftedBound {word : List Bool} {B : Nat} {c : M.Config} {side : Sides M}
    (mode : Fin 2) (bound : M.Bounded word B c) :
    (machine M).Bounded word B (lift M mode c side) := by
  refine ⟨bound.1, bound.2.1, ?_⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (banks M c.workHead c.workHead (Fin.castAdd _ j)).natAbs ≤ B
    simpa only [banks_left] using bound.2.2 j
  · change (banks M c.workHead c.workHead (Fin.natAdd _ j)).natAbs ≤ B
    simpa only [banks_right] using bound.2.2 j

private theorem sourceStep {word : List Bool} {c d : M.Config} {side : Sides M}
    (good : valid M c side) (h : M.step word c = some d) :
    ∃ side', valid M d side' ∧
      (machine M).step word (lift M 0 c side) = some (lift M 0 d side') := by
  unfold SearchTransducer.step at h
  cases step : M.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => simp [step] at h
  | some r =>
    obtain ⟨q,m,act,bit⟩ := r
    simp only [step, Option.map_some, Option.some.injEq] at h
    subst d
    let side' : Sides M := fun i => advance (origin (c.workHead i)) (act i).move (side i)
    refine ⟨side', fun i hi => nextSide _ _ _ (good i) hi, ?_⟩
    simp only [SearchTransducer.step, machine, lift, control_tag, banks_left, banks_right, if_true, step,
      Option.map_some, Option.some.injEq]
    apply bank_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [banks_left,banks_right]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [banks_left,banks_right, Option.getD_none, ite_self]
    · rfl

private theorem switch {word : List Bool} {c : M.Config} {side : Sides M}
    (halt : M.step word c = none) :
    (machine M).step word (lift M 0 c side) = some (lift M 1 c side) := by
  unfold SearchTransducer.step at halt
  have stop := Option.map_eq_none_iff.mp halt
  simp only [SearchTransducer.step, machine, lift, control_tag, banks_left, banks_right, if_true, stop,
    Option.map_some, Option.some.injEq, moveOffset, Int.add_zero, Option.getD_none, ite_self]
  rfl

private def parkNext (c : M.Config) (side : Sides M) : M.Config :=
  { c with workHead := fun i => c.workHead i + moveOffset (toward (origin (c.workHead i)) (side i)) }

private theorem parkStep {word : List Bool} {c : M.Config} {side : Sides M}
    (notDone : ¬ ∀ i, c.workHead i = 0) :
    (machine M).step word (lift M 1 c side) = some (lift M 1 (parkNext M c side) side) := by
  have h : ¬ ∀ i, origin (c.workHead i) = some true := by simpa only [origin_true] using notDone
  simp only [SearchTransducer.step, machine, lift, control_tag, banks_right,
    if_neg (show (1 : Fin 2) ≠ 0 by decide), if_neg h, Option.map_some, Option.some.injEq,
    show moveOffset .stay = 0 from rfl, Int.add_zero]
  apply bank_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [banks_left,banks_right,parkNext]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [banks_left,banks_right,parkNext,Option.getD_none,ite_self]
  · rfl

private theorem parkHalt {word : List Bool} {c : M.Config} {side : Sides M}
    (done : ∀ i, c.workHead i = 0) :
    (machine M).step word (lift M 1 c side) = none := by
  have h : ∀ i, origin (c.workHead i) = some true := by simpa only [origin_true] using done
  simp only [SearchTransducer.step, machine, lift, control_tag, banks_right,
    if_neg (show (1 : Fin 2) ≠ 0 by decide), if_pos h, Option.map_none]

private theorem toward_sign (p : Int) (side : Fin 2)
    (h : p ≠ 0 → (side = 1 ↔ p < 0)) :
    moveOffset (toward (origin p) side) = if p = 0 then 0 else if p < 0 then 1 else -1 := by
  by_cases z : p = 0
  · simp [z, origin, toward, moveOffset]
  · rw [toward, if_neg (fun e => z ((origin_true p).mp e)), if_neg z]
    by_cases neg : p < 0
    · rw [if_pos neg, if_pos ((h z).mpr neg)]
      rfl
    · rw [if_neg neg, if_neg (fun eq => neg ((h z).mp eq))]
      rfl

private theorem parkValid {c : M.Config} {side : Sides M} (stable : valid M c side) :
    valid M (parkNext M c side) side := by
  intro i away
  change c.workHead i + moveOffset (toward (origin (c.workHead i)) (side i)) ≠ 0 at away
  change side i = 1 ↔ c.workHead i + moveOffset (toward (origin (c.workHead i)) (side i)) < 0
  rw [toward_sign _ _ (stable i)] at away ⊢
  have nz : c.workHead i ≠ 0 := by intro h; simp [h] at away
  simp only [if_neg nz] at away ⊢
  rw [stable i nz]
  by_cases h : c.workHead i < 0 <;> simp [h] at away ⊢ <;> omega

private theorem parkDistance (p : Int) (s : Fin 2) (B : Nat)
    (stable : p ≠ 0 → (s = 1 ↔ p < 0)) (bound : p.natAbs ≤ B+1) :
    (p + moveOffset (toward (origin p) s)).natAbs ≤ B := by
  rw [toward_sign _ _ stable]
  by_cases z : p = 0
  · simp [z]
  · rw [if_neg z]
    by_cases h : p < 0
    · rw [if_pos h]
      have h₁ := Int.ofNat_natAbs_of_nonpos (show p ≤ 0 by omega)
      have h₂ := Int.ofNat_natAbs_of_nonpos (show p + 1 ≤ 0 by omega)
      omega
    · rw [if_neg h]
      have h₁ := Int.natAbs_of_nonneg (show 0 ≤ p by omega)
      have h₂ := Int.natAbs_of_nonneg (show 0 ≤ p + -1 by omega)
      omega

private theorem single {P : SearchTransducer} {word : List Bool} {B : Nat}
    {c d : P.Config} (move : P.step word c = some d)
    (left : P.Bounded word B c) (right : P.Bounded word B d) :
    P.BoundedSegment word B c d 1 := by
  refine ⟨move, ?_⟩
  intro j hj q hq
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact (Option.some.inj hq) ▸ left
  · change P.step word c = some q at hq
    rw [move] at hq
    exact (Option.some.inj hq) ▸ right

private theorem empty {P : SearchTransducer} {word : List Bool} {B : Nat} {c : P.Config}
    (bound : P.Bounded word B c) : P.BoundedSegment word B c c 0 := by
  refine ⟨rfl, ?_⟩
  intro j hj q hq
  have : j = 0 := by omega
  subst j
  exact (Option.some.inj hq) ▸ bound

def parked (c : M.Config) : M.Config := {c with workHead := fun _ => 0}

@[simp] theorem output_parked (c : M.Config) : (parked M c).outputReversed = c.outputReversed := rfl

@[simp] theorem cells_parked (c : M.Config) : (parked M c).workCell = c.workCell := rfl

@[simp] theorem input_parked (c : M.Config) : (parked M c).inputHead = c.inputHead := rfl

@[simp] theorem control_parked (c : M.Config) : (parked M c).state = c.state := rfl

@[simp] theorem heads_lift_parked (c : M.Config) (mode : Fin 2) (side : Sides M) :
    (lift M mode (parked M c) side).workHead = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change banks M (fun _ => (0 : Int)) (fun _ => 0) (Fin.castAdd M.workTapes j) = 0
    exact banks_left M _ _ j
  · change banks M (fun _ => (0 : Int)) (fun _ => 0) (Fin.natAdd M.workTapes j) = 0
    exact banks_right M _ _ j

private theorem parked_eq {c : M.Config} (h : ∀ i, c.workHead i = 0) :
    parked M c = c := by
  apply bank_ext
  · rfl
  · rfl
  · exact (funext h).symm
  · rfl
  · rfl

private theorem parkRun {word : List Bool} {B : Nat} (fuel : Nat)
    (cap : fuel ≤ B) (c : M.Config) (side : Sides M) (good : valid M c side)
    (lower : (-1 : Int) ≤ c.inputHead) (upper : c.inputHead ≤ (word.length : Int))
    (bound : ∀ i, (c.workHead i).natAbs ≤ fuel) :
    ∃ k ≤ fuel, (machine M).BoundedSegment word B (lift M 1 c side)
        (lift M 1 (parked M c) side) k := by
  induction fuel generalizing c with
  | zero =>
    have h (i : Fin M.workTapes) : c.workHead i = 0 :=
      Int.natAbs_eq_zero.mp (Nat.le_zero.mp (bound i))
    rw [parked_eq M h]
    exact ⟨0,le_rfl,empty (liftedBound M 1 ⟨lower,upper,fun i => (bound i).trans cap⟩)⟩
  | succ n ih =>
    by_cases h : ∀ i, c.workHead i = 0
    · rw [parked_eq M h]
      exact ⟨0,Nat.zero_le _,empty (liftedBound M 1 ⟨lower,upper,fun i => (bound i).trans cap⟩)⟩
    · let d := parkNext M c side
      have bound' (i : Fin M.workTapes) : (d.workHead i).natAbs ≤ n :=
        parkDistance _ _ n (good i) (bound i)
      have cap' : n ≤ B := (Nat.le_succ n).trans cap
      obtain ⟨k, hk, tail⟩ := ih cap' d (parkValid M good) lower upper bound'
      have first := single (parkStep M (word := word) (side := side) h)
        (liftedBound M 1 ⟨lower,upper,fun i => (bound i).trans cap⟩)
        (liftedBound M 1 ⟨lower,upper,fun i => (bound' i).trans cap'⟩)
      exact ⟨1+k, by omega, BoundedSegment.append _ first tail⟩

private theorem liftRun {word : List Bool} {B k : Nat} {c d : M.Config} {side : Sides M}
    (run : M.BoundedSegment word B c d k) (good : valid M c side) :
    ∃ side', valid M d side' ∧
      (machine M).BoundedSegment word B (lift M 0 c side) (lift M 0 d side') k := by
  induction k generalizing d with
  | zero =>
    have same : c = d := Option.some.inj run.1
    subst d
    exact ⟨side,good,empty (liftedBound M 0 (run.2 0 le_rfl _ run.1))⟩
  | succ k ih =>
    obtain ⟨m, pre, step⟩ := Option.bind_eq_some_iff.mp run.1
    have prefixRun : M.BoundedSegment word B c m k :=
      ⟨pre, fun i hi q hq => run.2 i (hi.trans (Nat.le_succ _)) q hq⟩
    obtain ⟨sideM, goodM, first⟩ := ih prefixRun
    obtain ⟨sideD, goodD, stepD⟩ := sourceStep M goodM step
    have move := single stepD (liftedBound M 0 (prefixRun.2 k le_rfl _ pre))
      (liftedBound M 0 (run.2 (k+1) le_rfl _ run.1))
    exact ⟨sideD,goodD,BoundedSegment.append _ first move⟩

def resumedState (q : Fin (machine M).states) : Fin M.states := ((controls M).symm q).1.2

@[simp] theorem resumedState_lift (mode : Fin 2) (c : M.Config) (side : Sides M) :
    resumedState M (lift M mode c side).state = c.state := by
  simp [resumedState,lift]

/-- Run the actual source tape program, park every original and shadow head,
and retain its terminal control state, output, and original work cells.
The parking step uses no more space than the source certificate. -/
theorem execute {word : List Bool} {B k : Nat} {c d : M.Config} {side : Sides M}
    (good : valid M c side) (run : M.BoundedSegment word B c d k) (halt : M.step word d = none) :
    ∃ (t : Nat) (side' : Sides M), t ≤ B ∧
      (machine M).BoundedSegment word B (lift M 0 c side) (lift M 1 (parked M d) side') (k+1+t) ∧
      (machine M).step word (lift M 1 (parked M d) side') = none := by
  obtain ⟨side',whereAt,trace⟩ := liftRun M run good
  have hBound := run.2 k le_rfl _ run.1
  have swap := single (switch M (side := side') halt)
    (liftedBound M 0 hBound) (liftedBound M 1 hBound)
  obtain ⟨t,ht,tail⟩ := parkRun M B le_rfl d side' whereAt hBound.1 hBound.2.1 hBound.2.2
  exact ⟨t,side',ht,BoundedSegment.append _ (BoundedSegment.append _ trace swap) tail,
    parkHalt M (fun _ => rfl)⟩

@[simp] theorem originalCell_lift (mode : Fin 2) (c : M.Config) (side : Sides M)
    (i : Fin M.workTapes) :
    (lift M mode c side).workCell (Fin.castAdd M.workTapes i) = c.workCell i :=
  banks_left M _ _ i

@[simp] theorem shadowCell_lift (mode : Fin 2) (c : M.Config) (side : Sides M)
    (i : Fin M.workTapes) :
    (lift M mode c side).workCell (Fin.natAdd M.workTapes i) = origin :=
  banks_right M _ _ i

/-- Initialize the stationary markers with one physical local transition. -/
abbrev markMachine : SearchTransducer where
  states := 2
  workTapes := M.workTapes + M.workTapes
  initialState := 0
  transition q _ _ := if q = 0 then some (1, .stay,
    banks M (fun _ => ⟨none,.stay⟩) (fun _ => ⟨some (some true),.stay⟩), none) else none

def markStart (c : M.Config) : (markMachine M).Config :=
  ⟨0, c.inputHead, banks M c.workHead c.workHead,
    banks M c.workCell (fun _ _ => none), c.outputReversed⟩

def markEnd (c : M.Config) : (markMachine M).Config :=
  ⟨1, c.inputHead, banks M c.workHead c.workHead,
    banks M c.workCell (fun _ => origin), c.outputReversed⟩

theorem markExecute {word : List Bool} {B : Nat} {c : M.Config}
    (atOrigin : ∀ i, c.workHead i = 0) (input : (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ word.length) :
    (markMachine M).BoundedSegment word B (markStart M c) (markEnd M c) 1 ∧
      (markMachine M).step word (markEnd M c) = none := by
  have first : (markMachine M).step word (markStart M c) = some (markEnd M c) := by
    simp only [SearchTransducer.step, markMachine, markStart, markEnd, if_true, Option.map_some,
      Option.some.injEq, moveOffset, Int.add_zero]
    apply bank_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [banks_left,banks_right,Int.add_zero]
    · funext i p
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [banks_left, Option.getD_none, ite_self]
      · simp only [banks_right, atOrigin, Option.getD_some, origin]
    · rfl
  have hd (i : Fin (markMachine M).workTapes) : banks M c.workHead c.workHead i = 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [banks_left] using atOrigin j
    · simpa only [banks_right] using atOrigin j
  refine ⟨single first ⟨input.1,input.2,?_⟩ ⟨input.1,input.2,?_⟩, ?_⟩
  · intro i
    change (banks M c.workHead c.workHead i).natAbs ≤ B
    simp [hd]
  · intro i
    change (banks M c.workHead c.workHead i).natAbs ≤ B
    simp [hd]
  · simp [SearchTransducer.step, markMachine, markEnd]

end Mathproof.MinimumGeneration.ParkOrigin
