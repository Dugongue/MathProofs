import Mathproof.MinimumGenerationPhysicalGreedyFixedTemplates

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateCompose

open SearchTransducer PhysicalGreedyTemplateProgram

set_option backward.isDefEq.respectTransparency false

variable {W : Nat}

abbrev Memory (W : Nat) := Fin W → Int → Option Bool

def cfg (M : Machine W) (state : Fin M.native.states) (input : Int) (out : List Bool)
    (cells : Memory W) : M.native.Config :=
  ⟨state,input,fun _ => 0,fun i => cells (M.banks i),out⟩

def Run (M : Machine W) (word : List Bool) (B : Nat) (input : Int) (out : List Bool)
    (before after : Memory W) : Prop :=
  ∃ (k : Nat) (q : Fin M.native.states),
    M.native.BoundedSegment word B (cfg M M.native.initialState input out before)
      (cfg M q input out after) k ∧ M.native.step word (cfg M q input out after) = none

theorem configEq {P : SearchTransducer} (a b : P.Config)
    (hq : a.state=b.state) (hi : a.inputHead=b.inputHead) (hh : a.workHead=b.workHead)
    (hc : a.workCell=b.workCell) (ho : a.outputReversed=b.outputReversed) : a=b := by
  cases a
  cases b
  simp_all

private theorem relocatedCfg (M : Machine W) (state : Fin M.native.states)
    (input : Int) (out : List Bool) (cells : Memory W) :
    M.native.bankConfig M.banks (cfg M state input out cells) (fun _ => 0) (fun _ _ => none) =
      ⟨state,input,fun _ => 0,cells,out⟩ := by
  apply configEq
  · rfl
  · rfl
  · funext j
    obtain ⟨i,rfl⟩ := (finCongr M.width).surjective j
    exact M.native.bankConfig_head_image M.banks _ (fun _ => 0) (fun _ _ => none) i
  · funext j
    obtain ⟨i,rfl⟩ := (finCongr M.width).surjective j
    exact M.native.bankConfig_cell_image M.banks _ (fun _ => 0) (fun _ _ => none) i
  · rfl

theorem Run.follow {P Q : Machine W} {word out : List Bool} {B : Nat} {input : Int}
    {x y z : Memory W} (first : Run P word B input out x y) (second : Run Q word B input out y z) :
    Run (P.follow Q) word B input out x z := by
  obtain ⟨a,i,r,h⟩ := first
  obtain ⟨b,j,s,k⟩ := second
  let N := P.follow Q
  let aa := P.native.bankConfig P.banks (cfg P P.native.initialState input out x)
    (fun _ => 0) (fun _ _ => none)
  let ab := P.native.bankConfig P.banks (cfg P i input out y) (fun _ => 0) (fun _ _ => none)
  let ba := Q.native.bankConfig Q.banks (cfg Q Q.native.initialState input out y)
    (fun _ => 0) (fun _ _ => none)
  let bb := Q.native.bankConfig Q.banks (cfg Q j input out z) (fun _ => 0) (fun _ _ => none)
  have ar := P.native.relocateBanks_segment P.banks r (heads := fun _ => 0)
    (cells := fun _ _ => none) (by simp)
  have br := Q.native.relocateBanks_segment Q.banks s (heads := fun _ => 0)
    (cells := fun _ _ => none) (by simp)
  have ah : (P.native.relocateBanks P.banks).step word ab = none := by
    unfold ab
    rw [relocateBanks_step,h]
    rfl
  have bh : (Q.native.relocateBanks Q.banks).step word bb = none := by
    unfold bb
    rw [relocateBanks_step,k]
    rfl
  have connect : thenEntry P.native Q.native P.banks Q.banks ab = ba := by
    unfold ab ba
    rw [relocatedCfg,relocatedCfg]
    rfl
  change (Q.native.relocateBanks Q.banks).BoundedSegment word B ba bb b at br
  rw [← connect] at br
  have both := thenSegment P.native Q.native P.banks Q.banks ar ah br
  have begin : thenLeft P.native Q.native P.banks Q.banks aa = cfg N N.native.initialState input out x := by
    unfold aa
    rw [relocatedCfg]
    rfl
  let sign := Fin.natAdd P.native.states j
  have finish : thenRight P.native Q.native P.banks Q.banks bb = cfg N sign input out z := by
    unfold bb
    rw [relocatedCfg]
    rfl
  rw [begin,finish] at both
  refine ⟨_,sign,both,?_⟩
  rw [← finish]
  change (thenMachine P.native Q.native P.banks Q.banks).step word _ = none
  rw [thenStep_right,bh]
  rfl

def lift (M : SearchTransducer) (e : Fin M.workTapes ↪ Fin W) : Machine W :=
  ⟨M.relocateBanks e,rfl⟩

/-- Lift one checked native subroutine into a shared layout, with different
bank widths allowed and all untouched caller banks preserved. -/
theorem liftRun (M : SearchTransducer) (e : Fin M.workTapes ↪ Fin W)
    {word out : List Bool} {B k : Nat} {input : Int} {before after : Memory W} {c d : M.Config}
    (native : M.BoundedSegment word B c d k) (halt : M.step word d = none)
    (state : c.state = M.initialState)
    (p₀ : c.inputHead=input) (p₁ : d.inputHead=input)
    (h₀ : c.workHead=(fun _ => 0)) (h₁ : d.workHead=(fun _ => 0))
    (o₀ : c.outputReversed=out) (o₁ : d.outputReversed=out)
    (c₀ : ∀ i, c.workCell i = before (e i)) (c₁ : ∀ i, d.workCell i = after (e i))
    (frame : ∀ j ∉ Set.range e, before j = after j) :
    Run (lift M e) word B input out before after := by
  let N := lift M e
  have run := M.relocateBanks_segment e native (heads := fun _ => 0) (cells := before) (by simp)
  have hhalt : (M.relocateBanks e).step word (M.bankConfig e d (fun _ => 0) before) = none := by
    rw [relocateBanks_step,halt]
    rfl
  have exactCfg (x : M.Config) (q : Fin M.states) (dst : Memory W)
      (st : x.state=q) (p : x.inputHead=input) (h : x.workHead=(fun _ => 0))
      (o : x.outputReversed=out) (data : ∀ i, x.workCell i = dst (e i))
      (frame : ∀ j ∉ Set.range e, before j=dst j) :
      M.bankConfig e x (fun _ => 0) before = cfg N q input out dst := by
    apply configEq
    · exact st
    · exact p
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hj
        exact (M.bankConfig_head_image e x (fun _ => 0) before i).trans (congrFun h i)
      · exact (M.bankConfig_frame e x (fun _ => 0) before hj).1
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hj
        exact (M.bankConfig_cell_image e x (fun _ => 0) before i).trans (data i)
      · exact (M.bankConfig_frame e x (fun _ => 0) before hj).2.trans (frame j hj)
    · exact o
  have begin := exactCfg c M.initialState before state p₀ h₀ o₀ c₀ (fun _ _ => rfl)
  have finish := exactCfg d d.state after rfl p₁ h₁ o₁ c₁ frame
  rw [begin,finish] at run
  rw [finish] at hhalt
  exact ⟨_,d.state,run,hhalt⟩

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateCompose
