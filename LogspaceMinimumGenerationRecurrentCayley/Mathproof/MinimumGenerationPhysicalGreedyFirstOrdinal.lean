import Mathproof.MinimumGenerationPhysicalGreedyOrdinalRequested

namespace Mathproof.MinimumGeneration.PhysicalGreedyFirstOrdinal

open SearchTransducer
open PhysicalGreedyOrdinalSetup (Bank order label ordinal zero prepared)
open PhysicalGreedyHeaderInstall (wordAt)
open PhysicalGreedyTemplateCompose (configEq)
open GreedyTapeScan (BitCall)
open PhysicalGreedyTape (kept)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {N T : Nat} (states : 7 ≤ T) (allowed member : BitCall T (95+N))

private abbrev A := PhysicalGreedyOrdinalSetup.machine N
private abbrev R := PhysicalGreedyOrdinalRequested.machine states allowed member (zero N)
private def idBanks : Bank N ↪ Bank N := Function.Embedding.refl _

abbrev machine := thenMachine (A (N := N)) (R states allowed member) idBanks idBanks

/-- Decode returned success directly from the composite finite control. -/
def returned (d : (machine states allowed member).Config) : Bool :=
  (finSumFinEquiv.symm d.state).elim (fun _ => false) fun q =>
    PhysicalGreedyOrdinalRequested.returned states allowed member (zero N)
      ⟨q,d.inputHead,d.workHead,d.workCell,d.outputReversed⟩

private theorem fullHead (P : SearchTransducer) (c : P.Config)
    (frame : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig (Function.Embedding.refl _) c (fun _ => 0) frame).workHead = c.workHead :=
  funext (fun j => P.bankConfig_head_image (Function.Embedding.refl _) c _ frame j)

private theorem fullCell (P : SearchTransducer) (c : P.Config)
    (frame : Fin P.workTapes → Int → Option Bool) :
    (P.bankConfig (Function.Embedding.refl _) c (fun _ => 0) frame).workCell = c.workCell :=
  funext (fun j => P.bankConfig_cell_image (Function.Embedding.refl _) c (fun _ => 0) frame j)

/-- The raw Cayley input alone supplies generator ordinal zero. Other ordinal
requests use the same compiled replay and the separate live-register installer. -/
theorem execute {n C : Nat} (G : Group (Fin n)) (cap : 17 ≤ C)
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (invariant : (Bank N → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable (label N) invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable (ordinal N) invariant)
    (started : invariant (prepared N n G.toOne.one.val))
    (allow : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member
      (B := C*(Nat.log2 ((@encodeCayley n G.toMul).length+1)+1))
      (@encodeCayley n G.toMul) 1 eligible allowed.answer (kept ∅ (ordinal N) (zero N)) invariant)
    (membership : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member
      (B := C*(Nat.log2 ((@encodeCayley n G.toMul).length+1)+1)) (@encodeCayley n G.toMul)
      2 (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer
      (kept ∅ (ordinal N) (zero N)) invariant) :
    let raw := @encodeCayley n G.toMul
    let B := C*(Nat.log2 (raw.length+1)+1)
    let P := machine states allowed member
    let expected := (GreedyOrdinal.collect (GreedyGenerator.accept query eligible) 0 n)[0]?
    ∃ (ticks : Nat) (d : P.Config),
      P.BoundedSegment raw B P.initial d ticks ∧ P.step raw d = none ∧
      P.logarithmicWorkspace C raw ∧ returned states allowed member d = expected.isSome ∧
      d.workCell (label N) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed=[] ∧ invariant d.workCell ∧
      (∃ i, d.workCell (ordinal N) = wordAt (TableIO.width n) i) ∧
      d.workCell (zero N) = wordAt (TableIO.width n) 0 ∧
      d.workCell (order N) = wordAt (TableIO.width n) n := by
  let raw := @encodeCayley n G.toMul
  let log := Nat.log2 (raw.length+1)+1
  let B := C*log
  let m := prepared N n G.toOne.one.val
  let blank : Bank N → Int → Option Bool := fun _ _ => none
  let S := A (N := N)
  let R' := R states allowed member
  obtain ⟨a,c,r,halt,_,head,output,data⟩ := PhysicalGreedyOrdinalSetup.execute G N
  have rawBound : 17*log ≤ B := Nat.mul_le_mul_right log cap
  have pos := r.2 a le_rfl c r.1
  have widths : TableIO.width n+1 ≤ B := by
    have cap₀ := PhysicalGreedyHeaderDriver.raw_bound G
    exact (show TableIO.width n+1 ≤ PhysicalGreedyHeader.width n+1 by unfold PhysicalGreedyHeader.width; omega).trans
      (cap₀.trans ((Nat.mul_le_mul_right log (by decide : 5 ≤ 17)).trans rawBound))
  have ø := PhysicalGreedyOrdinalSetup.zeroPrepared N n G.toOne.one.val
  obtain ⟨b,e,s,stop,answer,word,hE,outE,inv,idx,z,o,_⟩ :=
    PhysicalGreedyOrdinalRequested.executeWithRegisters states allowed member (prior := []) query eligible
      ∅ invariant stableLabel stableOrdinal (by simp) (by simp) allow membership
      (zero N) m 0 0 (Nat.two_pow_pos _)
      (PhysicalGreedyOrdinalSetup.headInitialized_order N n _)
      (PhysicalGreedyOrdinalSetup.headInitialized_label N n _)
      ø ø ⟨0,PhysicalGreedyOrdinalSetup.ordinalPrepared N n _⟩
      ⟨pos.1,pos.2.1⟩ widths started
  rw [GreedyOrdinal.ordinal_exact] at answer word
  let x := S.bankConfig idBanks c (fun _ => 0) blank
  let y := R'.bankConfig idBanks (PhysicalGreedyOrdinalRequested.entry states allowed member
    (zero N) c.inputHead [] m) (fun _ => 0) blank
  let y' := R'.bankConfig idBanks e (fun _ => 0) blank
  have st := S.relocateBanks_segment idBanks (PhysicalEntry.segment_mono r rawBound)
    (heads := fun _ => 0) (cells := blank) (by simp)
  have stStop : (S.relocateBanks idBanks).step raw x = none := by
    unfold x
    rw [relocateBanks_step,halt]
    rfl
  have rl := R'.relocateBanks_segment idBanks s (heads := fun _ => 0) (cells := blank) (by simp)
  have rlStop : (R'.relocateBanks idBanks).step raw y' = none := by
    unfold y'
    rw [relocateBanks_step,stop]
    rfl
  have next : thenEntry S R' idBanks idBanks x = y := by
    let q := PhysicalGreedyOrdinalRequested.entry states allowed member (zero N) c.inputHead [] m
    have hQ : q.workHead = fun _ => 0 := by
      funext j
      exact (TapeInstall.machine (order N) (PhysicalGreedyOrdinalRequested.installPlan (zero N))).bankConfig_head_image
        (Function.Embedding.refl _) _ (fun _ => 0) m j
    have qMem : q.workCell = m := by
      funext j
      exact (TapeInstall.machine (order N) (PhysicalGreedyOrdinalRequested.installPlan (zero N))).bankConfig_cell_image
        (Function.Embedding.refl _) _ (fun _ => 0) m j
    apply configEq
    · rfl
    · rfl
    · exact ((fullHead S c blank).trans head).trans ((fullHead R' q blank).trans hQ).symm
    · exact ((fullCell S c blank).trans data).trans ((fullCell R' q blank).trans qMem).symm
    · exact output
  change (R'.relocateBanks idBanks).BoundedSegment raw B y y' b at rl
  rw [← next] at rl
  have whole := thenSegment S R' idBanks idBanks st stStop rl
  have initial : (machine states allowed member).initial =
      thenLeft S R' idBanks idBanks (S.bankConfig idBanks S.initial (fun _ => 0) blank) :=
    configEq _ _ rfl rfl (fullHead S S.initial blank).symm (fullCell S S.initial blank).symm rfl
  rw [← initial] at whole
  let d := thenRight S R' idBanks idBanks y'
  have done : (machine states allowed member).step raw d = none := by
    change (machine states allowed member).step raw (thenRight S R' idBanks idBanks y') = none
    rw [thenStep_right,rlStop]
    rfl
  have eq : d.workCell = e.workCell := fullCell R' e blank
  have found : returned states allowed member d =
      PhysicalGreedyOrdinalRequested.returned states allowed member (zero N) e := by
    unfold returned
    rw [show d.state = finSumFinEquiv (Sum.inr e.state) from rfl,Equiv.symm_apply_apply]
    rfl
  refine ⟨_,d,whole,done,(BoundedSegment.logspaceOutput _ whole done).1,found.trans answer,
    (congrFun eq _).trans word,(fullHead R' e blank).trans hE,outE,eq.symm ▸ inv,?_ ,
    (congrFun eq _).trans z,(congrFun eq _).trans o⟩
  obtain ⟨i,remaining⟩ := idx
  exact ⟨i,(congrFun eq _).trans remaining⟩

end Mathproof.MinimumGeneration.PhysicalGreedyFirstOrdinal
