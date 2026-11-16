import Mathproof.MinimumGenerationPhysicalGreedyOrdinalInvariant
import Mathproof.MinimumGenerationPhysicalGreedyRaw
import Mathproof.MinimumGenerationPhysicalGreedyReaderFromRaw

namespace Mathproof.MinimumGeneration.PhysicalGreedyCycleInvariant

open SearchTransducer
open GreedyTapeScan (BitCall Prepared)
open PhysicalGreedyTape (Live found kept)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

variable {W N : Nat}

/-- The reader is ready for its last saved query, and the native Reingold
work window is blank for its next invocation. The cut, target and pointer
are allowed to change between successive calls. -/
def Ready {n : Nat} (G : Group (Fin n)) (ticks : List Bool) (B : Nat)
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W) (m : Fin W → Int → Option Bool) : Prop :=
  (∃ (cut : Nat) (x : Fin n) (pointer : Nat),
    cut ≤ n ∧ pointer ≤ Connectivity.ustconHeaderLength
      (BipartiteCayley.left G.toOne.one) (BipartiteCayley.left x)+(n+n)*(n+n)+1 ∧
    CayleyReaderCycle.Ready G cut (BipartiteCayley.left G.toOne.one)
      (BipartiteCayley.left x) pointer ticks (fun i => m (reader i))) ∧
  ∀ i p, p.natAbs ≤ B → m (native i) p = none

theorem transport {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W)
    {old new : Fin W → Int → Option Bool}
    (readerFrame : ∀ i, new (reader i) = old (reader i))
    (nativeFrame : ∀ i, new (native i) = old (native i))
    (prior : Ready G ticks B reader native old) : Ready G ticks B reader native new := by
  obtain ⟨⟨cut,x,p,small,valid,query⟩,blank⟩ := prior
  have same : (fun i => new (reader i)) = fun i => old (reader i) := funext readerFrame
  refine ⟨⟨cut,x,p,small,valid,?_⟩,?_⟩
  · rwa [same]
  · intro i p hp
    rw [nativeFrame i]
    exact blank i p hp

theorem stable {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W) (bank : Fin W)
    (readerAway : ∀ i, reader i ≠ bank) (nativeAway : ∀ i, native i ≠ bank) :
    GreedyTapeScanInvariant.Stable bank (Ready G ticks B reader native) := by
  intro old new frame prior
  exact transport G ticks reader native (fun i => frame _ (readerAway i))
    (fun i => frame _ (nativeAway i)) prior

/-- Feed the exact query and blank native window left by the native
membership machine into the next iteration's memory invariant. -/
theorem returned {n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W)
    {old new : Fin W → Int → Option Bool} (x : Fin n)
    (prior : Ready G ticks B reader native old)
    (readerReturn : CayleyReaderCycle.Ready G x.val (BipartiteCayley.left G.toOne.one)
      (BipartiteCayley.left x) 1 ticks (fun i => new (reader i)))
    (nativeReturn : ∀ i, new (native i) = old (native i)) :
    Ready G ticks B reader native new := by
  refine ⟨⟨x.val,x,1,x.isLt.le,by omega,readerReturn⟩,?_⟩
  intro i p hp
  rw [nativeReturn i]
  exact prior.2 i p hp

theorem initialized {n B : Nat} (G : Group (Fin n))
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W) (m : Fin W → Int → Option Bool)
    (readerInit : ∀ i, m (reader i) = PhysicalGreedyReaderSetup.outputData n G.toOne.one.val
      (PhysicalGreedyReaderSetup.reader i))
    (nativeInit : ∀ i p, p.natAbs ≤ B → m (native i) p = none) :
    Ready G (CayleyReaderClock.bits n) B reader native m := by
  refine ⟨⟨0,PhysicalGreedyReaderSetup.initialLabel G,1,Nat.zero_le _,by omega,?_⟩,nativeInit⟩
  rw [show (fun i => m (reader i)) = _ from funext readerInit]
  exact PhysicalGreedyReaderSetup.ready G

/-- The constant-eligible leaf is the stationary physical branch and always
preserves any invariant on its live workspace. -/
theorem allowAll {S : Nat} (label order : Fin W) (widthStates : 7 ≤ S)
    (member : BitCall S W) {n B : Nat} {word : List Bool}
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop) :
    GreedyTapeScanInvariant.Leaf label order widthStates (PhysicalGreedyRaw.allowAll widthStates)
      member (n := n) (B := B) word 1 (fun _ => true)
      (PhysicalGreedyRaw.allowAll (W := W) widthStates).answer keep invariant := by
  intro x c _ prepared h
  refine ⟨0,c,⟨rfl,?_⟩,rfl,rfl,prepared,rfl,h,fun _ _ => rfl⟩
  intro t ht d hd
  have ht0 : t = 0 := by omega
  subst t
  change some c = some d at hd
  cases hd
  exact ⟨prepared.inputLo,prepared.inputHi,by simp [prepared.heads]⟩

/-- Ordinal replay with the changing recurrent Cayley reader invariant.
The one actual subgroup-membership leaf supplies the only query decision. -/
theorem executeOrdinal {S n B : Nat} (G : Group (Fin n)) (ticks : List Bool)
    (reader : Fin 74 → Fin W) (native : Fin N → Fin W)
    (label order ordinal zero : Fin W) (widthStates : 7 ≤ S) (member : BitCall S W)
    (keep : Set (Fin W)) (hl : label ∉ keep ∧ label ≠ ordinal ∧ label ≠ zero)
    (ho : ordinal ∉ keep) (hlo : label ≠ order) (hoo : ordinal ≠ order) (hoz : ordinal ≠ zero)
    (readerLabel : ∀ i, reader i ≠ label) (nativeLabel : ∀ i, native i ≠ label)
    (readerOrdinal : ∀ i, reader i ≠ ordinal) (nativeOrdinal : ∀ i, native i ≠ ordinal)
    (bound : TableIO.width n + 1 ≤ B)
    (membership : GreedyTapeScanInvariant.Leaf label order widthStates
      (PhysicalGreedyRaw.allowAll widthStates) member (B := B) (@encodeCayley n G.toMul) 2
      (fun x => RawGreedyMembership.query (@encodeCayley n G.toMul) G.toOne.one
        (GreedyGenerator.before (fun _ => true) x.val) x)
      member.answer (kept keep ordinal zero) (Ready G ticks B reader native))
    (k i : Nat) (hi : i < 2^(TableIO.width n)) :
    let word := @encodeCayley n G.toMul
    let T := PhysicalGreedyTape.stages label order ordinal zero widthStates
      (PhysicalGreedyRaw.allowAll widthStates) member
    let accepted := GreedyGenerator.accept (RawGreedyMembership.query word G.toOne.one) (fun _ => true)
    let expected := (GreedyOrdinal.collect accepted 0 n)[i]?
    ∀ (c : (T.component 4).Config), c.state = T.entry 4 →
      Live (M := T.component 4) word n k i label order ordinal zero c →
      Ready G ticks B reader native c.workCell →
      ∃ (len : Nat) (d : T.machine.Config), T.machine.BoundedSegment word B (T.tag 4 c) d len ∧
        T.machine.step word d = none ∧
        found (label := label) (order := order) (ordinal := ordinal) (zero := zero)
          (widthStates := widthStates) (allowed := PhysicalGreedyRaw.allowAll widthStates)
          (member := member) d = expected.isSome ∧
        d.workCell label = work (encodeLabel (TableIO.width n) (expected.elim n Fin.val)) ∧
        d.workHead = (fun _ => 0) ∧ d.outputReversed = c.outputReversed ∧
        Ready G ticks B reader native d.workCell ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  dsimp only
  intro c entry live ready
  have physical := PhysicalGreedyOrdinalInvariant.execute (label := label) (order := order)
    (ordinal := ordinal) (zero := zero) (widthStates := widthStates)
    (allowed := PhysicalGreedyRaw.allowAll widthStates) (member := member)
    (RawGreedyMembership.query (@encodeCayley n G.toMul) G.toOne.one) (fun _ => true)
    keep (Ready G ticks B reader native)
    (stable G ticks reader native label readerLabel nativeLabel)
    (stable G ticks reader native ordinal readerOrdinal nativeOrdinal)
    hl ho hlo hoo hoz bound (allowAll label order widthStates member _ _) membership k i hi c entry live ready
  simpa only [GreedyOrdinal.ordinal_exact] using physical

end Mathproof.MinimumGeneration.PhysicalGreedyCycleInvariant
