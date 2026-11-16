import Mathproof.MinimumGenerationPhysicalGreedyOrdinalSetup

namespace Mathproof.MinimumGeneration.PhysicalGreedyOrdinalRequested

open SearchTransducer
open PhysicalGreedyOrdinalSetup (Bank label order ordinal zero)
open PhysicalGreedyHeaderInstall (wordAt outside_word)
open PhysicalGreedyTemplateCompose (configEq)
open PhysicalGreedyReaderInstall (copied)
open GreedyTapeScan (BitCall Prepared)
open PhysicalGreedyTape (Live found kept)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {N : Nat}

def installPlan (source : Bank N) (j : Bank N) : Option (Bank N) :=
  if j = ordinal N then some source else none

abbrev installer (source : Bank N) := TapeInstall.machine (order N) (installPlan source)

def memory (source : Bank N) (m : Bank N → Int → Option Bool) : Bank N → Int → Option Bool :=
  copied (installPlan source) m

private def identity {W : Nat} : Fin W ↪ Fin W := Function.Embedding.refl _

private theorem at_value (source : Bank N) (m : Bank N → Int → Option Bool) :
    memory source m (ordinal N) = m source := by
  simp [memory,copied,installPlan]

theorem away (source : Bank N) (m : Bank N → Int → Option Bool) (j : Bank N)
    (different : j ≠ ordinal N) :
    memory source m j = m j := by simp [memory,copied,installPlan,different]

/-- Install any requested ordinal from a live caller's raw-width register.
This copy is stationary on the real input and preserves all other tape
contents, including the changing reader state. -/
theorem install (source : Bank N) {n i B : Nat} {raw prior : List Bool} {p : Int}
    (m : Bank N → Int → Option Bool)
    (orderWord : m (order N) = wordAt (TableIO.width n) n)
    (requestWord : m source = wordAt (TableIO.width n) i)
    (oldWord : ∃ j, m (ordinal N) = wordAt (TableIO.width n) j)
    (legal : (-1 : Int) ≤ p ∧ p ≤ raw.length) (fit : TableIO.width n+1 ≤ B) :
    ∃ (k : Nat) (d : (installer source).Config),
      (installer source).BoundedSegment raw B (TapeInstall.start (order N) (installPlan source) p m prior) d k ∧
      (installer source).step raw d = none ∧ d.inputHead = p ∧ d.workHead = (fun _ => 0) ∧
      d.outputReversed = prior ∧ d.workCell = memory source m ∧
      d.workCell (ordinal N) = wordAt (TableIO.width n) i := by
  have different : order N ≠ ordinal N := fun h => by
    have z := congrArg Fin.val h
    change 74=93 at z
    omega
  let w := TableIO.width n
  obtain ⟨run,stop⟩ := TapeInstall.execute (order N) (installPlan source) (if_neg different)
    raw (encodeLabel w n) prior p m orderWord legal
  rw [length_encodeLabel] at run stop
  have installed : TapeInstall.installed (installPlan source) m w = memory source m := by
    funext j
    by_cases h : j=ordinal N
    · subst j
      obtain ⟨old,oldExact⟩ := oldWord
      rw [TapeInstall.installed_exact _ _ _ _ _ (if_pos rfl)]
      · exact (at_value source m).symm
      · intro p hp
        rw [oldExact,requestWord]
        exact (outside_word w old p hp).trans (outside_word w i p hp).symm
    · rw [TapeInstall.installed_source _ _ _ _ (if_neg h),away source m _ h]
  let result := TapeInstall.stop (order N) (installPlan source) p m prior w
  exact ⟨_,result,PhysicalEntry.segment_mono run fit,stop,rfl,rfl,rfl,installed,
    (congrFun installed (ordinal N)).trans ((at_value source m).trans requestWord)⟩

variable {S : Nat} (states : 7 ≤ S) (allowed member : BitCall S (95+N))

abbrev replayStages := PhysicalGreedyTape.stages (label N) (order N) (ordinal N) (zero N)
  states allowed member

abbrev machine (source : Bank N) :=
  thenMachine (installer source) (replayStages states allowed member).machine identity identity

def returned (source : Bank N) (d : (machine states allowed member source).Config) : Bool :=
  (finSumFinEquiv.symm d.state).elim (fun _ => false)
    (fun q => decide ((finProdFinEquiv.symm q).1 = (1 : Fin 5)))

def entry (source : Bank N) (p : Int) (prior : List Bool) (m : Bank N → Int → Option Bool) :
    (machine states allowed member source).Config :=
  thenLeft (installer source) (replayStages states allowed member).machine identity identity
    ((installer source).bankConfig identity
      (TapeInstall.start (order N) (installPlan source) p m prior) (fun _ => 0) m)

private theorem identityHead (M : SearchTransducer) (c : M.Config)
    (m : Fin M.workTapes → Int → Option Bool) :
    (M.bankConfig identity c (fun _ => 0) m).workHead = c.workHead := by
  funext j
  exact M.bankConfig_head_image identity c _ _ j

private theorem identityCell (M : SearchTransducer) (c : M.Config)
    (m : Fin M.workTapes → Int → Option Bool) :
    (M.bankConfig identity c (fun _ => 0) m).workCell = c.workCell := by
  funext j
  exact M.bankConfig_cell_image identity c _ _ j

/-- One actual physical execution installs the requested ordinal and runs
the invariant-preserving replay through its exact membership leaf. -/
theorem executeWithRegisters {n B : Nat} {raw prior : List Bool} {p : Int}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Bank N)) (invariant : (Bank N → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable (label N) invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable (ordinal N) invariant)
    (labelOutside : label N ∉ keep) (ordinalOutside : ordinal N ∉ keep)
    (eligibleRun : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member (B := B)
      raw 1 eligible allowed.answer (kept keep (ordinal N) (zero N)) invariant)
    (memberRun : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member (B := B)
      raw 2 (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer
      (kept keep (ordinal N) (zero N)) invariant)
    (source : Bank N) (m : Bank N → Int → Option Bool)
    (k i : Nat) (fits : i < 2^TableIO.width n)
    (orderWord : m (order N) = wordAt (TableIO.width n) n)
    (labelWord : m (label N) = wordAt (TableIO.width n) k)
    (requestWord : m source = wordAt (TableIO.width n) i)
    (zeroWord : m (zero N) = wordAt (TableIO.width n) 0)
    (oldWord : ∃ j, m (ordinal N) = wordAt (TableIO.width n) j)
    (legal : (-1 : Int) ≤ p ∧ p ≤ raw.length) (fit : TableIO.width n+1 ≤ B)
    (hready : invariant m) :
    let T := replayStages states allowed member
    let expected := GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) 0 n i
    ∃ (len : Nat) (d : (machine states allowed member source).Config),
      (machine states allowed member source).BoundedSegment raw B (entry states allowed member source p prior m) d len ∧
      (machine states allowed member source).step raw d = none ∧
      returned states allowed member source d = expected.isSome ∧
      d.workCell (label N) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧ invariant d.workCell ∧
      (∃ rem, d.workCell (ordinal N) = wordAt (TableIO.width n) rem) ∧
      d.workCell (zero N) = wordAt (TableIO.width n) 0 ∧
      d.workCell (order N) = wordAt (TableIO.width n) n ∧ ∀ j ∈ keep, d.workCell j = m j := by
  let T := replayStages states allowed member
  let P := installer source
  let cells := memory source m
  obtain ⟨a,d,r,h,inp,heads,out,data,index⟩ := install source m orderWord requestWord oldWord legal fit
  let t : (T.component 4).Config := ⟨T.entry 4,p,fun _ => 0,cells,prior⟩
  have il : label N ≠ ordinal N := fun e => by have z := congrArg Fin.val e; change 75=93 at z; omega
  have iz : label N ≠ zero N := fun e => by have z := congrArg Fin.val e; change 75=94 at z; omega
  have io : label N ≠ order N := fun e => by have z := congrArg Fin.val e; change 75=74 at z; omega
  have oo : ordinal N ≠ order N := fun e => by have z := congrArg Fin.val e; change 93=74 at z; omega
  have oz : ordinal N ≠ zero N := fun e => by have z := congrArg Fin.val e; change 93=94 at z; omega
  have prepared : Live (M := T.component 4) raw n k i (label N) (order N) (ordinal N) (zero N) t :=
    ⟨⟨legal.1,legal.2,rfl,(away source m _ il).trans labelWord,
      (away source m _ oo.symm).trans orderWord⟩,
      (at_value source m).trans requestWord,(away source m _ oz.symm).trans zeroWord⟩
  have keepIn : invariant cells := stableOrdinal m cells (away source m) hready
  obtain ⟨b,e,s,stop,answer,word,parked,output,inv,hIndex,hZero,hOrder,frame⟩ :=
    PhysicalGreedyOrdinalInvariant.executeWithRegisters (label := label N) (order := order N)
      (ordinal := ordinal N) (zero := zero N) (widthStates := states) (allowed := allowed) (member := member)
      query eligible keep invariant stableLabel stableOrdinal ⟨labelOutside,il,iz⟩
      ordinalOutside io oo oz fit eligibleRun memberRun k i fits t rfl prepared keepIn
  let pD := P.bankConfig identity d (fun _ => 0) m
  let qA := T.machine.bankConfig identity (T.tag 4 t) (fun _ => 0) m
  let qD := T.machine.bankConfig identity e (fun _ => 0) m
  have first := P.relocateBanks_segment identity r (heads := fun _ => 0) (cells := m) (by simp)
  have firstStop : (P.relocateBanks identity).step raw pD = none := by
    unfold pD
    rw [relocateBanks_step,h]
    rfl
  have second := T.machine.relocateBanks_segment identity s (heads := fun _ => 0) (cells := m) (by simp)
  have secondStop : (T.machine.relocateBanks identity).step raw qD = none := by
    unfold qD
    rw [relocateBanks_step,stop]
    rfl
  have handoff : thenEntry P T.machine identity identity pD = qA := by
    apply configEq
    · rfl
    · exact inp
    · exact ((identityHead P d m).trans heads).trans (identityHead T.machine (T.tag 4 t) m).symm
    · exact ((identityCell P d m).trans data).trans (identityCell T.machine (T.tag 4 t) m).symm
    · exact out
  change (T.machine.relocateBanks identity).BoundedSegment raw B qA qD b at second
  rw [← handoff] at second
  let z := thenRight P T.machine identity identity qD
  have eq : z.workCell = e.workCell := identityCell T.machine e m
  have terminal : returned states allowed member source z =
      found (label := label N) (order := order N) (ordinal := ordinal N) (zero := zero N)
        (widthStates := states) (allowed := allowed) (member := member) e := by
    unfold returned
    have tag : z.state = finSumFinEquiv (Sum.inr e.state) := rfl
    rw [tag,Equiv.symm_apply_apply]
    rfl
  refine ⟨_,z,thenSegment P T.machine identity identity first firstStop second,?_,terminal.trans answer,
    (congrFun eq _).trans word,(identityHead T.machine e m).trans parked,output,eq.symm ▸ inv,?_,(congrFun eq _).trans hZero,(congrFun eq _).trans hOrder,?_⟩
  · change (machine states allowed member source).step raw
      (thenRight P T.machine identity identity qD) = none
    rw [thenStep_right,secondStop]
    rfl
  · obtain ⟨rem,hr⟩ := hIndex
    exact ⟨rem,(congrFun eq _).trans hr⟩
  · intro j hj
    exact (congrFun eq j).trans ((frame j hj).trans (away source m j (fun e => ordinalOutside (e ▸ hj))))

theorem execute {n B : Nat} {raw prior : List Bool} {p : Int}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Bank N)) (invariant : (Bank N → Int → Option Bool) → Prop)
    (stableLabel : GreedyTapeScanInvariant.Stable (label N) invariant)
    (stableOrdinal : GreedyTapeScanInvariant.Stable (ordinal N) invariant)
    (labelOutside : label N ∉ keep) (ordinalOutside : ordinal N ∉ keep)
    (eligibleRun : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member (B := B)
      raw 1 eligible allowed.answer (kept keep (ordinal N) (zero N)) invariant)
    (memberRun : GreedyTapeScanInvariant.Leaf (label N) (order N) states allowed member (B := B)
      raw 2 (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer
      (kept keep (ordinal N) (zero N)) invariant)
    (source : Bank N) (m : Bank N → Int → Option Bool)
    (k i : Nat) (fits : i < 2^TableIO.width n)
    (orderWord : m (order N) = wordAt (TableIO.width n) n)
    (labelWord : m (label N) = wordAt (TableIO.width n) k)
    (requestWord : m source = wordAt (TableIO.width n) i)
    (zeroWord : m (zero N) = wordAt (TableIO.width n) 0)
    (oldWord : ∃ j, m (ordinal N) = wordAt (TableIO.width n) j)
    (legal : (-1 : Int) ≤ p ∧ p ≤ raw.length) (fit : TableIO.width n+1 ≤ B)
    (hready : invariant m) :
    let T := replayStages states allowed member
    let expected := GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) 0 n i
    ∃ (len : Nat) (d : (machine states allowed member source).Config),
      (machine states allowed member source).BoundedSegment raw B (entry states allowed member source p prior m) d len ∧
      (machine states allowed member source).step raw d = none ∧
      returned states allowed member source d = expected.isSome ∧
      d.workCell (label N) = wordAt (TableIO.width n) (expected.elim n Fin.val) ∧
      d.workHead = (fun _ => 0) ∧ d.outputReversed = prior ∧ invariant d.workCell ∧
      ∀ j ∈ keep, d.workCell j = m j := by
  obtain ⟨len,d,run,halt,answer,cell,heads,out,inv,_,_,_,frame⟩ :=
    executeWithRegisters states allowed member query eligible keep invariant stableLabel stableOrdinal
      labelOutside ordinalOutside eligibleRun memberRun source m k i fits orderWord labelWord requestWord
      zeroWord oldWord legal fit hready
  exact ⟨len,d,run,halt,answer,cell,heads,out,inv,frame⟩

end Mathproof.MinimumGeneration.PhysicalGreedyOrdinalRequested
