import Mathproof.MinimumGenerationPhysicalGreedyReaderInstall
import Mathproof.MinimumGenerationPhysicalGreedyTemplateFromRaw
import Mathproof.MinimumGenerationCayleyReaderCycle

namespace Mathproof.MinimumGeneration.PhysicalGreedyReaderSetup

open SearchTransducer PhysicalGreedyTemplateProgram PhysicalGreedyReaderInstall
open PhysicalGreedyTemplateCompose (Memory Run lift liftRun cfg configEq)
open PhysicalGreedyHeaderInstall (wordAt outside_word)
open CayleyQueryPrefixModel (width rawSpace keep cells)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev Bank := Fin 93

def reader : Fin 74 ↪ Bank :=
  ⟨Fin.castAdd 19,fun _ _ e => Fin.ext (congrArg (fun i : Bank => i.val) e)⟩

def header : Fin 18 ↪ Bank :=
  ⟨fun i => ⟨74+i.val,by have := i.isLt; omega⟩,
    fun _ _ e => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Bank => i.val) e))⟩

def headerOnly (n id : Nat) (i : Bank) : Int → Option Bool :=
  if h : 74 ≤ i.val ∧ i.val < 92 then
    PhysicalGreedyTemplateSetup.outputData n id 0 ⟨i.val-74,by omega⟩
  else fun _ => none

private def plan : List (Bank × Bank) → Bank → Option Bank
  | [], _ => none
  | (d,s)::tail, i => if i=d then some s else plan tail i

private theorem plan_member {maps : List (Bank × Bank)} {i j : Bank} (h : plan maps i = some j) :
    (i,j) ∈ maps := by
  induction maps with
  | nil => cases h
  | cons a rest ih =>
    obtain ⟨d,s⟩ := a
    by_cases same : i=d
    · subst d
      have eq : s=j := Option.some.inj (by simpa [plan] using h)
      simp [eq]
    · exact List.mem_cons_of_mem _ (ih (by simpa [plan,same] using h))

def rawCopies : List (Bank × Bank) :=
  [(21,header 1),(23,header 0),(24,header 1),(26,header 2),(27,header 1)]

def wideCopies : List (Bank × Bank) :=
  [(28,header 3),(29,header 6),(30,header 7),(31,header 8),(32,header 9),
   (33,header 4),(34,header 10),(71,header 5),(72,header 17),(92,header 3)]

def zeroBanks : Fin 2 ↪ Bank :=
  ⟨fun i => if i=0 then header 0 else 21,by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def orderBanks : Fin 2 ↪ Bank :=
  ⟨fun i => if i=0 then header 0 else 23,by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def clockBanks : Fin 3 ↪ Bank :=
  ⟨fun i => if i=0 then header 3 else if i=1 then 92 else 70,by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def shadows (i : Bank) : Bool := decide (35 ≤ i.val ∧ i.val < 70)

def afterRaw (n id : Nat) : Memory 93 := copied (plan rawCopies) (headerOnly n id)

def afterZero (n id : Nat) : Memory 93 := widened zeroBanks (afterRaw n id) (TableIO.width n) 0

def afterOrder (n id : Nat) : Memory 93 := widened orderBanks (afterZero n id) (TableIO.width n) n

def afterWide (n id : Nat) : Memory 93 := copied (plan wideCopies) (afterOrder n id)

def clocked (n id : Nat) : Memory 93 :=
  Function.update (Function.update (afterWide n id) (clockBanks 1)
    (wordAt (8 * TableIO.width n) 0)) (clockBanks 2) (InputPosition.work (CayleyReaderClock.bits n))

def outputData (n id : Nat) : Memory 93 := marked shadows (clocked n id)

def space (n : Nat) := (CayleyReaderClock.bits n).length+1

private def allBanks : Bank ↪ Bank := Function.Embedding.refl _

abbrev clockMachine : Machine 93 := lift (CayleyReaderClock.machine clockBanks) allBanks

def machine : Machine 93 :=
  (copyMachine (header 0) (plan rawCopies)).follow ((widenMachine zeroBanks).follow
    ((widenMachine orderBanks).follow ((copyMachine (header 3) (plan wideCopies)).follow
      (clockMachine.follow (markMachine shadows)))))

private theorem endpointWidth (n : Nat) : space n = 16 * TableIO.width n + 1 := by
  simp [space,CayleyReaderClock.bits,length_encodeLabel]

private theorem raise {P : Machine 93} {raw prior : List Bool} {pos : Int} {a b : Memory 93} {B D : Nat}
    (h : Run P raw B pos prior a b) (le : B ≤ D) : Run P raw D pos prior a b := by
  obtain ⟨k,q,run,done⟩ := h
  exact ⟨k,q,PhysicalEntry.segment_mono run le,done⟩

private theorem rawStage {raw prior : List Bool} {pos : Int} (n id : Nat)
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ raw.length) :
    Run (copyMachine (header 0) (plan rawCopies)) raw (space n) pos prior
      (headerOnly n id) (afterRaw n id) := by
  let w := TableIO.width n
  have go := copyRun (header 0) (plan rawCopies) (old := headerOnly n id) (prior := prior)
    (encodeLabel w n) rfl (by decide) hin (by
      intro i j map p hp
      have here := plan_member map
      simp only [rawCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at here
      rcases here with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals
        have h : p < 1 ∨ (w : Int) < p := by simpa only [length_encodeLabel] using hp
        first | exact (outside_word w 0 p h).symm
              | exact (outside_word w n p h).symm
              | exact (outside_word w id p h).symm)
  exact raise go (by rw [length_encodeLabel,endpointWidth]; omega)

private theorem zeroStage {raw prior : List Bool} {pos : Int} (n id : Nat)
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ raw.length) :
    Run (widenMachine zeroBanks) raw (space n) pos prior (afterRaw n id) (afterZero n id) := by
  let w := TableIO.width n
  have go := widenRun zeroBanks (old := afterRaw n id) (prior := prior) w 0 (encodeLabel w n)
    (length_encodeLabel _ _) rfl rfl (Nat.two_pow_pos _) hin
  exact raise go (by rw [endpointWidth]; dsimp [w]; omega)

private theorem orderStage {raw prior : List Bool} {pos : Int} (n id : Nat)
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ raw.length) :
    Run (widenMachine orderBanks) raw (space n) pos prior (afterZero n id) (afterOrder n id) := by
  let w := TableIO.width n
  have fit : n < 2^w := Nat.lt_log2_self
  have go := widenRun orderBanks (old := afterZero n id) (prior := prior) w n (encodeLabel w n)
    (length_encodeLabel _ _) rfl rfl fit hin
  exact raise go (by rw [endpointWidth]; dsimp [w]; omega)

private theorem wideStage {raw prior : List Bool} {pos : Int} (n id : Nat)
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ raw.length) :
    Run (copyMachine (header 3) (plan wideCopies)) raw (space n) pos prior
      (afterOrder n id) (afterWide n id) := by
  let w := width n
  have go := copyRun (header 3) (plan wideCopies) (old := afterOrder n id) (prior := prior)
    (encodeLabel w 0) rfl (by decide) hin (by
      intro i j map p hp
      have here := plan_member map
      simp only [wideCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at here
      rcases here with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals
        have h : p < 1 ∨ (w : Int) < p := by simpa only [length_encodeLabel] using hp
        exact (outside_word w _ p h).symm)
  exact raise go (by rw [length_encodeLabel,endpointWidth]; unfold w width; omega)

private theorem clockStage {n : Nat} (G : Group (Fin n)) {prior : List Bool} {pos : Int}
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ (@encodeCayley n G.toMul).length) :
    Run clockMachine (@encodeCayley n G.toMul) (space n) pos prior
      (afterWide n G.toOne.one.val) (clocked n G.toOne.one.val) := by
  let id := G.toOne.one.val
  let old := afterWide n id
  obtain ⟨k,d,run,stop,inp,out,heads,a,b,c,frame,_⟩ :=
    CayleyReaderClock.execute G clockBanks pos prior (encodeLabel (width n) 0) old
      hin (length_encodeLabel _ _) rfl rfl rfl
  refine liftRun (CayleyReaderClock.machine clockBanks) allBanks run stop rfl
    rfl inp rfl heads rfl out (fun _ => rfl) ?_ (fun j hj => False.elim (hj ⟨j,rfl⟩))
  intro j
  change d.workCell j = clocked n id j
  by_cases hc : j = clockBanks 2
  · rw [hc]
    simpa [clocked] using c
  by_cases hb : j = clockBanks 1
  · rw [hb] at hc ⊢
    simpa [clocked,hc,wordAt] using b
  by_cases ha : j = clockBanks 0
  · rw [ha] at hb hc ⊢
    simpa [clocked,hb,hc] using a
  · simpa [clocked,hb,hc] using frame j (by
      rintro ⟨i,rfl⟩
      fin_cases i <;> first | exact ha rfl | exact hb rfl | exact hc rfl)

/-- Prepare every immutable helper and reader tape by physical copying,
widening, clock construction, and simultaneous companion-marker writes. -/
theorem execute {n : Nat} (G : Group (Fin n)) {prior : List Bool} {pos : Int}
    (hin : (-1 : Int) ≤ pos ∧ pos ≤ (@encodeCayley n G.toMul).length) :
    Run machine (@encodeCayley n G.toMul) (space n) pos prior
      (headerOnly n G.toOne.one.val) (outputData n G.toOne.one.val) := by
  let id := G.toOne.one.val
  exact Run.follow (rawStage n id hin) (Run.follow (zeroStage n id hin)
    (Run.follow (orderStage n id hin) (Run.follow (wideStage n id hin)
      (Run.follow (clockStage G hin) (markRun shadows (clocked n id) (space n) hin)))))

private theorem shadow_marked {n id : Nat} (i : Fin 35) :
    outputData n id (reader (CayleyReaderCycle.shadowBank i)) = ParkOrigin.origin := by
  let j := reader (CayleyReaderCycle.shadowBank i)
  have hj : j.val = 35+i.val := rfl
  have low : 35 ≤ j.val := by rw [hj]; omega
  have high : j.val < 70 := by rw [hj]; have := i.isLt; omega
  have empty : clocked n id j = fun _ => none := by
    have a : j ≠ clockBanks 1 := fun e => by have e' := congrArg Fin.val e; change j.val=92 at e'; omega
    have b : j ≠ clockBanks 2 := fun e => by have e' := congrArg Fin.val e; change j.val=70 at e'; omega
    have c : j ≠ zeroBanks 1 := fun e => by have e' := congrArg Fin.val e; change j.val=21 at e'; omega
    have d : j ≠ orderBanks 1 := fun e => by have e' := congrArg Fin.val e; change j.val=23 at e'; omega
    have w : plan wideCopies j = none := by
      cases f : plan wideCopies j with
      | none => rfl
      | some s =>
        have m := plan_member f
        simp only [wideCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at m
        rcases m with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ |
          ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;>
          have z := congrArg Fin.val eq <;> omega
    have r : plan rawCopies j = none := by
      cases f : plan rawCopies j with
      | none => rfl
      | some s =>
        have m := plan_member f
        simp only [rawCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at m
        rcases m with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;>
          have z := congrArg Fin.val eq <;> omega
    simp [clocked,a,b,afterWide,copied,w,afterOrder,afterZero,widened,c,d,afterRaw,r,
      headerOnly,show ¬(74 ≤ j.val ∧ j.val < 92) by omega]
  funext p
  simp [outputData,marked,shadows,low,high,ParkOrigin.origin,j,empty]

def initialLabel {n : Nat} (G : Group (Fin n)) : Fin n := ⟨0,G.toOne.one.isLt.pos⟩

/-- The freshly installed reader can start with both sides of the initial
zero-cut query. Later calls may replace the query-dependent live banks. -/
theorem ready {n : Nat} (G : Group (Fin n)) :
    CayleyReaderCycle.Ready G 0 (BipartiteCayley.left G.toOne.one)
      (BipartiteCayley.left (initialLabel G)) 1 (CayleyReaderClock.bits n)
      (fun i => outputData n G.toOne.one.val (reader i)) := by
  let s := BipartiteCayley.left G.toOne.one
  let t := BipartiteCayley.left (initialLabel G)
  have words (j : Fin 35) (hj : j ∈ keep) :
      outputData n G.toOne.one.val (reader (CayleyReaderCycle.restoreBanks (CayleyReaderRestore.readerBanks j))) =
        cells G 0 s t 1 j := by
    fin_cases j <;> first | rfl | simp [keep] at hj
  have scratch (j : Fin 35) (hj : j ∉ keep) :
      outputData n G.toOne.one.val (reader (CayleyReaderCycle.restoreBanks (CayleyReaderRestore.readerBanks j))) =
        fun _ => none := by
    fin_cases j <;> first | rfl | simp [keep] at hj
  refine ⟨⟨rfl,?_,rfl,rfl,rfl,words,?_⟩,shadow_marked⟩
  · rw [show (CayleyReaderClock.bits n).length = 16*TableIO.width n from length_encodeLabel _ _]
    exact CayleyReaderRestore.resetClockEnough G
  · intro j z outside
    by_cases h : j ∈ keep
    · rw [words j h]
      exact CayleyReaderFrame.entryOutside G 0 s t 1 j z outside
    · rw [scratch j h]

theorem headerOnly_at (n id : Nat) (i : Fin 18) :
    headerOnly n id (header i) = PhysicalGreedyTemplateSetup.outputData n id 0 i := by
  have h : 74 ≤ (header i).val ∧ (header i).val < 92 := by
    change 74 ≤ 74+i.val ∧ 74+i.val < 92
    have := i.isLt
    omega
  unfold headerOnly
  rw [dif_pos h]
  have eq : (⟨(header i).val-74,by omega⟩ : Fin 18) = i := by
    apply Fin.ext
    change 74+i.val-74=i.val
    omega
  rw [eq]

/-- The persistent source block remains available for live query reloads. -/
theorem header_preserved (n id : Nat) (i : Fin 18) :
    outputData n id (header i) = PhysicalGreedyTemplateSetup.outputData n id 0 i := by
  let j := header i
  have lo : 74 ≤ j.val := by change 74 ≤ 74+i.val; omega
  have hi : j.val < 92 := by change 74+i.val < 92; have := i.isLt; omega
  have neq (k : Bank) (low : k.val < 74 ∨ 92 ≤ k.val) : j ≠ k := fun eq => by
    have same := congrArg Fin.val eq
    omega
  have a : j ≠ clockBanks 1 := neq _ (by decide)
  have b : j ≠ clockBanks 2 := neq _ (by decide)
  have c : j ≠ zeroBanks 1 := neq _ (by decide)
  have d : j ≠ orderBanks 1 := neq _ (by decide)
  have w : plan wideCopies j = none := by
    cases f : plan wideCopies j with
    | none => rfl
    | some s =>
      have m := plan_member f
      simp only [wideCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at m
      rcases m with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ |
        ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;> exact (neq _ (by decide) eq).elim
  have r : plan rawCopies j = none := by
    cases f : plan rawCopies j with
    | none => rfl
    | some s =>
      have m := plan_member f
      simp only [rawCopies,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at m
      rcases m with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;>
        exact (neq _ (by decide) eq).elim
  have noMark : ¬(35 ≤ j.val ∧ j.val < 70) := by omega
  change outputData n id j = _
  funext p
  simpa [outputData,marked,shadows,noMark,clocked,a,b,afterWide,copied,w,afterOrder,afterZero,
    widened,c,d,afterRaw,r] using congrFun (headerOnly_at n id i) p

end Mathproof.MinimumGeneration.PhysicalGreedyReaderSetup
