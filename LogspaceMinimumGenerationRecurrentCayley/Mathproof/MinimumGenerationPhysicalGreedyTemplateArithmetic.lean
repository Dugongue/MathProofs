import Mathproof.MinimumGenerationPhysicalGreedyHeaderDriver
import Mathproof.MinimumGenerationTapeMultiply

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateArithmetic

open SearchTransducer PhysicalGreedyHeader
open PhysicalGreedyHeaderInstall (wordAt outside_word)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

abbrev Bank := Fin 8
abbrev A := TapeAddition.machine
abbrev M := TapeMultiply.machine

def addBanks : Fin A.workTapes ↪ Bank :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Bank => i.val) h)⟩

def mulSlot (j : Fin 6) : Bank :=
  if j=0 then 4 else if j=1 then 5 else if j=2 then 2 else if j=3 then 3 else if j=4 then 6 else 7

def mulBanks : Fin M.workTapes ↪ Bank :=
  ⟨mulSlot, by
    intro i j e
    change Fin 6 at i j
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def copyPlan (i : Bank) : Option Bank := if i=5 ∨ i=6 then some 0 else none

abbrev C := TapeInstall.machine (3 : Bank) copyPlan
def allBanks : Bank ↪ Bank := Function.Embedding.refl _

abbrev stages : Stages 3 112 8 where
  first := 0
  entry i := if i=0 then A.initialState.castLE (by decide)
    else if i=1 then C.initialState.castLE (by decide) else M.initialState
  transition i := if i=0 then A.padTransition (by decide) addBanks
    else if i=1 then C.padTransition (by decide) allBanks else (M.relocateBanks mulBanks).transition
  next i _ := if i=0 then some 1 else if i=1 then some 2 else none

abbrev machine := stages.machine

def layout (w n a acc copy : Nat) (i : Bank) : Int → Option Bool :=
  wordAt w (if i=0 then a else if i=1 then n else if i=4 then acc
    else if i=5 ∨ i=6 then copy else 0)

def initial (w n : Nat) (p : Int) (prior : List Bool) : (stages.component 0).Config :=
  ⟨stages.entry 0,p,fun _ => 0,layout w n n 1 0,prior⟩

def start (w n : Nat) (p : Int) (prior : List Bool) : machine.Config :=
  stages.tag 0 (initial w n p prior)

private theorem cfgEq {P : SearchTransducer} (a b : P.Config)
    (hq : a.state = b.state) (hi : a.inputHead = b.inputHead)
    (hh : a.workHead = b.workHead) (hc : a.workCell = b.workCell)
    (ho : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem frameHead (P : SearchTransducer) (e : Fin P.workTapes ↪ Bank)
    (c : P.Config) (m : Bank → Int → Option Bool)
    (h : c.workHead = (fun _ => 0)) :
    (P.bankConfig e c (fun _ => 0) m).workHead = fun _ => 0 := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hj
    exact (P.bankConfig_head_image e c (fun _ => 0) m i).trans (congrFun h i)
  · exact (P.bankConfig_frame e c (fun _ => 0) m hj).1

private theorem frameCells (P : SearchTransducer) (e : Fin P.workTapes ↪ Bank)
    (c : P.Config) (old new : Bank → Int → Option Bool)
    (inside : ∀ i, c.workCell i = new (e i))
    (outside : ∀ j ∉ Set.range e, old j = new j) :
    (P.bankConfig e c (fun _ => 0) old).workCell = new := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hj
    exact (P.bankConfig_cell_image e c (fun _ => 0) old i).trans (inside i)
  · exact (P.bankConfig_frame e c (fun _ => 0) old hj).2.trans (outside j hj)

private theorem addLayout (w n a : Nat) (q : A.Config) (acc : ∀ i, q.workCell i = TapeAddition.cells w a n 0 i) :
    (A.bankConfig addBanks q (fun _ => 0) (layout w n n 1 0)).workCell = layout w n a 1 0 := by
  apply frameCells
  · intro i
    rw [acc, show TapeAddition.cells w a n 0 i = TapeAddition.register w
      (if i=0 then a else if i=1 then n else 0) from by fin_cases i <;> rfl]
    rw [register_work]
    fin_cases i <;> rfl
  · intro j nj
    have h : j ≠ 0 := fun e => nj ⟨0,by exact e.symm⟩
    simp [layout,h]

private theorem copyLayout (w n m : Nat) :
    TapeInstall.installed copyPlan (layout w n m 1 0) w = layout w n m 1 m := by
  funext i
  by_cases hi : i=5 ∨ i=6
  · calc
      _ = layout w n m 1 0 0 := TapeInstall.installed_exact _ _ _ _ _ (if_pos hi) (by
        intro p h
        rcases hi with rfl | rfl <;>
          exact (outside_word _ _ p h).trans (outside_word _ _ p h).symm)
      _ = _ := by rcases hi with rfl | rfl <;> rfl
  · rw [TapeInstall.installed_source _ _ _ _ (if_neg hi)]
    simp [layout,hi]

private theorem mulLayout (w n m sum oldCopy : Nat) (q : M.Config)
    (h : ∀ i, q.workCell i = TapeMultiply.cells w sum m m 0 i) :
    (M.bankConfig mulBanks q (fun _ => 0) (layout w n m 1 oldCopy)).workCell = layout w n m sum m := by
  apply frameCells
  · intro i
    rw [h, show TapeMultiply.cells w sum m m 0 i = TapeAddition.register w
      (if i=0 then sum else if i=1 ∨ i=4 then m else 0) from by fin_cases i <;> rfl]
    rw [register_work]
    fin_cases i <;> rfl
  · intro j nj
    have h : j ≠ 4 := fun e => nj ⟨0,by exact e.symm⟩
    have a : j ≠ 5 := fun e => nj ⟨1,by exact e.symm⟩
    have b : j ≠ 6 := fun e => nj ⟨4,by exact e.symm⟩
    simp [layout,h,a,b]

/-- One finite tape program produces both the doubled order and its square
plus one, leaving the permanent zero, source order and raw input untouched. -/
theorem execute (w n : Nat) (raw prior : List Bool) (p : Int)
    (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length) (fit : n+n < 2^w) :
    ∃ (steps : Nat) (d : machine.Config), machine.BoundedSegment raw (w+1) (start w n p prior) d steps ∧
      machine.step raw d = none ∧ d.inputHead = p ∧ d.workHead = (fun _ => 0) ∧
      d.workCell = layout w n (n+n) (1+(n+n)*(n+n)) (n+n) ∧ d.outputReversed = prior := by
  let m := n+n
  let f := layout w n n 1 0
  let g := layout w n m 1 0
  let h := layout w n m 1 m
  let a := TapeAddition.startConfig w n n 0 p prior
  let b := TapeAddition.stopConfig w m n p prior
  obtain ⟨r,s⟩ := TapeAddition.executeAddition raw prior p w n n 0 bounds (lt_of_le_of_lt (by omega) fit)
  let a' := A.padConfig (S := 112) (by decide) addBanks (A.bankConfig addBanks a (fun _ => 0) f)
  let b' := A.padConfig (S := 112) (by decide) addBanks (A.bankConfig addBanks b (fun _ => 0) f)
  have init : a' = initial w n p prior :=
    cfgEq _ _ rfl rfl (frameHead A addBanks a f rfl) (addLayout w n n a (fun _ => rfl)) rfl
  have r' := A.padMachine_segment (S := 112) (by decide) addBanks
    (A.relocateBanks_segment addBanks r (heads := fun _ => 0) (cells := f) (by simp))
  change (stages.component 0).BoundedSegment raw (w+1) a' b' _ at r'
  rw [init] at r'
  have stopB : (stages.component 0).step raw b' = none := by
    change (A.padMachine (S := 112) (by decide) addBanks).step raw b' = none
    unfold b'
    rw [A.padMachine_step,A.relocateBanks_step,s]
    rfl
  let c := TapeInstall.start 3 copyPlan p g prior
  let d := TapeInstall.stop 3 copyPlan p g prior w
  let c' := C.padConfig (S := 112) (by decide) allBanks (C.bankConfig allBanks c (fun _ => 0) g)
  let d' := C.padConfig (S := 112) (by decide) allBanks (C.bankConfig allBanks d (fun _ => 0) g)
  obtain ⟨copy,copyStop⟩ := TapeInstall.execute 3 copyPlan (by decide) raw (encodeLabel w 0)
    prior p g rfl bounds
  rw [length_encodeLabel] at copy copyStop
  have copy' := C.padMachine_segment (S := 112) (by decide) allBanks
    (C.relocateBanks_segment allBanks copy (heads := fun _ => 0) (cells := g) (by simp))
  change (stages.component 1).BoundedSegment raw (w+1) c' d' _ at copy'
  have hand1 : stages.enter (i := 0) (1 : Fin 3) b' = c' := by
    apply cfgEq
    · rfl
    · rfl
    · exact (frameHead A addBanks b f rfl).trans (frameHead C allBanks c g rfl).symm
    · exact (addLayout w n m b (fun _ => rfl)).trans
        (frameCells C allBanks c g g (fun _ => rfl) (fun _ _ => rfl)).symm
    · rfl
  rw [← hand1] at copy'
  have stopD : (stages.component 1).step raw d' = none := by
    change (C.padMachine (S := 112) (by decide) allBanks).step raw d' = none
    unfold d'
    rw [C.padMachine_step,C.relocateBanks_step,copyStop]
    rfl
  let u := TapeMultiply.startConfig w 1 m m 0 p prior
  let v := TapeMultiply.stopConfig w (1+m*m) m m p prior
  let u' := M.bankConfig mulBanks u (fun _ => 0) h
  let v' := M.bankConfig mulBanks v (fun _ => 0) h
  have shrink : (C.bankConfig allBanks d (fun _ => 0) g).workCell = h := by
    refine frameCells C allBanks d g h (fun j => congrFun (copyLayout w n m) j) ?_
    intro j hj
    exact False.elim (hj ⟨j,rfl⟩)
  have hand2 : stages.enter (i := 1) (2 : Fin 3) d' = u' := by
    apply cfgEq
    · rfl
    · rfl
    · exact (frameHead C allBanks d g rfl).trans (frameHead M mulBanks u h rfl).symm
    · exact shrink.trans (frameCells M mulBanks u h h (by
        intro i
        have key : u.workCell i = TapeMultiply.cells w 1 m m 0 i := rfl
        rw [key, show TapeMultiply.cells w 1 m m 0 i = TapeAddition.register w
          (if i=0 then 1 else if i=1 ∨ i=4 then m else 0) from by fin_cases i <;> rfl, register_work]
        fin_cases i <;> rfl) (fun _ _ => rfl)).symm
    · rfl
  obtain ⟨mul,mulStop⟩ := TapeMultiply.executeMultiply raw prior p w 1 m m 0 bounds fit fit
  have mul' := M.relocateBanks_segment mulBanks mul (heads := fun _ => 0) (cells := h) (by simp)
  change (stages.component 2).BoundedSegment raw (w+1) u' v' _ at mul'
  rw [← hand2] at mul'
  have stopV : (stages.component 2).step raw v' = none := by
    change (M.relocateBanks mulBanks).step raw v' = none
    unfold v'
    rw [M.relocateBanks_step,mulStop]
    rfl
  have route := Stages.Routed.call (T := stages) r' stopB (show stages.next 0 b'.state = some 1 by rfl)
    (Stages.Routed.call copy' stopD (show stages.next 1 d'.state = some 2 by rfl) (.finish mul'))
  obtain ⟨all,stop⟩ := stages.routed_stop route stopV rfl
  refine ⟨_,stages.tag 2 v',all,stop,rfl,frameHead M mulBanks v h rfl,?_,rfl⟩
  exact mulLayout w n m (1+m*m) m v (fun _ => rfl)

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateArithmetic
