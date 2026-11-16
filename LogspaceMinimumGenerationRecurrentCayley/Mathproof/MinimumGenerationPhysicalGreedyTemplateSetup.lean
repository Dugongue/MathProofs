import Mathproof.MinimumGenerationPhysicalGreedyTemplateCompose
import Mathproof.MinimumGenerationPhysicalGreedyTemplateWidth
import Mathproof.MinimumGenerationPhysicalGreedyTemplateInputs
import Mathproof.MinimumGenerationPhysicalGreedyTemplateArithmetic
import Mathproof.MinimumGenerationPhysicalGreedyHeaderCheckout

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateSetup

open SearchTransducer PhysicalGreedyHeader PhysicalGreedyTemplateProgram
open PhysicalGreedyTemplateCompose (Memory Run lift liftRun cfg)
open PhysicalGreedyHeaderInstall (wordAt outside outside_word)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

abbrev Bank := Fin 18

abbrev W := PhysicalGreedyTemplateWidth.machine
abbrev I := PhysicalGreedyTemplateInputs.machine
abbrev A := PhysicalGreedyTemplateArithmetic.machine
abbrev F := PhysicalGreedyFixedTemplates.machine
abbrev C := PhysicalGreedyHeaderCheckout.machine

def widthBanks : Fin W.workTapes ↪ Bank :=
  ⟨fun i => if i=0 then 0 else if i=1 then 17 else 3, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def inputBanks : Fin I.workTapes ↪ Bank :=
  ⟨fun i => if i=0 then 0 else if i=1 then 1 else if i=2 then 2
    else if i=3 then 5 else if i=4 then 17 else if i=5 then 11 else 6, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def arithmeticBanks : Fin A.workTapes ↪ Bank :=
  ⟨fun i => if i=0 then 5 else if i=1 then 17 else if i=2 then 13 else if i=3 then 3
    else if i=4 then 12 else if i=5 then 14 else if i=6 then 15 else 16, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

def fixedBanks : Fin F.native.workTapes ↪ Bank :=
  ⟨fun i => ⟨3+i.val,by have hi := i.isLt; change i.val < 11 at hi; omega⟩,
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Bank => i.val) h))⟩

def standardBanks (k : Nat) (h : k ≤ 18) : Fin k ↪ Bank :=
  ⟨Fin.castLE h,fun _ _ h => Fin.ext (congrArg (fun i : Bank => i.val) h)⟩

def checkoutBanks : Fin C.workTapes ↪ Bank := standardBanks 17 (by decide)

def zeroCopies (j : Bank) : Option Bank := if 4 ≤ j.val then some 3 else none

abbrev Z := TapeInstall.machine (3 : Bank) zeroCopies

def oneProgram : List (Command 15) := [.increment 1,.increment 9]

abbrev O := compile oneProgram

def wideBanks : Fin O.native.workTapes ↪ Bank :=
  ⟨fun i => ⟨3+i.val,by have h := i.isLt; change i.val < 15 at h; omega⟩,
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Bank => i.val) h))⟩

def machine : Machine 18 :=
  (lift W widthBanks).follow ((lift Z (standardBanks 18 le_rfl)).follow
    ((lift I inputBanks).follow ((lift O.native wideBanks).follow
      ((lift A arithmeticBanks).follow ((lift F.native fixedBanks).follow (lift C checkoutBanks))))))

/-- The first three registers keep their native raw width. The auxiliary
raw-width zero at bank 17 supplies the reusable widening template. -/
def entryData (n id label : Nat) (j : Bank) : Int → Option Bool :=
  if j=0 then wordAt (TableIO.width n) n
  else if j=1 then wordAt (TableIO.width n) label
  else if j=2 then wordAt (TableIO.width n) id
  else if j=17 then wordAt (TableIO.width n) 0
  else fun _ => none

private def widenedData (n id label : Nat) (j : Bank) : Int → Option Bool :=
  if j=3 then wordAt (width n) 0
  else if j=17 then wordAt (2*TableIO.width n) 0
  else entryData n id label j

private def wideData (n id label : Nat) (f : Bank → Nat) (j : Bank) : Int → Option Bool :=
  if j.val < 3 then entryData n id label j else wordAt (width n) (f j)

private def inputValue (n id : Nat) (j : Bank) : Nat :=
  if j=5 ∨ j=17 then n else if j=11 then id else 0

private def oneValue (n id : Nat) (j : Bank) : Nat :=
  if j=4 ∨ j=12 then 1 else inputValue n id j

private def productValue (n id : Nat) (j : Bank) : Nat :=
  if j=5 ∨ j=14 ∨ j=15 then graphOrder n
  else if j=12 then 1+graphOrder n*graphOrder n
  else oneValue n id j

private def fixedValue (n id : Nat) (j : Bank) : Nat :=
  if h : 3 ≤ j.val ∧ j.val < 11 then fixed n id ⟨j.val-3,by omega⟩
  else productValue n id j

def outputValue (n id : Nat) (j : Bank) : Nat :=
  if 11 ≤ j.val ∧ j.val < 17 then 0 else fixedValue n id j

def outputData (n id label : Nat) : Memory 18 := wideData n id label (outputValue n id)

private theorem widthStage {raw prior : List Bool} {input : Int} (n id label : Nat)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift W widthBanks) raw (width n+1) input prior
      (entryData n id label) (widenedData n id label) := by
  let w := TableIO.width n
  obtain ⟨k,d,run,halt,heads,pos,out,cs⟩ := PhysicalGreedyTemplateWidth.execute
    raw (encodeLabel w n) prior input w (length_encodeLabel _ _) hin
  have h : ∀ i, d.workCell i = widenedData n id label (widthBanks i) := by
    intro i
    rw [cs]
    fin_cases i <;> exact HeaderSetup.counterTape_eq_marked _
  refine liftRun W widthBanks run halt rfl rfl pos rfl heads rfl out ?_ h ?_
  · intro i
    fin_cases i
    · exact HeaderSetup.counterTape_eq_marked _
    · exact HeaderSetup.counterTape_eq_marked _
    · change InputScan.counterTape 0 [] = (fun _ => none)
      exact (HeaderSetup.counterTape_eq_marked []).trans (by funext p; simp [InputPosition.work])
  · intro j hj
    have a : j ≠ 3 := fun e => hj ⟨2,e.symm⟩
    have b : j ≠ 17 := fun e => hj ⟨1,e.symm⟩
    simp [widenedData,a,b]

private theorem fanoutStage {raw prior : List Bool} {input : Int} (n id label : Nat)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift Z (standardBanks 18 le_rfl)) raw (width n+1) input prior
      (widenedData n id label) (wideData n id label (fun _ => 0)) := by
  let w := width n
  let old := widenedData n id label
  obtain ⟨run,halt⟩ := TapeInstall.execute 3 zeroCopies (by decide) raw (encodeLabel w 0) prior input
    old rfl hin
  rw [length_encodeLabel] at run halt
  apply liftRun Z (standardBanks 18 le_rfl) run halt rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) ?_ (fun j h => False.elim (h ⟨j,rfl⟩))
  intro j
  change TapeInstall.installed zeroCopies old w j = wideData n id label (fun _ => 0) j
  by_cases big : 4 ≤ j.val
  · have win : outside w (old j) := by
      by_cases h17 : j = 17
      · subst j
        intro p hp
        exact outside_word (2*TableIO.width n) 0 p (hp.imp (fun h => h) (by
          intro hp
          dsimp [w,width] at hp
          omega))
      · have h3 : j ≠ 3 := fun he => by rw [he] at big; contradiction
        have h0 : j ≠ 0 := fun he => by rw [he] at big; contradiction
        have h1 : j ≠ 1 := fun he => by rw [he] at big; contradiction
        have h2 : j ≠ 2 := fun he => by rw [he] at big; contradiction
        simp [old,widenedData,entryData,h0,h1,h2,h3,h17,outside]
    have out : TapeInstall.installed zeroCopies old w j = old 3 :=
      TapeInstall.installed_exact _ _ _ _ _ (if_pos big) (by
        intro p hp
        exact (win p hp).trans (outside_word w 0 p hp).symm)
    rw [out]
    have hlt : ¬ j.val < 3 := by omega
    simp [wideData,hlt,old,widenedData]
  · rw [TapeInstall.installed_source _ _ _ _ (if_neg big)]
    fin_cases j <;> first | rfl | contradiction

private theorem inputStage {raw prior : List Bool} {input : Int} {n label : Nat} (id : Fin n)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift I inputBanks) raw (width n+1) input prior
      (wideData n id.val label (fun _ => 0)) (wideData n id.val label (inputValue n id.val)) := by
  let before := wideData n id.val label (fun _ => 0)
  let after := wideData n id.val label (inputValue n id.val)
  let m := fun j : PhysicalGreedyTemplateInputs.Bank => before (inputBanks j)
  obtain ⟨k,run,stop,heads,pos,out,n₁,n₂,ui,fixed⟩ :=
    PhysicalGreedyTemplateInputs.execute id m hin rfl rfl rfl rfl rfl
  have bc : TableIO.width n+1 ≤ width n+1 := by unfold width; omega
  apply liftRun I inputBanks (PhysicalEntry.segment_mono run bc) stop rfl rfl pos rfl heads rfl out
    (fun _ => rfl) ?_ ?_
  · intro j
    fin_cases j
    · exact fixed 0 (by decide)
    · exact fixed 1 (by decide)
    · exact fixed 2 (by decide)
    · exact n₁
    · exact n₂
    · exact ui
    · exact fixed 6 (by decide)
  · intro j hj
    have a : j ≠ 5 := fun e => hj ⟨3,e.symm⟩
    have b : j ≠ 17 := fun e => hj ⟨4,e.symm⟩
    have c : j ≠ 11 := fun e => hj ⟨5,e.symm⟩
    simp [wideData,inputValue,a,b,c]

private theorem oneStage {raw prior : List Bool} {input : Int} {n label : Nat} (id : Fin n)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift O.native wideBanks) raw (width n+1) input prior
      (wideData n id.val label (inputValue n id.val)) (wideData n id.val label (oneValue n id.val)) := by
  let nums : Fin 15 → Nat := fun i => inputValue n id.val (wideBanks i)
  let new := eval oneProgram nums
  obtain ⟨k,sg,run,halt⟩ := PhysicalGreedyTemplateProgram.execute (prior := prior) (w := width n)
    hin oneProgram nums (by trivial)
  apply liftRun O.native wideBanks run halt rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have a : j ≠ 4 := fun e => hj ⟨(1 : Fin 15),e.symm⟩
    have b : j ≠ 12 := fun e => hj ⟨(9 : Fin 15),e.symm⟩
    simp [wideData,oneValue,a,b]

private theorem arithmeticStage {raw prior : List Bool} {input : Int} {n label : Nat} (id : Fin n)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift A arithmeticBanks) raw (width n+1) input prior
      (wideData n id.val label (oneValue n id.val)) (wideData n id.val label (productValue n id.val)) := by
  have bound := (registerFit id.isLt ((Nat.zero_le _).trans_lt id.isLt)).2.1
  obtain ⟨k,d,run,halt,pos,parked,banks,out⟩ :=
    PhysicalGreedyTemplateArithmetic.execute (width n) n raw prior input hin bound
  apply liftRun A arithmeticBanks run halt rfl rfl pos rfl parked rfl out ?_ ?_ ?_
  · intro i
    fin_cases i <;> rfl
  · intro i
    rw [banks]
    fin_cases i <;> rfl
  · intro j hj
    have a : j ≠ 5 := fun e => hj ⟨0,e.symm⟩
    have b : j ≠ 12 := fun e => hj ⟨4,e.symm⟩
    have c : j ≠ 14 := fun e => hj ⟨5,e.symm⟩
    have d : j ≠ 15 := fun e => hj ⟨6,e.symm⟩
    simp [wideData,productValue,a,b,c,d]

private theorem fixedStage {raw prior : List Bool} {input : Int} {n label : Nat} (id : Fin n)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift F.native fixedBanks) raw (width n+1) input prior
      (wideData n id.val label (productValue n id.val)) (wideData n id.val label (fixedValue n id.val)) := by
  obtain ⟨k,sg,run,halt⟩ := PhysicalGreedyFixedTemplates.execute id (prior := prior) hin
  apply liftRun F.native fixedBanks run halt rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h : ¬(3 ≤ j.val ∧ j.val < 11) := fun h => by
      let i : Fin F.native.workTapes := ⟨j.val-3,by change j.val-3 < 11; omega⟩
      exact hj ⟨i,Fin.ext (by change 3+(j.val-3) = j.val; omega)⟩
    simp [wideData,fixedValue,h]

private theorem checkoutStage {raw prior : List Bool} {input : Int} {n label : Nat} (id : Fin n)
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run (lift C checkoutBanks) raw (width n+1) input prior
      (wideData n id.val label (fixedValue n id.val)) (outputData n id.val label) := by
  let before := wideData n id.val label (fixedValue n id.val)
  let m := fun j => before (checkoutBanks j)
  have guard (j : PhysicalGreedyHeaderInstall.Bank) (hj : 11 ≤ j.val) :
      outside (width n) (m j) := by
    have lo : ¬ (checkoutBanks j).val < 3 := by change ¬ j.val < 3; omega
    exact (by simpa [m,before,wideData,lo] using outside_word (width n) (fixedValue n id.val (checkoutBanks j)))
  obtain ⟨k,run,halt,pos,heads,out,frame,zeroed⟩ :=
    PhysicalGreedyHeaderCheckout.execute (n := n) (old := m) rfl guard hin
  apply liftRun C checkoutBanks run halt rfl rfl pos rfl heads rfl out (fun _ => rfl) ?_ ?_
  · intro j
    by_cases hi : 11 ≤ j.val
    · have after : outputData n id.val label (checkoutBanks j) = wordAt (width n) 0 := by
        have b : ¬(checkoutBanks j).val < 3 := by change ¬ j.val < 3; omega
        have c : 11 ≤ (checkoutBanks j).val ∧ (checkoutBanks j).val < 17 := ⟨hi,j.isLt⟩
        simp [outputData,wideData,outputValue,b,c]
      exact (zeroed j hi).trans after.symm
    · have b : ¬(11 ≤ (checkoutBanks j).val ∧ (checkoutBanks j).val < 17) := by
        change ¬(11 ≤ j.val ∧ j.val < 17)
        omega
      exact (frame j (by omega)).trans (by simp [m,before,outputData,wideData,outputValue,b])
  · intro j hj
    have bad : ¬(11 ≤ j.val ∧ j.val < 17) := fun h => by
      let jj : Fin C.workTapes := ⟨j.val, h.2⟩
      exact hj ⟨jj,Fin.ext rfl⟩
    simp [outputData,wideData,outputValue,bad]

/-- One physical initialization pass after the raw order/identity scan. This
grows the width, obtains the live inputs, computes the complete final header
template block, and clears every header scratch tape. -/
theorem execute {n : Nat} (id : Fin n) (label : Nat) {raw prior : List Bool} {input : Int}
    (hin : (-1 : Int) ≤ input ∧ input ≤ raw.length) :
    Run machine raw (width n+1) input prior (entryData n id.val label) (outputData n id.val label) :=
  Run.follow (widthStage n id.val label hin)
    (Run.follow (fanoutStage n id.val label hin)
      (Run.follow (inputStage id hin)
        (Run.follow (oneStage id hin)
          (Run.follow (arithmeticStage id hin)
            (Run.follow (fixedStage id hin) (checkoutStage id hin))))))

theorem output_ready (n id label : Nat) :
    PhysicalGreedyHeaderInstall.Ready n id label (fun j => outputData n id label (checkoutBanks j)) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have outside3 : ¬(checkoutBanks j).val < 3 := by change ¬ j.val < 3; omega
    have scratch : 11 ≤ (checkoutBanks j).val ∧ (checkoutBanks j).val < 17 := ⟨hj,j.isLt⟩
    simpa [outputData,wideData,outputValue,outside3,scratch] using outside_word (width n) 0

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateSetup
