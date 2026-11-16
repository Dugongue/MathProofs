import Mathproof.MinimumGenerationPhysicalGreedyHeaderInstall
import Mathproof.MinimumGenerationHeaderSetup

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateWidth

open SearchTransducer InputScan
open PhysicalGreedyHeaderInstall (outside_word wordAt)

set_option backward.isDefEq.respectTransparency false

abbrev W := TapeWiden.machine
abbrev B := Fin 3

def leftBanks : Fin W.workTapes ↪ B :=
  ⟨Fin.castLE (by decide), fun _ _ e => Fin.ext (congrArg (fun i : B => i.val) e)⟩

def rightBanks : Fin W.workTapes ↪ B :=
  ⟨Fin.natAdd 1, fun _ _ e => Fin.ext (Nat.add_left_cancel (congrArg (fun i : B => i.val) e))⟩

def copies (i : B) : Option B := if i=2 then some 1 else none

abbrev C := TapeInstall.machine (1 : B) copies

def same : B ↪ B := Function.Embedding.refl _

abbrev stages : Stages 3 6 3 where
  first := 0
  entry i := if i=1 then C.initialState.castLE (by decide) else W.initialState
  transition i := if i=0 then (W.relocateBanks leftBanks).transition
    else if i=1 then C.padTransition (by decide) same else (W.relocateBanks rightBanks).transition
  next i _ := if i=0 then some 1 else if i=1 then some 2 else none

abbrev machine := stages.machine

def content (src mid dst : List Bool) (i : B) : Int → Option Bool :=
  counterTape 0 (if i=0 then src else if i=1 then mid else dst)

def start (p : Int) (src prior : List Bool) (w : Nat) : machine.Config :=
  stages.tag 0 ⟨stages.entry 0,p,fun _ => 0,content src (encodeLabel w 0) [],prior⟩

private theorem cfgEq {P : SearchTransducer} (a b : P.Config)
    (hq : a.state=b.state) (hi : a.inputHead=b.inputHead) (hh : a.workHead=b.workHead)
    (hc : a.workCell=b.workCell) (ho : a.outputReversed=b.outputReversed) : a=b := by
  cases a
  cases b
  simp_all

private theorem copied (src : List Bool) (w : Nat) :
    TapeInstall.installed copies (content src (encodeLabel w 0) []) w =
      content src (encodeLabel w 0) (encodeLabel w 0) := by
  funext j
  fin_cases j
  · exact TapeInstall.installed_source _ _ _ _ (by decide)
  · exact TapeInstall.installed_source _ _ _ _ (by decide)
  · apply TapeInstall.installed_exact copies _ w 2 1 (by decide)
    intro p h
    change counterTape 0 [] p = counterTape 0 (encodeLabel w 0) p
    rw [HeaderSetup.counterTape_eq_marked, HeaderSetup.counterTape_eq_marked]
    have hblank : InputPosition.work [] p = none := by simp [InputPosition.work]
    rw [hblank]
    exact (outside_word w 0 p h).symm

/-- Expand the raw width into a reusable quadruple-width zero. The original
source template is preserved and no numeric header is supplied to the machine. -/
theorem execute (raw src prior : List Bool) (p : Int) (w : Nat)
    (width : src.length = w) (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length) :
    ∃ (ticks : Nat) (d : machine.Config),
      machine.BoundedSegment raw (4*w+1) (start p src prior w) d ticks ∧
      machine.step raw d = none ∧ d.workHead = (fun _ => 0) ∧
      d.inputHead = p ∧ d.outputReversed = prior ∧
      d.workCell = content src (encodeLabel (2*w) 0) (encodeLabel (4*w) 0) := by
  let z := encodeLabel w 0
  let zz := encodeLabel (2*w) 0
  let blank := content src z []
  let medium := content src zz []
  let both := content src zz zz
  let a := TapeWiden.startConfig p src z prior
  let b := TapeWiden.stopLabelConfig p src prior w 0
  let c := TapeInstall.start 1 copies p medium prior
  let d := TapeInstall.stop 1 copies p medium prior (2*w)
  let e := TapeWiden.startConfig p zz zz prior
  let f := TapeWiden.stopLabelConfig p zz prior (2*w) 0
  let a' := W.bankConfig leftBanks a (fun _ => 0) blank
  let b' := W.bankConfig leftBanks b (fun _ => 0) blank
  let c' := C.padConfig (S := 6) (by decide) same (C.bankConfig same c (fun _ => 0) medium)
  let d' := C.padConfig (S := 6) (by decide) same (C.bankConfig same d (fun _ => 0) medium)
  let e' := W.bankConfig rightBanks e (fun _ => 0) both
  let f' := W.bankConfig rightBanks f (fun _ => 0) both
  obtain ⟨A,SA⟩ := TapeWiden.executeWidenLabel raw src prior p w 0 bounds width (Nat.two_pow_pos _)
  obtain ⟨D,SD⟩ := TapeWiden.executeWidenLabel raw zz prior p (2*w) 0 bounds
    (length_encodeLabel _ _) (Nat.two_pow_pos _)
  have med : medium 1 = InputPosition.work zz := HeaderSetup.counterTape_eq_marked _
  obtain ⟨Crun,Cstop⟩ := TapeInstall.execute 1 copies (by decide) raw zz prior p medium med bounds
  have ww : zz.length = 2*w := length_encodeLabel _ _
  rw [ww] at Crun Cstop
  have ra := W.relocateBanks_segment leftBanks (PhysicalEntry.segment_mono A (by omega :
      2*w+1 ≤ 4*w+1)) (heads := fun _ => 0) (cells := blank) (by simp)
  have rc := C.padMachine_segment (S := 6) (by decide) same
    (C.relocateBanks_segment same (PhysicalEntry.segment_mono Crun (by omega : 2*w+1 ≤ 4*w+1))
      (heads := fun _ => 0) (cells := medium) (by simp))
  have rd := W.relocateBanks_segment rightBanks (PhysicalEntry.segment_mono D (by omega :
      2*(2*w)+1 ≤ 4*w+1)) (heads := fun _ => 0) (cells := both) (by simp)
  change (stages.component 0).BoundedSegment raw (4*w+1) a' b' _ at ra
  change (stages.component 1).BoundedSegment raw (4*w+1) c' d' _ at rc
  change (stages.component 2).BoundedSegment raw (4*w+1) e' f' _ at rd
  have init : a' = (⟨stages.entry 0,p,fun _ => 0,blank,prior⟩ : (stages.component 0).Config) := by
    apply cfgEq
    · rfl
    · rfl
    · funext j
      fin_cases j <;> rfl
    · funext j
      fin_cases j <;> rfl
    · rfl
  rw [init] at ra
  have j1 : stages.enter (i := 0) 1 b' = c' := by
    apply cfgEq
    · rfl
    · rfl
    · funext j
      fin_cases j <;> rfl
    · funext j
      fin_cases j <;> rfl
    · rfl
  rw [← j1] at rc
  have eqD : d'.workCell = both := by
    have eq := copied src (2*w)
    funext j
    have val := C.bankConfig_cell_image same d (fun _ => 0) medium j
    exact val.trans (congrFun eq j)
  have j2 : stages.enter (i := 1) 2 d' = e' := by
    apply cfgEq
    · rfl
    · rfl
    · funext j
      fin_cases j <;> rfl
    · rw [show (stages.enter (i := 1) 2 d').workCell = d'.workCell from rfl,eqD]
      funext j
      fin_cases j <;> rfl
    · rfl
  rw [← j2] at rd
  have sa : (stages.component 0).step raw b' = none := by
    change (W.relocateBanks leftBanks).step raw (W.bankConfig leftBanks b (fun _ => 0) blank) = none
    rw [W.relocateBanks_step, SA]
    rfl
  have sc : (stages.component 1).step raw d' = none := by
    change (C.padMachine (S := 6) (by decide) same).step raw d' = none
    unfold d'
    rw [C.padMachine_step,C.relocateBanks_step,Cstop]
    rfl
  have sd : (stages.component 2).step raw f' = none := by
    change (W.relocateBanks rightBanks).step raw (W.bankConfig rightBanks f (fun _ => 0) both) = none
    rw [W.relocateBanks_step,SD]
    rfl
  have route := Stages.Routed.call (T := stages) ra sa (show stages.next 0 b'.state = some 1 by rfl)
    (Stages.Routed.call rc sc (show stages.next 1 d'.state = some 2 by rfl) (.finish rd))
  obtain ⟨run,halt⟩ := stages.routed_stop route sd rfl
  refine ⟨_,stages.tag 2 f',run,halt,?_,rfl,rfl,?_⟩
  · funext j
    fin_cases j <;> rfl
  · have hw : 2*(2*w) = 4*w := by omega
    funext j
    fin_cases j <;> first | rfl | exact congrArg (counterTape 0) (congrArg (fun x => encodeLabel x 0) hw)

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateWidth
