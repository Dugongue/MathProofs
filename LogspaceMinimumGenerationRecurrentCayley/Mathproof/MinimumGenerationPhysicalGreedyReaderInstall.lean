import Mathproof.MinimumGenerationPhysicalGreedyTemplateCompose
import Mathproof.MinimumGenerationCayleyReaderClock
import Mathproof.MinimumGenerationParkOrigin

namespace Mathproof.MinimumGeneration.PhysicalGreedyReaderInstall

open SearchTransducer PhysicalGreedyTemplateProgram
open PhysicalGreedyTemplateCompose (Memory Run lift liftRun cfg configEq)
open PhysicalGreedyHeaderInstall (wordAt)
open InputPosition (work)
open Mathproof.Multitape.Locality (moveOffset)

set_option backward.isDefEq.respectTransparency false

variable {W : Nat}

private def sameBanks : Fin W ↪ Fin W := Function.Embedding.refl _

def copied (plan : Fin W → Option (Fin W)) (old : Memory W) : Memory W :=
  fun i => (plan i).elim (old i) old

abbrev copyMachine (clock : Fin W) (plan : Fin W → Option (Fin W)) : Machine W :=
  lift (TapeInstall.machine clock plan) sameBanks

theorem copyRun (clock : Fin W) (plan : Fin W → Option (Fin W))
    {word prior : List Bool} {input : Int} {old : Memory W} (bits : List Bool)
    (readClock : old clock = work bits) (clockOnly : plan clock = none)
    (inputLegal : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (frame : ∀ i j, plan i = some j → ∀ p, p<1 ∨ (bits.length : Int)<p → old i p = old j p) :
    Run (copyMachine clock plan) word (bits.length+1) input prior old (copied plan old) := by
  obtain ⟨r,h⟩ := TapeInstall.execute clock plan clockOnly word bits prior input old readClock inputLegal
  refine liftRun (TapeInstall.machine clock plan) sameBanks r h rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) ?_ (fun i hi => False.elim (hi ⟨i,rfl⟩))
  intro i
  change TapeInstall.installed plan old bits.length i = copied plan old i
  cases e : plan i with
  | none => exact (TapeInstall.installed_source _ _ _ _ e).trans (by simp [copied,e])
  | some j => exact (TapeInstall.installed_exact _ _ _ _ _ e (frame i j e)).trans (by simp [copied,e])

abbrev widenMachine (banks : Fin 2 ↪ Fin W) : Machine W := lift TapeWiden.machine banks

def widened (banks : Fin 2 ↪ Fin W) (old : Memory W) (w value : Nat) :=
  Function.update old (banks 1) (wordAt (2*w) value)

theorem widenRun (banks : Fin 2 ↪ Fin W) {word prior : List Bool} {input : Int}
    {old : Memory W} (w value : Nat) (template : List Bool) (hLen : template.length=w)
    (hSrc : old (banks 0)=work template) (hDst : old (banks 1)=wordAt w value)
    (fit : value < 2^w) (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    Run (widenMachine banks) word (2*w+1) input prior old (widened banks old w value) := by
  obtain ⟨run,stop⟩ := TapeWiden.executeWidenLabel word template prior input w value hin hLen fit
  have different : banks 0 ≠ banks 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (banks.injective h)
  have ha : (TapeWiden.startConfig input template (encodeLabel w value) prior).workHead = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  have hb : (TapeWiden.stopLabelConfig input template prior w value).workHead = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  refine liftRun TapeWiden.machine banks run stop rfl rfl rfl ha hb rfl rfl ?_ ?_ ?_
  · intro j
    fin_cases j
    · exact (HeaderSetup.counterTape_eq_marked template).trans hSrc.symm
    · exact (HeaderSetup.counterTape_eq_marked (encodeLabel w value)).trans hDst.symm
  · intro j
    fin_cases j
    · exact (HeaderSetup.counterTape_eq_marked template).trans
        (by simpa [widened,different] using hSrc.symm)
    · change InputScan.counterTape 0 (encodeLabel (2*w) value) = widened banks old w value (banks 1)
      simpa [widened,wordAt] using HeaderSetup.counterTape_eq_marked (encodeLabel (2*w) value)
  · intro j no
    have neq : j ≠ banks 1 := fun h => no ⟨1,h.symm⟩
    simp [widened,neq]

/-- Mark every selected companion tape at its parked head without moving
any tape. Unselected work tapes and the input/output stay unchanged. -/
def marking (select : Fin W → Bool) : SearchTransducer where
  states := 2
  workTapes := W
  initialState := 0
  transition q _ _ :=
    if q=0 then some (1,.stay,fun i => ⟨if select i then some (some true) else none,.stay⟩,none)
    else none

abbrev markMachine (select : Fin W → Bool) : Machine W := ⟨marking select,rfl⟩

def marked (select : Fin W → Bool) (old : Memory W) : Memory W :=
  fun i p => if select i && decide (p=0) then some true else old i p

theorem markRun (select : Fin W → Bool) {word prior : List Bool} {input : Int}
    (old : Memory W) (B : Nat) (hin : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    Run (markMachine select) word B input prior old (marked select old) := by
  let M := markMachine select
  let a := cfg M (0 : Fin 2) input prior old
  let d := cfg M (1 : Fin 2) input prior (marked select old)
  have run : M.native.step word a = some d := by
    unfold SearchTransducer.step
    change some _ = some d
    apply congrArg some
    apply configEq
    · rfl
    · simp [a,d,cfg,moveOffset]
    · funext i
      simp [a,d,cfg,moveOffset]
    · funext i p
      have useBank (i : Fin M.native.workTapes) : M.banks i = i := rfl
      by_cases k : select i <;> by_cases h : p=0 <;>
        simp [a,d,cfg,useBank,marked,k,h]
    · rfl
  have halt : M.native.step word d = none := rfl
  refine ⟨1,(1 : Fin 2),⟨run,?_⟩,halt⟩
  intro k hk e h
  have k' : k=0 ∨ k=1 := by omega
  rcases k' with rfl | rfl
  · change some a = some e at h
    cases h
    exact ⟨hin.1,hin.2,by simp [a,cfg]⟩
  · change M.native.step word a = some e at h
    rw [run] at h
    cases h
    exact ⟨hin.1,hin.2,by simp [d,cfg]⟩

end Mathproof.MinimumGeneration.PhysicalGreedyReaderInstall
