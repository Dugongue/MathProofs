import Mathproof.MinimumGenerationCayleyQueryDispatchDivision

namespace Mathproof.MinimumGeneration.CayleyQueryDispatch.OffsetInstall

open SearchTransducer
open InputPosition (work)
open Division

set_option backward.isDefEq.respectTransparency false

private def clock : Fin 5 := 0
def offsetBank : Fin 5 := 4
private def wiring (j : Fin 5) : Option (Fin 5) :=
  if j = (1 : Fin 5) ∨ j = 2 then some offsetBank else none

private abbrev Copy := TapeInstall.machine clock wiring
private def copyBanks : Fin 5 ↪ Fin 5 := Function.Embedding.refl _
private def divBanks : Fin 4 ↪ Fin 5 := ⟨Fin.castSucc, Fin.castSucc_injective _⟩

abbrev machine := thenMachine Copy Division.machine copyBanks divBanks

def live (w m : ℕ) (offset : List Bool) (i : Fin 5) : Int → Option Bool :=
  if i = clock then work (encodeLabel w m)
  else if i = 3 then work (encodeLabel w 0)
  else if i = offsetBank then work offset else fun _ => none

def start (w m : ℕ) (offset : List Bool) (input : Int) (out : List Bool) : machine.Config :=
  let initial := live w m offset
  thenLeft Copy Division.machine copyBanks divBanks
    (Copy.bankConfig copyBanks (TapeInstall.start clock wiring input initial out)
      (fun _ => 0) initial)

def finish (w m r : ℕ) (input : Int) (out : List Bool) : machine.Config :=
  let initial := live w m (encodeLabel w r)
  thenRight Copy Division.machine copyBanks divBanks
    (Division.machine.bankConfig divBanks (Division.finish w m r 0 input out)
      (fun _ => 0) initial)

private theorem sameConfig {P : SearchTransducer} (a b : P.Config)
    (hs : a.state = b.state) (hi : a.inputHead = b.inputHead) (hh : a.workHead = b.workHead)
    (hc : a.workCell = b.workCell) (ho : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem clockLen (w m : ℕ) : (encodeLabel w m).length = w := by simp [encodeLabel]

private theorem installCell (w m r : ℕ) (j : Fin 4) :
    TapeInstall.installed wiring (live w m (encodeLabel w r)) w (divBanks j) =
      (Division.start w m r 0 0 []).workCell j := by
  let old := live w m (encodeLabel w r)
  fin_cases j
  · exact TapeInstall.installed_source wiring old w _ (by decide)
  · exact installedLabel wiring old (1 : Fin 5) offsetBank le_rfl rfl rfl (by intros; rfl)
  · exact installedLabel wiring old (2 : Fin 5) offsetBank le_rfl rfl rfl (by intros; rfl)
  · exact TapeInstall.installed_source wiring old w _ (by decide)

private theorem join (w m r : ℕ) (input : Int) (out : List Bool) :
    let old := live w m (encodeLabel w r)
    let copyExit := Copy.bankConfig copyBanks (TapeInstall.stop clock wiring input old out w)
      (fun _ => 0) old
    thenEntry Copy Division.machine copyBanks divBanks copyExit =
      Division.machine.bankConfig divBanks (Division.start w m r 0 input out) (fun _ => 0) old := by
  intro old copyExit
  have outRange : offsetBank ∉ Set.range divBanks := by
    rintro ⟨j,h⟩
    have hr := congrArg (fun i : Fin 5 => i.val) h
    have hj := j.isLt
    change j.val = 4 at hr
    omega
  refine sameConfig _ _ rfl rfl ?_ ?_ rfl
  · funext j
    change copyExit.workHead j = _
    have h := bankConfig_head_image Copy copyBanks (TapeInstall.stop clock wiring input old out w) (fun _ => 0) old j
    change copyExit.workHead j = 0 at h
    rw [h]
    by_cases hz : j ∈ Set.range divBanks
    · obtain ⟨k,rfl⟩ := hz
      exact (bankConfig_head_image Division.machine divBanks (Division.start w m r 0 input out) (fun _ => 0) old k).symm
    · exact (bankConfig_frame Division.machine divBanks (Division.start w m r 0 input out) (fun _ => 0) old hz).1.symm
  · funext j
    have hx := bankConfig_cell_image Copy copyBanks (TapeInstall.stop clock wiring input old out w)
      (fun _ => 0) old j
    change copyExit.workCell j = TapeInstall.installed wiring old w j at hx
    change copyExit.workCell j = _
    rw [hx]
    by_cases hz : j ∈ Set.range divBanks
    · obtain ⟨k,rfl⟩ := hz
      rw [bankConfig_cell_image]
      exact installCell w m r k
    · have hj : j = offsetBank := by
        fin_cases j
        · exact (hz ⟨0,rfl⟩).elim
        · exact (hz ⟨1,rfl⟩).elim
        · exact (hz ⟨2,rfl⟩).elim
        · exact (hz ⟨3,rfl⟩).elim
        · rfl
      subst j
      exact (TapeInstall.installed_source wiring old w offsetBank (by decide)).trans
        (bankConfig_frame Division.machine divBanks (Division.start w m r 0 input out) (fun _ => 0) old outRange).2.symm

/-- One physical machine installs a live matrix-offset word into the two
division registers, then executes exact div/rem. -/
theorem execute {word out : List Bool} {input : Int} {w m r : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length) (positive : 0 < m)
    (fitM : m < 2^w) (fitR : r < 2^w) :
    machine.BoundedSegment word (w+1) (start w m (encodeLabel w r) input out)
      (finish w m r input out) ((w+2+w+1)+1+(r/m*(6*w+12)+(2*w+3))) ∧
    machine.step word (finish w m r input out) = none := by
  let old := live w m (encodeLabel w r)
  obtain ⟨copyRun, copyHalt⟩ :=
    TapeInstall.execute clock wiring (by decide) word (encodeLabel w m) out input old rfl ib
  rw [clockLen] at copyRun copyHalt
  obtain ⟨divRun, divHalt⟩ := Division.execute (q := 0) (out := out) ib positive fitM fitR
  have copy := relocateBanks_segment Copy copyBanks (heads := fun _ => 0) (cells := old)
    copyRun (by simp)
  have divide := relocateBanks_segment Division.machine divBanks (heads := fun _ => 0) (cells := old)
    divRun (by simp)
  rw [← join w m r input out] at divide
  have stopCopy := relocateBanks_step Copy copyBanks word
    (TapeInstall.stop clock wiring input old out w) (fun _ => 0) old
  rw [copyHalt] at stopCopy
  have stopDiv := relocateBanks_step Division.machine divBanks word
    (Division.finish w m r 0 input out) (fun _ => 0) old
  rw [divHalt] at stopDiv
  refine ⟨thenSegment Copy Division.machine copyBanks divBanks copy stopCopy divide, ?_⟩
  unfold finish
  rw [thenStep_right, stopDiv]
  rfl

/-- Literal output and preserved live offset after the composed execution. -/
theorem finishSpec (w m r : ℕ) (input : Int) (out : List Bool) :
    let c := finish w m r input out
    c.workCell (3 : Fin 5) = work (encodeLabel w (r/m)) ∧
    c.workCell (1 : Fin 5) = work (encodeLabel w (r%m)) ∧
    c.workCell offsetBank = work (encodeLabel w r) ∧
    c.inputHead = input ∧ c.outputReversed = out ∧ ∀ j, c.workHead j = 0 := by
  let c := Division.finish w m r 0 input out
  let old := live w m (encodeLabel w r)
  have hOut : offsetBank ∉ Set.range divBanks := by
    rintro ⟨j,h⟩
    have hr := congrArg (fun i : Fin 5 => i.val) h
    have hj := j.isLt
    change j.val = 4 at hr
    omega
  obtain ⟨hQuot,hRem,hInput,hOutput,hHeads⟩ := Division.finishSpec w m r 0 input out
  refine ⟨?_, ?_, ?_, hInput, hOutput, ?_⟩
  · change (Division.machine.bankConfig divBanks c (fun _ => 0) old).workCell
      (divBanks Division.quotient) = _
    rw [bankConfig_cell_image]
    simpa only [Nat.zero_add] using hQuot
  · change (Division.machine.bankConfig divBanks c (fun _ => 0) old).workCell
      (divBanks Division.remainder) = _
    rw [bankConfig_cell_image]
    exact hRem
  · change (Division.machine.bankConfig divBanks c (fun _ => 0) old).workCell offsetBank = _
    exact (bankConfig_frame _ _ _ _ _ hOut).2
  · intro j
    change (Division.machine.bankConfig divBanks c (fun _ => 0) old).workHead j = 0
    by_cases hz : j ∈ Set.range divBanks
    · obtain ⟨k,rfl⟩ := hz
      rw [bankConfig_head_image]
      exact hHeads k
    · exact (bankConfig_frame _ _ _ _ _ hz).1


end Mathproof.MinimumGeneration.CayleyQueryDispatch.OffsetInstall
