import Mathproof.MinimumGenerationCayleyQueryDispatchInstall

namespace Mathproof.MinimumGeneration.CayleyQueryDispatch.Division

open SearchTransducer
open InputPosition (work)
open Lax51Proofs.RamToTM (subBits)

set_option backward.isDefEq.respectTransparency false

def divisor : Fin 4 := 0
def remainder : Fin 4 := 1
def trial : Fin 4 := 2
def quotient : Fin 4 := 3

private abbrev subtract := RankPhysicalSubtract.machine
private def copies (i : Fin 4) : Option (Fin 4) := if i = remainder then some trial else none
private abbrev install := TapeInstall.machine divisor copies
private abbrev inc := TapeArithmetic.machine quotient .increment

private def pieces (i : Fin 3) : SearchTransducer :=
  if i = 0 then subtract else if i = 1 then install else inc

private theorem pieceSize (i : Fin 3) : (pieces i).states ≤ 7 := by
  fin_cases i <;> decide

private def subBanks : Fin 2 ↪ Fin 4 where
  toFun i := if i = 0 then divisor else trial
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | contradiction

private theorem workSize (i : Fin 3) : (pieces i).workTapes = if i = 0 then 2 else 4 := by
  fin_cases i <;> decide

private def castBanks {a b : ℕ} (h : a = b) : Fin a ↪ Fin b :=
  ⟨Fin.cast h, fun _ _ e => Fin.ext (congrArg (fun u : Fin b => u.val) e)⟩

private def banks (i : Fin 3) : Fin (pieces i).workTapes ↪ Fin 4 :=
  if h : i = 0 then (castBanks (by rw [workSize, if_pos h])).trans subBanks
  else castBanks (by rw [workSize, if_neg h])

private def afterPhase (i : Fin 3) (q : Fin (pieces i).states) : Option (Fin 3) :=
  if i = 0 then
    if q.val = (RankPhysicalSubtract.done true).val then none else some 1
  else if i = 1 then some 2 else some 0

/-- One bounded division cycle. The failed subtraction modifies only the
scratch register; the last successful remainder remains on its own bank. -/
abbrev stages : Stages 3 7 4 := Stages.ofMachines 0 pieces pieceSize banks afterPhase

abbrev machine := stages.machine

private def layout (w m r q : ℕ) (candidate : List Bool) (j : Fin 4) : Int → Option Bool :=
  if j = divisor then work (encodeLabel w m)
  else if j = remainder then work (encodeLabel w r)
  else if j = trial then work candidate
  else work (encodeLabel w q)

private def frame (i : Fin 3) (s : Fin 7) (input : Int) (out : List Bool)
    (cells : Fin 4 → Int → Option Bool) : (stages.component i).Config :=
  ⟨s, input, fun _ => 0, cells, out⟩

private def beginCycle (w m r q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 0).Config :=
  frame 0 0 input out (layout w m r q (encodeLabel w r))

def start (w m r q : ℕ) (input : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (beginCycle w m r q input out)

private def trialBits (w r m : ℕ) :=
  subBits (encodeLabel w r) (encodeLabel w m) false

private def endTest (w m r q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 0).Config :=
  frame 0 ((RankPhysicalSubtract.done (decide (r < m))).castLE (by decide))
    input out (layout w m r q (trialBits w r m))

private def installEntry (w m r q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 1).Config :=
  frame 1 0 input out (layout w m r q (encodeLabel w (r-m)))

private def installExit (w m r q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 1).Config :=
  frame 1 3 input out (layout w m (r-m) q (encodeLabel w (r-m)))

private def incEntry (w m u q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 2).Config :=
  frame 2 0 input out (layout w m u q (encodeLabel w u))

private def incExit (w m u q : ℕ) (input : Int) (out : List Bool) :
    (stages.component 2).Config :=
  frame 2 4 input out (layout w m u (q+1) (encodeLabel w u))

private theorem eqConfig {M : SearchTransducer} (a b : M.Config)
    (state : a.state = b.state) (input : a.inputHead = b.inputHead)
    (heads : a.workHead = b.workHead) (cells : a.workCell = b.workCell)
    (output : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private def tagNative (i : Fin 3) (c : (pieces i).Config) (cells : Fin 4 → Int → Option Bool) :
    (stages.component i).Config :=
  (pieces i).padConfig (pieceSize i) (banks i)
    ((pieces i).bankConfig (banks i) c (fun _ => 0) cells)

private theorem tagNative_eq {i : Fin 3} (c : (pieces i).Config)
    (old new : Fin 4 → Int → Option Bool)
    (heads : ∀ j, c.workHead j = 0)
    (bits : ∀ j, c.workCell j = new (banks i j))
    (keep : ∀ j ∉ Set.range (banks i), old j = new j) :
    tagNative i c old = frame i (c.state.castLE (pieceSize i)) c.inputHead c.outputReversed new := by
  refine eqConfig (tagNative i c old) (frame i _ _ _ new) rfl rfl ?_ ?_ rfl
  · funext j
    by_cases hj : j ∈ Set.range (banks i)
    · obtain ⟨k, rfl⟩ := hj
      exact (bankConfig_head_image (pieces i) (banks i) c (fun _ => 0) old k).trans (heads k)
    · exact (bankConfig_frame (pieces i) (banks i) c (fun _ => 0) old hj).1
  · funext j
    by_cases hj : j ∈ Set.range (banks i)
    · obtain ⟨k, rfl⟩ := hj
      exact (bankConfig_cell_image (pieces i) (banks i) c (fun _ => 0) old k).trans (bits k)
    · exact (bankConfig_frame (pieces i) (banks i) c (fun _ => 0) old hj).2.trans (keep j hj)

private theorem nativeSegment (i : Fin 3) {word : List Bool} {B k : ℕ} {c d : (pieces i).Config}
    (cells : Fin 4 → Int → Option Bool) (run : (pieces i).BoundedSegment word B c d k) :
    (stages.component i).BoundedSegment word B (tagNative i c cells) (tagNative i d cells) k :=
  (pieces i).padMachine_segment (pieceSize i) (banks i)
    (relocateBanks_segment (pieces i) (banks i) (heads := fun _ => 0) (cells := cells) run (by simp))

private theorem nativeHalt (i : Fin 3) {word : List Bool} {c : (pieces i).Config}
    (cells : Fin 4 → Int → Option Bool) (halt : (pieces i).step word c = none) :
    (stages.component i).step word (tagNative i c cells) = none := by
  have relocated := relocateBanks_step (pieces i) (banks i) word c (fun _ => 0) cells
  have rh := relocated.trans (congrArg _ halt)
  exact (padMachine_step (pieces i) (pieceSize i) (banks i) word _).trans (congrArg _ rh)

private theorem relabeledTrial (w r m : ℕ) (fit : r < 2^w) (ge : m ≤ r) :
    trialBits w r m = encodeLabel w (r-m) := by
  unfold trialBits
  rw [← RankPhysicalSubtract.fixedBits_eq_encodeLabel w r fit,
    ← RankPhysicalSubtract.fixedBits_eq_encodeLabel w m (ge.trans_lt fit),
    ← Lax51Proofs.RamToTM.fixedBits_sub_of_le w ge,
    RankPhysicalSubtract.fixedBits_eq_encodeLabel w (r-m) ((Nat.sub_le _ _).trans_lt fit)]

private theorem leftPhase {word : List Bool} {input : Int} {out : List Bool} {w m r q : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length) (hm : m < 2^w) (hr : r < 2^w) :
    let c := beginCycle w m r q input out
    let d := endTest w m r q input out
    (stages.component 0).BoundedSegment word (w+1) c d (2*w+3) ∧
    (stages.component 0).step word d = none := by
  let c := RankPhysicalSubtract.cfg 0 0 (encodeLabel w r) (encodeLabel w m) out input
  let d := RankPhysicalSubtract.cfg (RankPhysicalSubtract.done (decide (r<m))) 0
    (trialBits w r m) (encodeLabel w m) out input
  have run : (pieces 0).BoundedSegment word (w+1) c d (2*w+3) :=
    (RankPhysicalSubtract.execute_encoded word out input w r m ib hr hm).1
  have stop : (pieces 0).step word d = none :=
    (RankPhysicalSubtract.execute_encoded word out input w r m ib hr hm).2
  let old := layout w m r q (encodeLabel w r)
  let new := layout w m r q (trialBits w r m)
  have ec : tagNative 0 c old = beginCycle w m r q input out :=
    tagNative_eq (i := 0) c old old (by intro; rfl) (by intro j; fin_cases j <;> rfl) (by intros; rfl)
  have ed : tagNative 0 d old = endTest w m r q input out := by
    apply tagNative_eq (i := 0) d old new (by intro; rfl) (by intro j; fin_cases j <;> rfl)
    intro j hj
    have ne : j ≠ trial := by intro h; subst j; exact hj ⟨(1 : Fin 2),rfl⟩
    simp only [old, new, layout, if_neg ne]
  have step := nativeSegment 0 old run
  have halt := nativeHalt 0 old stop
  rw [ec, ed] at step
  rw [ed] at halt
  exact ⟨step,halt⟩

private theorem encLength (w n : ℕ) : (encodeLabel w n).length = w := by simp [encodeLabel]

private theorem workOutside {xs : List Bool} {p : Int}
    (h : p < 1 ∨ (xs.length : Int) < p) : work xs p = none := by
  unfold work
  by_cases h0 : p ≤ 0
  · simp [h0]
  · rw [if_neg h0]
    exact List.getElem?_eq_none (by omega)

private theorem installPhase {word : List Bool} {input : Int} {out : List Bool} {w m r q : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    let c := installEntry w m r q input out
    let d := installExit w m r q input out
    (stages.component 1).BoundedSegment word (w+1) c d (w+2+w+1) ∧
    (stages.component 1).step word d = none := by
  let old := layout w m r q (encodeLabel w (r-m))
  let new := layout w m (r-m) q (encodeLabel w (r-m))
  obtain ⟨run, halt⟩ := TapeInstall.execute divisor copies (by decide) word
    (encodeLabel w m) out input old rfl ib
  rw [encLength] at run halt
  let c : (pieces 1).Config := TapeInstall.start divisor copies input old out
  let d : (pieces 1).Config := TapeInstall.stop divisor copies input old out w
  have ec : tagNative 1 c old = installEntry w m r q input out := by
    apply tagNative_eq c old old (by intro; rfl) (by intro; rfl) (by intros; rfl)
  have ed : tagNative 1 d old = installExit w m r q input out := by
    apply tagNative_eq d old new (by intro; rfl) _ (fun j hj => (hj ⟨j,rfl⟩).elim)
    intro j
    change TapeInstall.installed copies old w j = new j
    by_cases h : j = remainder
    · subst j
      change TapeInstall.installed copies old w remainder = work (encodeLabel w (r-m))
      exact installedLabel copies old remainder trial le_rfl rfl rfl
        (fun p hp => workOutside (by simpa only [encLength] using hp))
    · exact (TapeInstall.installed_source copies old w j (by simp [copies,h])).trans (by
        simp only [new, old, layout, if_neg h])
  have seg := nativeSegment 1 old run
  have stop := nativeHalt 1 old halt
  rw [ec,ed] at seg
  rw [ed] at stop
  exact ⟨seg,stop⟩

private theorem workBlock (xs : List Bool) : TapeArithmetic.block (work xs) 1 xs := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem writeExact (w q : ℕ) (cell : Int → Option Bool)
    (bits : TapeArithmetic.block cell 1 (encodeLabel w (q+1)))
    (preserved : ∀ p, p < 1 ∨ (w : Int) + 1 ≤ p → cell p = work (encodeLabel w q) p) :
    cell = work (encodeLabel w (q+1)) := by
  funext p
  by_cases h : p < 1 ∨ (w : Int) + 1 ≤ p
  · rw [preserved p h]
    have range : p < 1 ∨ (w : Int) < p := by omega
    rw [workOutside (by simpa only [encLength] using range),
      workOutside (by simpa only [encLength] using range)]
  · let i : Fin (encodeLabel w (q+1)).length :=
      ⟨(p-1).toNat, by rw [encLength]; omega⟩
    have hp : (1 : Int) + i.val = p := by dsimp [i]; omega
    rw [← hp]
    exact (bits i).trans ((workBlock _) i).symm

private theorem incrementPhase {word : List Bool} {input : Int} {out : List Bool} {w m r q : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length) :
    let c := incEntry w m r q input out
    let d := incExit w m r q input out
    (stages.component 2).BoundedSegment word (w+1) c d (2*w+3) ∧
    (stages.component 2).step word d = none := by
  let old := layout w m r q (encodeLabel w r)
  let new := layout w m r (q+1) (encodeLabel w r)
  let c : inc.Config := ⟨0,input,fun _ => 0,old,out⟩
  have left : old quotient 0 = none := rfl
  have right : old quotient (0 + w + 1) = none := by
    change work (encodeLabel w q) (0 + w + 1) = none
    apply workOutside
    rw [encLength]
    omega
  obtain ⟨d, run, state, restored, bits, keep⟩ :=
    TapeArithmetic.executeIncrement word c w q rfl left right (workBlock _)
  have heads : ∀ j, d.workHead j = 0 := by
    intro j
    by_cases h : j = quotient
    · subst j
      exact restored
    · exact keep.heads j h
  have cells : ∀ j, d.workCell j = new j := by
    intro j
    by_cases h : j = quotient
    · subst j
      apply writeExact w q
      · exact bits
      · intro p hp
        exact keep.cells quotient p (.inr (by simpa [c] using hp))
    · have eq : d.workCell j = old j := by funext p; exact keep.cells j p (.inl h)
      rw [eq]
      fin_cases j <;> first | rfl | contradiction
  have clock : ∀ (p : Int), (0 : Int) ≤ p → p ≤ 0 + w + 1 → p.natAbs ≤ w + 1 := by
    intro p lo hi
    omega
  have bseg : inc.BoundedSegment word (w+1) c d (2*w+3) :=
    TapeRegisters.arithmeticBoundedSegment run ib clock (by simp [c])
  have stop : inc.step word d = none := TapeArithmetic.step_done word d state
  have ec : tagNative 2 c old = incEntry w m r q input out := by
    apply tagNative_eq (i := 2) c old old (by intro; rfl) (by intro; rfl) (by intros; rfl)
  have ed : tagNative 2 d old = incExit w m r q input out := by
    have eq := tagNative_eq (i := 2) d old new heads (by intro j; exact cells j)
      (fun j hj => (hj ⟨j,rfl⟩).elim)
    rw [eq, state, keep.input, keep.output]
    rfl
  have seg := nativeSegment 2 old bseg
  have hs := nativeHalt 2 old stop
  rw [ec, ed] at seg
  rw [ed] at hs
  exact ⟨seg,hs⟩

/-- One successful subtract/update cycle, with every literal handoff charged. -/
theorem executeCycle {word : List Bool} {input : Int} {out : List Bool} {w m r q : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length) (hm : m < 2^w) (hr : r < 2^w)
    (ge : m ≤ r) :
    machine.BoundedSegment word (w+1) (start w m r q input out)
      (start w m (r-m) (q+1) input out) (6*w+12) := by
  obtain ⟨sub, subHalt⟩ := leftPhase (q := q) (out := out) ib hm hr
  obtain ⟨copy, copyHalt⟩ := installPhase (w := w) (m := m) (r := r) (q := q) (out := out) ib
  obtain ⟨inc, incHalt⟩ := incrementPhase (w := w) (m := m) (r := r-m) (q := q) (out := out) ib
  have ready₁ : stages.next 0 (endTest w m r q input out).state = some 1 := by
    have h := Stages.ofMachines_next_at 0 pieces pieceSize banks afterPhase 0
      (RankPhysicalSubtract.done (decide (r<m)))
    exact h.trans (by simp [afterPhase, pieces, RankPhysicalSubtract.done, Nat.not_lt.mpr ge])
  have ready₂ : stages.next 1 (installExit w m r q input out).state = some 2 := rfl
  have ready₃ : stages.next 2 (incExit w m (r-m) q input out).state = some 0 := rfl
  have jump₁ := stages.segment_handoff subHalt ready₁ (sub.2 _ le_rfl _ sub.1)
  have join₁ : stages.enter 1 (endTest w m r q input out) = installEntry w m r q input out := by
    unfold Stages.enter endTest installEntry frame
    rw [relabeledTrial w r m hr ge]
    rfl
  rw [join₁] at jump₁
  have jump₂ := stages.segment_handoff copyHalt ready₂ (copy.2 _ le_rfl _ copy.1)
  have jump₃ := stages.segment_handoff incHalt ready₃ (inc.2 _ le_rfl _ inc.1)
  have join₂ : stages.enter 2 (installExit w m r q input out) = incEntry w m (r-m) q input out := rfl
  have join₃ : stages.enter 0 (incExit w m (r-m) q input out) = beginCycle w m (r-m) (q+1) input out := rfl
  rw [join₂] at jump₂
  rw [join₃] at jump₃
  have chain := BoundedSegment.append _
    (BoundedSegment.append _
      (BoundedSegment.append _
        (BoundedSegment.append _
          (BoundedSegment.append _ (stages.segment_component 0 sub) jump₁)
            (stages.segment_component 1 copy)) jump₂) (stages.segment_component 2 inc)) jump₃
  have count : 2*w+3+1+(w+2+w+1)+1+(2*w+3)+1 = 6*w+12 := by omega
  rw [count] at chain
  exact chain

def finish (w m r q : ℕ) (input : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (endTest w m (r % m) (q + r / m) input out)

/-- Physical quotient and remainder on live encoded banks. Space depends on
the width, and the iteration count is the quotient. -/
theorem execute {word : List Bool} {input : Int} {out : List Bool} {w m r q : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (pos : 0 < m) (hm : m < 2^w) (hr : r < 2^w) :
    machine.BoundedSegment word (w+1) (start w m r q input out)
      (finish w m r q input out) (r / m * (6*w+12) + (2*w+3)) ∧
    machine.step word (finish w m r q input out) = none := by
  by_cases h : r < m
  · obtain ⟨run, halt⟩ := leftPhase (q := q) (out := out) ib hm hr
    have terminal : stages.next 0 (endTest w m r q input out).state = none := by
      have proof := Stages.ofMachines_next_at 0 pieces pieceSize banks afterPhase 0
        (RankPhysicalSubtract.done (decide (r<m)))
      exact proof.trans (by simp [afterPhase, pieces, RankPhysicalSubtract.done, h])
    have finalHalt := stages.step_halt 0 halt
    rw [terminal] at finalHalt
    exact ⟨by simpa [start, finish, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h] using stages.segment_component 0 run,
      by simpa [finish, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h] using finalHalt⟩
  · have ge : m ≤ r := Nat.le_of_not_gt h
    have first := executeCycle (q := q) (out := out) ib hm hr ge
    have hr' : r-m < 2^w := (Nat.sub_le _ _).trans_lt hr
    obtain ⟨rest, halt⟩ := execute (r := r-m) (q := q+1) (out := out) ib pos hm hr'
    have divNext : r / m = (r-m) / m + 1 := calc
      _ = (r-m+m)/m := congrArg (·/m) (Nat.sub_add_cancel ge).symm
      _ = _ := by rw [Nat.add_div_of_dvd_left (dvd_refl m), Nat.div_self pos]
    have modNext : r % m = (r-m) % m := calc
      _ = (r-m+m)%m := congrArg (·%m) (Nat.sub_add_cancel ge).symm
      _ = _ := by simp
    have finishEq : finish w m (r-m) (q+1) input out = finish w m r q input out := by
      unfold finish
      rw [divNext, modNext]
      congr 2
      omega
    rw [finishEq] at rest halt
    have combined := BoundedSegment.append _ first rest
    have ticks : 6*w+12 + ((r-m)/m*(6*w+12) + (2*w+3)) = r/m*(6*w+12) + (2*w+3) := by
      rw [divNext, Nat.add_mul, Nat.one_mul]
      omega
    rw [ticks] at combined
    exact ⟨combined, halt⟩
termination_by r
decreasing_by omega

/-- The literal output banks hold the mathematical quotient and remainder. -/
theorem finishSpec (w m r q : ℕ) (input : Int) (out : List Bool) :
    let c := finish w m r q input out
    c.workCell quotient = work (encodeLabel w (q+r/m)) ∧
    c.workCell remainder = work (encodeLabel w (r%m)) ∧
    c.inputHead = input ∧ c.outputReversed = out ∧ ∀ j, c.workHead j = 0 :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩


section Matrix

open Connectivity (AdjBits ustconCell ustconHeaderLength)

def rowOf {m : ℕ} (s : Fin m) (offset : Fin (m*m)) : Fin m :=
  ⟨offset.val / m, (Nat.div_lt_iff_lt_mul s.isLt.pos).2 offset.isLt⟩

def colOf {m : ℕ} (s : Fin m) (offset : Fin (m*m)) : Fin m :=
  ⟨offset.val % m, Nat.mod_lt _ s.isLt.pos⟩

/-- A raw graph matrix offset indexes the exact projective row and column,
using the same virtual encoding as the connectivity machine. -/
theorem matrixCell {m : ℕ} (bits : AdjBits (Fin m)) (s t : Fin m) (offset : Fin (m*m)) :
    ustconCell bits s t ((ustconHeaderLength s t + offset.val : ℕ) : Int) =
      .data (bits (rowOf s offset) (colOf s offset)) := by
  have coord : offset.val = (rowOf s offset).val * m + (colOf s offset).val := by
    simpa [rowOf, colOf, Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div offset.val m).symm
  unfold ustconCell
  have nonnegative : ¬ ((ustconHeaderLength s t + offset.val : ℕ) : Int) < 0 := by omega
  rw [if_neg nonnegative, Int.toNat_natCast,
    if_pos (Nat.add_lt_add_left offset.isLt (ustconHeaderLength s t))]
  have eq := Connectivity.ustconRead_matrix bits s t (rowOf s offset) (colOf s offset)
  exact congrArg InputCell.data ((congrArg (fun a => Connectivity.ustconRead bits s t
    (ustconHeaderLength s t + a)) coord).trans eq)

/-- The fixed finite machine reads a prepared matrix offset register and
returns the two literal coordinate registers. In a square matrix the divisor
loop makes fewer rounds than there are vertices. -/
theorem executeMatrix {m : ℕ} (s : Fin m) (offset : Fin (m*m))
    {word out : List Bool} {input : Int} {w : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (fit : m*m ≤ 2^w) (fitDiv : m < 2^w) :
    let c := finish w m offset.val 0 input out
    machine.BoundedSegment word (w+1) (start w m offset.val 0 input out) c
      ((rowOf s offset).val*(6*w+12) + (2*w+3)) ∧ machine.step word c = none ∧
    c.workCell quotient = work (encodeLabel w (rowOf s offset).val) ∧
    c.workCell remainder = work (encodeLabel w (colOf s offset).val) ∧
    c.inputHead = input ∧ c.outputReversed = out ∧ ∀ j, c.workHead j = 0 := by
  obtain ⟨run, halt⟩ := execute (q := 0) (out := out) ib s.isLt.pos fitDiv (offset.isLt.trans_le fit)
  obtain ⟨a,b,c,d,e⟩ := finishSpec w m offset.val 0 input out
  exact ⟨run,halt,by simpa only [rowOf, Nat.zero_add] using a, b,c,d,e⟩

/-- Strip the unary header from a shifted virtual address in one actual
physical subtractor run. The input bank is a disposable address copy. -/
theorem executeShiftedOffset {m : ℕ} (s t : Fin m) (offset : Fin (m*m))
    {word out : List Bool} {input : Int} {w : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (fit : ustconHeaderLength s t + offset.val + 1 < 2^w) :
    let header := ustconHeaderLength s t + 1
    let address := ustconHeaderLength s t + offset.val + 1
    let S := RankPhysicalSubtract.machine
    let c := RankPhysicalSubtract.cfg 0 0 (encodeLabel w address) (encodeLabel w header) out input
    let d := RankPhysicalSubtract.cfg (RankPhysicalSubtract.done false) 0
      (encodeLabel w offset.val) (encodeLabel w header) out input
    S.BoundedSegment word (w+1) c d (2*w+3) ∧ S.step word d = none := by
  have ge : ustconHeaderLength s t + 1 ≤ ustconHeaderLength s t + offset.val + 1 := by omega
  have delta : ustconHeaderLength s t + offset.val + 1 - (ustconHeaderLength s t + 1) =
      offset.val := by omega
  simpa only [delta] using RankPhysicalSubtract.execute_encoded_of_le word out input w _ _ ib fit ge

end Matrix


end Mathproof.MinimumGeneration.CayleyQueryDispatch.Division
