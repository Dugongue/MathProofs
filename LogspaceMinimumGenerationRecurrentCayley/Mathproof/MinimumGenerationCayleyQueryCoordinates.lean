import Mathproof.MinimumGenerationCayleyQueryDispatchOffset

namespace Mathproof.MinimumGeneration.CayleyQueryCoordinates

open SearchTransducer CayleyQueryDispatch
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private abbrev D := OffsetInstall.machine
private abbrev S := CayleyQueryDispatch.machine

def orderClock : Fin 10 := 5
def slot (u : Fin 5) : Fin 10 := Fin.natAdd 5 u
def narrow (u : Fin 5) : Fin 10 := Fin.castAdd 5 u

def wiring (j : Fin 10) : Option (Fin 10) :=
  if j = slot rowBank ∨ j = slot rowTrial then some 3
  else if j = slot colBank ∨ j = slot colTrial then some 1 else none

private abbrev I := TapeInstall.machine orderClock wiring

private def piece (i : Fin 3) : SearchTransducer := if i = 0 then D else if i = 1 then I else S
private theorem pieceCap (i : Fin 3) : (piece i).states ≤ 35 := by fin_cases i <;> decide
private theorem tapeCount (i : Fin 3) : (piece i).workTapes = if i = 1 then 10 else 5 := by
  fin_cases i <;> decide

private def castBanks {a b : ℕ} (h : a = b) : Fin a ↪ Fin b :=
  ⟨Fin.cast h, fun _ _ e => Fin.ext (congrArg (fun u : Fin b => u.val) e)⟩

private def low : Fin 5 ↪ Fin 10 := ⟨narrow, fun _ _ e => Fin.ext (congrArg (fun u : Fin 10 => u.val) e)⟩
private def high : Fin 5 ↪ Fin 10 := ⟨slot, fun _ _ e => Fin.ext (Nat.add_left_cancel (congrArg (fun u : Fin 10 => u.val) e))⟩

private def banks (i : Fin 3) : Fin (piece i).workTapes ↪ Fin 10 :=
  if h : i=1 then castBanks (by rw [tapeCount, if_pos h])
  else (castBanks (by rw [tapeCount, if_neg h])).trans (if i=0 then low else high)

private def advance (i : Fin 3) (_ : Fin (piece i).states) : Option (Fin 3) :=
  if i = 0 then some 1 else if i = 1 then some 2 else none

abbrev stages : Stages 3 35 10 := Stages.ofMachines 0 piece pieceCap banks advance
abbrev machine := stages.machine

private def placed (i : Fin 3) (c : (piece i).Config)
    (heads : Fin 10 → Int) (cells : Fin 10 → Int → Option Bool) : (stages.component i).Config :=
  (piece i).padConfig (pieceCap i) (banks i)
    ((piece i).bankConfig (banks i) c heads cells)

private theorem exactPhase (i : Fin 3) {word : List Bool} {B k : ℕ} {c d : (piece i).Config}
    (h : (piece i).BoundedSegment word B c d k) (stop : (piece i).step word d = none)
    (heads : Fin 10 → Int) (cells : Fin 10 → Int → Option Bool)
    (spare : ∀ j ∉ Set.range (banks i), (heads j).natAbs ≤ B) :
    (stages.component i).BoundedSegment word B (placed i c heads cells) (placed i d heads cells) k ∧
      (stages.component i).step word (placed i d heads cells) = none := by
  have l := relocateBanks_segment (piece i) (banks i) (heads := heads) (cells := cells) h spare
  have m := relocateBanks_step (piece i) (banks i) word d heads cells
  rw [stop] at m
  have endPad := (piece i).padMachine_step (pieceCap i) (banks i) word
    ((piece i).bankConfig (banks i) d heads cells)
  exact ⟨(piece i).padMachine_segment (pieceCap i) (banks i) l,
    endPad.trans (congrArg _ m)⟩

private theorem cfgEq {P : SearchTransducer} (a b : P.Config)
    (s : a.state = b.state) (p : a.inputHead = b.inputHead) (h : a.workHead = b.workHead)
    (z : a.workCell = b.workCell) (o : a.outputReversed = b.outputReversed) : a = b := by
  cases a
  cases b
  simp_all

private theorem handoffEq {i j : Fin 3} (d : (stages.component i).Config) (e : (piece j).Config)
    (ready : e.state = (piece j).initialState) (sameIn : d.inputHead = e.inputHead)
    (sameOut : d.outputReversed = e.outputReversed)
    (sameHeads : ∀ k, d.workHead (banks j k) = e.workHead k)
    (sameCells : ∀ k, d.workCell (banks j k) = e.workCell k) :
    stages.enter j d = placed j e d.workHead d.workCell := by
  refine cfgEq (stages.enter j d) (placed j e d.workHead d.workCell) ?_ sameIn ?_ ?_ sameOut
  · change (piece j).initialState.castLE (pieceCap j) = e.state.castLE (pieceCap j)
    rw [ready]
  · funext u
    change d.workHead u = ((piece j).bankConfig (banks j) e d.workHead d.workCell).workHead u
    by_cases hu : u ∈ Set.range (banks j)
    · obtain ⟨k,rfl⟩ := hu
      rw [bankConfig_head_image]
      exact sameHeads k
    · exact (bankConfig_frame _ _ _ _ _ hu).1.symm
  · funext u
    change d.workCell u = ((piece j).bankConfig (banks j) e d.workHead d.workCell).workCell u
    by_cases hu : u ∈ Set.range (banks j)
    · obtain ⟨k,rfl⟩ := hu
      rw [bankConfig_cell_image]
      exact sameCells k
    · exact (bankConfig_frame _ _ _ _ _ hu).2.symm

def seed (w n : ℕ) (j : Fin 10) : Int → Option Bool :=
  if j = orderClock then work (encodeLabel w n) else fun _ => none

def start (w n r : ℕ) (input : Int) (out : List Bool) : machine.Config :=
  stages.tag 0 (placed 0 (OffsetInstall.start w (n+n) (encodeLabel w r) input out)
    (fun _ => 0) (seed w n))

private theorem clockWidth (w n : ℕ) : (encodeLabel w n).length = w := by simp [encodeLabel]

private theorem sideCell (w n x y : ℕ) (input : Int) (out : List Bool) (i : Fin 5) :
    (CayleyQueryDispatch.start w n x y input out).workCell i =
      if i = orderBank then work (encodeLabel w n)
      else if i = rowBank ∨ i = rowTrial then work (encodeLabel w x) else work (encodeLabel w y) := by
  fin_cases i <;> rfl

private theorem sideHead (w n x y : ℕ) (input : Int) (out : List Bool) (i : Fin 5) :
    (CayleyQueryDispatch.start w n x y input out).workHead i = 0 := by
  fin_cases i <;> rfl

private theorem notLow (j : Fin 5) : slot j ∉ Set.range (banks 0) := by
  rintro ⟨k,h⟩
  have q := congrArg (fun i : Fin 10 => i.val) h
  have qk := k.isLt
  change k.val < 5 at qk
  change k.val = 5 + j.val at q
  omega

private theorem copyLayout (w n x y : ℕ) (input : Int) (out : List Bool)
    (old : Fin 10 → Int → Option Bool)
    (hold : ∀ i : Fin 5, old (slot i) = seed w n (slot i))
    (row : old 3 = work (encodeLabel w x)) (col : old 1 = work (encodeLabel w y)) :
    ∀ j : Fin 5,
      TapeInstall.installed wiring old w (slot j) =
        (CayleyQueryDispatch.start w n x y input out).workCell j := by
  intro j
  rw [sideCell]
  have empty (q : Fin 5) (h : q ≠ orderBank) (p : Int) : old (slot q) p = none := by
    rw [hold]
    unfold seed
    have different : slot q ≠ orderClock := by
      intro e
      apply h
      have qE := congrArg (fun i : Fin 10 => i.val) e
      change 5+q.val = 5 at qE
      exact Fin.ext (by change q.val = 0; omega)
    rw [if_neg different]
  fin_cases j
  · rw [TapeInstall.installed_source wiring old w _ (by decide)]
    exact hold (0 : Fin 5)
  · exact installedLabel wiring old _ (3 : Fin 10) le_rfl row (by decide)
      (fun p _ => empty 1 (by decide) p)
  · exact installedLabel wiring old _ (1 : Fin 10) le_rfl col (by decide)
      (fun p _ => empty 2 (by decide) p)
  · exact installedLabel wiring old _ (3 : Fin 10) le_rfl row (by decide)
      (fun p _ => empty 3 (by decide) p)
  · exact installedLabel wiring old _ (1 : Fin 10) le_rfl col (by decide)
      (fun p _ => empty 4 (by decide) p)

/-- A fixed raw matrix-coordinate controller divides the live offset, copies
both literal coordinates into the side registers, and obtains the exact
left and right label banks from the physical side transitions. -/
theorem execute {n : ℕ} (s : Fin (n+n)) (offset : Fin ((n+n)*(n+n)))
    {word out : List Bool} {input : Int} {w : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (fitM : n+n < 2^w) (fitOffset : (n+n)*(n+n) ≤ 2^w) :
    let row := Division.rowOf s offset
    let col := Division.colOf s offset
    ∃ (len : ℕ) (endCfg : (stages.component 2).Config),
      machine.BoundedSegment word (w+1) (start w n offset.val input out)
        (stages.tag 2 endCfg) len ∧ machine.step word (stages.tag 2 endCfg) = none ∧
      endCfg.inputHead = input ∧ endCfg.outputReversed = out ∧ (∀ j, endCfg.workHead j=0) ∧
      (match BipartiteCayley.endpoints row col with
      | none => (endCfg.state : Nat) =
          (CayleyQueryDispatch.finish w n row.val col.val input out).state.val ∧
          CayleyQueryDispatch.crossBanks (CayleyQueryDispatch.finish w n row.val col.val input out) = none
      | some (x,y) => ∃ a b : Fin 5,
          endCfg.state.val = (CayleyQueryDispatch.finish w n row.val col.val input out).state.val ∧
          CayleyQueryDispatch.crossBanks (CayleyQueryDispatch.finish w n row.val col.val input out) = some (a,b) ∧
          endCfg.workCell (slot a) = work (encodeLabel w x.val) ∧
          endCfg.workCell (slot b) = work (encodeLabel w y.val)) := by
  let row := Division.rowOf s offset
  let col := Division.colOf s offset
  let initial := seed w n
  let d := OffsetInstall.finish w (n+n) offset.val input out
  obtain ⟨dr,ds⟩ := OffsetInstall.execute (w := w) (m := n+n) (r := offset.val)
    (out := out) ib s.isLt.pos fitM (offset.isLt.trans_le fitOffset)
  obtain ⟨xWord,yWord,_,di,dout,dh⟩ := OffsetInstall.finishSpec w (n+n) offset.val input out
  obtain ⟨first,firstStop⟩ := exactPhase 0 dr ds (fun _ => 0) initial (by simp)
  let Dend := placed 0 d (fun _ => 0) initial
  have dhead (j : Fin 10) : Dend.workHead j = 0 := by
    by_cases hj : j ∈ Set.range (banks 0)
    · obtain ⟨k,rfl⟩ := hj
      exact (bankConfig_head_image (piece 0) (banks 0) d (fun _ => 0) initial k).trans (dh k)
    · exact (bankConfig_frame (piece 0) (banks 0) d (fun _ => 0) initial hj).1
  have hold (i : Fin 5) : Dend.workCell (slot i) = initial (slot i) :=
    (bankConfig_frame (piece 0) (banks 0) d (fun _ => 0) initial (notLow i)).2
  have rw₀ : Dend.workCell 3 = work (encodeLabel w row.val) :=
    (bankConfig_cell_image (piece 0) (banks 0) d (fun _ => 0) initial (3 : Fin 5)).trans xWord
  have cw₀ : Dend.workCell 1 = work (encodeLabel w col.val) :=
    (bankConfig_cell_image (piece 0) (banks 0) d (fun _ => 0) initial (1 : Fin 5)).trans yWord
  let c := TapeInstall.start orderClock wiring input Dend.workCell out
  let e := TapeInstall.stop orderClock wiring input Dend.workCell out w
  obtain ⟨cr,cs⟩ := TapeInstall.execute orderClock wiring (by decide) word (encodeLabel w n) out input
    Dend.workCell (hold orderBank) ib
  rw [clockWidth] at cr cs
  obtain ⟨second,secondStop⟩ := exactPhase 1 cr cs Dend.workHead Dend.workCell (by intro j _; rw [dhead]; simp)
  have firstJoin := handoffEq (i := 0) (j := 1) Dend c rfl di dout
    (by intro k; exact dhead k) (by intro; rfl)
  have firstRoute : stages.next 0 Dend.state = some 1 :=
    Stages.ofMachines_next_at 0 piece pieceCap banks advance 0 d.state
  have jump₁ := stages.segment_handoff (i := 0) (j := 1) firstStop firstRoute (first.2 _ le_rfl _ first.1)
  rw [firstJoin] at jump₁
  let Cend := placed 1 e Dend.workHead Dend.workCell
  have ehead (j : Fin 10) : Cend.workHead j = 0 :=
    bankConfig_head_image (piece 1) (banks 1) e Dend.workHead Dend.workCell j
  have ecell (j : Fin 10) : Cend.workCell j = TapeInstall.installed wiring Dend.workCell w j :=
    bankConfig_cell_image (piece 1) (banks 1) e Dend.workHead Dend.workCell j
  let q := CayleyQueryDispatch.start w n row.val col.val input out
  let z := CayleyQueryDispatch.finish w n row.val col.val input out
  have xfit := row.isLt.trans fitM
  have yfit := col.isLt.trans fitM
  obtain ⟨sr,ss⟩ := CayleyQueryDispatch.execute word out input w n row.val col.val ib
    ((Nat.le_add_right n n).trans_lt fitM) xfit yfit
  obtain ⟨sIn,sOut,sHead,_,_,_,_⟩ := CayleyQueryDispatch.finishSpec w n row.val col.val input out xfit yfit
  obtain ⟨third,thirdStop⟩ := exactPhase 2 sr ss Cend.workHead Cend.workCell (by intro j _; rw [ehead]; simp)
  have secondJoin := handoffEq (i := 1) (j := 2) Cend q rfl rfl rfl
    (by intro k; exact (ehead (slot k)).trans (sideHead w n row.val col.val input out k).symm)
    (by intro k; exact (ecell (slot k)).trans (copyLayout w n row.val col.val input out Dend.workCell hold rw₀ cw₀ k))
  have secondRoute : stages.next 1 Cend.state = some 2 :=
    Stages.ofMachines_next_at 0 piece pieceCap banks advance 1 e.state
  have jump₂ := stages.segment_handoff (i := 1) (j := 2) secondStop secondRoute (second.2 _ le_rfl _ second.1)
  rw [secondJoin] at jump₂
  let last := placed 2 z Cend.workHead Cend.workCell
  have endRoute : stages.next 2 last.state = none :=
    Stages.ofMachines_next_at 0 piece pieceCap banks advance 2 z.state
  have stop := stages.step_halt 2 thirdStop
  rw [endRoute] at stop
  have full := BoundedSegment.append _ (BoundedSegment.append _ (BoundedSegment.append _
    (BoundedSegment.append _ (stages.segment_component 0 first) jump₁)
      (stages.segment_component 1 second)) jump₂) (stages.segment_component 2 third)
  have lastHead (j : Fin 10) : last.workHead j = 0 := by
    by_cases hj : j ∈ Set.range (banks 2)
    · obtain ⟨k,rfl⟩ := hj
      exact (bankConfig_head_image (piece 2) (banks 2) z Cend.workHead Cend.workCell k).trans (sHead k)
    · exact (bankConfig_frame (piece 2) (banks 2) z Cend.workHead Cend.workCell hj).1.trans (ehead j)
  refine ⟨_, last, full, stop, sIn, sOut, lastHead, ?_⟩
  have ports := CayleyQueryDispatch.crossBanksSpec row col w fitM.le input out
  cases hx : BipartiteCayley.endpoints row col with
  | none => simpa only [hx] using (show last.state.val = z.state.val ∧
      CayleyQueryDispatch.crossBanks z = none from ⟨rfl, by simpa only [hx] using ports⟩)
  | some raw =>
    obtain ⟨x,y⟩ := raw
    simp only [hx] at ports ⊢
    obtain ⟨a,b,val,ha,hb⟩ := ports
    exact ⟨a,b,rfl,val,(bankConfig_cell_image (piece 2) (banks 2) z Cend.workHead Cend.workCell a).trans ha,
      (bankConfig_cell_image (piece 2) (banks 2) z Cend.workHead Cend.workCell b).trans hb⟩

private def neutralSide (q : Fin S.states) : S.Config :=
  ⟨q, 0, fun _ => 0, fun _ _ => none, []⟩

/-- Decode the two dynamically selected physical endpoint banks from the
literal terminal stage, without looking at the virtual coordinates. -/
def orientation (q : Fin machine.states) : Option (Fin 5 × Fin 5) :=
  let (i, c) := (finProdFinEquiv : Fin 3 × Fin 35 ≃ Fin machine.states).symm q
  if i = 2 then
    if h : c.val < S.states then CayleyQueryDispatch.crossBanks (neutralSide ⟨c.val,h⟩) else none
  else none

private theorem orientation_exact (c : (stages.component 2).Config) (side : S.Config)
    (hs : c.state.val = side.state.val) :
    orientation (stages.tag 2 c).state = CayleyQueryDispatch.crossBanks side := by
  have h : c.state.val < S.states := hs ▸ side.state.isLt
  simp only [orientation, Stages.tag, Equiv.symm_apply_apply, dif_pos h]
  have ht : (⟨c.state.val,h⟩ : Fin S.states) = side.state := Fin.ext hs
  rw [ht]
  rfl

/-- The literal work tape contents required for the coordinate machine. -/
def entryCells (w n r : ℕ) (j : Fin 10) : Int → Option Bool :=
  if h : j.val < 5 then OffsetInstall.live w (n+n) (encodeLabel w r) ⟨j.val,h⟩
  else seed w n j

theorem startSpec (w n r : ℕ) (input : Int) (out : List Bool) :
    let c := start w n r input out
    c.state = machine.initialState ∧ c.inputHead = input ∧ c.outputReversed = out ∧
      (∀ j, c.workHead j = 0) ∧ c.workCell = entryCells w n r := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl

theorem executeLive {n : ℕ} (s : Fin (n+n)) (offset : Fin ((n+n)*(n+n)))
    {word out : List Bool} {input : Int} {w : ℕ}
    (ib : (-1 : Int) ≤ input ∧ input ≤ word.length)
    (fitM : n+n < 2^w) (fitOffset : (n+n)*(n+n) ≤ 2^w) :
    let row := Division.rowOf s offset
    let col := Division.colOf s offset
    ∃ (len : ℕ) (d : machine.Config),
      machine.BoundedSegment word (w+1) (start w n offset.val input out) d len ∧
      machine.step word d = none ∧ d.inputHead = input ∧ d.outputReversed = out ∧
      (∀ j, d.workHead j = 0) ∧
      match BipartiteCayley.endpoints row col with
      | none => orientation d.state = none
      | some (x,y) => ∃ a b, orientation d.state = some (a,b) ∧
        d.workCell (slot a) = work (encodeLabel w x.val) ∧
        d.workCell (slot b) = work (encodeLabel w y.val) := by
  let row := Division.rowOf s offset
  let col := Division.colOf s offset
  let native := CayleyQueryDispatch.finish w n row.val col.val input out
  obtain ⟨len,c,run,stop,head,outEq,heads,ports⟩ := execute s offset ib fitM fitOffset
  refine ⟨len,stages.tag 2 c,run,stop,head,outEq,heads,?_⟩
  cases kind : BipartiteCayley.endpoints (Division.rowOf s offset) (Division.colOf s offset) with
  | none =>
    obtain ⟨stateEq,ret⟩ := (by simpa only [kind] using ports :
      c.state.val = native.state.val ∧ CayleyQueryDispatch.crossBanks native = none)
    simpa only [kind] using (orientation_exact c native stateEq).trans ret
  | some e =>
    obtain ⟨x,y⟩ := e
    simp only [kind] at ports ⊢
    obtain ⟨a,b,stateEq,ret,xLabel,yLabel⟩ := ports
    exact ⟨a,b,(orientation_exact c native stateEq).trans ret,xLabel,yLabel⟩


end Mathproof.MinimumGeneration.CayleyQueryCoordinates
