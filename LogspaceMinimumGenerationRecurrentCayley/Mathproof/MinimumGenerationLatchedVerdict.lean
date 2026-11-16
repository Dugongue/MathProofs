import Mathproof.MinimumGenerationTapeCompose

namespace Mathproof.MinimumGeneration.LatchedVerdict

open SearchTransducer

/-- Store a macro's last emitted bit in finite control while preserving the
external output. Three states distinguish an empty result from either bit. -/
def pack : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def unpack (i : Fin 3) : Option Bool :=
  if i = 0 then none else some (i = 2)

@[simp] theorem unpack_pack (bit : Option Bool) : unpack (pack bit) = bit := by
  cases bit with
  | none => rfl
  | some b => cases b <;> decide

variable (M : SearchTransducer)

/-- The same local machine, with silent output and a finite verdict register. -/
abbrev machine : SearchTransducer where
  states := M.states * 3
  workTapes := M.workTapes
  initialState := finProdFinEquiv (M.initialState, 0)
  transition q input cells :=
    let (p, last) := finProdFinEquiv.symm q
    (M.transition p input cells).map fun (next, move, actions, bit) =>
      (finProdFinEquiv (next, (bit.map packBit).getD last), move, actions, none)
where
  packBit b := pack (some b)

def state (c : (machine M).Config) : Option Bool :=
  unpack (finProdFinEquiv.symm c.state).2

def lift (c : M.Config) (prior : List Bool) : (machine M).Config :=
  ⟨finProdFinEquiv (c.state, pack c.outputReversed.head?), c.inputHead,
    c.workHead, c.workCell, prior⟩

@[simp] theorem state_lift (c : M.Config) (prior : List Bool) :
    state M (lift M c prior) = c.outputReversed.head? := by
  simp [state, lift]

theorem step (word : List Bool) (c : M.Config) (prior : List Bool) :
    (machine M).step word (lift M c prior) = (M.step word c).map (fun d => lift M d prior) := by
  unfold SearchTransducer.step
  simp only [machine, lift, Equiv.symm_apply_apply]
  cases ht : M.transition c.state (readInput word c.inputHead)
      (fun i => c.workCell i (c.workHead i)) with
  | none => rfl
  | some p =>
    rcases p with ⟨q, a, act, out⟩
    cases out <;> rfl

theorem run (word : List Bool) (c : M.Config) (prior : List Bool) (k : Nat) :
    (machine M).runFrom word (lift M c prior) k =
      (M.runFrom word c k).map (fun d => lift M d prior) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih]
    cases old : M.runFrom word c k with
    | none => rfl
    | some d => exact step M word d prior

theorem execute {word prior : List Bool} {B k : Nat} {c d : M.Config}
    (h : M.BoundedSegment word B c d k) (halt : M.step word d = none) :
    (machine M).BoundedSegment word B (lift M c prior) (lift M d prior) k ∧
    (machine M).step word (lift M d prior) = none ∧
    state M (lift M d prior) = d.outputReversed.head? ∧ (lift M d prior).outputReversed = prior := by
  refine ⟨⟨by rw [run, h.1]; rfl, ?_⟩, by rw [step, halt]; rfl, state_lift M d prior, rfl⟩
  intro j hj v hv
  rw [run] at hv
  obtain ⟨x, hx, rfl⟩ := (Option.map_eq_some_iff.mp hv)
  exact h.2 j hj x hx

end Mathproof.MinimumGeneration.LatchedVerdict
