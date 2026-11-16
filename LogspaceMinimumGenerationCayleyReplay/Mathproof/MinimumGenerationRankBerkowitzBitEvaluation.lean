import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size

/-!
A finite-address Boolean gate evaluator that suspends one Boolean value per
unfinished binary gate. The gate and input accessors are supplied independently.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.BitEvaluation

inductive Gate (Address : Type)
  | literal (value : Bool)
  | input (address : Address)
  | nand (left right : Address)

inductive Control (Address : Type)
  | query (fuel : Nat) (address : Address)
  | result (value : Bool)

inductive Frame (Address : Type)
  | pending (fuel : Nat) (right : Address)
  | combine (left : Bool)

structure State (Address : Type) where
  control : Control Address
  stack : List (Frame Address)

variable {Address : Type} (circuit : Address → Gate Address) (input : Address → Bool)

/-- Reference evaluation with a bound on the number of binary gates along a path. -/
def eval : Nat → Address → Option Bool
  | 0, address =>
    match circuit address with
    | .literal value => some value
    | .input index => some (input index)
    | .nand _ _ => none
  | fuel + 1, address =>
    match circuit address with
    | .literal value => some value
    | .input index => some (input index)
    | .nand left right => do
      let x ← eval fuel left
      let y ← eval fuel right
      pure (!(x && y))

/-- A single executable transition. Each pending frame retains an address and
fuel. Each combining frame retains just the already-computed Boolean. -/
def step : State Address → Option (State Address)
  | ⟨.query fuel address, stack⟩ =>
    match circuit address with
    | .literal value => some ⟨.result value, stack⟩
    | .input index => some ⟨.result (input index), stack⟩
    | .nand left right =>
      match fuel with
      | 0 => none
      | fuel + 1 => some ⟨.query fuel left, .pending fuel right :: stack⟩
  | ⟨.result value, .pending fuel right :: stack⟩ =>
    some ⟨.query fuel right, .combine value :: stack⟩
  | ⟨.result value, .combine left :: stack⟩ =>
    some ⟨.result (!(left && value)), stack⟩
  | ⟨.result _, []⟩ => none

theorem eval_of_levels (level : Address → Nat)
    (hLevel : ∀ address left right, circuit address = .nand left right →
      level left < level address ∧ level right < level address)
    {depth : Nat} {address : Address} (hDepth : level address ≤ depth) :
    ∃ value, eval circuit input depth address = some value := by
  induction depth generalizing address with
  | zero =>
    cases hGate : circuit address with
    | literal b => exact ⟨b, by simp only [eval, hGate]⟩
    | input index => exact ⟨input index, by simp only [eval, hGate]⟩
    | nand left right =>
      have hChild := (hLevel address left right hGate).1
      omega
  | succ depth ih =>
    cases hGate : circuit address with
    | literal b => exact ⟨b, by simp only [eval, hGate]⟩
    | input index => exact ⟨input index, by simp only [eval, hGate]⟩
    | nand left right =>
      obtain ⟨hLeft, hRight⟩ := hLevel address left right hGate
      obtain ⟨x, hx⟩ := ih (address := left) (by omega)
      obtain ⟨y, hy⟩ := ih (address := right) (by omega)
      exact ⟨!(x && y), by simp [eval, hGate, hx, hy]⟩

@[simp] theorem step_halted (value : Bool) :
    step circuit input ⟨.result value, []⟩ = none := rfl


/-- An execution with a constraint on every configuration, including both endpoints. -/
inductive Runs (next : State Address → Option (State Address)) (valid : State Address → Prop) :
    State Address → State Address → Prop
  | refl {state} (check : valid state) : Runs next valid state state
  | cons {first middle last} (check : valid first) (transition : next first = some middle)
      (tail : Runs next valid middle last) : Runs next valid first last

namespace Runs

theorem trans {next : State Address → Option (State Address)}
    {valid : State Address → Prop} {first middle last : State Address}
    (firstRun : Runs next valid first middle) (secondRun : Runs next valid middle last) :
    Runs next valid first last := by
  induction firstRun with
  | refl _ => exact secondRun
  | cons check transition tail ih => exact .cons check transition (ih secondRun)

theorem mono {next : State Address → Option (State Address)}
    {valid stronger : State Address → Prop} {first last : State Address}
    (run : Runs next valid first last) (change : ∀ state, valid state → stronger state) :
    Runs next stronger first last := by
  induction run with
  | refl check => exact .refl (change _ check)
  | cons check transition _ ih => exact .cons (change _ check) transition ih

end Runs

def Control.fuelOK (limit : Nat) : Control Address → Prop
  | .query fuel _ => fuel ≤ limit
  | .result _ => True

def Frame.fuelOK (limit : Nat) : Frame Address → Prop
  | .pending fuel _ => fuel ≤ limit
  | .combine _ => True

def State.bounded (limit height : Nat) (state : State Address) : Prop :=
  state.control.fuelOK limit ∧
    (∀ frame ∈ state.stack, frame.fuelOK limit) ∧ state.stack.length ≤ height

private theorem eval_execute (fuel : Nat) (address : Address) (value : Bool)
    (stack : List (Frame Address)) (limit height : Nat) (hFuel : fuel ≤ limit)
    (hStack : ∀ frame ∈ stack, frame.fuelOK limit) (hHeight : stack.length + fuel ≤ height)
    (heval : eval circuit input fuel address = some value) :
    Runs (step circuit input) (State.bounded limit height)
      ⟨.query fuel address, stack⟩ ⟨.result value, stack⟩ := by
  induction fuel generalizing address value stack with
  | zero =>
    have hBase : stack.length ≤ height := by omega
    cases hGate : circuit address with
    | literal b =>
      have hv : b = value := by simpa only [eval, hGate, Option.some.injEq] using heval
      subst value
      exact .cons ⟨hFuel, hStack, hBase⟩
        (by simp only [step, hGate]) (.refl ⟨trivial, hStack, hBase⟩)
    | input index =>
      have hv : input index = value := by
        simpa only [eval, hGate, Option.some.injEq] using heval
      subst value
      exact .cons ⟨hFuel, hStack, hBase⟩
        (by simp only [step, hGate]) (.refl ⟨trivial, hStack, hBase⟩)
    | nand left right => simp [eval, hGate] at heval
  | succ fuel ih =>
    have hBase : stack.length ≤ height := by omega
    cases hGate : circuit address with
    | literal b =>
      have hv : b = value := by simpa only [eval, hGate, Option.some.injEq] using heval
      subst value
      exact .cons ⟨hFuel, hStack, hBase⟩
        (by simp only [step, hGate]) (.refl ⟨trivial, hStack, hBase⟩)
    | input index =>
      have hv : input index = value := by
        simpa only [eval, hGate, Option.some.injEq] using heval
      subst value
      exact .cons ⟨hFuel, hStack, hBase⟩
        (by simp only [step, hGate]) (.refl ⟨trivial, hStack, hBase⟩)
    | nand left right =>
      cases hx : eval circuit input fuel left with
      | none => simp [eval, hGate, hx] at heval
      | some x =>
        cases hy : eval circuit input fuel right with
        | none => simp [eval, hGate, hx, hy] at heval
        | some y =>
          have hv : (!(x && y)) = value := by
            simpa [eval, hGate, hx, hy] using heval
          subst value
          have hPred : fuel ≤ limit := by omega
          have hPending : ∀ frame ∈ Frame.pending fuel right :: stack, frame.fuelOK limit := by
            intro frame hMem
            rcases List.mem_cons.mp hMem with hEq | hOld
            · subst frame
              exact hPred
            · exact hStack frame hOld
          have hCombine : ∀ frame ∈ Frame.combine x :: stack, frame.fuelOK limit := by
            intro frame hMem
            rcases List.mem_cons.mp hMem with hEq | hOld
            · subst frame
              trivial
            · exact hStack frame hOld
          have hBigger : stack.length + 1 ≤ height := by omega
          have hSize1 : (Frame.pending fuel right :: stack).length + fuel ≤ height := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hHeight
          have hSize2 : (Frame.combine x :: stack).length + fuel ≤ height := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hHeight
          have hLeft := ih left x (Frame.pending fuel right :: stack) hPred hPending hSize1 hx
          have hRight := ih right y (Frame.combine x :: stack) hPred hCombine hSize2 hy
          have hStep : step circuit input ⟨.query (fuel + 1) address, stack⟩ =
              some ⟨.query fuel left, .pending fuel right :: stack⟩ := by
            simp only [step, hGate]
          refine .cons ⟨hFuel, hStack, hBase⟩ hStep ?_
          refine hLeft.trans (.cons ⟨trivial, hPending, hBigger⟩ rfl ?_)
          exact hRight.trans (.cons ⟨trivial, hCombine, hBigger⟩ rfl
            (.refl ⟨trivial, hStack, hBase⟩))

theorem execute (depth : Nat) (address : Address) (value : Bool)
    (heval : eval circuit input depth address = some value) :
    Runs (step circuit input) (State.bounded depth depth)
      ⟨.query depth address, []⟩ ⟨.result value, []⟩ :=
  eval_execute circuit input depth address value [] depth depth (by rfl) (by simp)
    (by simp) heval

/-- Concrete fixed-width bit encoding of a natural register. -/
def bits (width value : Nat) : List Bool :=
  List.ofFn fun position : Fin width => value.testBit position.val

@[simp] theorem bits_length (width value : Nat) : (bits width value).length = width := by
  simp [bits]

theorem bits_injective_on {width x y : Nat} (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (h : bits width x = bits width y) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < width
  · exact congrFun (List.ofFn_injective h) ⟨i, hi⟩
  · have hpow : 2 ^ width ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hx.trans_le hpow),
      Nat.testBit_eq_false_of_lt (hy.trans_le hpow)]

variable {addressWidth : Nat}

def Control.encode (fuelWidth : Nat) : Control (Fin (2 ^ addressWidth)) → List Bool
  | .query fuel address => false :: bits fuelWidth fuel ++ bits addressWidth address.val
  | .result value => [true, value] ++ List.replicate (fuelWidth + addressWidth - 1) false

def Frame.encode (fuelWidth : Nat) : Frame (Fin (2 ^ addressWidth)) → List Bool
  | .pending fuel right => false :: bits fuelWidth fuel ++ bits addressWidth right.val
  | .combine left => [true, left] ++ List.replicate (fuelWidth + addressWidth - 1) false

theorem Control.encode_length {fuelWidth : Nat} (hPositive : 0 < fuelWidth + addressWidth)
    (control : Control (Fin (2 ^ addressWidth))) :
    (control.encode fuelWidth).length = 1 + fuelWidth + addressWidth := by
  cases control <;> simp [Control.encode] <;> omega

theorem Frame.encode_length {fuelWidth : Nat} (hPositive : 0 < fuelWidth + addressWidth)
    (frame : Frame (Fin (2 ^ addressWidth))) :
    (frame.encode fuelWidth).length = 1 + fuelWidth + addressWidth := by
  cases frame <;> simp [Frame.encode] <;> omega

def State.encode (fuelWidth : Nat) (state : State (Fin (2 ^ addressWidth))) : List Bool :=
  state.control.encode fuelWidth ++ (state.stack.map (Frame.encode fuelWidth)).flatten

private theorem Control.encode_injective_on {fuelWidth : Nat} {x y : Control (Fin (2 ^ addressWidth))}
    (hx : x.fuelOK (2 ^ fuelWidth - 1)) (hy : y.fuelOK (2 ^ fuelWidth - 1))
    (h : x.encode fuelWidth = y.encode fuelWidth) : x = y := by
  cases x with
  | query xFuel xAddr =>
    cases y with
    | query yFuel yAddr =>
      simp only [Control.encode] at h
      obtain ⟨hFuel, hAddr⟩ := List.append_inj h (by simp)
      have hPos : 0 < 2 ^ fuelWidth := Nat.two_pow_pos _
      change xFuel ≤ 2 ^ fuelWidth - 1 at hx
      change yFuel ≤ 2 ^ fuelWidth - 1 at hy
      congr
      · exact bits_injective_on (width := fuelWidth) (by omega) (by omega) (List.cons.inj hFuel).2
      · exact Fin.ext (bits_injective_on xAddr.isLt yAddr.isLt hAddr)
    | result value => simp [Control.encode] at h
  | result xv =>
    cases y with
    | query fuel addr => simp [Control.encode] at h
    | result yv => simpa [Control.encode] using h

private theorem Frame.encode_injective_on {fuelWidth : Nat} {x y : Frame (Fin (2 ^ addressWidth))}
    (hx : x.fuelOK (2 ^ fuelWidth - 1)) (hy : y.fuelOK (2 ^ fuelWidth - 1))
    (h : x.encode fuelWidth = y.encode fuelWidth) : x = y := by
  let toControl : Frame (Fin (2 ^ addressWidth)) → Control (Fin (2 ^ addressWidth))
    | .pending fuel address => .query fuel address
    | .combine value => .result value
  have hControl : toControl x = toControl y :=
    Control.encode_injective_on
      (show (toControl x).fuelOK _ from by cases x <;> exact hx)
      (show (toControl y).fuelOK _ from by cases y <;> exact hy)
      (show (toControl x).encode _ = (toControl y).encode _ from by
        cases x <;> cases y <;> exact h)
  cases x <;> cases y <;> simpa [toControl] using hControl

theorem State.encode_injective_on {fuelWidth limit height : Nat}
    (hPositive : 0 < fuelWidth + addressWidth) (hLimit : limit < 2 ^ fuelWidth)
    {x y : State (Fin (2 ^ addressWidth))}
    (hx : x.bounded limit height) (hy : y.bounded limit height)
    (h : x.encode fuelWidth = y.encode fuelWidth) : x = y := by
  have controlOK (control : Control (Fin (2 ^ addressWidth)))
      (hControl : control.fuelOK limit) : control.fuelOK (2 ^ fuelWidth - 1) := by
    cases control <;> simp only [Control.fuelOK] at * <;> omega
  have frameOK (frame : Frame (Fin (2 ^ addressWidth)))
      (hFrame : frame.fuelOK limit) : frame.fuelOK (2 ^ fuelWidth - 1) := by
    cases frame <;> simp only [Frame.fuelOK] at * <;> omega
  have stackInj (xs ys : List (Frame (Fin (2 ^ addressWidth))))
      (hxs : ∀ frame ∈ xs, frame.fuelOK limit) (hys : ∀ frame ∈ ys, frame.fuelOK limit)
      (hStack : (xs.map (Frame.encode fuelWidth)).flatten =
        (ys.map (Frame.encode fuelWidth)).flatten) : xs = ys := by
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons b bs => cases b <;> simp [Frame.encode] at hStack
    | cons a as ih =>
      cases ys with
      | nil => cases a <;> simp [Frame.encode] at hStack
      | cons b bs =>
        simp only [List.map_cons, List.flatten_cons] at hStack
        obtain ⟨hAb, hTail⟩ := List.append_inj hStack (by simp [Frame.encode_length hPositive])
        have hEq := Frame.encode_injective_on
          (frameOK a (hxs a (by simp))) (frameOK b (hys b (by simp))) hAb
        have hRest := ih bs (by intro f hf; exact hxs f (List.mem_cons_of_mem a hf))
          (by intro f hf; exact hys f (List.mem_cons_of_mem b hf)) hTail
        exact congrArg₂ List.cons hEq hRest
  obtain ⟨hCtrl, hStack⟩ := List.append_inj h (by simp [Control.encode_length hPositive])
  have hCtrlEq := Control.encode_injective_on (controlOK _ hx.1) (controlOK _ hy.1) hCtrl
  have hStackEq := stackInj _ _ hx.2.1 hy.2.1 hStack
  cases x
  cases y
  congr


theorem State.encode_length {fuelWidth : Nat} (hPositive : 0 < fuelWidth + addressWidth)
    (state : State (Fin (2 ^ addressWidth))) :
    (state.encode fuelWidth).length = (state.stack.length + 1) * (1 + fuelWidth + addressWidth) := by
  have hStack (stack : List (Frame (Fin (2 ^ addressWidth)))) :
      (stack.map (Frame.encode fuelWidth)).flatten.length =
        stack.length * (1 + fuelWidth + addressWidth) := by
    induction stack with
    | nil => simp
    | cons frame tail ih =>
      simp [Frame.encode_length hPositive, ih, Nat.add_mul, Nat.add_comm]
  simp [State.encode, Control.encode_length hPositive, hStack, Nat.add_mul, Nat.add_comm]

theorem execute_encoded_bound (circuit : Fin (2 ^ addressWidth) → Gate (Fin (2 ^ addressWidth)))
    (input : Fin (2 ^ addressWidth) → Bool) (depth fuelWidth : Nat)
    (address : Fin (2 ^ addressWidth)) (value : Bool) (hPositive : 0 < fuelWidth + addressWidth)
    (hEval : eval circuit input depth address = some value) :
    Runs (step circuit input)
      (fun state => State.bounded depth depth state ∧
        (state.encode fuelWidth).length ≤ (depth + 1) * (1 + fuelWidth + addressWidth))
      ⟨.query depth address, []⟩ ⟨.result value, []⟩ := by
  have hRun := execute circuit input depth address value hEval
  have tighten (state : State (Fin (2 ^ addressWidth))) (hBound : state.bounded depth depth) :
      (state.encode fuelWidth).length ≤ (depth + 1) * (1 + fuelWidth + addressWidth) := by
    rw [State.encode_length hPositive]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hBound.2.2 1)
  exact hRun.mono (fun state check => ⟨check, tighten state check⟩)

theorem execute_total_encoded
    (circuit : Fin (2 ^ addressWidth) → Gate (Fin (2 ^ addressWidth)))
    (input : Fin (2 ^ addressWidth) → Bool) (level : Fin (2 ^ addressWidth) → Nat)
    (hLevel : ∀ address left right, circuit address = .nand left right →
      level left < level address ∧ level right < level address)
    (depth : Nat) (address : Fin (2 ^ addressWidth)) (hDepth : level address ≤ depth) :
    ∃ value, eval circuit input depth address = some value ∧
      Runs (step circuit input)
        (fun state => State.bounded depth depth state ∧
          (state.encode (depth.size + 1)).length ≤ (depth + 1) * (2 + depth.size + addressWidth))
        ⟨.query depth address, []⟩ ⟨.result value, []⟩ ∧
      step circuit input ⟨.result value, []⟩ = none := by
  obtain ⟨value, hEval⟩ := eval_of_levels circuit input level hLevel hDepth
  refine ⟨value, hEval, ?_, step_halted circuit input value⟩
  have hRun := execute_encoded_bound circuit input depth (depth.size + 1) address value
    (by omega) hEval
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRun

theorem State.encode_injective_at_depth {limit : Nat}
    {x y : State (Fin (2 ^ addressWidth))}
    (hx : x.bounded limit limit) (hy : y.bounded limit limit)
    (h : x.encode (limit.size + 1) = y.encode (limit.size + 1)) : x = y := by
  have hFit : limit < 2 ^ (limit.size + 1) :=
    (Nat.lt_size_self limit).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  exact State.encode_injective_on (by omega) hFit hx hy h


end Mathproof.MinimumGeneration.RankBerkowitz.BitEvaluation
