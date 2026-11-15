import Lean.Elab.Tactic.Omega

/-!
# Ordinal replay for residual quotient towers

The residual transitions are indexed by a uniform radix. Missing ordinals give
vacuous paths. A traversal enumerates all complete ordinal sequences and replays
each sequence from the original label using quotient and remainder. Old labels
are absent from the replay state. The register bound is for this executable
algorithm at the residual-transition interface.
-/

namespace Mathproof.MinimumGeneration.TowerReplay

/-- Read child ordinal j in the source subgroup associated with the level
and current source label. -/
abbrev Child := Nat → Nat → Nat → Option Nat

/-- Specification of membership before changing the traversal. -/
def Obligation (child : Child) (base : Nat → Bool) (radix : Nat) :
    Nat → Nat → Prop
  | 0, label => base label = true
  | level + 1, label =>
      ∀ j < radix, ∀ next, child (level + 1) label j = some next →
        Obligation child base radix level next

/-- A replay starting at one original source label, consuming one digit per level. -/
def replay (child : Child) (radix : Nat) : Nat → Nat → Nat → Option Nat
  | 0, label, _ => some label
  | level + 1, label, code =>
      match child (level + 1) label (code % radix) with
      | none => none
      | some next => replay child radix level next (code / radix)

/-- Missing children impose no condition on the padded enumeration. -/
def checkPath (child : Child) (base : Nat → Bool) (radix level label code : Nat) : Bool :=
  match replay child radix level label code with
  | none => true
  | some leaf => base leaf

/-- Run a half-open range scan without allocating the range. -/
def scan (check : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | count + 1, start =>
      if check start then scan check count (start + 1) else false

theorem scan_eq_true_iff (check : Nat → Bool) (count start : Nat) :
    scan check count start = true ↔
      ∀ k, start ≤ k → k < start + count → check k = true := by
  induction count generalizing start with
  | zero =>
    simp [scan]
    intro k hlo hhi
    omega
  | succ count ih =>
    constructor
    · intro h k hstart hend
      have hs : check start = true := by
        cases hc : check start <;> simp [scan, hc] at h ⊢
      by_cases heq : k = start
      · simpa [heq] using hs
      · have htail : scan check count (start + 1) = true := by
          simpa [scan, hs] using h
        exact (ih (start + 1)).mp htail k (by omega) (by omega)
    · intro h
      have hs : check start = true := h start (Nat.le_refl _) (by omega)
      have htail : scan check count (start + 1) = true :=
        (ih (start + 1)).mpr (fun k hlo hhi => h k (by omega) (by omega))
      simp [scan, hs, htail]

/-- One bounded counter and one reconstructed label replace the recursive list
of suspended labels. -/
def decide (child : Child) (base : Nat → Bool) (radix level root : Nat) : Bool :=
  scan (checkPath child base radix level root) (radix ^ level) 0

/-- The code with low digit j followed by the code tail is in range. -/
private theorem packed_lt {radix level j tail : Nat}
    (hj : j < radix) (htail : tail < radix ^ level) :
    j + radix * tail < radix ^ (level + 1) := by
  have hmul := Nat.mul_le_mul_left radix (show tail + 1 ≤ radix ^ level by omega)
  have hstrict : j + radix * tail < radix * (tail + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [Nat.pow_succ, Nat.mul_comm (radix ^ level) radix]
  exact Nat.lt_of_lt_of_le hstrict hmul

theorem obligation_iff_paths (child : Child) (base : Nat → Bool)
    {radix : Nat} (hRadix : 0 < radix) (level root : Nat) :
    Obligation child base radix level root ↔
      ∀ code < radix ^ level, checkPath child base radix level root code = true := by
  induction level generalizing root with
  | zero =>
    simp only [Obligation, Nat.pow_zero, checkPath, replay]
    constructor
    · intro h _ _
      exact h
    · intro h
      exact h 0 (by decide)
  | succ level ih =>
    constructor
    · intro h code hCode
      have hDigit := Nat.mod_lt code hRadix
      have hTail : code / radix < radix ^ level := by
        exact (Nat.div_lt_iff_lt_mul hRadix).mpr (by simpa [Nat.pow_succ] using hCode)
      cases hChild : child (level + 1) root (code % radix) with
      | none => simp [checkPath, replay, hChild]
      | some next =>
        have hNext := (ih next).mp (h _ hDigit next hChild) _ hTail
        simpa [checkPath, replay, hChild] using hNext
    · intro h j hj next hChild
      apply (ih next).mpr
      intro tail hTail
      have hs := h (j + radix * tail) (packed_lt hj hTail)
      have hm : (j + radix * tail) % radix = j := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      have hd : (j + radix * tail) / radix = tail := by
        rw [Nat.add_mul_div_left j tail hRadix, Nat.div_eq_of_lt hj, Nat.zero_add]
      simpa [checkPath, replay, hm, hd, hChild] using hs

/-- The finite replay algorithm solves exactly the group-side recursive
membership obligation. -/
theorem decide_eq_true_iff (child : Child) (base : Nat → Bool) {radix : Nat}
    (hRadix : 0 < radix) (level root : Nat) :
    decide child base radix level root = true ↔
      Obligation child base radix level root := by
  rw [decide, scan_eq_true_iff, obligation_iff_paths child base hRadix level root]
  simp

/-- The live replay state has exactly one source label. -/
structure Registers where
  level : Nat
  label : Nat
  code : Nat
  deriving DecidableEq

/-- The one-step residual transition of the replay. -/
def step (child : Child) (radix : Nat) (r : Registers) : Option Registers :=
  match r.level with
  | 0 => none
  | level + 1 =>
    (child (level + 1) r.label (r.code % radix)).map
      (fun next => ⟨level, next, r.code / radix⟩)

/-- The initial code is overwritten by its unprocessed suffix. -/
def Fits (radix level source : Nat) (r : Registers) : Prop :=
  r.level ≤ level ∧ r.label < source ∧ r.code < radix ^ r.level

theorem step_fits (child : Child) {radix level source : Nat} (hRadix : 0 < radix)
    (hChild : ∀ l x j y, x < source → child l x j = some y → y < source)
    {r s : Registers} (hr : Fits radix level source r)
    (hs : step child radix r = some s) :
    Fits radix level source s := by
  obtain ⟨l, x, code⟩ := r
  obtain ⟨hle, hx, hcode⟩ := hr
  cases l with
  | zero => simp [step] at hs
  | succ l =>
    cases hc : child (l + 1) x (code % radix) with
    | none => simp [step, hc] at hs
    | some y =>
      have heq : s = ⟨l, y, code / radix⟩ := by
        simpa [step, hc, eq_comm] using hs
      subst s
      refine ⟨by change l ≤ level; change l + 1 ≤ level at hle; omega,
        hChild _ _ _ _ hx hc, ?_⟩
      apply (Nat.div_lt_iff_lt_mul hRadix).mpr
      simpa [Nat.pow_succ] using hcode

/-- A label of range source, a remaining-depth counter and a suffix together
fit in three binary registers of the stated widths. -/
theorem fits_binary (radix level source width labelWidth depthWidth : Nat)
    (hRadix : radix ≤ 2 ^ width) (hSource : source ≤ 2 ^ labelWidth)
    (hDepth : level < 2 ^ depthWidth) {r : Registers}
    (hr : Fits radix level source r) :
    r.level < 2 ^ depthWidth ∧ r.label < 2 ^ labelWidth ∧
      r.code < 2 ^ (width * level) := by
  refine ⟨Nat.lt_of_le_of_lt hr.1 hDepth, Nat.lt_of_lt_of_le hr.2.1 hSource,
    Nat.lt_of_lt_of_le hr.2.2 ?_⟩
  rw [Nat.pow_mul]
  exact Nat.le_trans (Nat.pow_le_pow_left hRadix r.level)
    (Nat.pow_le_pow_right (Nat.two_pow_pos width) hr.1)


/-- Controller state consists of the outer counter, the next index, and at most
one live replay. The fixed root label is a program input. -/
inductive Control where
  | scan (count index : Nat)
  | walk (count nextIndex : Nat) (r : Registers)
  | halt (answer : Bool)
  deriving DecidableEq

def controlStep (child : Child) (base : Nat → Bool) (radix total root : Nat) :
    Control → Option Control
  | .scan 0 _ => some (.halt true)
  | .scan (count + 1) index =>
    some (.walk count (index + 1) ⟨total, root, index⟩)
  | .walk count nextIndex ⟨0, label, _⟩ =>
    some (if base label then .scan count nextIndex else .halt false)
  | .walk count nextIndex ⟨level + 1, label, code⟩ =>
    match child (level + 1) label (code % radix) with
    | none => some (.scan count nextIndex)
    | some next => some (.walk count nextIndex ⟨level, next, code / radix⟩)
  | .halt _ => none

inductive ControlRuns (child : Child) (base : Nat → Bool) (radix total root : Nat) :
    Control → Control → Prop where
  | refl (a : Control) : ControlRuns child base radix total root a a
  | head {a b c : Control} :
      controlStep child base radix total root a = some b →
      ControlRuns child base radix total root b c →
      ControlRuns child base radix total root a c

theorem ControlRuns.single {child : Child} {base : Nat → Bool}
    {radix total root : Nat} {a b : Control}
    (h : controlStep child base radix total root a = some b) :
    ControlRuns child base radix total root a b :=
  .head h (.refl b)

theorem ControlRuns.trans {child : Child} {base : Nat → Bool}
    {radix total root : Nat} {a b c : Control}
    (h : ControlRuns child base radix total root a b)
    (g : ControlRuns child base radix total root b c) :
    ControlRuns child base radix total root a c := by
  induction h with
  | refl => exact g
  | head hs _ ih => exact .head hs (ih g)

/-- The explicit transition program implements one replay check. -/
theorem control_walk_runs (child : Child) (base : Nat → Bool)
    (radix total root count nextIndex level label code : Nat) :
    ControlRuns child base radix total root (.walk count nextIndex ⟨level, label, code⟩)
      (if checkPath child base radix level label code then .scan count nextIndex
        else .halt false) := by
  induction level generalizing label code with
  | zero =>
    apply ControlRuns.single
    rfl
  | succ level ih =>
    cases h : child (level + 1) label (code % radix) with
    | none =>
      apply ControlRuns.single
      simp [controlStep, checkPath, replay, h]
    | some next =>
      have hpath : checkPath child base radix (level + 1) label code =
          checkPath child base radix level next (code / radix) := by
        simp [checkPath, replay, h]
      rw [hpath]
      have hs : controlStep child base radix total root
          (.walk count nextIndex ⟨level + 1, label, code⟩) =
          some (.walk count nextIndex ⟨level, next, code / radix⟩) := by
        simp [controlStep, h]
      exact ControlRuns.head hs (ih next (code / radix))

/-- The physical order of scans and replays yields the executable Boolean
specification, including the early false return. -/
theorem control_scan_runs (child : Child) (base : Nat → Bool)
    (radix total root count index : Nat) :
    ControlRuns child base radix total root (.scan count index)
      (.halt (scan (checkPath child base radix total root) count index)) := by
  induction count generalizing index with
  | zero => exact ControlRuns.single rfl
  | succ count ih =>
    have hrun := control_walk_runs child base radix total root count (index + 1) total root index
    have hstart : ControlRuns child base radix total root (.scan (count + 1) index)
        (.walk count (index + 1) ⟨total, root, index⟩) :=
      ControlRuns.single rfl
    cases h : checkPath child base radix total root index with
    | false => simpa [scan, h] using hstart.trans hrun
    | true =>
      simp [h] at hrun
      simpa [scan, h] using (hstart.trans hrun).trans (ih (index + 1))

def ControlFits (radix total source : Nat) : Control → Prop
  | .scan count index => count + index = radix ^ total
  | .walk count index r => count + index = radix ^ total ∧ Fits radix total source r
  | .halt _ => True

theorem controlStep_fits (child : Child) (base : Nat → Bool)
    {radix total root source : Nat} (hRadix : 0 < radix) (hRoot : root < source)
    (hChild : ∀ l x j y, x < source → child l x j = some y → y < source)
    {a b : Control} (ha : ControlFits radix total source a)
    (hs : controlStep child base radix total root a = some b) :
    ControlFits radix total source b := by
  cases a with
  | halt answer => simp [controlStep] at hs
  | scan count index =>
    cases count with
    | zero =>
      have hb : b = .halt true := by simpa [controlStep, eq_comm] using hs
      subst b
      trivial
    | succ count =>
      have hb : b = .walk count (index + 1) ⟨total, root, index⟩ := by
        simpa [controlStep, eq_comm] using hs
      subst b
      change count + (index + 1) = radix ^ total ∧
        (total ≤ total ∧ root < source ∧ index < radix ^ total)
      change count + 1 + index = radix ^ total at ha
      exact ⟨by omega, Nat.le_refl _, hRoot, by omega⟩
  | walk count index r =>
    obtain ⟨level, label, code⟩ := r
    obtain ⟨hc, hr⟩ := ha
    cases level with
    | zero =>
      cases hb : base label with
      | false =>
        have he : b = .halt false := by simpa [controlStep, hb, eq_comm] using hs
        subst b
        trivial
      | true =>
        have he : b = .scan count index := by simpa [controlStep, hb, eq_comm] using hs
        subst b
        exact hc
    | succ level =>
      cases h : child (level + 1) label (code % radix) with
      | none =>
        have hb : b = .scan count index := by simpa [controlStep, h, eq_comm] using hs
        subst b
        exact hc
      | some next =>
        have hb : b = .walk count index ⟨level, next, code / radix⟩ := by
          simpa [controlStep, h, eq_comm] using hs
        subst b
        exact ⟨hc, step_fits child hRadix hChild hr (by simp [step, h])⟩

/-- Each reachable state of the controller satisfies the register invariant. -/
theorem control_fits_of_runs (child : Child) (base : Nat → Bool)
    {radix total root source : Nat} (hRadix : 0 < radix) (hRoot : root < source)
    (hChild : ∀ l x j y, x < source → child l x j = some y → y < source)
    {b : Control} (hr : ControlRuns child base radix total root
      (.scan (radix ^ total) 0) b) :
    ControlFits radix total source b := by
  have transfer {a b : Control}
      (run : ControlRuns child base radix total root a b)
      (ha : ControlFits radix total source a) : ControlFits radix total source b := by
    induction run with
    | refl => exact ha
    | head hs _ ih => exact ih (controlStep_fits child base hRadix hRoot hChild ha hs)
  exact transfer hr (by simp [ControlFits])

/-- The replay controller halts with the exact recursive membership answer. -/
theorem control_decides (child : Child) (base : Nat → Bool)
    {radix : Nat} (hRadix : 0 < radix) (total root : Nat) :
    ∃ answer,
      ControlRuns child base radix total root (.scan (radix ^ total) 0) (.halt answer) ∧
      controlStep child base radix total root (.halt answer) = none ∧
      (answer = true ↔ Obligation child base radix total root) :=
  ⟨decide child base radix total root,
    control_scan_runs child base radix total root (radix ^ total) 0,
    rfl, decide_eq_true_iff child base hRadix total root⟩


/-- One round drops a positive amount from the integer logarithm of the group
order. The square bound derives from the size of a self-centralizing socle. -/
def GoodRound (before after : Nat) : Prop :=
  ∃ drop : Nat, 0 < drop ∧ after + drop ≤ before ∧ before ≤ 4 * (drop * drop)

theorem goodRound_of_half {before after : Nat} (hb : 0 < before)
    (h : 2 * after ≤ before) : GoodRound before after := by
  have hpos : 0 < before - after := by omega
  refine ⟨before - after, hpos, by omega, ?_⟩
  have hp : before - after ≤ (before - after) * (before - after) := by
    simpa using Nat.mul_le_mul_left (before - after) (show 1 ≤ before - after by omega)
  omega

theorem goodRound_of_socle {before middle after factor : Nat} (hfactor : 0 < factor)
    (hlarge : before ≤ 2 * middle) (hshrinks : after + factor ≤ middle)
    (hh : middle ≤ before) (hembed : middle ≤ 2 * (factor * factor)) :
    GoodRound before after :=
  ⟨factor, hfactor, Nat.le_trans hshrinks hh, by omega⟩

private theorem log2_mono {a b : Nat} (hb : b ≠ 0) (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · simp [ha]
  exact (Nat.le_log2 hb).mpr (Nat.le_trans (Nat.log2_self_le ha) h)

/-- The order relations of one radical-socle round imply its discrete height
decrease. The input after radical removal is middle, the socle has size factor,
and the quotient by it has size after. -/
theorem goodRound_of_orders {before middle after factor : Nat} (hb : 1 < before)
    (ha : 0 < after) (hf : 0 < factor) (hm : middle ≤ before)
    (hprod : after * factor = middle) (haut : middle ≤ factor ^ factor.log2) :
    GoodRound before.log2 after.log2 := by
  have hmid : middle ≠ 0 := by
    rw [← hprod]
    exact Nat.ne_of_gt (Nat.mul_pos ha hf)
  have hlog : middle.log2 ≤ before.log2 := log2_mono (by omega) hm
  have hsum : after.log2 + factor.log2 ≤ middle.log2 := by
    apply (Nat.le_log2 hmid).mpr
    rw [Nat.pow_add, ← hprod]
    exact Nat.mul_le_mul (Nat.log2_self_le (Nat.ne_of_gt ha))
      (Nat.log2_self_le (Nat.ne_of_gt hf))
  have hbefore : 0 < before.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  by_cases hhalf : 2 * middle.log2 ≤ before.log2
  · exact goodRound_of_half hbefore (by omega)
  · have hfac : 0 < factor.log2 := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, Nat.pow_zero] at haut
      have hmz : middle.log2 = 0 := by
        have hle : middle.log2 < 1 := (Nat.log2_lt hmid).mpr (by omega)
        omega
      omega
    have hstrict : middle < (2 ^ (factor.log2 + 1)) ^ factor.log2 :=
      Nat.lt_of_le_of_lt haut (Nat.pow_lt_pow_left Nat.lt_log2_self (Nat.ne_of_gt hfac))
    rw [← Nat.pow_mul] at hstrict
    have hl2 := (Nat.log2_lt hmid).mpr hstrict
    have haux : factor.log2 ≤ factor.log2 * factor.log2 := by
      simpa using Nat.mul_le_mul_left factor.log2 (show 1 ≤ factor.log2 by omega)
    have hs : (factor.log2 + 1) * factor.log2 ≤ 2 * (factor.log2 * factor.log2) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact goodRound_of_socle hfac (by omega) hsum hlog
      (Nat.le_trans (Nat.le_of_lt hl2) hs)

/-- Telescope the discrete square-root decrease without using real-valued logs. -/
theorem roundCount_sq_le (height : Nat → Nat) (first count : Nat)
    (h : ∀ j < count, GoodRound (height (first + j)) (height (first + j + 1))) :
    count * count ≤ 25 * height first := by
  induction count generalizing first with
  | zero => simp
  | succ count ih =>
    obtain ⟨drop, hpos, hbudget, hsquare⟩ := h 0 (by omega)
    simp only [Nat.add_zero] at hbudget hsquare
    have ht : count * count ≤ 25 * height (first + 1) :=
      ih (first + 1) (fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (j + 1) (by omega))
    have hb : height (first + 1) ≤ height first := by omega
    have hcap : count * count ≤ (10 * drop) * (10 * drop) := by
      calc
        count * count ≤ 25 * height first := Nat.le_trans ht (Nat.mul_le_mul_left 25 hb)
        _ ≤ 25 * (4 * (drop * drop)) := Nat.mul_le_mul_left 25 hsquare
        _ = (10 * drop) * (10 * drop) := by
          rw [Nat.mul_mul_mul_comm, ← Nat.mul_assoc]
    have hCount : count ≤ 10 * drop := Nat.mul_self_le_mul_self_iff.mp hcap
    change (count + 1) * (count + 1) ≤ 25 * height first
    rw [Nat.mul_succ, Nat.succ_mul]
    omega

private theorem square_le_four_pow_two (k : Nat) : k * k ≤ 4 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k < 3
    · have cases_k : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases cases_k with rfl | rfl | rfl <;> decide
    · have hthree : 3 ≤ k := by omega
      have hkk := Nat.mul_le_mul_right k hthree
      have hstep : (k + 1) * (k + 1) ≤ 2 * (k * k) := by
        rw [Nat.mul_succ, Nat.succ_mul]
        omega
      calc
        (k + 1) * (k + 1) ≤ 2 * (k * k) := hstep
        _ ≤ 2 * (4 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 4 * 2 ^ (k + 1) := by
          rw [Nat.pow_add_one, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, ← Nat.mul_assoc]

/-- Enough bits for an ordinal among at most h+1 possible indices. -/
def ordinalWidth (h : Nat) : Nat := (h + 1).log2 + 1

theorem ordinalWidth_covers (h : Nat) : h + 1 < 2 ^ ordinalWidth h :=
  Nat.lt_log2_self

theorem ordinalWidth_sq_le (h : Nat) : ordinalWidth h * ordinalWidth h ≤ 8 * (h + 1) := by
  have hp := square_le_four_pow_two (ordinalWidth h)
  have hlog := Nat.log2_self_le (show h + 1 ≠ 0 by omega)
  calc
    ordinalWidth h * ordinalWidth h ≤ 4 * 2 ^ ordinalWidth h := hp
    _ = 8 * 2 ^ (h + 1).log2 := by
      rw [ordinalWidth, Nat.pow_add_one, Nat.mul_comm (2 ^ (h + 1).log2) 2, ← Nat.mul_assoc]
    _ ≤ 8 * (h + 1) := Nat.mul_le_mul_left _ hlog

private theorem cross_le_squares (a b : Nat) : 2 * (a * b) ≤ a * a + b * b := by
  have smallerFirst (x y : Nat) (h : x ≤ y) : 2 * (x * y) ≤ x * x + y * y := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm k x]
    omega
  rcases Nat.le_total a b with h | h
  · exact smallerFirst a b h
  · simpa [Nat.mul_comm b a, Nat.add_comm (b * b)] using smallerFirst b a h

/-- Twice the round count suffices for the two kinds of quotient steps.
The packed ordinal word then has linear size in the initial logarithm. -/
theorem packedWidth_le (h rounds level : Nat)
    (hRounds : rounds * rounds ≤ 25 * h) (hLevel : level ≤ 2 * rounds) :
    level * ordinalWidth h ≤ 54 * (h + 1) := by
  have hwidth := ordinalWidth_sq_le h
  have hl : level * level ≤ 100 * h := by
    calc
      level * level ≤ (2 * rounds) * (2 * rounds) := Nat.mul_le_mul hLevel hLevel
      _ = 4 * (rounds * rounds) := by rw [Nat.mul_mul_mul_comm]
      _ ≤ 4 * (25 * h) := Nat.mul_le_mul_left 4 hRounds
      _ = 100 * h := by rw [← Nat.mul_assoc]
  have hc := cross_le_squares level (ordinalWidth h)
  omega


/-- Connect the ordinal interface to certified membership predicates. -/
theorem obligation_iff_membership (child : Child) (base : Nat → Bool) (radix : Nat)
    (member : Nat → Nat → Prop)
    (hBase : ∀ x, base x = true ↔ member 0 x)
    (hStep : ∀ l x, member (l + 1) x ↔
      ∀ j < radix, ∀ y, child (l + 1) x j = some y → member l y)
    (l x : Nat) : Obligation child base radix l x ↔ member l x := by
  induction l generalizing x with
  | zero => exact hBase x
  | succ l ih =>
    rw [hStep l x]
    constructor
    · intro h j hj y hChild
      exact (ih y).mp (h j hj y hChild)
    · intro h j hj y hChild
      exact (ih y).mpr (h j hj y hChild)

/-- The executable controller gives the certified membership answer. -/
theorem control_decides_membership (child : Child) (base : Nat → Bool) {radix : Nat}
    (hRadix : 0 < radix) (member : Nat → Nat → Prop)
    (hBase : ∀ x, base x = true ↔ member 0 x)
    (hStep : ∀ l x, member (l + 1) x ↔
      ∀ j < radix, ∀ y, child (l + 1) x j = some y → member l y)
    (l x : Nat) :
    ∃ answer,
      ControlRuns child base radix l x (.scan (radix ^ l) 0) (.halt answer) ∧
      controlStep child base radix l x (.halt answer) = none ∧
      (answer = true ↔ member l x) := by
  obtain ⟨answer, hr, hh, hcorrect⟩ := control_decides child base hRadix l x
  exact ⟨answer, hr, hh,
    hcorrect.trans (obligation_iff_membership child base radix member hBase hStep l x)⟩

/-- The scan counters need one extra bit for the inclusive limit, while the
live replay suffix stays strictly below it. -/
def ControlBinaryFits (packedWidth labelWidth depthWidth : Nat) : Control → Prop
  | .scan count index => count < 2 ^ (packedWidth + 1) ∧ index < 2 ^ (packedWidth + 1)
  | .walk count index r =>
    (count < 2 ^ (packedWidth + 1) ∧ index < 2 ^ (packedWidth + 1)) ∧
    r.level < 2 ^ depthWidth ∧ r.label < 2 ^ labelWidth ∧ r.code < 2 ^ packedWidth
  | .halt _ => True

theorem controlFits_binary {radix total source width labelWidth depthWidth : Nat}
    (hRadix : radix ≤ 2 ^ width) (hSource : source ≤ 2 ^ labelWidth)
    (hDepth : total < 2 ^ depthWidth) {s : Control}
    (hs : ControlFits radix total source s) :
    ControlBinaryFits (width * total) labelWidth depthWidth s := by
  have hcap : radix ^ total < 2 ^ (width * total + 1) := by
    rw [Nat.pow_add_one, Nat.pow_mul]
    have hle := Nat.pow_le_pow_left hRadix total
    have hp : 0 < (2 ^ width) ^ total := Nat.pow_pos (Nat.two_pow_pos _)
    omega
  cases s with
  | halt => trivial
  | scan count index =>
    change count + index = radix ^ total at hs
    exact ⟨by omega, by omega⟩
  | walk count index r =>
    obtain ⟨hcount, hr⟩ := hs
    exact ⟨⟨by omega, by omega⟩, fits_binary radix total source width labelWidth depthWidth
      hRadix hSource hDepth hr⟩

/-- Numeric budget for the remaining number of transitions. It is only an
analysis measure. The controller itself stores its two original counters. -/
def controlPotential (total : Nat) : Control → Nat
  | .scan count _ => (total + 2) * count + 1
  | .walk count _ r => (total + 2) * count + r.level + 2
  | .halt _ => 0

theorem controlStep_decreases (child : Child) (base : Nat → Bool)
    (radix total root : Nat) {s t : Control}
    (h : controlStep child base radix total root s = some t) :
    controlPotential total t < controlPotential total s := by
  cases s with
  | halt => simp [controlStep] at h
  | scan count index =>
    cases count with
    | zero =>
      have ht : t = .halt true := by simpa [controlStep, eq_comm] using h
      subst t
      simp [controlPotential]
    | succ count =>
      have ht : t = .walk count (index + 1) ⟨total, root, index⟩ := by
        simpa [controlStep, eq_comm] using h
      subst t
      simp only [controlPotential, Nat.mul_succ]
      omega
  | walk count index r =>
    obtain ⟨l, x, code⟩ := r
    cases l with
    | zero =>
      cases hb : base x with
      | false =>
        have ht : t = .halt false := by simpa [controlStep, hb, eq_comm] using h
        subst t
        simp [controlPotential]
      | true =>
        have ht : t = .scan count index := by simpa [controlStep, hb, eq_comm] using h
        subst t
        simp only [controlPotential]
        omega
    | succ l =>
      cases hc : child (l + 1) x (code % radix) with
      | none =>
        have ht : t = .scan count index := by simpa [controlStep, hc, eq_comm] using h
        subst t
        simp only [controlPotential]
        omega
      | some y =>
        have ht : t = .walk count index ⟨l, y, code / radix⟩ := by
          simpa [controlStep, hc, eq_comm] using h
        subst t
        simp only [controlPotential]
        omega

/-- Execute at most n controller steps. Once halted, preserve the state. -/
def runWithin (next : Control → Option Control) : Nat → Control → Control
  | 0, s => s
  | n + 1, s =>
    match next s with
    | none => s
    | some t => runWithin next n t

theorem runWithin_eq_halt (child : Child) (base : Nat → Bool) (radix total root : Nat)
    {s t : Control} (run : ControlRuns child base radix total root s t)
    (hh : controlStep child base radix total root t = none)
    {n : Nat} (hn : controlPotential total s ≤ n) :
    runWithin (controlStep child base radix total root) n s = t := by
  induction run generalizing n with
  | refl s =>
    cases n <;> simp [runWithin, hh]
  | head hs run ih =>
    have hdrop := controlStep_decreases child base radix total root hs
    cases n with
    | zero => omega
    | succ n =>
      simp only [runWithin, hs]
      exact ih hh (by omega)

/-- The controller halts within a polynomially bounded number of its own
transitions when the ordinal width is linear in the source log-order. -/
theorem runWithin_decides (child : Child) (base : Nat → Bool) (radix total root : Nat) :
    runWithin (controlStep child base radix total root)
      ((total + 2) * radix ^ total + 1) (.scan (radix ^ total) 0) =
    .halt (decide child base radix total root) := by
  exact runWithin_eq_halt child base radix total root
    (control_scan_runs child base radix total root (radix ^ total) 0)
    rfl (Nat.le_refl _)

theorem scanCount_le_polynomial {source radix total rounds : Nat} (hSource : 0 < source)
    (hRounds : rounds * rounds ≤ 25 * source.log2) (hLevel : total ≤ 2 * rounds)
    (hRadix : radix ≤ 2 ^ ordinalWidth source.log2) :
    radix ^ total ≤ (source * 2) ^ 54 := by
  have hwidth := packedWidth_le source.log2 rounds total hRounds hLevel
  calc
    radix ^ total ≤ (2 ^ ordinalWidth source.log2) ^ total :=
      Nat.pow_le_pow_left hRadix total
    _ = 2 ^ (total * ordinalWidth source.log2) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (54 * (source.log2 + 1)) := Nat.pow_le_pow_right (by decide) hwidth
    _ = (2 ^ (source.log2 + 1)) ^ 54 := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (source * 2) ^ 54 := by
      apply Nat.pow_le_pow_left _ 54
      rw [Nat.pow_add_one]
      exact Nat.mul_le_mul_right 2 (Nat.log2_self_le (Nat.ne_of_gt hSource))


private theorem controlBinaryFits_pad {packed target labelWidth depthWidth : Nat}
    (hPacked : packed ≤ target) {s : Control}
    (h : ControlBinaryFits packed labelWidth depthWidth s) :
    ControlBinaryFits target labelWidth depthWidth s := by
  have hPow : 2 ^ packed ≤ 2 ^ target := Nat.pow_le_pow_right (by decide) hPacked
  have hPowSucc : 2 ^ (packed + 1) ≤ 2 ^ (target + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  cases s with
  | halt => trivial
  | scan count index =>
    exact ⟨Nat.lt_of_lt_of_le h.1 hPowSucc, Nat.lt_of_lt_of_le h.2 hPowSucc⟩
  | walk count index r =>
    exact ⟨⟨Nat.lt_of_lt_of_le h.1.1 hPowSucc, Nat.lt_of_lt_of_le h.1.2 hPowSucc⟩,
      h.2.1, h.2.2.1, Nat.lt_of_lt_of_le h.2.2.2 hPow⟩

private theorem level_le_log {h total rounds : Nat}
    (hRounds : rounds * rounds ≤ 25 * h) (hDepth : total ≤ 2 * rounds) :
    total ≤ 50 * h := by
  have hle : rounds ≤ rounds * rounds := by
    by_cases hr : rounds = 0
    · simp [hr]
    · have hr' : 1 ≤ rounds := by omega
      simpa using Nat.mul_le_mul_left rounds hr'
  omega

/-- A single linear-in-log-order bound for all reachable controller registers. -/
theorem controllerLogWidth (child : Child) (base : Nat → Bool)
    {source radix total root rounds : Nat} (hRadix : 0 < radix) (hRoot : root < source)
    (hChild : ∀ l x j y, x < source → child l x j = some y → y < source)
    (hRounds : rounds * rounds ≤ 25 * source.log2) (hDepth : total ≤ 2 * rounds)
    (hRadixWidth : radix ≤ 2 ^ ordinalWidth source.log2)
    {s : Control}
    (hr : ControlRuns child base radix total root (.scan (radix ^ total) 0) s) :
    ControlBinaryFits (54 * (source.log2 + 1)) (source.log2 + 1) (source.log2 + 6) s := by
  have htot := level_le_log hRounds hDepth
  have hlt : total < 2 ^ (source.log2 + 6) := by
    rw [Nat.pow_add]
    have hh : source.log2 < 2 ^ source.log2 := Nat.lt_two_pow_self
    change total < 2 ^ source.log2 * 64
    omega
  have hr' := control_fits_of_runs child base hRadix hRoot hChild hr
  have hb := controlFits_binary hRadixWidth (Nat.le_of_lt (Nat.lt_log2_self (n := source))) hlt hr'
  apply controlBinaryFits_pad _ hb
  rw [Nat.mul_comm]
  exact packedWidth_le source.log2 rounds total hRounds hDepth

/-- The controller's initialization budget is polynomial in the table order. -/
theorem initialPotential_le_polynomial {source radix total rounds : Nat} (hSource : 0 < source)
    (hRounds : rounds * rounds ≤ 25 * source.log2) (hDepth : total ≤ 2 * rounds)
    (hRadixWidth : radix ≤ 2 ^ ordinalWidth source.log2) :
    controlPotential total (.scan (radix ^ total) 0) ≤
      (50 * source + 2) * (source * 2) ^ 54 + 1 := by
  have ht := level_le_log hRounds hDepth
  have hs := Nat.log2_le_self source
  have hh : total + 2 ≤ 50 * source + 2 := by omega
  have hp := scanCount_le_polynomial hSource hRounds hDepth hRadixWidth
  exact Nat.add_le_add_right (Nat.mul_le_mul hh hp) 1


/-- The floor-logarithm of a radical quotient satisfies a geometric decrease
with a constant rounding term. -/
theorem radicalLog_shrinks {before after factor : Nat}
    (hAfter : 0 < after)
    (hprod : after * factor = before) (hOrder : after ≤ factor ^ 3) :
    4 * after.log2 ≤ 3 * before.log2 + 2 := by
  have ha4 : after ^ 4 ≤ before ^ 3 := by
    rw [← hprod, Nat.mul_pow, Nat.pow_add_one after 3]
    exact Nat.mul_le_mul_left _ hOrder
  have hlo : 2 ^ (4 * after.log2) ≤ after ^ 4 := by
    rw [Nat.mul_comm 4, Nat.pow_mul]
    exact Nat.pow_le_pow_left (Nat.log2_self_le (Nat.ne_of_gt hAfter)) 4
  have hhi : before ^ 3 < 2 ^ (3 * (before.log2 + 1)) := by
    rw [Nat.mul_comm 3, Nat.pow_mul]
    exact Nat.pow_lt_pow_left Nat.lt_log2_self (by decide)
  have hp := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp
    (Nat.lt_of_le_of_lt (Nat.le_trans hlo ha4) hhi)
  omega

/-- Shifting away two trailing bits eliminates the rounding term. This
measure is zero once the quotient has fewer than eight elements. -/
def radicalHeight (order : Nat) : Nat := order.log2 - 2

theorem radicalHeight_shrinks {before after factor : Nat}
    (hAfter : 0 < after)
    (hprod : after * factor = before) (hOrder : after ≤ factor ^ 3) :
    4 * radicalHeight after ≤ 3 * radicalHeight before := by
  have h := radicalLog_shrinks hAfter hprod hOrder
  simp only [radicalHeight]
  omega

/-- Sum the widths of consecutively suspended small-quotient frames. -/
def levelSum (height : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => height start + levelSum height (start + 1) count

theorem levelSum_geometric (height : Nat → Nat) (start count : Nat)
    (h : ∀ j < count, 4 * height (start + j + 1) ≤ 3 * height (start + j)) :
    levelSum height start count ≤ 4 * height start := by
  induction count generalizing start with
  | zero => simp [levelSum]
  | succ count ih =>
    have hz := h 0 (by omega)
    simp only [Nat.add_zero] at hz
    have ht : levelSum height (start + 1) count ≤ 4 * height (start + 1) :=
      ih (start + 1) (fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (j + 1) (by omega))
    simp only [levelSum]
    omega

/-- Active quotient labels above the fixed small-order tail have a total width
at most sixteen times the first shifted logarithm. -/
theorem radicalLabelWidths_le (orders : Nat → Nat) (start count : Nat)
    (hHigh : ∀ j < count, 3 ≤ (orders (start + j)).log2)
    (hShrink : ∀ j < count,
      4 * radicalHeight (orders (start + j + 1)) ≤
        3 * radicalHeight (orders (start + j))) :
    levelSum (fun i => (orders i).log2 + 1) start count ≤
      16 * radicalHeight (orders start) := by
  have hsum := levelSum_geometric (fun i => radicalHeight (orders i)) start count hShrink
  have hpoint :
      levelSum (fun i => (orders i).log2 + 1) start count ≤
        4 * levelSum (fun i => radicalHeight (orders i)) start count := by
    clear hsum hShrink
    induction count generalizing start with
    | zero => simp [levelSum]
    | succ count ih =>
      have hz := hHigh 0 (by omega)
      simp only [Nat.add_zero] at hz
      have ht := ih (start + 1) (fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHigh (j + 1) (by omega))
      simp only [levelSum]
      unfold radicalHeight at *
      omega
  omega

private theorem height_mono_from (height : Nat → Nat)
    (h : ∀ j, 4 * height (j + 1) ≤ 3 * height j) (start count : Nat) :
    height (start + count) ≤ height start := by
  induction count with
  | zero => simp
  | succ count ih =>
    have ht := h (start + count)
    change height (start + count + 1) ≤ height start
    omega

private theorem halving_after_three (height : Nat → Nat)
    (h : ∀ j, 4 * height (j + 1) ≤ 3 * height j) (i : Nat) :
    2 * height (i + 3) ≤ height i := by
  have h0 := h i
  have h1 := h (i + 1)
  have h2 := h (i + 2)
  change 4 * height (i + 2) ≤ 3 * height (i + 1) at h1
  change 4 * height (i + 3) ≤ 3 * height (i + 2) at h2
  omega

private theorem blocks_le_height (height : Nat → Nat)
    (h : ∀ j, 4 * height (j + 1) ≤ 3 * height j) (start blocks : Nat) :
    2 ^ blocks * height (start + 3 * blocks) ≤ height start := by
  induction blocks with
  | zero => simp [Nat.pow_zero]
  | succ blocks ih =>
    have hnext := halving_after_three height h (start + 3 * blocks)
    have htip : start + 3 * (blocks + 1) = start + 3 * blocks + 3 := by omega
    change 2 ^ (blocks + 1) * height (start + 3 * (blocks + 1)) ≤ height start
    rw [Nat.pow_add_one, Nat.mul_assoc, htip]
    exact Nat.le_trans (Nat.mul_le_mul_left _ hnext) ih

/-- A still-positive shifted logarithm lies within a logarithmic number of
geometrically decreasing levels. Apply to the shifted logarithm to obtain
log-log depth in the original order. -/
theorem geometricDepth_lt (height : Nat → Nat) (start depth : Nat)
    (h : ∀ j, 4 * height (j + 1) ≤ 3 * height j)
    (hActive : 0 < height (start + depth)) :
    depth < 3 * ((height start).log2 + 1) := by
  have hdiv := Nat.div_add_mod depth 3
  have hdiff : start + 3 * (depth / 3) + depth % 3 = start + depth := by omega
  have hback := height_mono_from height h (start + 3 * (depth / 3)) (depth % 3)
  rw [hdiff] at hback
  have hpos : 0 < height (start + 3 * (depth / 3)) := Nat.lt_of_lt_of_le hActive hback
  have hpow : 2 ^ (depth / 3) ≤ height start :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ hpos) (blocks_le_height height h start (depth / 3))
  have hs : height start ≠ 0 := Nat.ne_of_gt
    (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hpow)
  have hlog := (Nat.le_log2 hs).mpr hpow
  have hmod := Nat.mod_lt depth (show 0 < 3 by decide)
  omega

end Mathproof.MinimumGeneration.TowerReplay
