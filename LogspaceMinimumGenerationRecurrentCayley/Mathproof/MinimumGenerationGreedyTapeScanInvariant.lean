import Mathproof.MinimumGenerationGreedyTapeScan
import Batteries.Tactic.OpenPrivate

namespace Mathproof.MinimumGeneration.GreedyTapeScanInvariant

open SearchTransducer
open GreedyTapeScan (BitCall Prepared stages found)

open private compareSegment incrementSegment next_step foundAt from Mathproof.MinimumGenerationGreedyTapeScan

set_option backward.isDefEq.respectTransparency false

variable {S W : Nat}

variable (label order : Fin W) (widthStates : 7 ≤ S) (allowed member : BitCall S W)

/-- A tape-content invariant whose proof is independent of the live cursor value. -/
def Stable (invariant : (Fin W → Int → Option Bool) → Prop) :=
  ∀ (old new : Fin W → Int → Option Bool),
    (∀ j, j ≠ label → new j = old j) → invariant old → invariant new

/-- A physical callback may update its private workspace while maintaining
the invariant required for the next candidate. -/
def Leaf {n B : Nat} (word : List Bool) (i : Fin 4)
    (test : Fin n → Bool) (answer : Fin S → Bool) (keep : Set (Fin W))
    (invariant : (Fin W → Int → Option Bool) → Prop) :=
  let T := stages label order widthStates allowed member
  let P := T.component i
  ∀ (x : Fin n) (c : P.Config),
    c.state = T.entry i → Prepared word n x.val label order c → invariant c.workCell →
    ∃ (k : Nat) (d : P.Config), P.BoundedSegment word B c d k ∧ P.step word d = none ∧
      answer d.state = test x ∧ Prepared word n x.val label order d ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧
      ∀ j ∈ keep, d.workCell j = c.workCell j

private theorem scanRoute {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop)
    (stable : Stable label invariant) (hKeep : label ∉ keep) (different : label ≠ order)
    (hB : TableIO.width n + 1 ≤ B)
    (hEligible : Leaf label order widthStates allowed member (B := B) word 1 eligible allowed.answer keep invariant)
    (hMember : Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer keep invariant)
    (k : Nat) (hk : k ≤ n)
    (c : ((stages label order widthStates allowed member).component 0).Config)
    (hEntry : c.state = (stages label order widthStates allowed member).entry 0)
    (hc : Prepared word n k label order c)
    (hInv : invariant c.workCell) :
    let T := stages label order widthStates allowed member
    let expected := GreedyGenerator.next query eligible k
    ∃ (ticks : Nat) (phase : Fin 4) (d : (T.component phase).Config),
      T.Routed word B 0 c phase d ticks ∧ (T.component phase).step word d = none ∧
      T.next phase d.state = none ∧
      found label order widthStates allowed member (T.tag phase d) = expected.isSome ∧
      (∀ x : Fin n, expected = some x → Prepared word n x.val label order d) ∧
      (expected = none → Prepared word n n label order d) ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  let T := stages label order widthStates allowed member
  obtain ⟨tested, hCmp, hStop, hEqual, hInput, hHeads, hCells, hOut⟩ :=
    compareSegment label order widthStates allowed member hk hB c hEntry hc
  have hData : Prepared word n k label order tested :=
    ⟨hInput.symm ▸ hc.inputLo, hInput.symm ▸ hc.inputHi, hHeads.trans hc.heads,
      (congrFun hCells label).trans hc.cursor, (congrFun hCells order).trans hc.order⟩
  have hTest : invariant tested.workCell := by rw [hCells]; exact hInv
  by_cases hEnd : k = n
  · have hDone : T.next 0 tested.state = none := by simp [T, stages, hEqual.mpr hEnd]
    have expected : GreedyGenerator.next query eligible k = none := by
      simp [GreedyGenerator.next, hEnd, ChiefExecution.firstHitFrom]
    refine ⟨_, 0, tested, .finish hCmp, hStop, hDone, ?_, ?_, ?_, hOut, hTest, fun j _ => congrFun hCells j⟩
    · rw [foundAt, expected]
      rfl
    · intro x hx
      rw [expected] at hx
      contradiction
    · intro _
      simpa [hEnd] using hData
  have hlt : k < n := by omega
  let x : Fin n := ⟨k, hlt⟩
  have goAllow : T.next 0 tested.state = some 1 := by
    simp [T, stages, hEqual, hEnd]
  have advance (v : (T.component 3).Config) (he : v.state = T.entry 3)
      (hv : Prepared word n k label order v)
      (hV : invariant v.workCell) :
      ∃ (l : Nat) (f : Fin 4) (z : (T.component f).Config),
        T.Routed word B 3 v f z l ∧ (T.component f).step word z = none ∧ T.next f z.state = none ∧
        found label order widthStates allowed member (T.tag f z) =
          (GreedyGenerator.next query eligible (k+1)).isSome ∧
        (∀ a : Fin n, GreedyGenerator.next query eligible (k+1) = some a → Prepared word n a.val label order z) ∧
        (GreedyGenerator.next query eligible (k+1) = none → Prepared word n n label order z) ∧
        z.outputReversed = v.outputReversed ∧ invariant z.workCell ∧ ∀ j ∈ keep, z.workCell j = v.workCell j := by
    obtain ⟨inc, run, stop, prep, out, fixed⟩ :=
      incrementSegment label order widthStates allowed member hB v he hv different
    have routeBack : T.next 3 inc.state = some 0 := by rfl
    have prep' : Prepared word n (k+1) label order (T.enter 0 inc) :=
      ⟨prep.inputLo, prep.inputHi, prep.heads, prep.cursor, prep.order⟩
    obtain ⟨rest, f, z, hRun, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hInvOut, hFrame⟩ :=
      scanRoute query eligible keep invariant stable hKeep different hB hEligible hMember
        (k+1) (by omega) (T.enter 0 inc) rfl prep'
          (stable v.workCell inc.workCell fixed hV)
    exact ⟨_, f, z, .call run stop routeBack hRun, hHalt, hFinal, hFound, hLabel, hNone,
      hOutput.trans out, hInvOut, fun j hj => (hFrame j hj).trans (fixed j (fun he => hKeep (he ▸ hj)))⟩
  let a := T.enter 1 tested
  have hEligibleIn : Prepared word n x.val label order a :=
    ⟨hData.inputLo, hData.inputHi, hData.heads, hData.cursor, hData.order⟩
  obtain ⟨p, d, hAllowRun, hAllowStop, hAllowAns, hAllowPrep, hAllowOut, hAllowInv, hAllowFrame⟩ :=
    hEligible x a rfl hEligibleIn hTest
  cases hAllow : eligible x with
  | false =>
    have goInc : T.next 1 d.state = some 3 := by
      simp [T, stages, hAllowAns, hAllow, show (1 : Fin 4) ≠ 0 by decide]
    have prep : Prepared word n k label order (T.enter 3 d) :=
      ⟨hAllowPrep.inputLo, hAllowPrep.inputHi, hAllowPrep.heads, hAllowPrep.cursor, hAllowPrep.order⟩
    obtain ⟨l, f, z, tail, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hInvOut, hFrame⟩ :=
      advance (T.enter 3 d) rfl prep hAllowInv
    have hNext : GreedyGenerator.next query eligible k = GreedyGenerator.next query eligible (k+1) := by
      rw [next_step query eligible hlt]
      change (if GreedyGenerator.accept query eligible x then _ else _) = _
      simp [GreedyGenerator.accept, hAllow]
    refine ⟨_, f, z, .call hCmp hStop goAllow (.call hAllowRun hAllowStop goInc tail),
      hHalt, hFinal, ?_, ?_, ?_, hOutput.trans (hAllowOut.trans hOut), hInvOut, ?_⟩
    · rwa [hNext]
    · rwa [hNext]
    · rwa [hNext]
    · intro j hj
      exact (hFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j))
  | true =>
    have goMember : T.next 1 d.state = some 2 := by
      simp [T, stages, hAllowAns, hAllow, show (1 : Fin 4) ≠ 0 by decide]
    let m := T.enter 2 d
    have prepMem : Prepared word n x.val label order m :=
      ⟨hAllowPrep.inputLo, hAllowPrep.inputHi, hAllowPrep.heads, hAllowPrep.cursor, hAllowPrep.order⟩
    obtain ⟨r, checked, hQueryRun, hQueryStop, hQueryAns, hQueryPrep, hQueryOut, hQueryInv, hQueryFrame⟩ :=
      hMember x m rfl prepMem hAllowInv
    cases hQuery : query (GreedyGenerator.before eligible x.val) x with
    | false =>
      have halt : T.next 2 checked.state = none := by
        simp [T, stages, hQueryAns, hQuery, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
      have hNext : GreedyGenerator.next query eligible k = some x := by
        rw [next_step query eligible hlt]
        change (if GreedyGenerator.accept query eligible x then _ else _) = _
        simp [GreedyGenerator.accept, hAllow, hQuery]
        rfl
      refine ⟨_, 2, checked, .call hCmp hStop goAllow (.call hAllowRun hAllowStop goMember (.finish hQueryRun)),
        hQueryStop, halt, ?_, ?_, ?_, hQueryOut.trans (hAllowOut.trans hOut), hQueryInv, ?_⟩
      · rw [foundAt, hNext]
        rfl
      · intro a ha
        rw [hNext] at ha
        cases ha
        exact hQueryPrep
      · intro ha
        rw [hNext] at ha
        contradiction
      · intro j hj
        exact (hQueryFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j))
    | true =>
      have goInc : T.next 2 checked.state = some 3 := by
        simp [T, stages, hQueryAns, hQuery, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
      have prep : Prepared word n k label order (T.enter 3 checked) :=
        ⟨hQueryPrep.inputLo, hQueryPrep.inputHi, hQueryPrep.heads, hQueryPrep.cursor, hQueryPrep.order⟩
      obtain ⟨l, f, z, tail, hHalt, hFinal, hFound, hLabel, hNone, hOutput, hInvOut, hFrame⟩ :=
        advance (T.enter 3 checked) rfl prep hQueryInv
      have hNext : GreedyGenerator.next query eligible k = GreedyGenerator.next query eligible (k+1) := by
        rw [next_step query eligible hlt]
        change (if GreedyGenerator.accept query eligible x then _ else _) = _
        simp [GreedyGenerator.accept, hAllow, hQuery]
      refine ⟨_, f, z, .call hCmp hStop goAllow
          (.call hAllowRun hAllowStop goMember (.call hQueryRun hQueryStop goInc tail)),
        hHalt, hFinal, ?_, ?_, ?_, hOutput.trans (hQueryOut.trans (hAllowOut.trans hOut)), hInvOut, ?_⟩
      · rwa [hNext]
      · rwa [hNext]
      · rwa [hNext]
      · intro j hj
        exact (hFrame j hj).trans ((hQueryFrame j hj).trans ((hAllowFrame j hj).trans (congrFun hCells j)))
termination_by n - k
decreasing_by omega

/-- The fixed controller executes the entire candidate scan. The two leaves
decide eligibility and prefix membership for one live candidate each. The scan
installs no oracle for the least acceptable candidate. -/
theorem execute {word : List Bool} {n B : Nat}
    (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (keep : Set (Fin W)) (invariant : (Fin W → Int → Option Bool) → Prop)
    (stable : Stable label invariant) (hKeep : label ∉ keep) (different : label ≠ order)
    (hB : TableIO.width n + 1 ≤ B)
    (hEligible : Leaf label order widthStates allowed member (B := B) word 1 eligible allowed.answer keep invariant)
    (hMember : Leaf label order widthStates allowed member (B := B) word 2
      (fun x => query (GreedyGenerator.before eligible x.val) x) member.answer keep invariant)
    (k : Nat) (hk : k ≤ n)
    (c : ((stages label order widthStates allowed member).component 0).Config)
    (hEntry : c.state = (stages label order widthStates allowed member).entry 0)
    (hc : Prepared word n k label order c)
    (hInv : invariant c.workCell) :
    let T := stages label order widthStates allowed member
    let expected := GreedyGenerator.next query eligible k
    ∃ (ticks : Nat) (d : T.machine.Config),
      T.machine.BoundedSegment word B (T.tag 0 c) d ticks ∧ T.machine.step word d = none ∧
      found label order widthStates allowed member d = expected.isSome ∧
      (∀ x : Fin n, expected = some x → Prepared word n x.val label order d) ∧
      (expected = none → Prepared word n n label order d) ∧
      d.outputReversed = c.outputReversed ∧ invariant d.workCell ∧ ∀ j ∈ keep, d.workCell j = c.workCell j := by
  let T := stages label order widthStates allowed member
  obtain ⟨ticks, i, d, route, stop, done, answer, foundPrep, nonePrep, out, inv, frame⟩ :=
    scanRoute label order widthStates allowed member query eligible keep invariant stable hKeep different hB hEligible hMember
       k hk c hEntry hc hInv
  obtain ⟨run, halt⟩ := T.routed_stop route stop done
  refine ⟨ticks, T.tag i d, run, halt, answer, ?_, ?_, out, inv, frame⟩
  · intro x hx
    obtain ⟨a, b, h, p, q⟩ := foundPrep x hx
    exact ⟨a, b, h, p, q⟩
  · intro hx
    obtain ⟨a, b, h, p, q⟩ := nonePrep hx
    exact ⟨a, b, h, p, q⟩

end Mathproof.MinimumGeneration.GreedyTapeScanInvariant
