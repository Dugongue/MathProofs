import Mathproof.MinimumGenerationNativeReingoldTidy

namespace Mathproof.MinimumGeneration.NativeBipartiteReingold

open SearchTransducer ReingoldLiveInput Cslib.Complexity

/-- Keep the inspected window and permit arbitrary caller cells outside it. -/
def patchWork (M : SearchTransducer) (B : ℕ) (outside : Fin M.workTapes → Int → Option Bool)
    (c : M.Config) : M.Config :=
  { c with workCell := fun i p => if p.natAbs ≤ B then c.workCell i p else outside i p }

theorem callbackStep_patchWork (M : SearchTransducer) (B : ℕ)
    (outside : Fin M.workTapes → Int → Option Bool) (source : Int → InputCell)
    (c : M.Config) (bound : ∀ i, (c.workHead i).natAbs ≤ B) :
    callbackStep M source (patchWork M B outside c) =
      (callbackStep M source c).map (patchWork M B outside) := by
  have sc : (fun i => (patchWork M B outside c).workCell i ((patchWork M B outside c).workHead i)) =
      (fun i => c.workCell i (c.workHead i)) := by
    funext i
    simp [patchWork, bound i]
  unfold callbackStep
  change (M.transition c.state (source c.inputHead) _).map _ =
    ((M.transition c.state (source c.inputHead) (fun i => c.workCell i (c.workHead i))).map _).map _
  rw [sc]
  cases command : M.transition c.state (source c.inputHead) (fun i => c.workCell i (c.workHead i)) with
  | none => rfl
  | some op =>
    obtain ⟨q, move, write, output⟩ := op
    simp only [Option.map_some, Option.some.injEq]
    congr 1
    funext i p
    by_cases inside : p.natAbs ≤ B
    · simp [patchWork, inside]
    · have neq : p ≠ c.workHead i := fun eq => inside (by simpa only [eq] using bound i)
      simp [patchWork, inside, neq]

theorem callbackRun_patchWork (M : SearchTransducer) (B : ℕ)
    (outside : Fin M.workTapes → Int → Option Bool) (source : Int → InputCell)
    (start : M.Config) (k : ℕ)
    (bounds : ∀ j < k, ∀ c, callbackRun M source start j = some c →
      ∀ i, (c.workHead i).natAbs ≤ B) :
    callbackRun M source (patchWork M B outside start) k =
      (callbackRun M source start k).map (patchWork M B outside) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [callbackRun, callbackRun, ih (fun j hj => bounds j (by omega))]
    cases h : callbackRun M source start k
    · rfl
    next c =>
      change callbackStep M source (patchWork M B outside c) =
        (callbackStep M source c).map (patchWork M B outside)
      exact callbackStep_patchWork M B outside source c (bounds k (by omega) c h)

open scoped Classical in
/-- The checked native prefix trace with a finite blank input window. -/
def WindowCertificate (M : SearchTransducer) (C : ℕ) : Prop :=
  ∀ {n : ℕ}
      (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : ℕ) (x : Fin n)
      (outside : Fin M.workTapes → Int → Option Bool)
      (B : ℕ), C * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) ≤ B →
      let cells := inputCells G eligible cut x
      let start := patchWork M B outside M.initial
      ∃ (k : ℕ) (d : M.Config),
        callbackRun M cells start k = some d ∧ callbackStep M cells d = none ∧
        d.outputReversed = [decide (x ∈ @Subgroup.closure (Fin n) G (seed eligible cut))] ∧
        (∀ j c, j ≤ k → callbackRun M cells start j = some c →
          (-1 : Int) ≤ c.inputHead ∧
          c.inputHead ≤ (encUSTCON (instanceOf G eligible cut x)).length ∧
          ∀ i, (c.workHead i).natAbs ≤ B) ∧
        d.inputHead = 0 ∧ d.workHead = (fun _ => 0) ∧ d.workCell = start.workCell
/-- One actual finite tidy Reingold machine has a certificate for every
group query and arbitrary contents outside the initialized window. -/
theorem nativePrefixWindowRun : ∃ (M : SearchTransducer) (C : ℕ), WindowCertificate M C := by
  obtain ⟨M, C, certificate⟩ := nativePrefixTidyRun
  refine ⟨M, C, ?_⟩
  intro n G eligible cut x outside B budget
  let source := inputCells G eligible cut x
  obtain ⟨k,d,run,halt,out,bound,hInput,hHead,hBlank⟩ := certificate G eligible cut x
  have sim (j : ℕ) (hj : j ≤ k) :
      callbackRun M source (patchWork M B outside M.initial) j =
        (callbackRun M source M.initial j).map (patchWork M B outside) :=
    callbackRun_patchWork M B outside source M.initial j (fun i hi c h b =>
      ((bound i c (hi.le.trans hj) h).2.2 b).trans budget)
  have halt' : callbackStep M source (patchWork M B outside d) = none := by
    rw [callbackStep_patchWork _ _ _ _ _ (fun i => ((bound k d le_rfl run).2.2 i).trans budget)]
    rw [halt]
    rfl
  refine ⟨k, patchWork M B outside d, ?_, halt', out, ?_, hInput, hHead, ?_⟩
  · rw [sim k le_rfl, run]
    rfl
  · intro j c hJ hp
    rw [sim j hJ] at hp
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hp
    have a := bound j v hJ hv
    exact ⟨a.1,a.2.1,fun i => (a.2.2 i).trans budget⟩
  · simp [patchWork, hBlank, SearchTransducer.initial]

end Mathproof.MinimumGeneration.NativeBipartiteReingold
