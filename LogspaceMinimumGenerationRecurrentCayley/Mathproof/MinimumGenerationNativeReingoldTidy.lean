import Mathproof.MinimumGenerationNativeBipartiteExecution
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

namespace Mathproof.MinimumGeneration.NativeBipartiteReingold

open SearchTransducer ReingoldLiveInput NativeReingoldLowering
open Turing Turing.MultiTapeTM Cslib.Complexity

private theorem recoverRun {K N : ℕ} {Q : Type*} (tm : MultiTapeTM K Bool Q)
    (layout : Q ≃ Fin N) {word : List Bool} (c : Turing.Cfg K Bool Q word)
    (k : ℕ) {d : (compile tm layout).Config}
    (run : (compile tm layout).runFrom word (project tm layout c) k = some d) :
    d = project tm layout (tm.runFrom c k) := by
  induction k generalizing d with
  | zero =>
    cases run
    rfl
  | succ k ih =>
    rw [SearchTransducer.runFrom] at run
    obtain ⟨before, pre, step⟩ := Option.bind_eq_some_iff.mp run
    rw [ih pre, step_exact] at step
    split at step
    · contradiction
    · cases step
      change _ = project tm layout (tm.step^[Nat.succ k] c)
      rw [Function.iterate_succ_apply']
      rfl

private theorem compileTidy {K N : ℕ} {Q : Type*} (tm : MultiTapeTM K Bool Q)
    (layout : Q ≃ Fin N) (word answer : List Bool) (t s : ℕ)
    (cert : tm.ComputesTidilyInTimeAndSpace word answer t s) :
    ∃ (k : ℕ) (d : (compile tm layout).Config),
      (compile tm layout).BoundedSegment word s (compile tm layout).initial d k ∧
      (compile tm layout).step word d = none ∧ d.outputReversed.reverse = answer ∧
      d.inputHead = 0 ∧ d.workHead = (fun _ => 0) ∧ d.workCell = (fun _ _ => none) := by
  obtain ⟨k, d, hrun, hstop, hout⟩ :=
    compile_correct tm layout word answer t s cert.computesInTimeAndSpace
  let start := tm.initCfg word
  have projectRun : d = project tm layout (tm.runFrom start k) := by
    have hh := hrun.1
    rw [initial_exact] at hh
    exact recoverRun tm layout start k hh
  have halted : (tm.runFrom start k).state = none := by
    rw [projectRun, step_exact] at hstop
    split at hstop
    · assumption
    · contradiction
  have tidy : tm.runFrom start t = wordsCfg word none (fun _ => []) answer := by
    have hh := (computesTidily_iff_runFrom.mp cert).1
    simpa only [start, MultiTapeNTM.initCfg, Cfg.init_eq_wordsCfg] using hh
  have same : tm.runFrom start k = tm.runFrom start t := by
    by_cases h : k ≤ t
    · exact (tm.runFrom_eq_of_halt start h halted).symm
    · have stopT : (tm.runFrom start t).state = none := by rw [tidy]; rfl
      exact tm.runFrom_eq_of_halt start (by omega) stopT
  refine ⟨k, d, hrun, hstop, hout, ?_⟩
  rw [projectRun, same, tidy]
  simp [project, wordsCfg]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- The encoded binary connectivity machine starts and stops at the origin
with blank work tapes. Its output is the single answer bit. -/
def EncodedTidyCertificate (M : SearchTransducer) (C : ℕ) : Prop :=
  ∀ (I : USTCONInstance), let word := encUSTCON I
    ∃ (k : ℕ) (d : M.Config),
      M.BoundedSegment word (C * (Nat.log2 word.length + 1)) M.initial d k ∧
      M.step word d = none ∧ d.outputReversed = [decide (I ∈ USTCON)] ∧
      d.inputHead = 0 ∧ d.workHead = (fun _ => 0) ∧ d.workCell = (fun _ _ => none)

theorem nativeEncodedTidyRun : ∃ M C, EncodedTidyCertificate M C := by
  classical
  obtain ⟨t, C, original⟩ := NativeReingoldCayley.nativeBinaryCertificate
  obtain ⟨D, K, Q, finiteQ, tm, tidy⟩ :=
    original.exists_computableTidilyInTimeAndSpace
  letI : Finite Q := finiteQ
  letI : Fintype Q := Fintype.ofFinite Q
  let layout : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  refine ⟨compile tm layout, D * (C + 1), ?_⟩
  intro I
  let word := encUSTCON I
  let l := Nat.log2 word.length + 1
  let answer := decide (I ∈ USTCON)
  have cert := tidy I
  change tm.ComputesTidilyInTimeAndSpace word [answer] (2 * t I + 3 * (C * l) + D)
    (D * (C * l + 1)) at cert
  obtain ⟨k, d, run, halt, out, input, heads, work⟩ := compileTidy tm layout word [answer] _ _ cert
  have out' : d.outputReversed = [answer] := by simpa using congrArg List.reverse out
  refine ⟨k, d, ⟨run.1, ?_⟩, halt, out', input, heads, work⟩
  intro j hj c hc
  have ⟨lo, hi, space⟩ := run.2 j hj c hc
  refine ⟨lo, hi, fun i => (space i).trans ?_⟩
  have bound : D * (C * l + 1) ≤ (D * (C + 1)) * l := by
    rw [Nat.mul_assoc, Nat.add_mul, one_mul]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (by dsimp [l]; omega) _)
  exact bound

private theorem sameTerminal (M : SearchTransducer) (w : List Bool) (c : M.Config)
    {k l : ℕ} {d e : M.Config}
    (a : M.runFrom w c k = some d) (ha : M.step w d = none)
    (b : M.runFrom w c l = some e) (hb : M.step w e = none) : d = e := by
  have notAfter {u v : ℕ} {x y : M.Config} (h : u < v)
      (p : M.runFrom w c u = some x) (stop : M.step w x = none)
      (q : M.runFrom w c v = some y) : False := by
    have he : v = u + 1 + (v - (u + 1)) := by omega
    rw [he, SearchTransducer.runFrom_add, SearchTransducer.runFrom, p, Option.bind_some, stop] at q
    simp at q
  rcases lt_trichotomy k l with h | rfl | h
  · exact (notAfter h a ha b).elim
  · exact Option.some.inj (a.symm.trans b)
  · exact (notAfter h b hb a).elim

open scoped Classical in
/-- Actual physical work banks of the native Reingold machine are blank and
parked at its terminal configuration, even for the two-copy prefix query. -/
theorem nativePrefixTidyRun :
    ∃ (M : SearchTransducer) (C : Nat), ∀ {n : Nat}
      (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n),
      let word := @encodeCayley n G.toMul
      let cells := inputCells G eligible cut x
      ∃ (k : Nat) (d : M.Config),
        callbackRun M cells M.initial k = some d ∧ callbackStep M cells d = none ∧
        d.outputReversed = [decide (x ∈ @Subgroup.closure (Fin n) G (seed eligible cut))] ∧
        (∀ j c, j ≤ k → callbackRun M cells M.initial j = some c →
          (-1 : Int) ≤ c.inputHead ∧
          c.inputHead ≤ (encUSTCON (instanceOf G eligible cut x)).length ∧
          ∀ i, (c.workHead i).natAbs ≤ C * (Nat.log2 (word.length + 1) + 1)) ∧
        d.inputHead = 0 ∧ d.workHead = (fun _ => 0) ∧ d.workCell = (fun _ _ => none) := by
  obtain ⟨M, C, tidy⟩ := nativeEncodedTidyRun
  have ordinary : NativeReingoldCayley.EncodedRunCertificate M C := by
    intro I
    obtain ⟨k,d,hRun,hStop,hOut,_⟩ := tidy I
    exact ⟨k,d,hRun,hStop,hOut⟩
  refine ⟨M, 3 * C, ?_⟩
  intro n G eligible cut x
  obtain ⟨k,d,run,halt,out,bound⟩ := exactRun ordinary G eligible cut x
  let I := instanceOf G eligible cut x
  let word := encUSTCON I
  obtain ⟨l,e,erun,ehalt,_,clean⟩ := tidy I
  have sameCells := encodedCells G eligible cut x
  have dhalt : M.step word d = none := by
    change callbackStep M (inputCells G eligible cut x) d = none at halt
    rw [callbackStep_eq M word _ sameCells] at halt
    exact halt
  have drun : M.runFrom word M.initial k = some d := by
    change callbackRun M (inputCells G eligible cut x) M.initial k = some d at run
    rw [callbackRun_eq M word _ sameCells] at run
    exact run
  have same := sameTerminal M word M.initial drun dhalt erun.1 ehalt
  refine ⟨k,d,run,halt,out,bound,?_⟩
  simpa only [same] using clean

end Mathproof.MinimumGeneration.NativeBipartiteReingold
