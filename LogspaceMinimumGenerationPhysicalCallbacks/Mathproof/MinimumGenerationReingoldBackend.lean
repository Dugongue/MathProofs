import Mathproof.MinimumGenerationConnectivity

namespace Mathproof.MinimumGeneration.ReingoldBackend

open Connectivity

/-- Addressed reader transition with a virtual bit source. The bit source
defaults to false when no input address is requested. -/
def next {Q : Type*} (halt : Q → Bool) (address : Q → Option ℕ)
    (step : Q → Bool → Q × List Bool) (read : ℕ → Bool) (c : Q × List Bool) :
    Q × List Bool :=
  if halt c.1 then c
  else
    let r := step c.1 ((address c.1).elim false read)
    (r.1, c.2 ++ r.2)

/-- An exact run with the bit source invoked only when its current control
state requests a virtual input address. -/
def run {Q : Type*} (init : Q) (halt : Q → Bool) (address : Q → Option ℕ)
    (step : Q → Bool → Q × List Bool) (read : ℕ → Bool) (ticks : ℕ) : Q × List Bool :=
  (next halt address step read)^[ticks] (init, [])

theorem run_read_congr {Q : Type*} (init : Q) (halt : Q → Bool) (address : Q → Option ℕ)
    (step : Q → Bool → Q × List Bool) {f g : ℕ → Bool} (hread : ∀ i, f i = g i) (ticks : ℕ) :
    run init halt address step f ticks = run init halt address step g ticks := by
  rw [funext hread]

/-- The materialized and virtual encodings induce the same state, output and
next-address request at every prefix, including after the reader has halted. -/
theorem run_ustconRead {Q : Type*} {n : ℕ} (init : Q) (halt : Q → Bool) (address : Q → Option ℕ)
    (step : Q → Bool → Q × List Bool) (bits : AdjBits (Fin n)) (s t : Fin n) (ticks : ℕ) :
    run init halt address step (ustconRead bits s t) ticks =
      run init halt address step (fun i => ((ustconWord bits s t)[i]?).getD false) ticks :=
  run_read_congr init halt address step (ustconRead_spec bits s t) ticks

/-- A bound on every encoded state of a certified addressed-run correctness
proof transfers to the virtual graph source without an adjacency matrix. -/
theorem run_virtual_exact {Q : Type*} {n : ℕ}
    (init : Q) (halt : Q → Bool) (address : Q → Option ℕ) (step : Q → Bool → Q × List Bool)
    (encode : Q → List Bool) (bits : AdjBits (Fin n)) (s t : Fin n) (verdict : Bool)
    (B : ℕ)
    (correct : ∃ k,
      let c := run init halt address step (fun i => ((ustconWord bits s t)[i]?).getD false) k
      halt c.1 = true ∧ c.2 = [verdict])
    (bounded : ∀ k,
      (encode (run init halt address step
        (fun i => ((ustconWord bits s t)[i]?).getD false) k).1).length ≤ B) :
    (∃ k, let c := run init halt address step (ustconRead bits s t) k
      halt c.1 = true ∧ c.2 = [verdict]) ∧
      ∀ k, (encode (run init halt address step (ustconRead bits s t) k).1).length ≤ B := by
  obtain ⟨k, hk⟩ := correct
  refine ⟨⟨k, ?_⟩, ?_⟩
  · dsimp only at hk ⊢
    rw [run_ustconRead]
    exact hk
  · intro j
    rw [run_ustconRead]
    exact bounded j


section Evaluation

variable {Q : Type*} (halt : Q → Bool) (address : Q → Option ℕ)
  (step : Q → Bool → Q × List Bool) (read : ℕ → Bool)

private abbrev transition := next halt address step read

/-- The proposition used to justify the loop's termination. The extracted
program runs the actual transition and can test halting without a fuel register. -/
def Eventually (c : Q × List Bool) : Prop :=
  ∃ k, halt ((transition halt address step read)^[k] c).1 = true

private theorem find_positive (c : Q × List Bool)
    (h : Eventually halt address step read c) (notDone : halt c.1 ≠ true) :
    0 < Nat.find h := by
  by_contra hn
  have hz : Nat.find h = 0 := by omega
  have hm := Nat.find_spec h
  rw [hz] at hm
  exact notDone hm

private theorem tail_exists (c : Q × List Bool)
    (h : Eventually halt address step read c) (notDone : halt c.1 ≠ true) :
    Eventually halt address step read (transition halt address step read c) := by
  have positive := find_positive halt address step read c h notDone
  refine ⟨Nat.find h - 1, ?_⟩
  rw [← Function.iterate_succ_apply, show (Nat.find h - 1).succ = Nat.find h by omega]
  exact Nat.find_spec h

private theorem tail_smaller (c : Q × List Bool)
    (h : Eventually halt address step read c) (notDone : halt c.1 ≠ true) :
    Nat.find (tail_exists halt address step read c h notDone) < Nat.find h := by
  have positive := find_positive halt address step read c h notDone
  have hm : halt ((transition halt address step read)^[Nat.find h - 1]
      (transition halt address step read c)).1 = true := by
    rw [← Function.iterate_succ_apply, show (Nat.find h - 1).succ = Nat.find h by omega]
    exact Nat.find_spec h
  exact (Nat.find_min' _ hm).trans_lt (Nat.sub_lt positive (by decide))

/-- The executable addressed-reader evaluation. Its well-founded measure
exists only in the proof and is erased from the machine-level data. -/
def evaluate (c : Q × List Bool) (terminates : Eventually halt address step read c) : List Bool :=
  if h : halt c.1 = true then c.2
  else evaluate (transition halt address step read c)
    (tail_exists halt address step read c terminates h)
termination_by Nat.find terminates
decreasing_by exact tail_smaller halt address step read c terminates h

theorem evaluate_eq_at_halt (c : Q × List Bool) (k : ℕ)
    (h : halt ((transition halt address step read)^[k] c).1 = true) :
    evaluate halt address step read c (show Eventually halt address step read c from ⟨k, h⟩) =
      ((transition halt address step read)^[k] c).2 := by
  induction k generalizing c with
  | zero =>
    change halt c.1 = true at h
    rw [evaluate, dif_pos h]
    rfl
  | succ k ih =>
    rw [evaluate, Function.iterate_succ_apply]
    split
    · rename_i hDone
      have hf : transition halt address step read c = c := by simp [next, hDone]
      rw [hf, Function.iterate_fixed hf]
    · apply ih
      simpa only [Function.iterate_succ_apply] using h

end Evaluation

/-- A single executable loop consumes the virtual adjacency input and returns
the checked verdict of the same program on the materialized encoding. -/
theorem evaluate_virtual_exact {Q : Type*} {n : ℕ}
    (init : Q) (halt : Q → Bool) (address : Q → Option ℕ) (step : Q → Bool → Q × List Bool)
    (bits : AdjBits (Fin n)) (s t : Fin n) (verdict : Bool)
    (correct : ∃ k,
      let c := run init halt address step (fun i => ((ustconWord bits s t)[i]?).getD false) k
      halt c.1 = true ∧ c.2 = [verdict]) :
    ∃ h : Eventually halt address step (ustconRead bits s t) (init, []),
      evaluate halt address step (ustconRead bits s t) (init, []) h = [verdict] := by
  obtain ⟨k, stop, answer⟩ := correct
  have stop' : halt (run init halt address step (ustconRead bits s t) k).1 = true := by
    rw [run_ustconRead]
    exact stop
  have answer' : (run init halt address step (ustconRead bits s t) k).2 = [verdict] := by
    rw [run_ustconRead]
    exact answer
  exact ⟨⟨k, stop'⟩, (evaluate_eq_at_halt _ _ _ _ _ k stop').trans answer'⟩

end Mathproof.MinimumGeneration.ReingoldBackend
