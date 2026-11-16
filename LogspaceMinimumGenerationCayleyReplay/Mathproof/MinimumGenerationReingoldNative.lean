/-
Use the Reingold addressed reader and correctness proofs of Samuel
Schlesinger and contributors to Complexitylib / CSLib Frontier.
The reused modules and their Apache-2.0 license are distributed separately.
-/
import Mathproof.MinimumGenerationReingoldBackend
import Mathproof.MinimumGenerationReingoldLiveInput
import Complexity.Computability.USTCON.Reader.Invariant

namespace Mathproof.MinimumGeneration.ReingoldNative

open Connectivity ReingoldBackend
open Cslib.Complexity

private abbrev Reader := Cslib.USTCON.Reader.State
private abbrev backend := Cslib.USTCON.Reader.machine

private theorem encode_eq (I : USTCONInstance) : I.encode = ustconWord I.adj I.s I.t := by
  have hm : I.toSTCONInstance.matrix =
      List.ofFn (fun i : Fin (I.n * I.n) => matrixRead I.adj I.s.isLt.pos i.val) := by
    apply List.ofFn_inj.mpr
    funext i
    unfold matrixRead
    have hi : i.val < I.n * I.n := i.isLt
    rw [dif_pos hi]
    rfl
  change I.toSTCONInstance.encode = _
  rw [STCONInstance.encode, hm]
  change _ = ((List.replicate I.n true ++ [false]) ++
      ((List.replicate I.s true ++ [false]) ++ ((List.replicate I.t true ++ [false]) ++ []))) ++
    List.ofFn (fun i : Fin (I.n * I.n) => matrixRead I.adj I.s.isLt.pos i.val)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  rfl

private def convert (q : Turing.ReadMachine.Cfg Reader) : Reader × List Bool :=
  (q.state, q.out)

private theorem semiconj (I : USTCONInstance) :
    Function.Semiconj convert (backend.next I.encode)
      (next backend.halt backend.addr backend.step (fun i => I.encode.getD i false)) := by
  intro q
  unfold Turing.ReadMachine.next Turing.ReadMachine.readBit next
  by_cases h : backend.halt q.state = true
  · simp [h, convert]
  · simp only [h, convert]
    cases backend.addr q.state <;> rfl

private theorem exact_materialized (I : USTCONInstance) (k : ℕ) :
    run backend.init backend.halt backend.addr backend.step
      (fun i => ((ustconWord I.adj I.s I.t)[i]?).getD false) k =
      convert (backend.run I.encode k) := by
  rw [← encode_eq I]
  exact ((semiconj I).iterate_right k ⟨backend.init, []⟩).symm

/-- Every actual Reingold read request is serviced by the unmaterialized
adjacency callback, with the same full run at every finite prefix. -/
theorem exact_read (I : USTCONInstance) (k : ℕ) :
    run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k =
      convert (backend.run I.encode k) :=
  (run_ustconRead _ _ _ _ I.adj I.s I.t k).trans (exact_materialized I k)

/-- The explicit scalar and stack bounds of the actual reader survive on the
virtual input run. -/
theorem state_bounds (I : USTCONInstance) (k : ℕ) :
    Cslib.USTCON.Reader.Bounds I
      (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).1 := by
  rw [exact_read]
  exact (Cslib.USTCON.Reader.inv_run (I := I) k).1

private theorem termination (I : USTCONInstance) :
    Eventually backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) (backend.init, []) := by
  obtain ⟨k, h, _⟩ := Cslib.USTCON.Reader.exists_run_eq I
  refine ⟨k, ?_⟩
  change backend.halt
    (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).1 = true
  rw [exact_read]
  exact h

/-- An executable decision procedure calling the actual imported Reingold
reader. Only the virtual input accessor is evaluated. -/
def execute (I : USTCONInstance) : Bool :=
  (evaluate backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t)
    (backend.init, []) (termination I)).headD false

theorem execute_spec (I : USTCONInstance) : execute I = true ↔ I.graph.Reachable I.s I.t := by
  classical
  obtain ⟨k, stop, answer⟩ := Cslib.USTCON.Reader.exists_run_eq I
  have halt : backend.halt
      (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).1 = true := by
    rw [exact_read]
    exact stop
  have out :
      (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).2 =
        [decide (I ∈ USTCON)] := by
    rw [exact_read]
    exact answer
  unfold execute
  rw [evaluate_eq_at_halt _ _ _ _ _ k halt]
  change (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).2.headD false =
    true ↔ _
  rw [out]
  change decide (I ∈ USTCON) = true ↔ I ∈ USTCON
  simp


open Cslib.USTCON.Reader
open Cslib.Reachability.Reingold

/-- Bit allowance for the reader's eleven binary numerals, ten-way control,
and framed stacks. Binary numerals are charged twice their length for
self-delimiting framing. Labels fit in 65 bits and a frame adds a three-bit
program counter. A marker is charged for each stack item and terminator. -/
def stateBits (q : Reader) : ℕ :=
  24 + 2 * (q.cnt.size + q.n.size + q.s.size + q.t.size +
    q.depth.size + q.len.size + q.c.size + q.w.size + q.j.size +
    q.ev.vertex.1.size + q.ev.vertex.2.size) +
    66 * q.ev.lower.length + 69 * q.ev.frames.length

private theorem size_counter {x T : ℕ} (h : x ≤ numLabels ^ T) : x.size ≤ 65 * T + 1 := by
  refine (Nat.size_le_size h).trans (Nat.size_le.2 ?_)
  calc numLabels ^ T ≤ (2 ^ 65) ^ T := Nat.pow_le_pow_left (by norm_num [numLabels]) T
    _ = 2 ^ (65 * T) := (pow_mul _ _ _).symm
    _ < 2 ^ (65 * T + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

private theorem stateBits_of_bounds (I : USTCONInstance) (q : Reader) (h : Bounds I q) :
    stateBits q ≤ 50000000 * (I.n.size + 1) := by
  set a := I.n.size
  have hD : depthOf I = 16 * a + 524 := rfl
  have hT : lenOf I = 4168 * a + 136240 := by simp only [lenOf, walkLength, depth]; ring
  have nSize (x : ℕ) (hx : x ≤ I.n) : x.size ≤ a := Nat.size_le_size hx
  have trivialSize (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have hcnt := nSize _ h.cnt
  have hn := nSize _ h.n
  have hs := nSize _ h.s
  have ht := nSize _ h.t
  have hv₁ := nSize _ h.v₁.le
  have hv₂ := nSize _ h.v₂.le
  have hd := (trivialSize _).trans h.depth
  have hl := (trivialSize _).trans h.len
  have hj := (trivialSize _).trans h.j
  have hc := size_counter h.c
  have hw := size_counter h.w
  have hstack := h.lower
  have hframes := h.frames
  simp only [hD, hT] at hd hl hj hc hw hstack hframes
  unfold stateBits
  omega

/-- Every prefix of the adapted Reingold reader satisfies a logarithmic
bit budget for its live scalar and stack fields. -/
theorem stateBits_bound (I : USTCONInstance) (k : ℕ) :
    stateBits (run backend.init backend.halt backend.addr backend.step (ustconRead I.adj I.s I.t) k).1 ≤
      50000000 * ((ustconWord I.adj I.s I.t).length.log2 + 2) := by
  refine (stateBits_of_bounds I _ (state_bounds I k)).trans (Nat.mul_le_mul_left _ ?_)
  have h := I.size_n_le_log2
  rw [encode_eq] at h
  omega


/-- Treat arbitrary supplied adjacency bits as an undirected simple graph.
On symmetric loopless bits this leaves each query's value unchanged. -/
def normalizedBits {n : ℕ} (bits : AdjBits (Fin n)) (a b : Fin n) : Bool :=
  if a = b then false else bits a b && bits b a

def instanceOf {n : ℕ} (bits : AdjBits (Fin n)) (s t : Fin n) : USTCONInstance where
  n := n
  adj := normalizedBits bits
  symm a b := by simp [normalizedBits, eq_comm, Bool.and_comm]
  loopless a := by simp [normalizedBits]
  s := s
  t := t

/-- The actual executable Reingold backend satisfies the callback decider
interface used by the project’s connectivity and Cayley word proofs. -/
def decider (n : ℕ) : Decider (Fin n) :=
  fun bits s t => execute (instanceOf bits s t)

theorem decider_correct (n : ℕ) : Correct (decider n) := by
  intro G bits describes s t
  have graphEq : (instanceOf bits s t).graph = G := by
    ext a b
    change Fin n at a b
    change normalizedBits bits a b = true ↔ G.Adj a b
    by_cases eq : a = b
    · subst b
      have noLoop : ¬ G.Adj a a := G.loopless.irrefl a
      simp [normalizedBits, noLoop]
    · rw [normalizedBits, if_neg eq, Bool.and_eq_true, describes, describes]
      exact ⟨And.left, fun h => ⟨h, h.symm⟩⟩
  unfold decider
  rw [execute_spec]
  change (instanceOf bits s t).graph.Reachable s t ↔ G.Reachable s t
  rw [graphEq]
  rfl


/-- Exact connectivity from the actual encoded Cayley table. The same
Reingold executable handles the full graph, rank prefixes, and edge deletion
through the checked raw adjacency reader. -/
theorem raw_cayley_query (n : ℕ) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : ReingoldLiveInput.Query n) (s t : Fin n) :
    decider n (ReingoldLiveInput.rawAdj (@encodeCayley n G.toMul) n
      G.toOne.one.val allowed query) s t = true ↔
      (ReingoldLiveInput.queryGraph n G allowed query).Reachable s t :=
  decider_correct n (ReingoldLiveInput.queryGraph n G allowed query) _
    (ReingoldLiveInput.rawAdj_correct n G allowed query) s t

end Mathproof.MinimumGeneration.ReingoldNative
