import Mathproof.MinimumGenerationNativeReingoldLowering
import Mathproof.MinimumGenerationReingoldLiveInput
import Mathproof.MinimumGenerationLatchedVerdict
import Complexity.Computability.Complexity.Problems.USTCON

namespace Mathproof.MinimumGeneration.NativeReingoldCayley

open Cslib.Complexity Connectivity ReingoldLiveInput SearchTransducer
open Turing.MultiTapeTM

/-- The graph-query instance has raw Cayley adjacency bits as its matrix. -/
def instanceOf (n : ℕ) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) : USTCONInstance where
  n := n
  adj := rawAdj (@encodeCayley n G.toMul) n G.toOne.one.val allowed query
  symm a b := by
    apply Bool.eq_iff_iff.mpr
    rw [rawAdj_correct, rawAdj_correct]
    exact ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
  loopless a := by
    cases h : rawAdj (@encodeCayley n G.toMul) n G.toOne.one.val allowed query a a
    · rfl
    · exact ((queryGraph n G allowed query).loopless.irrefl a
        ((rawAdj_correct n G allowed query a a).mp h)).elim
  s := s
  t := t

theorem graph_eq (n : ℕ) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) :
    (instanceOf n G allowed query s t).graph = queryGraph n G allowed query := by
  ext a b
  exact rawAdj_correct n G allowed query a b

theorem encode_eq (I : USTCONInstance) : encUSTCON I = ustconWord I.adj I.s I.t := by
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

theorem instance_encoding (n : ℕ) (G : Group (Fin n)) (allowed : Fin n → Bool)
    (query : Query n) (s t : Fin n) :
    encUSTCON (instanceOf n G allowed query s t) =
      virtualWord (@encodeCayley n G.toMul) n G.toOne.one.val allowed query s t := by
  rw [encode_eq]
  rfl

private theorem log_bound {raw virtual : List Bool} (h : virtual.length + 1 ≤ 4 * (raw.length + 1)) :
    (Nat.log2 virtual.length + 1) ≤ 3 * (Nat.log2 (raw.length + 1) + 1) := by
  have hPow := Nat.lt_log2_self (n := raw.length + 1)
  have hUpper : virtual.length + 1 < 2 ^ (Nat.log2 (raw.length + 1) + 3) := by
    rw [show Nat.log2 (raw.length + 1) + 3 = (Nat.log2 (raw.length + 1) + 1) + 2 by omega,
      Nat.pow_add]
    norm_num
    refine h.trans_lt ?_
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hPow (by decide : 0 < 4)
  by_cases hZero : virtual.length = 0
  · rw [hZero]
    simp only [Nat.log2_zero]
    omega
  · have hLt : virtual.length < 2 ^ (Nat.log2 (raw.length + 1) + 3) := by omega
    have hLog := (Nat.log2_lt hZero).mpr hLt
    omega

/-- The compiled finite controller consumes the project's virtual Cayley cells,
halts while retaining the caller's prior output, and leaves its verdict in
control. This contract is for the callback execution semantics. -/
def CallbackCertificate (M : SearchTransducer) (C : ℕ) : Prop := by
  classical
  exact ∀ n (G : Group (Fin n)) (allowed : Fin n → Bool) (query : Query n)
      (s t : Fin n) (prior : List Bool),
    let word := @encodeCayley n G.toMul
    let vw := virtualWord word n G.toOne.one.val allowed query s t
    let cell := virtualCell word n G.toOne.one.val allowed query s t
    let start := LatchedVerdict.lift M M.initial prior
    let machine := LatchedVerdict.machine M
    ∃ (k : ℕ) (d : machine.Config),
      callbackRun machine cell start k = some d ∧ callbackStep machine cell d = none ∧
      LatchedVerdict.state M d = some (decide ((queryGraph n G allowed query).Reachable s t)) ∧
      d.outputReversed = prior ∧ ∀ j c, callbackRun machine cell start j = some c →
        (-1 : Int) ≤ c.inputHead ∧ c.inputHead ≤ (vw.length : Int) ∧
        ∀ i, (c.workHead i).natAbs ≤ C * (Nat.log2 (word.length + 1) + 1)

open scoped Classical in
/-- A uniform native binary Reingold machine with the literal encoding and
answer. -/
def NativeCertificate : Prop :=
  ∃ (time : USTCONInstance → ℕ) (C : ℕ),
    ComputableInTimeAndSpace (fun I : USTCONInstance => decide (I ∈ USTCON))
      encUSTCON ⟨fun b : Bool => [b], by intro a b h; simpa using h⟩ time
      (fun I => C * (Nat.log2 (encUSTCON I).length + 1))

open scoped Classical in
/-- A uniform binary machine decides each literally encoded undirected graph.
The complete terminal output consists of the answer bit. -/
def EncodedRunCertificate (M : SearchTransducer) (C : ℕ) : Prop :=
  ∀ (I : USTCONInstance),
    let word := encUSTCON I
    ∃ (k : ℕ) (d : M.Config),
      M.BoundedSegment word (C * (Nat.log2 word.length + 1)) M.initial d k ∧
      M.step word d = none ∧ d.outputReversed = [decide (I ∈ USTCON)]

open scoped Classical in
/-- The latched graph machine works uniformly on all USTCON encodings. -/
def EncodedCertificate (M : SearchTransducer) (C : ℕ) : Prop :=
  ∀ (I : USTCONInstance) (prior : List Bool),
    let word := encUSTCON I
    let L := LatchedVerdict.machine M
    ∃ (k : ℕ) (d : L.Config),
      L.BoundedSegment word (C * (Nat.log2 word.length + 1))
        (LatchedVerdict.lift M M.initial prior) d k ∧
      L.step word d = none ∧ LatchedVerdict.state M d = some (decide (I ∈ USTCON)) ∧
      d.outputReversed = prior

/-- Lower the native machine while keeping its single literal output bit. -/
theorem liftEncodedRun (certificate : NativeCertificate) :
    ∃ M C, EncodedRunCertificate M C := by
  classical
  obtain ⟨time, C, K, Q, finiteQ, tm, correct⟩ := certificate
  letI : Finite Q := finiteQ
  letI : Fintype Q := Fintype.ofFinite Q
  let layout : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let M := NativeReingoldLowering.compile tm layout
  refine ⟨M, C, ?_⟩
  intro I
  let answer := decide (I ∈ USTCON)
  have cert := correct I
  change tm.ComputesInTimeAndSpace (encUSTCON I) [answer] (time I)
    (C * (Nat.log2 (encUSTCON I).length + 1)) at cert
  obtain ⟨k, d, hrun, hstop, hout⟩ :=
    NativeReingoldLowering.compile_correct tm layout (encUSTCON I) [answer] (time I) _ cert
  have hout' : d.outputReversed = [answer] := by
    have hh := congrArg List.reverse hout
    simpa using hh
  exact ⟨k, d, hrun, hstop, hout'⟩

/-- The native resource certificate supplies one latched finite controller for
all encoded undirected graph queries. -/
theorem liftEncodedCertificate (certificate : NativeCertificate) :
    ∃ M C, EncodedCertificate M C := by
  classical
  obtain ⟨M, C, encoded⟩ := liftEncodedRun certificate
  refine ⟨M, C, ?_⟩
  intro I prior
  obtain ⟨k, d, hrun, hstop, hout'⟩ := encoded I
  obtain ⟨hrun', hstop', hresult, hprior⟩ := LatchedVerdict.execute M (prior := prior) hrun hstop
  refine ⟨k, LatchedVerdict.lift M d prior, hrun', hstop', ?_, hprior⟩
  rw [hresult, hout']
  rfl

/-- Specialize the native graph controller to full, prefix and edge-deleted
Cayley graphs, with requests evaluated against the raw input callback. -/
theorem liftCertificate (certificate : NativeCertificate) :
    ∃ M C, CallbackCertificate M C := by
  classical
  obtain ⟨M, C, encoded⟩ := liftEncodedCertificate certificate
  refine ⟨M, 3 * C, ?_⟩
  intro n G allowed query s t prior
  let word := @encodeCayley n G.toMul
  let vw := virtualWord word n G.toOne.one.val allowed query s t
  let cell := virtualCell word n G.toOne.one.val allowed query s t
  let I := instanceOf n G allowed query s t
  have hs : encUSTCON I = vw := instance_encoding n G allowed query s t
  have hverdict : (I ∈ USTCON) = ((queryGraph n G allowed query).Reachable s t) := by
    change (I.graph.Reachable s t) = _
    rw [graph_eq]
    rfl
  obtain ⟨k, d, hrun, hstop, hresult, hprior⟩ := encoded I prior
  rw [hs] at hrun hstop
  refine ⟨k, d, ?_, ?_, ?_, hprior, ?_⟩
  · rw [cayley_callbackRun]
    exact hrun.1
  · rw [callbackStep_eq _ _ _ (virtualCell_spec word n G.toOne.one.val allowed query s t)]
    exact hstop
  · simpa [hverdict] using hresult
  · intro j c hj
    rw [cayley_callbackRun] at hj
    have hle : j ≤ k := by
      by_contra hh
      have he : j = k + 1 + (j - (k + 1)) := by omega
      rw [he, runFrom_add, SearchTransducer.runFrom, hrun.1, Option.bind_some, hstop] at hj
      simp at hj
    obtain ⟨lo, hi, work⟩ := hrun.2 j hle c hj
    have hL := log_bound (virtualWord_length_le n G allowed query s t)
    refine ⟨lo, hi, fun i => (work i).trans ?_⟩
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left C hL

end Mathproof.MinimumGeneration.NativeReingoldCayley
