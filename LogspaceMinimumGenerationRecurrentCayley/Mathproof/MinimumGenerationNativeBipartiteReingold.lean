import Mathproof.MinimumGenerationBipartiteGeometry
import Mathproof.MinimumGenerationNativeReingoldCayley
import Mathproof.MinimumGenerationVirtualVerdict

namespace Mathproof.MinimumGeneration.NativeBipartiteReingold

open Connectivity SearchTransducer ReingoldLiveInput
open Cslib.Complexity
open BipartiteCayley (split left right rawBits rawBits_correct bits_correct)

variable {n : Nat}

abbrev seed (eligible : Fin n → Bool) (cut : Nat) :=
  {z : Fin n | eligible z = true ∧ z.val < cut}

abbrev graph (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) :=
  (@BipartiteCayley.graph (Fin n) G (seed eligible cut)).comap split

theorem rawAdj (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (i j : Fin (n+n)) :
    rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut i j = true ↔
      (graph G eligible cut).Adj i j := by
  rw [rawBits_correct]
  exact bits_correct G eligible cut i j

def instanceOf (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n) :
    USTCONInstance where
  n := n+n
  adj := rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut
  symm a b := by
    apply Bool.eq_iff_iff.mpr
    rw [rawAdj, rawAdj]
    exact ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
  loopless a := by
    cases h : rawBits (@encodeCayley n G.toMul) G.toOne.one eligible cut a a
    · rfl
    · exact (((graph G eligible cut).loopless.irrefl a) ((rawAdj G eligible cut a a).mp h)).elim
  s := left G.toOne.one
  t := left x

private def vertexIndex (a : Fin n ⊕ Fin n) : Fin (n+n) :=
  match a with
  | .inl x => left x
  | .inr x => right x

private theorem split_index (a : Fin n ⊕ Fin n) : split (vertexIndex a) = a := by
  cases a <;> simp [vertexIndex]

private theorem reachable_eq (H : SimpleGraph (Fin n ⊕ Fin n)) (s t : Fin n) :
    (H.comap split).Reachable (left s) (left t) ↔ H.Reachable (.inl s) (.inl t) := by
  constructor
  · intro reach
    simpa only [SimpleGraph.Hom.comap_apply, BipartiteCayley.split_left] using
      reach.map (SimpleGraph.Hom.comap split H)
  · intro reach
    let f : H →g H.comap split := ⟨vertexIndex, by
      intro a b h
      change H.Adj (split (vertexIndex a)) (split (vertexIndex b))
      simpa only [split_index] using h⟩
    exact reach.map f

theorem instance_member (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n) :
    instanceOf G eligible cut x ∈ USTCON ↔ x ∈ @Subgroup.closure (Fin n) G (seed eligible cut) := by
  let I := instanceOf G eligible cut x
  have h : I.graph = graph G eligible cut := by
    ext a b
    exact rawAdj G eligible cut a b
  change I.graph.Reachable (left G.toOne.one) (left x) ↔ _
  rw [h]
  exact (reachable_eq (@BipartiteCayley.graph (Fin n) G (seed eligible cut)) G.toOne.one x).trans
    (@BipartiteCayley.reachable_iff_mem_closure (Fin n) G (seed eligible cut) x)

def inputCells (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n) :
    Int → InputCell :=
  let I := instanceOf G eligible cut x
  ustconCell I.adj I.s I.t

theorem encodedCells (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n)
    (j : Int) : inputCells G eligible cut x j =
      readInput (encUSTCON (instanceOf G eligible cut x)) j := by
  unfold inputCells
  rw [NativeReingoldCayley.encode_eq]
  exact ustconCell_spec _ _ _ j

open scoped Classical in
/-- The native two-copy run computes prefix subgroup membership with every
virtual position and workspace bound charged against the original input. -/
theorem exactRun {M : SearchTransducer} {C : Nat}
    (certificate : NativeReingoldCayley.EncodedRunCertificate M C)
    (G : Group (Fin n)) (eligible : Fin n → Bool) (cut : Nat) (x : Fin n) :
    let word := @encodeCayley n G.toMul
    let cells := inputCells G eligible cut x
    let limit := (3 * C) * (Nat.log2 (word.length + 1) + 1)
    ∃ (k : Nat) (d : M.Config),
      callbackRun M cells M.initial k = some d ∧ callbackStep M cells d = none ∧
      d.outputReversed = [decide (x ∈ @Subgroup.closure (Fin n) G (seed eligible cut))] ∧
      ∀ j c, j ≤ k → callbackRun M cells M.initial j = some c →
        (-1 : Int) ≤ c.inputHead ∧
        c.inputHead ≤ (encUSTCON (instanceOf G eligible cut x)).length ∧
        ∀ i, (c.workHead i).natAbs ≤ limit := by
  classical
  let I := instanceOf G eligible cut x
  let w := encUSTCON I
  let src := inputCells G eligible cut x
  have matchCell : ∀ j, src j = readInput w j := encodedCells G eligible cut x
  obtain ⟨k, d, run, halt, output⟩ := certificate I
  have matchAnswer : decide (I ∈ USTCON) =
      decide (x ∈ @Subgroup.closure (Fin n) G (seed eligible cut)) := by
    simp only [decide_eq_decide]
    exact instance_member G eligible cut x
  have spaceCost : C * (Nat.log2 w.length + 1) ≤
      (3 * C) * (Nat.log2 ((@encodeCayley n G.toMul).length + 1) + 1) := by
    have mono : Nat.log2 w.length ≤ Nat.log2 (w.length + 1) := by
      by_cases h : w.length = 0
      · simp [h]
      · apply (Nat.le_log2 (by omega)).2
        exact (Nat.log2_self_le h).trans (by omega)
    apply (Nat.mul_le_mul_left C (Nat.succ_le_succ mono)).trans
    change C * (Nat.log2 ((encUSTCON I).length + 1) + 1) ≤ _
    rw [NativeReingoldCayley.encode_eq]
    exact BipartiteCayley.nativeSpaceFromRaw G eligible cut G.toOne.one x C
  refine ⟨k, d, (callbackRun_eq M w _ matchCell _ _).trans run.1,
    (callbackStep_eq M w _ matchCell _).trans halt, output.trans (congrArg (fun b => [b]) matchAnswer), ?_⟩
  intro j c hj hr
  rw [callbackRun_eq M w _ matchCell] at hr
  obtain ⟨lo, hi, space⟩ := run.2 j hj c hr
  exact ⟨lo, hi, fun i => (space i).trans spaceCost⟩

end Mathproof.MinimumGeneration.NativeBipartiteReingold
