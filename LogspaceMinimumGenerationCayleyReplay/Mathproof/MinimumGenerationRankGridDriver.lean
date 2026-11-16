import Mathproof.MinimumGenerationMacroDispatch
import Mathproof.MinimumGenerationRankScan

namespace Mathproof.MinimumGeneration.RankGridDriver

open SearchTransducer RankMinors RankBerkowitz

/-- The finite controller restarts a completed grid probe until its cursor is
exhausted. The result stays in a work bank for the enclosing rank caller. -/
structure ProbeCode (S W : Nat) where
  start : Fin S
  transition : MacroTransition S W
  more : Fin S → Bool

def ProbeCode.stages {S W : Nat} (P : ProbeCode S W) : Stages 1 S W where
  first := 0
  entry := fun _ => P.start
  transition := fun _ => P.transition
  next := fun _ q => if P.more q then some 0 else none

namespace ProbeCode

variable {S W : Nat} (P : ProbeCode S W)

abbrev Cfg := (P.stages.component 0).Config

structure Layout (Q : Type*) where
  ready : List Q → Nat → P.Cfg → Prop
  output : Nat → P.Cfg → Prop

def update {Q : Type*} (degree : Q → Nat) (test : Q → Bool) (best : Nat) (q : Q) : Nat :=
  if test q then max best (degree q) else best

/-- One physical probe must advance its cursor and keep the exact new running
maximum. Each premise certifies one concrete transition segment, including the
workspace bound and the unchanged prior output. -/
structure Contract {Q : Type*} (word : List Bool) (B : Nat) (degree : Q → Nat)
    (test : Q → Bool) (L : P.Layout Q) : Prop where
  exhausted : ∀ best c, L.ready [] best c →
    ∃ k d, (P.stages.component 0).BoundedSegment word B c d k ∧
      (P.stages.component 0).step word d = none ∧ P.more d.state = false ∧
      L.output best d ∧ d.outputReversed = c.outputReversed
  probe : ∀ q qs best c, L.ready (q::qs) best c →
    ∃ k d, (P.stages.component 0).BoundedSegment word B c d k ∧
      (P.stages.component 0).step word d = none ∧ P.more d.state = true ∧
      L.ready qs (update degree test best q) (P.stages.enter 0 d) ∧
      d.outputReversed = c.outputReversed

private theorem route {Q : Type*} {word : List Bool} {B : Nat} {degree : Q → Nat}
    {test : Q → Bool} {L : P.Layout Q}
    (h : P.Contract word B degree test L) (qs : List Q) (best : Nat)
    (c : P.Cfg) (hc : L.ready qs best c) :
    ∃ k d, P.stages.Routed word B 0 c 0 d k ∧
      (P.stages.component 0).step word d = none ∧ P.stages.next 0 d.state = none ∧
      L.output (qs.foldl (update degree test) best) d ∧ d.outputReversed = c.outputReversed := by
  induction qs generalizing best c with
  | nil =>
    obtain ⟨k,d,hSeg,hStop,hNone,hOut,hPrior⟩ := h.exhausted best c hc
    exact ⟨k,d,.finish hSeg,hStop,by simp [stages,hNone],hOut,hPrior⟩
  | cons q qs ih =>
    obtain ⟨k,d,hSeg,hStop,hNext,hReady,hPrior⟩ := h.probe q qs best c hc
    obtain ⟨l,z,hTail,hLast,hDone,hOut,hPrior'⟩ := ih _ _ hReady
    have hr : P.stages.next 0 d.state = some 0 := by simp [stages,hNext]
    exact ⟨k+1+l,z,.call hSeg hStop hr hTail,hLast,hDone,hOut,hPrior'.trans hPrior⟩

theorem execute {Q : Type*} {word : List Bool} {B : Nat} {degree : Q → Nat}
    {test : Q → Bool} {L : P.Layout Q} (h : P.Contract word B degree test L)
    (qs : List Q) (best : Nat) (c : P.Cfg) (hc : L.ready qs best c) :
    ∃ k d, P.stages.machine.BoundedSegment word B (P.stages.tag 0 c) (P.stages.tag 0 d) k ∧
      P.stages.machine.step word (P.stages.tag 0 d) = none ∧
      L.output (qs.foldl (update degree test) best) d ∧ d.outputReversed = c.outputReversed := by
  obtain ⟨k,d,hRoute,hStop,hNext,hOut,hPrior⟩ := P.route h qs best c hc
  obtain ⟨hs,hc⟩ := P.stages.routed_stop hRoute hStop hNext
  exact ⟨k,d,hs,hc,hOut,hPrior⟩

end ProbeCode

open ProbeCode

private theorem fold_le_iff {Q : Type*} (degree : Q → Nat) (test : Q → Bool)
    (qs : List Q) (best cap : Nat) :
    qs.foldl (update degree test) best ≤ cap ↔
      best ≤ cap ∧ ∀ q ∈ qs, test q = true → degree q ≤ cap := by
  induction qs generalizing best with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons,ih]
    by_cases h : test q = true
    · simp only [update,h,if_true,max_le_iff,List.mem_cons]
      constructor
      · rintro ⟨⟨hb,hd⟩,ht⟩
        refine ⟨hb,?_⟩
        intro s hs hv
        rcases hs with rfl | hs
        · exact hd
        · exact ht s hs hv
      · rintro ⟨hb,ht⟩
        exact ⟨⟨hb,ht q (Or.inl rfl) h⟩,fun s hs => ht s (Or.inr hs)⟩
    · simp only [update,h,if_false,List.mem_cons]
      constructor
      · rintro ⟨hb,ht⟩
        refine ⟨hb,?_⟩
        intro s hs hv
        rcases hs with rfl | hs
        · exact (h hv).elim
        · exact ht s hs hv
      · rintro ⟨hb,ht⟩
        exact ⟨hb,fun s hs => ht s (Or.inr hs)⟩

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m n : Nat}

noncomputable def probe (A : Matrix (Fin m) (Fin n) K) (a : K → Fin m → K) (b : K → Fin n → K)
    (q : K × Fin (n+1)) : Bool :=
  decide (Berkowitz.balancedCoefficient (weightedGram A (a q.1) (b q.1))
    ⟨n-q.2.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ≠ 0)

theorem fold_eq_grid (A : Matrix (Fin m) (Fin n) K)
    (a : K → Fin m → K) (b : K → Fin n → K) (qs : List (K × Fin (n+1)))
    (hCover : ∀ q, q ∈ qs) :
    qs.foldl (update (fun q => q.2.val) (probe A a b)) 0 =
      scanWeightedBerkowitzRank A a b := by
  unfold scanWeightedBerkowitzRank
  apply Nat.le_antisymm
  · apply (fold_le_iff _ _ _ _ _).mpr
    refine ⟨Nat.zero_le _,?_⟩
    intro q _ hq
    apply Finset.le_sup (b := q) (f := fun t : K × Fin (n+1) => t.2.val)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, of_decide_eq_true hq⟩
  · apply Finset.sup_le_iff.mpr
    intro q hq
    have hw := (fold_le_iff (fun q : K × Fin (n+1) => q.2.val) (probe A a b) qs 0 _
      ).mp (Nat.le_refl _)
    exact hw.2 q (hCover q) (decide_eq_true (Finset.mem_filter.mp hq).2)

/-- The physical outer scan returns the exact weighted Berkowitz scan as
soon as its prepared single-probe executable has been supplied. -/
theorem executeBerkowitzScan {S W : Nat} (P : ProbeCode S W) {word : List Bool} {B : Nat}
    (A : Matrix (Fin m) (Fin n) K) (a : K → Fin m → K) (b : K → Fin n → K)
    (L : P.Layout (K × Fin (n+1)))
    (h : P.Contract word B (fun q => q.2.val) (probe A a b) L)
    (qs : List (K × Fin (n+1))) (hCover : ∀ q, q ∈ qs)
    (c : P.Cfg) (hc : L.ready qs 0 c) :
    ∃ k d, P.stages.machine.BoundedSegment word B (P.stages.tag 0 c) (P.stages.tag 0 d) k ∧
      P.stages.machine.step word (P.stages.tag 0 d) = none ∧
      L.output (scanWeightedBerkowitzRank A a b) d ∧ d.outputReversed = c.outputReversed := by
  obtain ⟨k,d,hs,hh,ho,hp⟩ := P.execute h qs 0 c hc
  rw [fold_eq_grid A a b qs hCover] at ho
  exact ⟨k,d,hs,hh,ho,hp⟩

end Mathproof.MinimumGeneration.RankGridDriver
