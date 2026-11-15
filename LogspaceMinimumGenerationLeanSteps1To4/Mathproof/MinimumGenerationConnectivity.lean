import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathproof.MinimumGenerationCayley
import Mathproof.MinimumGenerationProblem
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-!
A decision-to-search reduction for undirected connectivity. The forest
is specified by independent edge-prefix queries, allowing an edge to be
recomputed while streaming a path. Resource claims about compiling the
decision oracle to a finite-control machine are outside this file.
-/

namespace Mathproof.MinimumGeneration.Connectivity

open SimpleGraph

variable {V : Type*}

/-- The subgraph using only ranks strictly below the threshold. -/
def earlier (G : SimpleGraph V) (rank : Sym2 V → Nat) (k : Nat) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ rank s(u, v) < k
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [← Sym2.eq_swap (a := u) (b := v)]
    exact h.2⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- Keep an edge exactly when its endpoints are disconnected at lower ranks. -/
def spanning (G : SimpleGraph V) (rank : Sym2 V → Nat) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (earlier G rank (rank s(u, v))).Reachable u v
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [← Sym2.eq_swap (a := u) (b := v)]
    intro hw
    exact h.2 hw.symm⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

private theorem reach_of_adj_reach {F H : SimpleGraph V}
    (h : ∀ {u v}, F.Adj u v → H.Reachable u v) {u v : V}
    (hr : F.Reachable u v) : H.Reachable u v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.rfl
  | cons ha _ ih => exact (h ha).trans ih

theorem earlier_spanning_reachable_iff (G : SimpleGraph V) (rank : Sym2 V → Nat)
    (k : Nat) (u v : V) :
    (earlier (spanning G rank) rank k).Reachable u v ↔ (earlier G rank k).Reachable u v := by
  constructor
  · intro h
    apply h.mono
    intro x y hx
    change (G.Adj x y ∧ ¬ (earlier G rank (rank s(x, y))).Reachable x y) ∧
      rank s(x, y) < k at hx
    exact ⟨hx.1.1, hx.2⟩
  have aux : ∀ k u v, (earlier G rank k).Reachable u v →
      (earlier (spanning G rank) rank k).Reachable u v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u v h
      apply reach_of_adj_reach _ h
      intro x y ha
      change G.Adj x y ∧ rank s(x, y) < k at ha
      by_cases hh : (earlier G rank (rank s(x, y))).Reachable x y
      · apply (ih (rank s(x, y)) ha.2 x y hh).mono
        exact fun _ _ h => ⟨h.1, Nat.lt_trans h.2 ha.2⟩
      · exact Adj.reachable ⟨⟨ha.1, hh⟩, ha.2⟩
  exact aux k u v

private theorem earlier_spanning_acyclic (G : SimpleGraph V) (rank : Sym2 V → Nat)
    (rank_inj : Function.Injective rank) (k : Nat) :
    (earlier (spanning G rank) rank k).IsAcyclic := by
  classical
  induction k with
  | zero =>
    have h : earlier (spanning G rank) rank 0 = ⊥ := by
      ext u v
      simp [earlier]
    rw [h]
    exact isAcyclic_bot
  | succ k ih =>
    by_cases hex : ∃ u v, (spanning G rank).Adj u v ∧ rank s(u, v) = k
    · obtain ⟨u, v, huv, hr⟩ := hex
      have heq : earlier (spanning G rank) rank (k + 1) =
          earlier (spanning G rank) rank k ⊔ edge u v := by
        ext x y
        rw [sup_adj, adj_edge]
        change ((spanning G rank).Adj x y ∧ rank s(x, y) < k + 1) ↔
          ((spanning G rank).Adj x y ∧ rank s(x, y) < k) ∨ (s(u, v) = s(x, y) ∧ x ≠ y)
        constructor
        · intro ⟨hxy, hlt⟩
          by_cases hlt' : rank s(x, y) < k
          · exact Or.inl ⟨hxy, hlt'⟩
          · exact Or.inr ⟨rank_inj (by omega), hxy.ne⟩
        · rintro (⟨hxy, hlt⟩ | ⟨he, _⟩)
          · exact ⟨hxy, by omega⟩
          · refine ⟨(adj_congr_of_sym2 _ he).mp huv, ?_⟩
            rw [← he, hr]
            omega
      rw [heq]
      apply ih.sup_edge_of_not_reachable
      intro h
      exact huv.2 (hr ▸ (earlier_spanning_reachable_iff G rank k u v).1 h)
    · have heq : earlier (spanning G rank) rank (k + 1) =
          earlier (spanning G rank) rank k := by
        ext x y
        change ((spanning G rank).Adj x y ∧ rank s(x, y) < k + 1) ↔
          ((spanning G rank).Adj x y ∧ rank s(x, y) < k)
        constructor
        · intro ⟨ha, hb⟩
          exact ⟨ha, by
            by_contra! hc
            exact hex ⟨x, y, ha, by omega⟩⟩
        · intro ⟨ha, hb⟩
          exact ⟨ha, by omega⟩
      simpa only [heq] using ih

/-- Pairwise rank identities make independent prefix tests a spanning forest. -/
theorem spanning_spec (G : SimpleGraph V) (rank : Sym2 V → Nat)
    (rank_inj : Function.Injective rank) (bound : Nat)
    (inside : ∀ {x y}, G.Adj x y → rank s(x, y) < bound) :
    (spanning G rank).IsAcyclic ∧ ∀ u v, (spanning G rank).Reachable u v ↔ G.Reachable u v := by
  have hfull : earlier G rank bound = G := by
    ext x y
    exact ⟨And.left, fun h => ⟨h, inside h⟩⟩
  have hf : earlier (spanning G rank) rank bound = spanning G rank := by
    ext x y
    exact ⟨And.left, fun h => ⟨h, inside h.1⟩⟩
  exact ⟨hf ▸ earlier_spanning_acyclic G rank rank_inj bound,
    fun u v => by simpa only [hfull, hf] using earlier_spanning_reachable_iff G rank bound u v⟩



private theorem first_step_iff (F : SimpleGraph V) (hF : F.IsAcyclic)
    {u w t : V} (huw : F.Adj u w) (p : F.Walk w t)
    (hp : (Walk.cons huw p).IsPath) (v : V) :
    (F.Adj u v ∧ (F.deleteEdges {s(u, v)}).Reachable v t) ↔ v = w := by
  have hu : u ∉ p.support := (Walk.cons_isPath_iff _ _).1 hp |>.2
  constructor
  · intro ⟨huv, hvt⟩
    by_contra hn
    have hfirst : s(u, v) ≠ s(u, w) := by
      intro he
      rcases Sym2.eq_iff.1 he with ⟨_, hvw⟩ | ⟨_, hvu⟩
      · exact hn hvw
      · exact huv.ne hvu.symm
    have htail : s(u, v) ∉ p.edges := fun he => hu (p.fst_mem_support_of_mem_edges he)
    have hut : (F.deleteEdges {s(u, v)}).Reachable u t :=
      reachable_deleteEdges_iff_exists_walk.2
        ⟨Walk.cons huw p, by simpa only [Walk.edges_cons, List.mem_cons, not_or] using (
          And.intro hfirst htail)⟩
    have hb := (isAcyclic_iff_forall_adj_isBridge.1 hF) huv
    exact (isBridge_iff.1 hb) (hut.trans hvt.symm)
  · rintro rfl
    exact ⟨huw, reachable_deleteEdges_iff_exists_walk.2
      ⟨p, fun he => hu (p.fst_mem_support_of_mem_edges he)⟩⟩

section Oracle

variable [DecidableEq V]

abbrev AdjBits (V : Type*) := V → V → Bool
abbrev Decider (V : Type*) := AdjBits V → V → V → Bool

/-- Semantic contract for a connectivity decider that accepts an adjacency predicate. -/
def Correct (solve : Decider V) : Prop :=
  ∀ (F : SimpleGraph V) (bits : AdjBits V),
    (∀ x y, bits x y = true ↔ F.Adj x y) →
    ∀ x y, solve bits x y = true ↔ F.Reachable x y

def earlierBits (bits : AdjBits V) (rank : Sym2 V → Nat) (k : Nat) : AdjBits V :=
  fun x y => bits x y && decide (rank s(x, y) < k)

def spanningBits (solve : Decider V) (bits : AdjBits V) (rank : Sym2 V → Nat) :
    AdjBits V :=
  fun x y => bits x y && !(solve (earlierBits bits rank (rank s(x, y))) x y)

def withoutBits (bits : AdjBits V) (u v : V) : AdjBits V :=
  fun x y => bits x y && decide (s(x, y) ≠ s(u, v))

omit [DecidableEq V] in
theorem earlierBits_spec (G : SimpleGraph V) (bits : AdjBits V)
    (hb : ∀ x y, bits x y = true ↔ G.Adj x y) (rank : Sym2 V → Nat) (k : Nat) (x y : V) :
    earlierBits bits rank k x y = true ↔ (earlier G rank k).Adj x y := by
  simp [earlierBits, earlier, hb]

omit [DecidableEq V] in
theorem spanningBits_spec (solve : Decider V) (hsolve : Correct solve)
    (G : SimpleGraph V) (bits : AdjBits V) (hb : ∀ x y, bits x y = true ↔ G.Adj x y)
    (rank : Sym2 V → Nat) (x y : V) :
    spanningBits solve bits rank x y = true ↔ (spanning G rank).Adj x y := by
  have h := hsolve (earlier G rank (rank s(x, y))) _ (earlierBits_spec G bits hb rank _) x y
  simp only [spanningBits, Bool.and_eq_true, Bool.not_eq_true', hb, spanning]
  rw [← Bool.not_eq_true, h]

theorem withoutBits_spec (G : SimpleGraph V) (bits : AdjBits V)
    (hb : ∀ x y, bits x y = true ↔ G.Adj x y) (u v x y : V) :
    withoutBits bits u v x y = true ↔ (G.deleteEdges {s(u, v)}).Adj x y := by
  simp only [withoutBits, Bool.and_eq_true, decide_eq_true_eq, hb, deleteEdges_adj, Set.mem_singleton_iff]

/-- The next path vertex is selected by testing the neighbors against
connectivity after removing the candidate edge. -/
def nextVertex (order : List V) (solve : Decider V) (bits : AdjBits V)
    (rank : Sym2 V → Nat) (u t : V) : Option V :=
  if u = t then none else
    let tree := spanningBits solve bits rank
    order.find? fun v => tree u v && solve (withoutBits tree u v) v t

theorem nextVertex_of_cons (order : List V) (covered : ∀ v : V, v ∈ order)
    (solve : Decider V) (hsolve : Correct solve) (G : SimpleGraph V) (bits : AdjBits V)
    (hb : ∀ x y, bits x y = true ↔ G.Adj x y) (rank : Sym2 V → Nat)
    (hF : (spanning G rank).IsAcyclic) {u v t : V}
    (huv : (spanning G rank).Adj u v) (p : (spanning G rank).Walk v t)
    (hp : (Walk.cons huv p).IsPath) :
    nextVertex order solve bits rank u t = some v := by
  have hne : u ≠ t := fun he => Walk.not_nil_cons (hp.nil_iff_eq.2 he)
  let tree := spanningBits solve bits rank
  let test := fun w => tree u w && solve (withoutBits tree u w) w t
  have ht (w : V) : test w = true ↔ w = v := by
    change (tree u w && solve (withoutBits tree u w) w t) = true ↔ w = v
    rw [Bool.and_eq_true, spanningBits_spec solve hsolve G bits hb rank u w,
      hsolve ((spanning G rank).deleteEdges {s(u, w)}) _
        (withoutBits_spec (spanning G rank) tree (spanningBits_spec solve hsolve G bits hb rank)
          u w) w t]
    exact first_step_iff (spanning G rank) hF huv p hp w
  unfold nextVertex
  rw [if_neg hne]
  change order.find? test = some v
  cases he : order.find? test with
  | none => exact ((List.find?_eq_none.1 he) v (covered v) ((ht v).2 rfl)).elim
  | some w =>
    rw [(ht w).1 (List.find?_some he)]

/-- This trace lists the output tape contents of an iteration. The step function
takes only the current vertex and target. -/
def trace (next : V → V → Option V) (t : V) : Nat → V → List V
  | 0, _ => []
  | k + 1, u =>
    match next u t with
    | none => []
    | some v => v :: trace next t k v

theorem trace_eq_path_tail (order : List V) (covered : ∀ v : V, v ∈ order)
    (solve : Decider V) (hsolve : Correct solve) (G : SimpleGraph V) (bits : AdjBits V)
    (hb : ∀ x y, bits x y = true ↔ G.Adj x y) (rank : Sym2 V → Nat)
    (hF : (spanning G rank).IsAcyclic) {u t : V}
    (p : (spanning G rank).Walk u t) (hp : p.IsPath) (fuel : Nat)
    (enough : p.length ≤ fuel) :
    trace (nextVertex order solve bits rank) t fuel u = p.support.tail := by
  induction p generalizing fuel with
  | nil =>
    cases fuel <;> simp [trace, nextVertex]
  | @cons u v t huv p ih =>
    cases fuel with
    | zero =>
      simp only [Walk.length_cons] at enough
      omega
    | succ k =>
      have hs := nextVertex_of_cons order covered solve hsolve G bits hb rank hF huv p hp
      simp only [Walk.length_cons] at enough
      have ht := ih hp.of_cons k (by omega)
      change (match nextVertex order solve bits rank u t with
        | none => []
        | some w => w :: trace (nextVertex order solve bits rank) t k w) = _
      rw [hs]
      change v :: trace (nextVertex order solve bits rank) t k v = _
      rw [ht]
      rw [Walk.support_cons, List.tail_cons]
      exact Walk.cons_tail_support p

end Oracle


/-- Numeric ranks for unordered edges on a labelled finite graph. -/
def finRank (n : Nat) : Sym2 (Fin n) → Nat :=
  Sym2.lift ⟨fun x y => min x.val y.val + n * max x.val y.val,
    by intro x y; simp only [min_comm, max_comm]⟩

theorem finRank_injective (n : Nat) : Function.Injective (finRank n) := by
  simp only [Function.Injective, Sym2.forall]
  intro a b c d h
  change min a.val b.val + n * max a.val b.val =
    min c.val d.val + n * max c.val d.val at h
  have ha : min a.val b.val < n := lt_of_le_of_lt (min_le_left _ _) a.isLt
  have hc : min c.val d.val < n := lt_of_le_of_lt (min_le_left _ _) c.isLt
  have hn : 0 < n := a.isLt.pos
  have hlo : min a.val b.val = min c.val d.val := by
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]
      using congrArg (fun z => z % n) h
  have hhi : max a.val b.val = max c.val d.val := by
    simpa only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hc, Nat.zero_add]
      using congrArg (fun z => z / n) h
  rcases le_total a.val b.val with hab | hba <;>
    rcases le_total c.val d.val with hcd | hdc
  · simp only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at hlo hhi
    exact Sym2.eq_iff.2 (Or.inl ⟨Fin.ext hlo, Fin.ext hhi⟩)
  · simp only [min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc] at hlo hhi
    exact Sym2.eq_iff.2 (Or.inr ⟨Fin.ext hlo, Fin.ext hhi⟩)
  · simp only [min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd] at hlo hhi
    exact Sym2.eq_iff.2 (Or.inr ⟨Fin.ext hhi, Fin.ext hlo⟩)
  · simp only [min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc] at hlo hhi
    exact Sym2.eq_iff.2 (Or.inl ⟨Fin.ext hhi, Fin.ext hlo⟩)

theorem finRank_lt (n : Nat) (e : Sym2 (Fin n)) : finRank n e < n * n := by
  induction e with
  | h x y =>
    change min x.val y.val + n * max x.val y.val < n * n
    have hmin : min x.val y.val < n := lt_of_le_of_lt (min_le_left _ _) x.isLt
    have hmax : max x.val y.val + 1 ≤ n := max_lt_iff.2 ⟨x.isLt, y.isLt⟩
    calc
      _ < n + n * max x.val y.val := Nat.add_lt_add_right hmin _
      _ = n * (max x.val y.val + 1) := by simp [Nat.mul_succ, Nat.add_comm]
      _ ≤ n * n := Nat.mul_le_mul_left _ hmax

/-- Ranks use two vertex words' worth of bits. -/
theorem finRank_bitBound (n : Nat) (e : Sym2 (Fin n)) :
    finRank n e < 2 ^ (2 * (n.log2 + 1)) := by
  apply lt_trans (finRank_lt n e)
  have hn : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  rw [Nat.two_mul, Nat.pow_add]
  exact lt_of_le_of_lt (Nat.mul_le_mul_right n hn.le)
    (Nat.mul_lt_mul_of_pos_left hn (Nat.pow_pos (by decide : 0 < 2)))

/-- An actual signed generator index. False denotes the generator and true
denotes its inverse. -/
abbrev Letter (m : Nat) := Fin m × Bool

section Cayley

variable {G : Type*} [Group G] [DecidableEq G] {m : Nat}

def letterValue (gen : Fin m → G) (l : Letter m) : G :=
  if l.2 then (gen l.1)⁻¹ else gen l.1

def signedLabel (gen : Fin m → G) (x y : G) : Option (Letter m) :=
  ((List.finRange m).flatMap (fun i => [(i, false), (i, true)])).find?
    (fun l => decide (x * letterValue gen l = y))

theorem signedLabel_sound (gen : Fin m → G) {x y : G} {l : Letter m}
    (h : signedLabel gen x y = some l) : x * letterValue gen l = y := by
  have h' := List.find?_some h
  exact of_decide_eq_true h'

theorem signedLabel_complete (gen : Fin m → G) {x y : G}
    (h : (mulCayley (Set.range gen)).Adj x y) :
    ∃ l, signedLabel gen x y = some l := by
  obtain ⟨z, ⟨i, rfl⟩, hz | hz⟩ := Mathproof.MinimumGeneration.cayley_adj_has_label _ h
  · cases hscan : signedLabel gen x y with
    | none =>
      have hm : (i, false) ∈ (List.finRange m).flatMap (fun i => [(i, false), (i, true)]) :=
        List.mem_flatMap.2 ⟨i, by simp, by simp⟩
      have hn := (List.find?_eq_none.1 hscan) (i, false) hm
      exact (hn (by simpa [letterValue] using hz)).elim
    | some l => exact ⟨l, rfl⟩
  · cases hscan : signedLabel gen x y with
    | none =>
      have hm : (i, true) ∈ (List.finRange m).flatMap (fun i => [(i, false), (i, true)]) :=
        List.mem_flatMap.2 ⟨i, by simp, by simp⟩
      have hn := (List.find?_eq_none.1 hscan) (i, true) hm
      exact (hn (by simpa [letterValue] using hz)).elim
    | some l => exact ⟨l, rfl⟩

def cayleyBits (gen : Fin m → G) : AdjBits G :=
  fun x y => decide (x ≠ y) && (signedLabel gen x y).isSome

theorem cayleyBits_spec (gen : Fin m → G) (x y : G) :
    cayleyBits gen x y = true ↔ (mulCayley (Set.range gen)).Adj x y := by
  constructor
  · intro hh
    simp only [cayleyBits, Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hh.2
    have he := signedLabel_sound gen hl
    rw [mulCayley_adj']
    refine ⟨hh.1, gen l.1, ⟨l.1, rfl⟩, ?_⟩
    cases hsign : l.2
    · exact Or.inl (by simpa [letterValue, hsign] using he)
    · right
      have he' : x * (gen l.1)⁻¹ = y := by simpa [letterValue, hsign] using he
      rw [← he', inv_mul_cancel_right]
  · intro h
    obtain ⟨l, hl⟩ := signedLabel_complete gen h
    simp [cayleyBits, h.ne, hl]

/-- A single streaming step in the Cayley witness word. -/
def nextLetter (order : List G) (solve : Decider G) (rank : Sym2 G → Nat)
    (gen : Fin m → G) (u t : G) : Option (G × Letter m) :=
  (nextVertex order solve (cayleyBits gen) rank u t).bind
    (fun v => (signedLabel gen u v).map (fun a => (v, a)))

def wordTrace (next : G → G → Option (G × Letter m)) (t : G) : Nat → G → List (Letter m)
  | 0, _ => []
  | k + 1, u =>
    match next u t with
    | none => []
    | some (v, l) => l :: wordTrace next t k v

theorem wordTrace_correct (order : List G) (covered : ∀ v : G, v ∈ order)
    (solve : Decider G) (hsolve : Correct solve) (rank : Sym2 G → Nat) (gen : Fin m → G)
    (hF : (spanning (mulCayley (Set.range gen)) rank).IsAcyclic) {u t : G}
    (p : (spanning (mulCayley (Set.range gen)) rank).Walk u t) (hp : p.IsPath)
    (fuel : Nat) (enough : p.length ≤ fuel) :
    let word := wordTrace (nextLetter order solve rank gen) t fuel u
    word.length = p.length ∧ word.foldl (fun x l => x * letterValue gen l) u = t := by
  induction p generalizing fuel with
  | nil =>
    cases fuel <;> simp [wordTrace, nextLetter, nextVertex]
  | @cons u v t huv p ih =>
    cases fuel with
    | zero =>
      simp only [Walk.length_cons] at enough
      omega
    | succ k =>
      obtain ⟨a, ha⟩ := signedLabel_complete gen huv.1
      have hv := nextVertex_of_cons order covered solve hsolve
        (mulCayley (Set.range gen)) (cayleyBits gen) (cayleyBits_spec gen) rank hF huv p hp
      have hs : nextLetter order solve rank gen u t = some (v, a) := by
        simp [nextLetter, hv, ha]
      have hprod := signedLabel_sound gen ha
      simp only [Walk.length_cons] at enough
      have hi := ih hp.of_cons k (by omega)
      dsimp only
      simp only [wordTrace, hs, List.length_cons, List.foldl_cons, Walk.length_cons, hprod]
      exact ⟨congrArg (· + 1) hi.1, hi.2⟩

end Cayley


/-- A streamed word through the Cayley graph, starting at the identity.
The initial decision separates unreachable targets before the scan. -/
def searchWord {n m : Nat} [Group (Fin n)] (solve : Decider (Fin n))
    (gen : Fin m → Fin n) (target : Fin n) : Option (List (Letter m)) :=
  if solve (cayleyBits gen) 1 target then
    some (wordTrace (nextLetter (List.finRange n) solve (finRank n) gen) target n 1)
  else none

theorem searchWord_isSome {n m : Nat} [grp : Group (Fin n)] (solve : Decider (Fin n))
    (hs : Correct solve) (gen : Fin m → Fin n) (target : Fin n) :
    (searchWord solve gen target).isSome = true ↔ target ∈ Subgroup.closure (Set.range gen) := by
  have hd := hs (@mulCayley (Fin n) (Set.range gen) grp.toMul) _ (cayleyBits_spec gen) 1 target
  rw [← Mathproof.MinimumGeneration.cayley_reachable_iff_mem_closure, ← hd]
  simp [searchWord]

/-- The successful search emits fewer than n signed generator indices and
evaluates to the target. The theorem needs only correctness of the Boolean
decision subroutine. -/
theorem searchWord_output {n m : Nat} [grp : Group (Fin n)] (solve : Decider (Fin n))
    (hs : Correct solve) (gen : Fin m → Fin n) (target : Fin n) (word : List (Letter m))
    (h : searchWord solve gen target = some word) :
    word.length < n ∧ word.foldl (fun x l => grp.toMul.mul x (letterValue gen l)) 1 = target := by
  have hmem := (searchWord_isSome solve hs gen target).1 (by simp [h])
  have hr := (Mathproof.MinimumGeneration.cayley_reachable_iff_mem_closure _ _).2 hmem
  have hd := (hs (@mulCayley (Fin n) (Set.range gen) grp.toMul) _ (cayleyBits_spec gen) 1 target).2 hr
  have hword : wordTrace (nextLetter (List.finRange n) solve (finRank n) gen) target n 1 = word := by
    simpa [searchWord, hd] using h
  have hf := spanning_spec (@mulCayley (Fin n) (Set.range gen) grp.toMul) (finRank n) (finRank_injective n)
    (n * n) (fun {x y} _ => finRank_lt n s(x, y))
  obtain ⟨p, hp⟩ := ((hf.2 1 target).2 hr).exists_isPath
  have hlen : p.length < n := by simpa using hp.length_lt
  have ht := wordTrace_correct (List.finRange n) (by simp) solve hs (finRank n) gen
    hf.1 p hp n hlen.le
  rw [← hword]
  exact ⟨ht.1 ▸ hlen, ht.2⟩


/-- Only a vertex label and a remaining step count are retained across
successive calls. The emitted letter is carried separately. -/
structure Cursor (G : Type*) where
  current : G
  fuel : Nat

def cursorStep {G : Type*} {m : Nat} (next : G → G → Option (G × Letter m))
    (target : G) (c : Cursor G) : Option (Cursor G × Letter m) :=
  match c.fuel with
  | 0 => none
  | k + 1 => (next c.current target).map (fun (v, a) => (⟨v, k⟩, a))

def cursorOutput {G : Type*} {m : Nat} (next : G → G → Option (G × Letter m))
    (target : G) : Nat → Cursor G → List (Letter m)
  | 0, _ => []
  | steps + 1, c =>
    match cursorStep next target c with
    | none => []
    | some (c', a) => a :: cursorOutput next target steps c'

theorem cursorOutput_eq_wordTrace {G : Type*} {m : Nat} (next : G → G → Option (G × Letter m))
    (target : G) (steps : Nat) (c : Cursor G) :
    cursorOutput next target steps c = wordTrace next target (min steps c.fuel) c.current := by
  induction steps generalizing c with
  | zero => simp [cursorOutput, wordTrace]
  | succ k ih =>
    obtain ⟨u, j⟩ := c
    cases j with
    | zero => simp [cursorOutput, cursorStep, wordTrace]
    | succ j =>
      cases e : next u target with
      | none => simp [cursorOutput, cursorStep, wordTrace, Nat.succ_min_succ, e]
      | some p =>
        obtain ⟨v, a⟩ := p
        simp [cursorOutput, cursorStep, wordTrace, Nat.succ_min_succ, e, ih]

theorem cursorStep_fuel_lt {G : Type*} {m : Nat} (next : G → G → Option (G × Letter m))
    (target : G) {c c' : Cursor G} {a : Letter m} (h : cursorStep next target c = some (c', a)) :
    c'.fuel < c.fuel := by
  obtain ⟨u, j⟩ := c
  cases j with
  | zero => simp [cursorStep] at h
  | succ j =>
    cases e : next u target with
    | none => simp [cursorStep, e] at h
    | some p =>
      obtain ⟨v, b⟩ := p
      simp only [cursorStep, e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact Nat.lt_succ_self _

/-- Each stored cursor coordinate fits in one vertex-width word. -/
theorem cursor_register_width {n : Nat} (c : Cursor (Fin n)) (hn : c.fuel ≤ n) :
    c.current.val < 2 ^ (n.log2 + 1) ∧ c.fuel < 2 ^ (n.log2 + 1) :=
  ⟨lt_trans c.current.isLt Nat.lt_log2_self, lt_of_le_of_lt hn Nat.lt_log2_self⟩


/-!
The virtual input below uses the layout of
Complexitylib's undirected-connectivity instances at the source boundary.
A matrix bit is recovered by division and remainder, so callers need not
construct an adjacency matrix. This implements the input layout independently
of the Lean version of the physical decision machine.
-/

private def unaryField (k : Nat) : List Bool := List.replicate k true ++ [false]

private def unaryFields : List Nat → List Bool
  | [] => []
  | k :: ks => unaryField k ++ unaryFields ks

private def unaryRead : List Nat → Nat → Bool
  | [], _ => false
  | k :: ks, i =>
    if i < k + 1 then decide (i < k) else unaryRead ks (i - (k + 1))

private theorem unaryField_read (k i : Nat) (h : i < k + 1) :
    ((unaryField k)[i]?).getD false = decide (i < k) := by
  by_cases hlt : i < k
  · unfold unaryField
    rw [List.getElem?_append_left (by simpa using hlt)]
    simp [hlt]
  · have he : i = k := by omega
    subst i
    simp [unaryField]

private theorem unaryRead_spec (fields : List Nat) (i : Nat) :
    unaryRead fields i = ((unaryFields fields)[i]?).getD false := by
  induction fields generalizing i with
  | nil => simp [unaryRead, unaryFields]
  | cons k ks ih =>
    by_cases h : i < k + 1
    · simp only [unaryRead, unaryFields, if_pos h]
      rw [List.getElem?_append_left (by simpa [unaryField] using h)]
      exact (unaryField_read k i h).symm
    · simp only [unaryRead, unaryFields, if_neg h]
      have hle : (unaryField k).length ≤ i := by
        simpa [unaryField] using Nat.le_of_not_gt h
      rw [List.getElem?_append_right hle]
      simpa only [unaryField, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, Nat.zero_add] using ih (i - (k + 1))

/-- Read the rank-indexed part of the USTCON input without allocating
any of its rows. -/
def matrixRead {n : Nat} (bits : AdjBits (Fin n)) (hn : 0 < n) (i : Nat) : Bool :=
  if h : i < n * n then
    bits ⟨i / n, (Nat.div_lt_iff_lt_mul hn).2 h⟩ ⟨i % n, Nat.mod_lt _ hn⟩
  else false

def ustconHeaderLength {n : Nat} (s t : Fin n) : Nat :=
  n + s.val + t.val + 3

def ustconWord {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) : List Bool :=
  unaryFields [n, s.val, t.val] ++ (List.ofFn fun i : Fin (n * n) => matrixRead bits s.isLt.pos i.val)

/-- Bit reader of the virtual graph input. The only graph operation is
the supplied adjacency predicate. -/
def ustconRead {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) (i : Nat) : Bool :=
  if i < ustconHeaderLength s t then unaryRead [n, s.val, t.val] i
  else matrixRead bits s.isLt.pos (i - ustconHeaderLength s t)

private theorem ustconHeader_length {n : Nat} (s t : Fin n) :
    (unaryFields [n, s.val, t.val]).length = ustconHeaderLength s t := by
  simp [unaryFields, unaryField, ustconHeaderLength]
  omega

theorem ustconWord_length {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) :
    (ustconWord bits s t).length = ustconHeaderLength s t + n * n := by
  simp [ustconWord, ustconHeader_length]

/-- The virtual reader returns exactly the bits of the materialized input,
including the blank convention for positions past its end. -/
theorem ustconRead_spec {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) (i : Nat) :
    ustconRead bits s t i = ((ustconWord bits s t)[i]?).getD false := by
  unfold ustconRead ustconWord
  by_cases h : i < ustconHeaderLength s t
  · rw [if_pos h, List.getElem?_append_left (by simpa [ustconHeader_length] using h)]
    exact unaryRead_spec _ _
  · have hle : (unaryFields [n, s.val, t.val]).length ≤ i := by
      simpa [ustconHeader_length] using Nat.le_of_not_gt h
    rw [if_neg h, List.getElem?_append_right hle, ustconHeader_length, List.getElem?_ofFn]
    by_cases hb : i - ustconHeaderLength s t < n * n
    · simp only [dif_pos hb, Option.getD_some]
    · simp [matrixRead, hb]

/-- A matrix address decodes directly to the two labelled endpoints. -/
theorem matrixRead_coordinates {n : Nat} (bits : AdjBits (Fin n)) (hn : 0 < n)
    (a b : Fin n) : matrixRead bits hn (a.val * n + b.val) = bits a b := by
  have h : a.val * n + b.val < n * n := by
    calc
      _ < a.val * n + n := Nat.add_lt_add_left b.isLt _
      _ = (a.val + 1) * n := by rw [Nat.succ_mul]
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
  unfold matrixRead
  rw [dif_pos h]
  congr 1
  · apply Fin.ext
    change (a.val * n + b.val) / n = a.val
    rw [Nat.mul_comm a.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  · apply Fin.ext
    change (a.val * n + b.val) % n = b.val
    rw [Nat.mul_comm a.val n, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt b.isLt]

theorem ustconRead_matrix {n : Nat} (bits : AdjBits (Fin n)) (s t a b : Fin n) :
    ustconRead bits s t (ustconHeaderLength s t + (a.val * n + b.val)) = bits a b := by
  unfold ustconRead
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact matrixRead_coordinates bits s.isLt.pos a b


/-- The same virtual input as a read-only tape in the local transducer model. -/
def ustconCell {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) (i : Int) :
    Mathproof.MinimumGeneration.InputCell :=
  if i < 0 then .leftEnd
  else if i.toNat < ustconHeaderLength s t + n * n then .data (ustconRead bits s t i.toNat)
  else .rightEnd

theorem ustconCell_spec {n : Nat} (bits : AdjBits (Fin n)) (s t : Fin n) (i : Int) :
    ustconCell bits s t i =
      Mathproof.MinimumGeneration.SearchTransducer.readInput (ustconWord bits s t) i := by
  unfold ustconCell Mathproof.MinimumGeneration.SearchTransducer.readInput
  by_cases hi : i < 0
  · simp [hi]
  · rw [if_neg hi, if_neg hi, ← ustconWord_length bits s t]
    by_cases hb : i.toNat < (ustconWord bits s t).length
    · simp [hb, ustconRead_spec, List.getElem?_eq_getElem hb]
    · rw [if_neg hb, List.getElem?_eq_none_iff.2 (Nat.le_of_not_gt hb)]
      rfl

/-- The output semantics of the cursor agrees with the exact successful
finite-group word search. -/
theorem searchWord_eq_cursorOutput {n m : Nat} [Group (Fin n)] (solve : Decider (Fin n))
    (gen : Fin m → Fin n) (target : Fin n) (word : List (Letter m))
    (hw : searchWord solve gen target = some word) :
    cursorOutput (nextLetter (List.finRange n) solve (finRank n) gen) target n ⟨1, n⟩ = word := by
  rw [cursorOutput_eq_wordTrace]
  unfold searchWord at hw
  split at hw
  · simpa using hw
  · contradiction
end Mathproof.MinimumGeneration.Connectivity
