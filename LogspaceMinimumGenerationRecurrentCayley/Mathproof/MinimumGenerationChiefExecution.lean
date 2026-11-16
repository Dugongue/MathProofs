import Mathproof.MinimumGenerationChief
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Mathproof.MinimumGeneration.ChiefExecution

open Subgroup

-- A concrete arithmetic instance on Fin must never replace the input group's operators.
local instance (priority := 2000) groupTableMul {n : Nat} [table : Group (Fin n)] : Mul (Fin n) :=
  table.toMul
local instance (priority := 2000) groupTableInv {n : Nat} [table : Group (Fin n)] : Inv (Fin n) :=
  table.toInv
local instance (priority := 2000) groupTableOne {n : Nat} [table : Group (Fin n)] : One (Fin n) :=
  table.toOne

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- One executable saturation pass over the implicit Cayley graph. -/
def expand (seeds seen : Finset G) : Finset G :=
  Finset.univ.filter fun y => y ∈ seen ∨
    ∃ x ∈ seen, ∃ s ∈ seeds, y = x * s ∨ y = x * s⁻¹

@[simp] theorem mem_expand {seeds seen : Finset G} {y : G} :
    y ∈ expand seeds seen ↔ y ∈ seen ∨
      ∃ x ∈ seen, ∃ s ∈ seeds, y = x * s ∨ y = x * s⁻¹ := by
  simp [expand]

/-- Search up to the given number of edge steps, with a monotone visited set. -/
def reached (seeds : Finset G) : Nat → Finset G
  | 0 => {1}
  | k + 1 => expand seeds (reached seeds k)

theorem reached_subset_succ (seeds : Finset G) (k : Nat) :
    reached seeds k ⊆ reached seeds (k + 1) :=
  fun _ hx => mem_expand.mpr (Or.inl hx)

private theorem card_reached_of_not_stable (seeds : Finset G) (k : Nat)
    (h : reached seeds k ≠ reached seeds (k + 1)) :
    k + 1 ≤ (reached seeds k).card := by
  induction k with
  | zero => simp [reached]
  | succ k ih =>
    have hprev : reached seeds k ≠ reached seeds (k + 1) := by
      intro he
      apply h
      change expand seeds (reached seeds k) = expand seeds (reached seeds (k + 1))
      rw [he]
    have hstrict : reached seeds k ⊂ reached seeds (k + 1) :=
      Finset.ssubset_iff_subset_ne.2 ⟨reached_subset_succ seeds k, hprev⟩
    have hc := Finset.card_lt_card hstrict
    have hck := ih hprev
    omega

theorem reached_stable (seeds : Finset G) :
    expand seeds (reached seeds (Fintype.card G)) = reached seeds (Fintype.card G) := by
  by_contra h
  have hh := card_reached_of_not_stable seeds (Fintype.card G) (Ne.symm h)
  have hbound := Finset.card_le_card
    (Finset.subset_univ (reached seeds (Fintype.card G)))
  rw [Finset.card_univ] at hbound
  omega

/-- Exact executable subgroup query. This saturation implementation stores the
visited set. Its interface can also be realized by a space-bounded edge walker. -/
def subgroupMembers (seeds : Finset G) : Finset G :=
  reached seeds (Fintype.card G)

private theorem reached_mem_closure (seeds : Finset G) (k : Nat) {y : G}
    (hy : y ∈ reached seeds k) : y ∈ closure (↑seeds : Set G) := by
  induction k generalizing y with
  | zero =>
    have h : y = 1 := by simpa [reached] using hy
    subst y
    exact one_mem _
  | succ k ih =>
    change y ∈ expand seeds (reached seeds k) at hy
    rcases mem_expand.mp hy with hx | ⟨x, hx, s, hs, he | he⟩
    · exact ih hx
    · exact he ▸ mul_mem (ih hx) (subset_closure hs)
    · exact he ▸ mul_mem (ih hx) (inv_mem (subset_closure hs))

private theorem one_mem_reached (seeds : Finset G) (k : Nat) : 1 ∈ reached seeds k := by
  induction k with
  | zero => simp [reached]
  | succ k ih => exact reached_subset_succ seeds k ih

@[simp] theorem mem_subgroupMembers (seeds : Finset G) (y : G) :
    y ∈ subgroupMembers seeds ↔ y ∈ closure (↑seeds : Set G) := by
  constructor
  · exact reached_mem_closure seeds _
  · intro hy
    have hfix : expand seeds (subgroupMembers seeds) = subgroupMembers seeds :=
      reached_stable seeds
    refine closure_induction_right (p := fun x _ => x ∈ subgroupMembers seeds)
      (one_mem_reached seeds _) ?_ ?_ hy
    · intro x _ s hs hx
      rw [← hfix]
      exact mem_expand.2 (Or.inr ⟨x, hx, s, hs, Or.inl rfl⟩)
    · intro x _ s hs hx
      rw [← hfix]
      exact mem_expand.2 (Or.inr ⟨x, hx, s, hs, Or.inr rfl⟩)

/-- Finite conjugacy enumeration using only table operations. -/
def conjugateMembers (seeds : Finset G) : Finset G :=
  Finset.univ.filter fun y => ∃ s ∈ seeds, ∃ a : G, a * s * a⁻¹ = y

@[simp] theorem mem_conjugateMembers (seeds : Finset G) (y : G) :
    y ∈ conjugateMembers seeds ↔ y ∈ Group.conjugatesOfSet (↑seeds : Set G) := by
  simp [conjugateMembers, Group.mem_conjugatesOfSet_iff, isConj_iff]

/-- Execute a normal-closure query by generating from the conjugates. -/
def normalMembers (seeds : Finset G) : Finset G :=
  subgroupMembers (conjugateMembers seeds)

@[simp] theorem mem_normalMembers (seeds : Finset G) (y : G) :
    y ∈ normalMembers seeds ↔ y ∈ normalClosure (↑seeds : Set G) := by
  unfold normalMembers normalClosure
  rw [mem_subgroupMembers]
  have h : (↑(conjugateMembers seeds) : Set G) = Group.conjugatesOfSet (↑seeds : Set G) := by
    ext x
    exact mem_conjugateMembers seeds x
  rw [h]


section ChiefScan

variable {n : Nat} [Group (Fin n)]

/-- Sort by principal normal-closure size, using the input label to break ties. -/
def principalKey (x : Fin n) : Nat :=
  (normalMembers ({x} : Finset (Fin n))).card * n + x.val

def prefixSeeds (n : Nat) [Group (Fin n)] (cut : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun x => principalKey x < cut

/-- The actual member set returned by a chief-prefix query. -/
def prefixMembers (n : Nat) [Group (Fin n)] (cut : Nat) : Finset (Fin n) :=
  normalMembers (prefixSeeds n cut)

/-- The subgroup semantics of the executable member set. -/
noncomputable def prefixSubgroup (n : Nat) [Group (Fin n)] (cut : Nat) : Subgroup (Fin n) :=
  normalClosure (↑(prefixSeeds n cut) : Set (Fin n))

instance prefixSubgroup_normal (n : Nat) [Group (Fin n)] (cut : Nat) :
    (prefixSubgroup n cut).Normal :=
  inferInstanceAs (normalClosure (↑(prefixSeeds n cut) : Set (Fin n))).Normal

@[simp] theorem mem_prefixMembers (n : Nat) [Group (Fin n)] (cut : Nat) (x : Fin n) :
    x ∈ prefixMembers n cut ↔ x ∈ prefixSubgroup n cut :=
  mem_normalMembers _ _

@[simp] theorem mem_prefixSeeds (cut : Nat) (x : Fin n) :
    x ∈ prefixSeeds n cut ↔ principalKey x < cut := by
  simp [prefixSeeds]

theorem principalKey_injective : Function.Injective (principalKey : Fin n → Nat) := by
  intro x y h
  have hmod (z : Fin n) : principalKey z % n = z.val := by
    simp [principalKey, Nat.add_mod, Nat.mod_eq_of_lt z.isLt]
  exact Fin.ext ((hmod x).symm.trans ((congrArg (· % n) h).trans (hmod y)))

theorem principalKey_lt_endpoint (x : Fin n) : principalKey x < (n + 1) * n := by
  let c := (normalMembers ({x} : Finset (Fin n))).card
  have hc : c ≤ n := by
    simpa [c] using Finset.card_le_card (Finset.subset_univ (normalMembers ({x} : Finset (Fin n))))
  change c * n + x.val < (n + 1) * n
  calc
    c * n + x.val < c * n + n := Nat.add_lt_add_left x.isLt _
    _ = (c + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (n + 1) * n := Nat.mul_le_mul_right n (Nat.succ_le_succ hc)

theorem principalKey_lt_of_normalClosure_lt (x y : Fin n)
    (h : normalClosure ({x} : Set (Fin n)) < normalClosure ({y} : Set (Fin n))) :
    principalKey x < principalKey y := by
  have hsub : normalMembers ({x} : Finset (Fin n)) ⊆ normalMembers ({y} : Finset (Fin n)) := by
    intro z hz
    apply (mem_normalMembers _ _).2
    have hzx := (mem_normalMembers _ _).1 hz
    simp only [Finset.coe_singleton] at hzx ⊢
    exact h.le hzx
  have hne : normalMembers ({x} : Finset (Fin n)) ≠ normalMembers ({y} : Finset (Fin n)) := by
    intro he
    apply h.ne
    ext z
    have hx := mem_normalMembers ({x} : Finset (Fin n)) z
    have hy := mem_normalMembers ({y} : Finset (Fin n)) z
    simp only [Finset.coe_singleton] at hx hy
    rw [he] at hx
    exact hx.symm.trans hy
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  let c := (normalMembers ({x} : Finset (Fin n))).card
  let d := (normalMembers ({y} : Finset (Fin n))).card
  change c * n + x.val < d * n + y.val
  calc
    c * n + x.val < c * n + n := Nat.add_lt_add_left x.isLt _
    _ = (c + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ d * n := Nat.mul_le_mul_right n hc
    _ ≤ d * n + y.val := Nat.le_add_right _ _

theorem prefixSeeds_succ_at (x : Fin n) :
    prefixSeeds n (principalKey x + 1) = prefixSeeds n (principalKey x) ∪ {x} := by
  ext y
  rw [Finset.mem_union, Finset.mem_singleton, mem_prefixSeeds, mem_prefixSeeds]
  constructor
  · intro h
    rcases (show principalKey y < principalKey x ∨ principalKey y = principalKey x by omega) with hlt | he
    · exact Or.inl hlt
    · exact Or.inr (principalKey_injective he)
  · rintro (h | rfl)
    · omega
    · omega

theorem prefixSubgroup_succ_at (x : Fin n) :
    prefixSubgroup n (principalKey x + 1) =
      prefixSubgroup n (principalKey x) ⊔ normalClosure ({x} : Set (Fin n)) := by
  unfold prefixSubgroup
  rw [prefixSeeds_succ_at, Finset.coe_union, Finset.coe_singleton, normalClosure_union]

theorem prefixSubgroup_mono : Monotone (prefixSubgroup n) := by
  intro a b h
  apply normalClosure_mono
  intro z hz
  exact (mem_prefixSeeds b z).2 (lt_of_lt_of_le ((mem_prefixSeeds a z).1 hz) h)

theorem prefixSubgroup_zero : prefixSubgroup n 0 = ⊥ := by
  have h : prefixSeeds n 0 = ∅ := by ext z; simp
  unfold prefixSubgroup
  rw [h, Finset.coe_empty, normalClosure_empty]

theorem prefixSubgroup_endpoint : prefixSubgroup n ((n + 1) * n) = ⊤ := by
  apply top_unique
  intro z _
  exact subset_normalClosure ((mem_prefixSeeds _ z).2 (principalKey_lt_endpoint z))

/-- The strict subgroup changes, in input scan order. -/
def chiefBoundaries (n : Nat) [Group (Fin n)] : List Nat :=
  (List.range ((n + 1) * n)).filter fun cut => decide (prefixMembers n cut ≠ prefixMembers n (cut + 1))

theorem mem_chiefBoundaries_iff (cut : Nat) :
    cut ∈ chiefBoundaries n ↔ cut < (n + 1) * n ∧
      prefixSubgroup n cut < prefixSubgroup n (cut + 1) := by
  have eq_iff : prefixMembers n cut = prefixMembers n (cut + 1) ↔
      prefixSubgroup n cut = prefixSubgroup n (cut + 1) := by
    constructor
    · intro h
      ext x
      rw [← mem_prefixMembers, h, mem_prefixMembers]
    · intro h
      ext x
      rw [mem_prefixMembers, h, ← mem_prefixMembers]
  simp only [chiefBoundaries, List.mem_filter, List.mem_range, decide_eq_true_eq, ne_eq, eq_iff]
  refine and_congr_right fun _ => ⟨?_, fun h => h.ne⟩
  exact fun h => lt_of_le_of_ne (prefixSubgroup_mono (Nat.le_succ cut)) h

theorem key_of_mem_chiefBoundaries {cut : Nat} (hc : cut ∈ chiefBoundaries n) :
    ∃ x : Fin n, principalKey x = cut := by
  by_contra! h
  have hseeds : prefixSeeds n cut = prefixSeeds n (cut + 1) := by
    ext z
    rw [mem_prefixSeeds, mem_prefixSeeds]
    have hz := h z
    omega
  have hh := (mem_chiefBoundaries_iff cut).1 hc
  have he : prefixSubgroup n cut = prefixSubgroup n (cut + 1) := by
    unfold prefixSubgroup
    rw [hseeds]
  exact hh.2.ne he

/-- Each returned strict prefix change is a chief step. -/
theorem chiefBoundary_no_intermediate {cut : Nat} (hc : cut ∈ chiefBoundaries n)
    (L : Subgroup (Fin n)) [L.Normal]
    (h₁ : prefixSubgroup n cut < L) (h₂ : L < prefixSubgroup n (cut + 1)) : False := by
  obtain ⟨x, rfl⟩ := key_of_mem_chiefBoundaries hc
  rw [prefixSubgroup_succ_at] at h₂
  refine chief_step_of_principalClosure_scan _ _ L ?_ h₁ h₂
  intro z _ hz
  exact subset_normalClosure ((mem_prefixSeeds _ z).2 (principalKey_lt_of_normalClosure_lt z x hz))

end ChiefScan


section Oracle

variable {n : Nat} [Group (Fin n)]

/-- Bool-valued interface for callers that supply their own implementation of
subgroup reachability. -/
def CorrectMembership (query : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ (seed : Fin n → Bool) x,
    query seed x = true ↔ x ∈ closure {s | seed s = true}

/-- Scan finite labels with a Boolean accumulator. -/
def anyLabel {m : Nat} (p : Fin m → Bool) : Bool :=
  Fin.foldl m (fun a x => a || p x) false

theorem anyLabel_eq_true {m : Nat} (p : Fin m → Bool) : anyLabel p = true ↔ ∃ x, p x = true := by
  have aux (m : Nat) (p : Fin m → Bool) (a : Bool) :
      Fin.foldl m (fun b x => b || p x) a = true ↔ a = true ∨ ∃ x, p x = true := by
    induction m generalizing a with
    | zero => simp
    | succ m ih =>
      rw [Fin.foldl_succ, ih, Fin.exists_fin_succ]
      simp [or_assoc]
  simpa [anyLabel] using aux m p false

/-- Scan finite labels with a cardinality counter and no visited set. -/
def countLabel {m : Nat} (p : Fin m → Bool) : Nat :=
  Fin.foldl m (fun a x => a + if p x then 1 else 0) 0

theorem countLabel_eq {m : Nat} (p : Fin m → Bool) :
    countLabel p = (Finset.univ.filter fun x => p x = true).card := by
  classical
  have aux (m : Nat) (p : Fin m → Bool) (a : Nat) :
      Fin.foldl m (fun b x => b + if p x then 1 else 0) a =
        a + ∑ x : Fin m, (if p x then 1 else 0) := by
    induction m generalizing a with
    | zero => simp
    | succ m ih =>
      rw [Fin.foldl_succ, ih, Fin.sum_univ_succ]
      exact Nat.add_assoc _ _ _
  simpa [countLabel, Finset.sum_boole] using aux m p 0

/-- A conjugacy query expressed as bounded scans of source labels. -/
def conjugateBit (seed : Fin n → Bool) (x : Fin n) : Bool :=
  anyLabel fun s => seed s && anyLabel (fun a => decide (a * s * a⁻¹ = x))

def normalBit (query : (Fin n → Bool) → Fin n → Bool) (seed : Fin n → Bool) (x : Fin n) : Bool :=
  query (conjugateBit seed) x

theorem normalBit_spec {query : (Fin n → Bool) → Fin n → Bool} (h : CorrectMembership query)
    (seed : Fin n → Bool) (x : Fin n) :
    normalBit query seed x = true ↔ x ∈ normalClosure {s | seed s = true} := by
  have he : {y | conjugateBit seed y = true} = Group.conjugatesOfSet {s | seed s = true} := by
    ext y
    simp [conjugateBit, anyLabel_eq_true, Group.mem_conjugatesOfSet_iff, isConj_iff]
  rw [normalBit, h, he, normalClosure]

def principalKeyWith (query : (Fin n → Bool) → Fin n → Bool) (x : Fin n) : Nat :=
  (countLabel fun y => normalBit query (fun z => decide (z = x)) y) * n + x.val

theorem principalKeyWith_eq {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (x : Fin n) :
    principalKeyWith query x = principalKey x := by
  have he : (Finset.univ.filter fun y => normalBit query (fun z => decide (z = x)) y = true) =
      normalMembers ({x} : Finset (Fin n)) := by
    ext y
    simp [normalBit_spec h]
  simp only [principalKeyWith, principalKey, countLabel_eq, he]

def prefixBit (query : (Fin n → Bool) → Fin n → Bool) (cut : Nat) (x : Fin n) : Bool :=
  normalBit query (fun s => decide (principalKeyWith query s < cut)) x

theorem prefixBit_spec {query : (Fin n → Bool) → Fin n → Bool} (h : CorrectMembership query)
    (cut : Nat) (x : Fin n) :
    prefixBit query cut x = true ↔ x ∈ prefixSubgroup n cut := by
  rw [prefixBit, normalBit_spec h]
  have he : {s : Fin n | decide (principalKeyWith query s < cut) = true} =
      (↑(prefixSeeds n cut) : Set (Fin n)) := by
    ext y
    simp [principalKeyWith_eq h]
  rw [he]
  rfl

def chiefBit (query : (Fin n → Bool) → Fin n → Bool) (cut : Nat) : Bool :=
  anyLabel fun z => !(prefixBit query cut z) && prefixBit query (cut + 1) z

theorem chiefBit_spec {query : (Fin n → Bool) → Fin n → Bool} (h : CorrectMembership query) (cut : Nat) :
    chiefBit query cut = true ↔ prefixSubgroup n cut < prefixSubgroup n (cut + 1) := by
  simp only [chiefBit, anyLabel_eq_true, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, ← Bool.not_eq_true, prefixBit_spec h]
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    refine lt_of_le_of_ne (prefixSubgroup_mono (Nat.le_succ cut)) ?_
    exact fun he => hx₁ (he.ge hx₂)
  · intro hlt
    by_contra! hc
    exact hlt.not_ge (fun x hx => by by_contra hn; exact hc x hn hx)

/-- A bounded counter-only scan for the first acceptable label. -/
def firstHitFrom {m : Nat} (test : Fin m → Bool) (start : Nat) : Nat → Option (Fin m)
  | 0 => none
  | fuel + 1 =>
    if h : start < m then
      if test ⟨start, h⟩ then some ⟨start, h⟩
      else firstHitFrom test (start + 1) fuel
    else none

theorem firstHitFrom_eq_some_iff {m : Nat} (test : Fin m → Bool) (start fuel : Nat) (x : Fin m) :
    firstHitFrom test start fuel = some x ↔
      start ≤ x.val ∧ x.val < start + fuel ∧ test x = true ∧
        ∀ y : Fin m, start ≤ y.val → y.val < x.val → test y = false := by
  induction fuel generalizing start with
  | zero => simp [firstHitFrom]; omega
  | succ fuel ih =>
    by_cases ht : start < m
    · let z : Fin m := ⟨start, ht⟩
      by_cases hb : test z = true
      · simp only [firstHitFrom, dif_pos ht]
        change (if test z then some z else firstHitFrom test (start + 1) fuel) = some x ↔ _
        rw [if_pos hb]
        constructor
        · intro he
          have e : z = x := Option.some.inj he
          subst x
          exact ⟨le_rfl, by simp [z], hb, fun y hy hy' => by
            change y.val < start at hy'
            omega⟩
        · rintro ⟨hl, _, _, hm⟩
          have hzx : z.val = x.val := by
            by_contra hn
            have hs : z.val < x.val := by change start < x.val; change start ≠ x.val at hn; omega
            simpa [hb] using hm z le_rfl hs
          exact congrArg some (Fin.ext hzx)
      · simp only [firstHitFrom, dif_pos ht]
        change (if test z then some z else firstHitFrom test (start + 1) fuel) = some x ↔ _
        rw [if_neg hb, ih]
        constructor
        · rintro ⟨hl, hr, hx, hm⟩
          refine ⟨by omega, by omega, hx, fun y hy hy' => ?_⟩
          by_cases he : y.val = start
          · have hez : y = z := Fin.ext he
            subst y
            exact Bool.eq_false_of_not_eq_true hb
          · exact hm y (by omega) hy'
        · rintro ⟨hl, hr, hx, hm⟩
          have he : x.val ≠ start := by
            intro he
            have hez : x = z := Fin.ext he
            subst x
            exact hb hx
          exact ⟨by omega, by omega, hx, fun y hy hy' => hm y (by omega) hy'⟩
    · simp only [firstHitFrom, dif_neg ht, reduceCtorEq, false_iff]
      intro h
      have hm := x.isLt
      omega

/-- Search one boundary at a time with a bounded scan and no boundary list. -/
def nextChiefWith (query : (Fin n → Bool) → Fin n → Bool) (start : Nat) :
    Option (Fin ((n + 1) * n)) :=
  firstHitFrom (fun x => chiefBit query x.val) start ((n + 1) * n - start)

theorem nextChiefWith_spec {query : (Fin n → Bool) → Fin n → Bool} (h : CorrectMembership query)
    (start : Nat) (cut : Fin ((n + 1) * n)) :
    nextChiefWith query start = some cut ↔
      start ≤ cut.val ∧ cut.val ∈ chiefBoundaries n ∧
        ∀ b : Nat, start ≤ b → b < cut.val → b ∉ chiefBoundaries n := by
  rw [nextChiefWith, firstHitFrom_eq_some_iff, chiefBit_spec h, mem_chiefBoundaries_iff]
  constructor
  · rintro ⟨hs, _, hc, hm⟩
    refine ⟨hs, ⟨cut.isLt, hc⟩, fun b hb hbc hb' => ?_⟩
    have he := hm ⟨b, lt_trans hbc cut.isLt⟩ hb hbc
    have hh := (chiefBit_spec h b).2 ((mem_chiefBoundaries_iff b).1 hb').2
    simp [hh] at he
  · rintro ⟨hs, ⟨hl, hc⟩, hm⟩
    refine ⟨hs, by omega, hc, fun y hy hy' => ?_⟩
    apply Bool.eq_false_of_not_eq_true
    intro he
    exact hm y.val hy hy' ((mem_chiefBoundaries_iff _).2 ⟨y.isLt, (chiefBit_spec h _).1 he⟩)

end Oracle


section QuotientQueries

variable {n : Nat} [Group (Fin n)]

/-- Two raw labels name the same coset exactly when their difference lies in the prefix. -/
def sameCosetBit (query : (Fin n → Bool) → Fin n → Bool) (cut : Nat) (x y : Fin n) : Bool :=
  prefixBit query cut (x⁻¹ * y)

theorem sameCosetBit_spec {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (cut : Nat) (x y : Fin n) :
    sameCosetBit query cut x y = true ↔
      QuotientGroup.mk' (prefixSubgroup n cut) x = QuotientGroup.mk' (prefixSubgroup n cut) y := by
  rw [sameCosetBit, prefixBit_spec h, QuotientGroup.mk'_eq_mk']
  constructor
  · intro hm
    exact ⟨x⁻¹ * y, hm, by simp⟩
  · rintro ⟨z, hz, he⟩
    simpa [← he] using hz

/-- The least original table label in the coset of a given label. -/
def representativeWith (query : (Fin n → Bool) → Fin n → Bool) (cut : Nat) (x : Fin n) :
    Option (Fin n) :=
  firstHitFrom (sameCosetBit query cut x) 0 n

theorem representativeWith_spec {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (cut : Nat) (x z : Fin n) :
    representativeWith query cut x = some z ↔
      QuotientGroup.mk' (prefixSubgroup n cut) x = QuotientGroup.mk' (prefixSubgroup n cut) z ∧
        ∀ y : Fin n, y.val < z.val →
          QuotientGroup.mk' (prefixSubgroup n cut) x ≠ QuotientGroup.mk' (prefixSubgroup n cut) y := by
  rw [representativeWith, firstHitFrom_eq_some_iff]
  simp only [Nat.zero_add, Nat.zero_le, z.isLt, true_and, true_implies, ← Bool.not_eq_true, sameCosetBit_spec h]

private theorem firstHitFrom_eq_none_iff {m : Nat} (test : Fin m → Bool) (start fuel : Nat) :
    firstHitFrom test start fuel = none ↔
      ∀ x : Fin m, start ≤ x.val → x.val < start + fuel → test x = false := by
  induction fuel generalizing start with
  | zero =>
    simp only [firstHitFrom, Nat.add_zero, true_iff]
    intro x hlo hhi
    omega
  | succ fuel ih =>
    by_cases ht : start < m
    · let z : Fin m := ⟨start, ht⟩
      change (if _ : start < m then if test z then some z else firstHitFrom test (start + 1) fuel
          else none) = none ↔ _
      rw [dif_pos ht]
      by_cases hb : test z = true
      · simp only [if_pos hb, reduceCtorEq, false_iff]
        intro h
        have hf := h z le_rfl (by change start < start + (fuel + 1); omega)
        simp [hb] at hf
      · rw [if_neg hb, ih]
        constructor
        · intro he x hx₁ hx₂
          by_cases hxz : x.val = start
          · have hxx : x = z := Fin.ext hxz
            subst x
            exact Bool.eq_false_of_not_eq_true hb
          · exact he x (by omega) (by omega)
        · intro he x hx₁ hx₂
          exact he x (by omega) (by omega)
    · rw [firstHitFrom, dif_neg ht]
      simp only [true_iff]
      intro x hx₁ _
      have hx := x.isLt
      omega

theorem representativeWith_exists {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (cut : Nat) (x : Fin n) :
    ∃ z : Fin n, representativeWith query cut x = some z := by
  cases he : representativeWith query cut x with
  | some z => exact ⟨z, rfl⟩
  | none =>
    have hf := (firstHitFrom_eq_none_iff (sameCosetBit query cut x) 0 n).1 he x
      (Nat.zero_le _) (by simp)
    have ht := (sameCosetBit_spec h cut x x).2 rfl
    simp [ht] at hf

/-- Multiply quotient labels and return the canonical label for their product. -/
def quotientMulWith (query : (Fin n → Bool) → Fin n → Bool) (cut : Nat) (x y : Fin n) :
    Option (Fin n) :=
  representativeWith query cut (x * y)

theorem quotientMulWith_spec {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (cut : Nat) (x y : Fin n) :
    ∃ z : Fin n, quotientMulWith query cut x y = some z ∧
      QuotientGroup.mk' (prefixSubgroup n cut) z =
        QuotientGroup.mk' (prefixSubgroup n cut) x * QuotientGroup.mk' (prefixSubgroup n cut) y := by
  obtain ⟨z, hz⟩ := representativeWith_exists h cut (x * y)
  have hq := ((representativeWith_spec h cut (x * y) z).1 hz).1
  exact ⟨z, hz, hq.symm.trans (map_mul _ x y)⟩

end QuotientQueries


section FiniteFallback

variable {n : Nat} [Group (Fin n)]

/-- Supply the query interface by finite saturation when no bounded-space
reachability implementation is available. -/
def finiteMemberBit (seed : Fin n → Bool) (x : Fin n) : Bool :=
  decide (x ∈ subgroupMembers (Finset.univ.filter fun y => seed y = true))

theorem finiteMemberBit_correct : CorrectMembership (finiteMemberBit (n := n)) := by
  intro seed x
  simp [finiteMemberBit]

theorem representativeWith_invariant {query : (Fin n → Bool) → Fin n → Bool}
    (h : CorrectMembership query) (cut : Nat) {x y : Fin n}
    (hxy : QuotientGroup.mk' (prefixSubgroup n cut) x = QuotientGroup.mk' (prefixSubgroup n cut) y) :
    representativeWith query cut x = representativeWith query cut y := by
  obtain ⟨a, ha⟩ := representativeWith_exists h cut x
  obtain ⟨b, hb⟩ := representativeWith_exists h cut y
  obtain ⟨hxa, hminA⟩ := (representativeWith_spec h cut x a).1 ha
  obtain ⟨hyb, hminB⟩ := (representativeWith_spec h cut y b).1 hb
  have hab : a = b := Fin.ext (le_antisymm
    (le_of_not_gt fun hgt => hminA b hgt (hxy.trans hyb))
    (le_of_not_gt fun hgt => hminB a hgt (hxy.symm.trans hxa)))
  rw [ha, hb, hab]

end FiniteFallback

end Mathproof.MinimumGeneration.ChiefExecution
