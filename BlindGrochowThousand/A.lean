import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace A

inductive Probe where
  | fixed (exponent modulus : Nat)
  | nullity (exponent modulus : Nat)
  | power (exponent : Nat)
  | characteristic (modulus : Nat)
  deriving Repr

private def partitionsAux : Nat → Nat → Nat → List (List Nat)
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel + 1, n, limit =>
    if n = 0 then [[]] else
      (List.range (min limit n)).flatMap fun i =>
        let d := i + 1
        (partitionsAux fuel (n - d) d).map (d :: ·)

/-- Enumerate cycle types for the symmetric group of the given degree. -/
def partitions (n : Nat) : List (List Nat) := partitionsAux n n n

def canonical : Nat → List Nat → Prop
  | _, [] => True
  | limit, d :: rest => 0 < d ∧ d ≤ limit ∧ canonical d rest

private theorem canonical_length_le_sum (xs : List Nat) (limit : Nat)
    (h : canonical limit xs) : xs.length ≤ xs.sum := by
  induction xs generalizing limit with
  | nil => simp
  | cons d rest ih =>
    have hi := ih d h.2.2
    have hd := h.1
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem mem_partitionsAux_of_canonical (xs : List Nat) (fuel limit : Nat)
    (h : canonical limit xs) (hFuel : xs.length ≤ fuel) :
    xs ∈ partitionsAux fuel xs.sum limit := by
  induction xs generalizing fuel limit with
  | nil => cases fuel <;> simp [partitionsAux]
  | cons d rest ih =>
    obtain ⟨hd, hLimit, hTail⟩ := h
    cases fuel with
    | zero => simp at hFuel
    | succ fuel =>
      have hFuel' : rest.length ≤ fuel := by simpa using hFuel
      have hmem : d - 1 ∈ List.range (min limit (d + rest.sum)) :=
        List.mem_range.mpr (by omega)
      have hidx : d - 1 + 1 = d := by omega
      have hdif : d + rest.sum - d = rest.sum := by omega
      change d :: rest ∈ partitionsAux (fuel + 1) (d + rest.sum) limit
      simp only [partitionsAux]
      split
      · omega
      · apply List.mem_flatMap.mpr
        refine ⟨d - 1, hmem, ?_⟩
        simp only [hidx, hdif]
        exact List.mem_map.mpr ⟨rest, ih fuel d hTail hFuel', rfl⟩

/-- All nonincreasing positive cycle lists of degree n occur in the enumeration. -/
theorem enumeration_complete (xs : List Nat) (n : Nat) (hc : canonical n xs)
    (hs : xs.sum = n) : xs ∈ partitions n := by
  have h := mem_partitionsAux_of_canonical xs n n hc (hs ▸ canonical_length_le_sum xs n hc)
  simpa [hs, partitions] using h

private def fixedMark (k : Nat) (xs : List Nat) : Nat := (xs.filter (fun d => k % d = 0)).sum

private def nullityMark (k : Nat) (xs : List Nat) : Nat := (xs.map (Nat.gcd k)).sum

private def insertCycle (d : Nat) : List Nat → List Nat
  | [] => [d]
  | e :: rest => if d ≤ e then d :: e :: rest else e :: insertCycle d rest

private def sortCycles : List Nat → List Nat
  | [] => []
  | d :: rest => insertCycle d (sortCycles rest)

private def poweredCycles (k : Nat) (xs : List Nat) : List Nat :=
  sortCycles (xs.flatMap (fun d => List.replicate (d.gcd k) (d / d.gcd k)))

private def cyclicCharacteristic (m : Nat) (xs : List Nat) : List Nat :=
  xs.foldl (fun coeff d =>
    (List.range (coeff.length + d)).map fun i =>
      let c := coeff[i]?.getD 0
      let prev := if d ≤ i then coeff[i - d]?.getD 0 else 0
      (c + m - prev) % m) [1]

def fingerprint (test : List Probe) (xs : List Nat) : List (List Nat) :=
  test.map fun probe =>
    match probe with
    | .fixed k m => [fixedMark k xs % m]
    | .nullity k m => [nullityMark k xs % m]
    | .power k => poweredCycles k xs
    | .characteristic m => cyclicCharacteristic m xs

private def eqSignature (test : List Probe) (x y : List Nat) : Bool :=
  fingerprint test x == fingerprint test y

private def deck (test : List Probe) (n : Nat) : List (List (List Nat)) :=
  (partitions n).map (fingerprint test)

/-- At the proposed cutoff the two explicit witnesses collide. All smaller degrees are
separated. At the requested follow-on degree the panel identifies exactly the given
number of equivalence classes. -/
def firstCollision (test : List Probe) (cutoff : Nat) (left right : List Nat)
    (followOn classes : Nat) : Bool :=
  decide ((partitions cutoff).contains left ∧ (partitions cutoff).contains right ∧
       left ≠ right ∧ eqSignature test left right) &&
  ((List.range cutoff).all fun n => decide (deck test n).Nodup) &&
  ((deck test followOn).eraseDups.length == classes)

theorem verified_panel_recovers_below {test : List Probe} {cutoff : Nat}
    {left right : List Nat} {followOn classes : Nat}
    (h : firstCollision test cutoff left right followOn classes = true)
    {n : Nat} (hn : n < cutoff) {u v : List Nat}
    (hu : canonical n u) (hv : canonical n v) (hsu : u.sum = n) (hsv : v.sum = n)
    (heq : fingerprint test u = fingerprint test v) : u = v := by
  unfold firstCollision at h
  have hall := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have hnd : (deck test n).Nodup :=
    of_decide_eq_true ((List.all_eq_true.mp hall) n (List.mem_range.mpr hn))
  exact List.inj_on_of_nodup_map hnd (enumeration_complete u n hu hsu)
    (enumeration_complete v n hv hsv) heq

theorem verified_panel_has_witness {test : List Probe} {cutoff : Nat}
    {left right : List Nat} {followOn classes : Nat}
    (h : firstCollision test cutoff left right followOn classes = true) :
    (partitions cutoff).contains left ∧ (partitions cutoff).contains right ∧
      left ≠ right ∧ fingerprint test left = fingerprint test right := by
  unfold firstCollision at h
  obtain ⟨hl, hr, hne, heq⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  exact ⟨hl, hr, hne, beq_iff_eq.mp heq⟩

theorem fixed_01 : firstCollision [.fixed 10 6, .fixed 12 9, .fixed 14 5, .fixed 21 7] 10 [5, 5] [10] 11 54 = true := by decide +kernel
theorem fixed_02 : firstCollision [.fixed 2 6, .fixed 9 7, .fixed 10 7, .fixed 12 6] 10 [5, 5] [10] 11 55 = true := by decide +kernel
theorem fixed_03 : firstCollision [.fixed 14 10, .fixed 16 10, .fixed 20 7, .fixed 21 5] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 51 = true := by decide +kernel
theorem fixed_04 : firstCollision [.fixed 10 7, .fixed 12 10, .fixed 18 5, .fixed 21 10] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 52 = true := by decide +kernel
theorem fixed_05 : firstCollision [.fixed 9 10, .fixed 10 5, .fixed 20 0] 9 [3, 3, 3] [9] 10 37 = true := by decide +kernel
theorem fixed_06 : firstCollision [.fixed 6 5, .fixed 9 0, .fixed 14 9, .fixed 20 9] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem fixed_07 : firstCollision [.fixed 10 0, .fixed 21 0] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_08 : firstCollision [.fixed 3 5, .fixed 22 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [5, 3] 9 25 = true := by decide +kernel
theorem fixed_09 : firstCollision [.fixed 2 10, .fixed 15 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem fixed_10 : firstCollision [.fixed 2 9, .fixed 3 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 24 = true := by decide +kernel
theorem fixed_11 : firstCollision [.fixed 2 9, .fixed 3 7] 8 [4, 4] [8] 9 25 = true := by decide +kernel
theorem fixed_12 : firstCollision [.fixed 2 8, .fixed 15 0] 8 [1, 1, 1, 1, 1, 1, 1, 1] [5, 3] 9 27 = true := by decide +kernel
theorem fixed_13 : firstCollision [.fixed 15 10, .fixed 16 4, .fixed 22 6] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_14 : firstCollision [.fixed 15 5, .fixed 18 0, .fixed 22 9] 8 [4, 4] [8] 9 26 = true := by decide +kernel
theorem fixed_15 : firstCollision [.fixed 14 10, .fixed 15 7, .fixed 15 9] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_16 : firstCollision [.fixed 10 0, .fixed 12 8, .fixed 21 5] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_17 : firstCollision [.fixed 9 7, .fixed 19 2, .fixed 22 10] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_18 : firstCollision [.fixed 3 9, .fixed 6 8, .fixed 14 9] 8 [4, 4] [8] 9 26 = true := by decide +kernel
theorem fixed_19 : firstCollision [.fixed 3 8, .fixed 14 10, .fixed 17 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 27 = true := by decide +kernel
theorem fixed_20 : firstCollision [.fixed 3 5, .fixed 10 4, .fixed 22 6] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_21 : firstCollision [.fixed 2 10, .fixed 15 7, .fixed 18 9] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_22 : firstCollision [.fixed 2 9, .fixed 19 9, .fixed 21 0] 8 [4, 4] [8] 9 27 = true := by decide +kernel
theorem fixed_23 : firstCollision [.fixed 2 9, .fixed 10 7, .fixed 21 7] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_24 : firstCollision [.fixed 2 9, .fixed 2 10, .fixed 3 7] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_25 : firstCollision [.fixed 2 5, .fixed 16 2, .fixed 21 0] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_26 : firstCollision [.fixed 2 5, .fixed 4 8, .fixed 9 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem fixed_27 : firstCollision [.fixed 2 0, .fixed 3 5, .fixed 14 3] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_28 : firstCollision [.fixed 9 7, .fixed 10 8, .fixed 17 10, .fixed 22 3] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_29 : firstCollision [.fixed 7 10, .fixed 9 7, .fixed 11 3, .fixed 22 9] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_30 : firstCollision [.fixed 7 5, .fixed 12 4, .fixed 14 5, .fixed 15 9] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_31 : firstCollision [.fixed 6 8, .fixed 9 9, .fixed 12 7, .fixed 20 7] 8 [2, 2, 2, 2] [4, 4] 9 29 = true := by decide +kernel
theorem fixed_32 : firstCollision [.fixed 5 0, .fixed 14 7, .fixed 20 8, .fixed 21 4] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_33 : firstCollision [.fixed 4 7, .fixed 6 0, .fixed 20 8, .fixed 21 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem fixed_34 : firstCollision [.fixed 3 8, .fixed 14 7, .fixed 17 0, .fixed 21 2] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_35 : firstCollision [.fixed 3 6, .fixed 9 5, .fixed 14 0, .fixed 22 4] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_36 : firstCollision [.fixed 2 10, .fixed 3 9, .fixed 17 0, .fixed 17 2] 8 [4, 4] [8] 9 27 = true := by decide +kernel
theorem fixed_37 : firstCollision [.fixed 2 9, .fixed 3 9, .fixed 5 4, .fixed 16 0] 8 [4, 4] [8] 9 28 = true := by decide +kernel
theorem fixed_38 : firstCollision [.fixed 2 3, .fixed 3 5, .fixed 10 8, .fixed 21 5] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_39 : firstCollision [.fixed 2 0, .fixed 3 0, .fixed 3 9, .fixed 8 10] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem fixed_40 : firstCollision [.fixed 2 8, .fixed 3 0] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_41 : firstCollision [.fixed 7 7, .fixed 9 9, .fixed 10 8] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_42 : firstCollision [.fixed 11 7, .fixed 14 2, .fixed 15 9, .fixed 22 8] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_43 : firstCollision [.fixed 10 2, .fixed 10 8, .fixed 14 4, .fixed 15 7] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem fixed_44 : firstCollision [.fixed 9 5, .fixed 9 7, .fixed 13 3, .fixed 22 8] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_45 : firstCollision [.fixed 7 5, .fixed 10 8, .fixed 15 9, .fixed 21 9] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_46 : firstCollision [.fixed 2 8, .fixed 11 9, .fixed 15 5, .fixed 21 3] 8 [2, 2, 2, 2] [4, 4] 9 27 = true := by decide +kernel
theorem fixed_47 : firstCollision [.fixed 1 9, .fixed 9 3, .fixed 10 8, .fixed 21 7] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem fixed_48 : firstCollision [.fixed 9 7, .fixed 10 10] 7 [1, 1, 1, 1, 1, 1, 1] [5, 2] 8 20 = true := by decide +kernel
theorem fixed_49 : firstCollision [.fixed 3 5, .fixed 10 7, .fixed 11 10, .fixed 17 7] 7 [5, 2] [7] 8 20 = true := by decide +kernel
theorem fixed_50 : firstCollision [.fixed 3 4, .fixed 8 3, .fixed 14 7, .fixed 15 5] 7 [2, 2, 1, 1, 1] [4, 3] 8 20 = true := by decide +kernel
theorem nullity_01 : firstCollision [.nullity 6 7, .nullity 9 6, .nullity 10 9, .nullity 20 4] 10 [7, 3] [9, 1] 11 54 = true := by decide +kernel
theorem nullity_02 : firstCollision [.nullity 3 5, .nullity 8 8, .nullity 13 5, .nullity 14 9] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 54 = true := by decide +kernel
theorem nullity_03 : firstCollision [.nullity 3 0, .nullity 8 7, .nullity 18 6, .nullity 22 9] 10 [7, 3] [9, 1] 11 55 = true := by decide +kernel
theorem nullity_04 : firstCollision [.nullity 6 0, .nullity 14 5, .nullity 21 9] 9 [4, 4, 1] [5, 2, 2] 10 40 = true := by decide +kernel
theorem nullity_05 : firstCollision [.nullity 3 9, .nullity 14 7, .nullity 20 5] 9 [4, 4, 1] [5, 2, 2] 10 41 = true := by decide +kernel
theorem nullity_06 : firstCollision [.nullity 3 5, .nullity 17 6, .nullity 18 10] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 37 = true := by decide +kernel
theorem nullity_07 : firstCollision [.nullity 2 5, .nullity 15 9, .nullity 18 9] 9 [7, 2] [8, 1] 10 41 = true := by decide +kernel
theorem nullity_08 : firstCollision [.nullity 1 10, .nullity 3 8, .nullity 18 9] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 38 = true := by decide +kernel
theorem nullity_09 : firstCollision [.nullity 12 8, .nullity 15 10, .nullity 17 6, .nullity 18 8] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem nullity_10 : firstCollision [.nullity 7 4, .nullity 8 4, .nullity 9 7, .nullity 14 8] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [9] 10 38 = true := by decide +kernel
theorem nullity_11 : firstCollision [.nullity 7 3, .nullity 11 3, .nullity 15 10, .nullity 18 0] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem nullity_12 : firstCollision [.nullity 7 2, .nullity 9 5, .nullity 18 3, .nullity 20 8] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [9] 10 40 = true := by decide +kernel
theorem nullity_13 : firstCollision [.nullity 6 10, .nullity 7 6, .nullity 9 9, .nullity 15 2] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 37 = true := by decide +kernel
theorem nullity_14 : firstCollision [.nullity 6 9, .nullity 7 7, .nullity 9 10, .nullity 17 2] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 39 = true := by decide +kernel
theorem nullity_15 : firstCollision [.nullity 6 6, .nullity 14 8, .nullity 18 7, .nullity 21 10] 9 [4, 4, 1] [5, 2, 2] 10 40 = true := by decide +kernel
theorem nullity_16 : firstCollision [.nullity 6 5, .nullity 9 6, .nullity 20 8, .nullity 20 10] 9 [4, 4, 1] [5, 2, 2] 10 40 = true := by decide +kernel
theorem nullity_17 : firstCollision [.nullity 5 3, .nullity 6 5, .nullity 11 5, .nullity 15 9] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 39 = true := by decide +kernel
theorem nullity_18 : firstCollision [.nullity 3 10, .nullity 4 0, .nullity 13 5, .nullity 14 0] 9 [5, 4] [8, 1] 10 41 = true := by decide +kernel
theorem nullity_19 : firstCollision [.nullity 3 7, .nullity 10 4, .nullity 11 8, .nullity 18 5] 9 [4, 4, 1] [5, 2, 2] 10 39 = true := by decide +kernel
theorem nullity_20 : firstCollision [.nullity 3 3, .nullity 6 6, .nullity 11 4, .nullity 22 5] 9 [3, 3, 3] [7, 1, 1] 10 37 = true := by decide +kernel
theorem nullity_21 : firstCollision [.nullity 3 3, .nullity 4 10, .nullity 6 0, .nullity 7 5] 9 [5, 4] [8, 1] 10 41 = true := by decide +kernel
theorem nullity_22 : firstCollision [.nullity 3 0, .nullity 5 8, .nullity 13 3, .nullity 18 8] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 40 = true := by decide +kernel
theorem nullity_23 : firstCollision [.nullity 1 6, .nullity 6 10, .nullity 15 4, .nullity 22 6] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 37 = true := by decide +kernel
theorem nullity_24 : firstCollision [.nullity 11 10, .nullity 18 7, .nullity 20 5] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_25 : firstCollision [.nullity 11 4, .nullity 14 0, .nullity 20 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 27 = true := by decide +kernel
theorem nullity_26 : firstCollision [.nullity 10 8, .nullity 11 6, .nullity 18 0] 8 [3, 3, 2] [6, 1, 1] 9 27 = true := by decide +kernel
theorem nullity_27 : firstCollision [.nullity 8 6, .nullity 10 0, .nullity 17 6] 8 [3, 3, 2] [6, 1, 1] 9 26 = true := by decide +kernel
theorem nullity_28 : firstCollision [.nullity 8 0, .nullity 13 10, .nullity 18 8] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem nullity_29 : firstCollision [.nullity 7 5, .nullity 10 0, .nullity 18 0] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem nullity_30 : firstCollision [.nullity 6 8, .nullity 13 7, .nullity 20 10] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_31 : firstCollision [.nullity 6 7, .nullity 11 10, .nullity 14 7] 8 [3, 3, 2] [6, 1, 1] 9 27 = true := by decide +kernel
theorem nullity_32 : firstCollision [.nullity 6 3, .nullity 13 4, .nullity 16 9] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 25 = true := by decide +kernel
theorem nullity_33 : firstCollision [.nullity 6 3, .nullity 11 7, .nullity 15 3] 8 [4, 4] [5, 3] 9 24 = true := by decide +kernel
theorem nullity_34 : firstCollision [.nullity 5 0, .nullity 18 5, .nullity 22 3] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_35 : firstCollision [.nullity 4 3, .nullity 6 7, .nullity 17 9] 8 [3, 3, 2] [6, 1, 1] 9 27 = true := by decide +kernel
theorem nullity_36 : firstCollision [.nullity 2 8, .nullity 4 4, .nullity 21 9] 8 [5, 1, 1, 1] [6, 2] 9 26 = true := by decide +kernel
theorem nullity_37 : firstCollision [.nullity 1 9, .nullity 16 5, .nullity 18 10] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem nullity_38 : firstCollision [.nullity 14 5, .nullity 18 10, .nullity 19 9, .nullity 22 10] 8 [3, 3, 2] [6, 1, 1] 9 27 = true := by decide +kernel
theorem nullity_39 : firstCollision [.nullity 9 7, .nullity 14 7, .nullity 16 3, .nullity 17 2] 8 [5, 1, 1, 1] [6, 2] 9 29 = true := by decide +kernel
theorem nullity_40 : firstCollision [.nullity 8 5, .nullity 9 8, .nullity 9 9, .nullity 22 6] 8 [5, 1, 1, 1] [6, 2] 9 29 = true := by decide +kernel
theorem nullity_41 : firstCollision [.nullity 7 10, .nullity 14 5, .nullity 14 7, .nullity 20 7] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_42 : firstCollision [.nullity 7 4, .nullity 9 4, .nullity 10 5, .nullity 16 0] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 29 = true := by decide +kernel
theorem nullity_43 : firstCollision [.nullity 6 8, .nullity 16 6, .nullity 19 6, .nullity 22 3] 8 [3, 3, 2] [6, 1, 1] 9 26 = true := by decide +kernel
theorem nullity_44 : firstCollision [.nullity 6 8, .nullity 8 3, .nullity 12 4, .nullity 21 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem nullity_45 : firstCollision [.nullity 6 3, .nullity 13 7, .nullity 17 5, .nullity 22 6] 8 [3, 3, 2] [6, 1, 1] 9 24 = true := by decide +kernel
theorem nullity_46 : firstCollision [.nullity 5 4, .nullity 6 6, .nullity 10 0, .nullity 17 3] 8 [3, 3, 2] [6, 1, 1] 9 26 = true := by decide +kernel
theorem nullity_47 : firstCollision [.nullity 4 8, .nullity 17 8, .nullity 18 8, .nullity 19 5] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_48 : firstCollision [.nullity 4 7, .nullity 6 10, .nullity 11 9, .nullity 16 4] 8 [3, 3, 2] [6, 1, 1] 9 28 = true := by decide +kernel
theorem nullity_49 : firstCollision [.nullity 4 4, .nullity 5 0, .nullity 22 3, .nullity 22 9] 8 [3, 3, 2] [6, 1, 1] 9 26 = true := by decide +kernel
theorem nullity_50 : firstCollision [.nullity 4 0, .nullity 6 8, .nullity 8 7, .nullity 11 6] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem hybrid_01 : firstCollision [.fixed 14 7, .nullity 17 4, .nullity 21 8] 10 [4, 4, 2] [8, 1, 1] 11 52 = true := by decide +kernel
theorem hybrid_02 : firstCollision [.fixed 13 5, .nullity 7 0, .nullity 20 5] 10 [4, 3, 3] [6, 2, 2] 11 54 = true := by decide +kernel
theorem hybrid_03 : firstCollision [.fixed 11 6, .fixed 16 8, .nullity 5 9] 10 [4, 1, 1, 1, 1, 1, 1] [5, 3, 2] 11 54 = true := by decide +kernel
theorem hybrid_04 : firstCollision [.fixed 10 0, .fixed 17 9, .nullity 5 8] 10 [2, 2, 2, 2, 2] [10] 11 53 = true := by decide +kernel
theorem hybrid_05 : firstCollision [.fixed 9 10, .nullity 16 7, .nullity 18 0] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 53 = true := by decide +kernel
theorem hybrid_06 : firstCollision [.fixed 9 9, .nullity 14 5, .nullity 20 7] 10 [5, 5] [10] 11 54 = true := by decide +kernel
theorem hybrid_07 : firstCollision [.fixed 8 5, .fixed 11 6, .nullity 7 10] 10 [2, 2, 1, 1, 1, 1, 1, 1] [7, 3] 11 53 = true := by decide +kernel
theorem hybrid_08 : firstCollision [.fixed 4 10, .fixed 21 5, .nullity 3 4] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [5, 5] 11 51 = true := by decide +kernel
theorem hybrid_09 : firstCollision [.fixed 3 8, .nullity 4 10, .nullity 11 7] 10 [6, 4] [8, 2] 11 54 = true := by decide +kernel
theorem hybrid_10 : firstCollision [.fixed 3 2, .fixed 22 8, .nullity 3 9] 10 [4, 4, 2] [8, 1, 1] 11 54 = true := by decide +kernel
theorem hybrid_11 : firstCollision [.fixed 21 5, .nullity 9 9, .nullity 20 6, .nullity 22 4] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [10] 11 54 = true := by decide +kernel
theorem hybrid_12 : firstCollision [.fixed 19 10, .nullity 3 4, .nullity 3 7, .nullity 10 6] 10 [4, 2, 2, 2] [7, 3] 11 53 = true := by decide +kernel
theorem hybrid_13 : firstCollision [.fixed 15 10, .fixed 18 9, .nullity 4 8, .nullity 8 5] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 51 = true := by decide +kernel
theorem hybrid_14 : firstCollision [.fixed 13 0, .fixed 15 10, .nullity 3 7, .nullity 11 0] 10 [5, 5] [8, 2] 11 55 = true := by decide +kernel
theorem hybrid_15 : firstCollision [.fixed 13 0, .fixed 14 8, .nullity 1 4, .nullity 20 4] 10 [5, 5] [6, 4] 11 54 = true := by decide +kernel
theorem hybrid_16 : firstCollision [.fixed 10 5, .fixed 21 7, .nullity 6 2, .nullity 17 2] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [7, 3] 11 46 = true := by decide +kernel
theorem hybrid_17 : firstCollision [.fixed 9 3, .nullity 3 8, .nullity 11 0, .nullity 16 6] 10 [4, 2, 2, 2] [7, 1, 1, 1] 11 53 = true := by decide +kernel
theorem hybrid_18 : firstCollision [.fixed 5 9, .fixed 16 8, .nullity 4 4, .nullity 11 4] 10 [4, 3, 3] [6, 2, 2] 11 54 = true := by decide +kernel
theorem hybrid_19 : firstCollision [.fixed 5 7, .fixed 16 4, .nullity 4 4, .nullity 7 7] 10 [4, 3, 3] [6, 2, 2] 11 52 = true := by decide +kernel
theorem hybrid_20 : firstCollision [.fixed 5 0, .fixed 17 7, .nullity 13 4, .nullity 18 10] 10 [7, 3] [8, 2] 11 54 = true := by decide +kernel
theorem hybrid_21 : firstCollision [.fixed 5 0, .fixed 11 7, .nullity 13 7, .nullity 15 7] 10 [6, 4] [7, 3] 11 54 = true := by decide +kernel
theorem hybrid_22 : firstCollision [.fixed 4 10, .fixed 18 8, .nullity 3 5, .nullity 18 7] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 53 = true := by decide +kernel
theorem hybrid_23 : firstCollision [.fixed 4 0, .fixed 13 7, .fixed 16 4, .nullity 21 8] 10 [5, 5] [7, 3] 11 54 = true := by decide +kernel
theorem hybrid_24 : firstCollision [.fixed 2 10, .nullity 11 5, .nullity 13 9, .nullity 21 7] 10 [4, 4, 2] [8, 1, 1] 11 54 = true := by decide +kernel
theorem hybrid_25 : firstCollision [.fixed 1 7, .fixed 21 8, .fixed 22 10, .nullity 5 4] 10 [2, 2, 2, 2, 2] [10] 11 54 = true := by decide +kernel
theorem hybrid_26 : firstCollision [.fixed 1 6, .fixed 4 5, .nullity 11 0, .nullity 16 9] 10 [4, 3, 3] [6, 2, 2] 11 54 = true := by decide +kernel
theorem hybrid_27 : firstCollision [.fixed 1 4, .fixed 6 3, .nullity 3 9, .nullity 4 8] 10 [4, 2, 2, 2] [7, 3] 11 55 = true := by decide +kernel
theorem hybrid_28 : firstCollision [.fixed 1 3, .fixed 15 5, .nullity 7 7, .nullity 8 5] 10 [5, 3, 2] [7, 1, 1, 1] 11 54 = true := by decide +kernel
theorem hybrid_29 : firstCollision [.fixed 1 2, .fixed 6 6, .nullity 3 0, .nullity 17 9] 10 [4, 4, 2] [8, 1, 1] 11 55 = true := by decide +kernel
theorem hybrid_30 : firstCollision [.fixed 1 2, .fixed 4 5, .fixed 14 5, .nullity 15 5] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 49 = true := by decide +kernel
theorem hybrid_31 : firstCollision [.fixed 21 7, .nullity 1 9, .nullity 21 8] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 39 = true := by decide +kernel
theorem hybrid_32 : firstCollision [.fixed 19 3, .nullity 10 5, .nullity 15 8] 9 [3, 2, 2, 2] [5, 4] 10 39 = true := by decide +kernel
theorem hybrid_33 : firstCollision [.fixed 19 3, .nullity 8 10, .nullity 13 8] 9 [6, 3] [7, 2] 10 39 = true := by decide +kernel
theorem hybrid_34 : firstCollision [.fixed 17 9, .nullity 11 5, .nullity 20 7] 9 [6, 3] [7, 2] 10 39 = true := by decide +kernel
theorem hybrid_35 : firstCollision [.fixed 17 4, .nullity 5 9, .nullity 9 6] 9 [3, 2, 1, 1, 1, 1] [5, 4] 10 39 = true := by decide +kernel
theorem hybrid_36 : firstCollision [.fixed 9 4, .nullity 13 0, .nullity 21 7] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 40 = true := by decide +kernel
theorem hybrid_37 : firstCollision [.fixed 9 4, .nullity 5 9, .nullity 21 0] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 41 = true := by decide +kernel
theorem hybrid_38 : firstCollision [.fixed 6 9, .fixed 21 9, .nullity 7 3] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 38 = true := by decide +kernel
theorem hybrid_39 : firstCollision [.fixed 2 10, .nullity 11 5, .nullity 15 4] 9 [5, 4] [6, 3] 10 39 = true := by decide +kernel
theorem hybrid_40 : firstCollision [.fixed 2 9, .fixed 9 10, .nullity 10 6] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 36 = true := by decide +kernel
theorem hybrid_41 : firstCollision [.fixed 2 7, .fixed 20 5, .nullity 15 6] 9 [3, 3, 3] [9] 10 39 = true := by decide +kernel
theorem hybrid_42 : firstCollision [.fixed 2 0, .fixed 3 9, .nullity 9 3] 9 [3, 3, 3] [9] 10 40 = true := by decide +kernel
theorem hybrid_43 : firstCollision [.fixed 18 3, .fixed 20 10, .nullity 19 3, .nullity 21 5] 9 [4, 4, 1] [5, 2, 2] 10 39 = true := by decide +kernel
theorem hybrid_44 : firstCollision [.fixed 10 9, .fixed 13 6, .fixed 20 4, .nullity 9 10] 9 [3, 3, 3] [9] 10 40 = true := by decide +kernel
theorem hybrid_45 : firstCollision [.fixed 9 10, .nullity 3 4, .nullity 4 3, .nullity 19 2] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 38 = true := by decide +kernel
theorem hybrid_46 : firstCollision [.fixed 9 7, .nullity 19 8, .nullity 20 2, .nullity 20 8] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [9] 10 38 = true := by decide +kernel
theorem hybrid_47 : firstCollision [.fixed 9 6, .nullity 1 5, .nullity 9 8, .nullity 18 5] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 40 = true := by decide +kernel
theorem hybrid_48 : firstCollision [.fixed 9 6, .fixed 12 0, .fixed 18 10, .nullity 11 6] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 40 = true := by decide +kernel
theorem hybrid_49 : firstCollision [.fixed 9 4, .fixed 18 9, .nullity 4 6, .nullity 15 0] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 40 = true := by decide +kernel
theorem hybrid_50 : firstCollision [.fixed 7 6, .nullity 5 3, .nullity 6 9, .nullity 19 2] 9 [7, 2] [8, 1] 10 40 = true := by decide +kernel
theorem extension_01 : firstCollision [.nullity 9 8, .power 5] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [5, 5] 11 55 = true := by decide +kernel
theorem extension_02 : firstCollision [.fixed 15 5, .power 22] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 52 = true := by decide +kernel
theorem extension_03 : firstCollision [.fixed 11 2, .power 5] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [5, 5] 11 54 = true := by decide +kernel
theorem extension_04 : firstCollision [.fixed 3 9, .power 22] 10 [5, 5] [10] 11 54 = true := by decide +kernel
theorem extension_05 : firstCollision [.fixed 2 10, .power 21] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [7, 3] 11 55 = true := by decide +kernel
theorem extension_06 : firstCollision [.fixed 1 3, .power 5] 10 [2, 2, 2, 2, 2] [10] 11 55 = true := by decide +kernel
theorem extension_07 : firstCollision [.nullity 14 3, .nullity 21 8, .power 16] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [8, 2] 11 55 = true := by decide +kernel
theorem extension_08 : firstCollision [.nullity 3 5, .nullity 6 8, .power 8] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 54 = true := by decide +kernel
theorem extension_09 : firstCollision [.fixed 21 5, .nullity 7 5, .power 26] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 55 = true := by decide +kernel
theorem extension_10 : firstCollision [.fixed 15 10, .nullity 21 7, .power 28] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [4, 4, 2] 11 55 = true := by decide +kernel
theorem extension_11 : firstCollision [.fixed 13 4, .nullity 9 9, .power 28] 10 [4, 3, 3] [6, 1, 1, 1, 1] 11 55 = true := by decide +kernel
theorem extension_12 : firstCollision [.fixed 11 4, .nullity 7 3, .power 2] 10 [3, 3, 1, 1, 1, 1] [6, 2, 2] 11 55 = true := by decide +kernel
theorem extension_13 : firstCollision [.fixed 11 4, .nullity 5 7, .power 20] 10 [2, 2, 2, 2, 2] [10] 11 53 = true := by decide +kernel
theorem extension_14 : firstCollision [.fixed 11 4, .nullity 5 3, .power 10] 10 [2, 2, 2, 1, 1, 1, 1] [5, 5] 11 53 = true := by decide +kernel
theorem extension_15 : firstCollision [.fixed 9 6, .nullity 13 2, .power 10] 10 [2, 2, 1, 1, 1, 1, 1, 1] [5, 5] 11 54 = true := by decide +kernel
theorem extension_16 : firstCollision [.fixed 2 10, .nullity 21 8, .power 12] 10 [2, 2, 2, 1, 1, 1, 1] [4, 3, 3] 11 55 = true := by decide +kernel
theorem extension_17 : firstCollision [.fixed 2 7, .nullity 10 2, .power 15] 10 [3, 1, 1, 1, 1, 1, 1, 1] [5, 5] 11 55 = true := by decide +kernel
theorem extension_18 : firstCollision [.fixed 1 6, .nullity 19 7, .power 4] 10 [4, 3, 3] [6, 2, 2] 11 55 = true := by decide +kernel
theorem extension_19 : firstCollision [.fixed 9 3, .nullity 15 5, .power 10] 10 [2, 2, 2, 2, 2] [5, 5] 11 54 = true := by decide +kernel
theorem extension_20 : firstCollision [.fixed 3 10, .fixed 19 10, .power 10] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2] 11 53 = true := by decide +kernel
theorem extension_21 : firstCollision [.nullity 22 8, .power 21] 9 [3, 3, 3] [7, 1, 1] 10 40 = true := by decide +kernel
theorem extension_22 : firstCollision [.nullity 17 3, .power 9] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem extension_23 : firstCollision [.nullity 16 8, .power 27] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [9] 10 41 = true := by decide +kernel
theorem extension_24 : firstCollision [.nullity 11 8, .power 9] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [9] 10 40 = true := by decide +kernel
theorem extension_25 : firstCollision [.nullity 1 10, .power 3] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 41 = true := by decide +kernel
theorem extension_26 : firstCollision [.nullity 1 8, .power 21] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 39 = true := by decide +kernel
theorem extension_27 : firstCollision [.fixed 8 7, .power 27] 9 [3, 3, 3] [9] 10 41 = true := by decide +kernel
theorem extension_28 : firstCollision [.nullity 20 3, .nullity 22 9, .power 21] 9 [3, 3, 3] [7, 1, 1] 10 41 = true := by decide +kernel
theorem extension_29 : firstCollision [.nullity 11 5, .nullity 19 7, .power 21] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 40 = true := by decide +kernel
theorem extension_30 : firstCollision [.nullity 9 2, .nullity 14 6, .power 27] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem extension_31 : firstCollision [.nullity 7 5, .nullity 15 7, .power 18] 9 [3, 2, 2, 2] [6, 1, 1, 1] 10 41 = true := by decide +kernel
theorem extension_32 : firstCollision [.fixed 13 9, .nullity 19 6, .power 18] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 41 = true := by decide +kernel
theorem extension_33 : firstCollision [.fixed 13 5, .nullity 7 5, .power 6] 9 [2, 2, 1, 1, 1, 1, 1] [6, 3] 10 40 = true := by decide +kernel
theorem extension_34 : firstCollision [.fixed 2 9, .fixed 9 10, .power 6] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 37 = true := by decide +kernel
theorem extension_35 : firstCollision [.fixed 16 9, .power 27] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 39 = true := by decide +kernel
theorem extension_36 : firstCollision [.nullity 21 0, .power 10] 8 [2, 2, 2, 2] [5, 1, 1, 1] 9 29 = true := by decide +kernel
theorem extension_37 : firstCollision [.nullity 19 9, .power 10] 8 [2, 2, 2, 2] [5, 1, 1, 1] 9 28 = true := by decide +kernel
theorem extension_38 : firstCollision [.nullity 17 7, .power 22] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_39 : firstCollision [.nullity 13 7, .power 10] 8 [2, 2, 2, 2] [5, 1, 1, 1] 9 28 = true := by decide +kernel
theorem extension_40 : firstCollision [.nullity 13 6, .power 22] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_41 : firstCollision [.nullity 11 10, .power 2] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_42 : firstCollision [.nullity 11 4, .power 22] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem extension_43 : firstCollision [.nullity 11 0, .power 22] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_44 : firstCollision [.nullity 9 6, .power 10] 8 [2, 2, 2, 2] [5, 1, 1, 1] 9 28 = true := by decide +kernel
theorem extension_45 : firstCollision [.nullity 9 4, .power 22] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem extension_46 : firstCollision [.nullity 9 4, .power 2] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem extension_47 : firstCollision [.nullity 7 5, .power 22] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_48 : firstCollision [.nullity 7 5, .power 2] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem extension_49 : firstCollision [.nullity 5 4, .power 22] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem extension_50 : firstCollision [.nullity 1 8, .power 22] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem characteristic_01 : firstCollision [.characteristic 2, .fixed 11 10, .nullity 13 7] 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [4, 4, 2] 11 54 = true := by decide +kernel
theorem characteristic_02 : firstCollision [.characteristic 3, .nullity 1 4, .nullity 10 3] 9 [2, 2, 2, 1, 1, 1] [6, 3] 10 41 = true := by decide +kernel
theorem characteristic_03 : firstCollision [.characteristic 3, .fixed 11 6, .nullity 19 3] 9 [3, 1, 1, 1, 1, 1, 1] [9] 10 41 = true := by decide +kernel
theorem characteristic_04 : firstCollision [.characteristic 3, .fixed 2 9, .fixed 7 9] 9 [1, 1, 1, 1, 1, 1, 1, 1, 1] [3, 3, 3] 10 40 = true := by decide +kernel
theorem characteristic_05 : firstCollision [.characteristic 8, .fixed 14 10] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 29 = true := by decide +kernel
theorem characteristic_06 : firstCollision [.characteristic 4, .nullity 11 6] 8 [1, 1, 1, 1, 1, 1, 1, 1] [4, 4] 9 29 = true := by decide +kernel
theorem characteristic_07 : firstCollision [.characteristic 4, .nullity 5 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem characteristic_08 : firstCollision [.characteristic 4, .fixed 3 3] 8 [2, 2, 2, 2] [4, 4] 9 29 = true := by decide +kernel
theorem characteristic_09 : firstCollision [.characteristic 2, .nullity 14 7, .nullity 19 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem characteristic_10 : firstCollision [.characteristic 2, .nullity 14 4, .nullity 19 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem characteristic_11 : firstCollision [.characteristic 2, .nullity 11 5, .nullity 14 6] 8 [2, 2, 1, 1, 1, 1] [8] 9 28 = true := by decide +kernel
theorem characteristic_12 : firstCollision [.characteristic 2, .nullity 7 7, .nullity 14 6] 8 [1, 1, 1, 1, 1, 1, 1, 1] [8] 9 28 = true := by decide +kernel
theorem characteristic_13 : firstCollision [.characteristic 2, .nullity 6 3, .nullity 13 8] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem characteristic_14 : firstCollision [.characteristic 2, .nullity 2 4, .nullity 19 7] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem characteristic_15 : firstCollision [.characteristic 2, .fixed 22 8, .nullity 5 7] 8 [1, 1, 1, 1, 1, 1, 1, 1] [8] 9 28 = true := by decide +kernel
theorem characteristic_16 : firstCollision [.characteristic 2, .fixed 21 6, .nullity 3 5] 8 [2, 1, 1, 1, 1, 1, 1] [4, 4] 9 29 = true := by decide +kernel
theorem characteristic_17 : firstCollision [.characteristic 2, .fixed 19 6, .nullity 19 5] 8 [2, 1, 1, 1, 1, 1, 1] [4, 4] 9 29 = true := by decide +kernel
theorem characteristic_18 : firstCollision [.characteristic 2, .fixed 19 4, .nullity 15 6] 8 [1, 1, 1, 1, 1, 1, 1, 1] [4, 4] 9 29 = true := by decide +kernel
theorem characteristic_19 : firstCollision [.characteristic 2, .fixed 18 8, .nullity 3 5] 8 [2, 1, 1, 1, 1, 1, 1] [4, 4] 9 28 = true := by decide +kernel
theorem characteristic_20 : firstCollision [.characteristic 2, .fixed 17 10, .nullity 19 2] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem characteristic_21 : firstCollision [.characteristic 2, .fixed 15 4, .nullity 13 5] 8 [1, 1, 1, 1, 1, 1, 1, 1] [4, 2, 2] 9 27 = true := by decide +kernel
theorem characteristic_22 : firstCollision [.characteristic 2, .fixed 15 4, .nullity 9 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem characteristic_23 : firstCollision [.characteristic 2, .fixed 14 9, .nullity 5 5] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem characteristic_24 : firstCollision [.characteristic 2, .fixed 14 8, .nullity 5 6] 8 [1, 1, 1, 1, 1, 1, 1, 1] [4, 4] 9 27 = true := by decide +kernel
theorem characteristic_25 : firstCollision [.characteristic 2, .fixed 14 7, .fixed 21 7] 8 [4, 4] [8] 9 29 = true := by decide +kernel
theorem characteristic_26 : firstCollision [.characteristic 2, .fixed 9 7, .nullity 7 2] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem characteristic_27 : firstCollision [.characteristic 2, .fixed 9 0, .nullity 15 3] 8 [2, 2, 2, 2] [8] 9 29 = true := by decide +kernel
theorem characteristic_28 : firstCollision [.characteristic 2, .fixed 6 8, .nullity 11 4] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem characteristic_29 : firstCollision [.characteristic 2, .fixed 6 5, .nullity 7 0] 8 [3, 3, 2] [6, 1, 1] 9 29 = true := by decide +kernel
theorem characteristic_30 : firstCollision [.characteristic 2, .fixed 5 7, .nullity 19 3] 8 [2, 2, 2, 2] [8] 9 29 = true := by decide +kernel
theorem characteristic_31 : firstCollision [.characteristic 2, .fixed 5 0, .nullity 7 2] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem characteristic_32 : firstCollision [.characteristic 2, .fixed 3 8, .nullity 3 5] 8 [1, 1, 1, 1, 1, 1, 1, 1] [4, 2, 2] 9 29 = true := by decide +kernel
theorem characteristic_33 : firstCollision [.characteristic 2, .fixed 3 5, .nullity 9 3] 8 [2, 2, 2, 2] [8] 9 29 = true := by decide +kernel
theorem characteristic_34 : firstCollision [.characteristic 2, .fixed 3 0, .nullity 2 6] 8 [2, 2, 2, 2] [8] 9 29 = true := by decide +kernel
theorem characteristic_35 : firstCollision [.characteristic 4, .fixed 17 4, .fixed 21 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 28 = true := by decide +kernel
theorem characteristic_36 : firstCollision [.characteristic 2, .fixed 17 8, .nullity 5 2] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 27 = true := by decide +kernel
theorem characteristic_37 : firstCollision [.characteristic 2, .fixed 15 8, .nullity 15 2] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem characteristic_38 : firstCollision [.characteristic 2, .fixed 9 9, .fixed 22 8] 8 [2, 2, 2, 2] [4, 4] 9 28 = true := by decide +kernel
theorem characteristic_39 : firstCollision [.characteristic 2, .fixed 6 8, .fixed 9 8] 8 [1, 1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2] 9 26 = true := by decide +kernel
theorem characteristic_40 : firstCollision [.characteristic 7, .fixed 21 9, .nullity 21 6] 7 [1, 1, 1, 1, 1, 1, 1] [7] 8 21 = true := by decide +kernel
theorem characteristic_41 : firstCollision [.characteristic 3, .nullity 2 4] 6 [1, 1, 1, 1, 1, 1] [3, 3] 8 18 = true := by decide +kernel
theorem characteristic_42 : firstCollision [.characteristic 3, .fixed 16 2] 6 [1, 1, 1, 1, 1, 1] [3, 3] 8 18 = true := by decide +kernel
theorem characteristic_43 : firstCollision [.characteristic 2, .nullity 21 8] 6 [2, 2, 2] [4, 1, 1] 8 20 = true := by decide +kernel
theorem characteristic_44 : firstCollision [.characteristic 2, .nullity 21 6] 6 [2, 2, 2] [4, 1, 1] 8 18 = true := by decide +kernel
theorem characteristic_45 : firstCollision [.characteristic 2, .nullity 17 4] 6 [1, 1, 1, 1, 1, 1] [4, 2] 8 15 = true := by decide +kernel
theorem characteristic_46 : firstCollision [.characteristic 2, .nullity 15 5] 6 [2, 2, 2] [4, 1, 1] 8 17 = true := by decide +kernel
theorem characteristic_47 : firstCollision [.characteristic 2, .nullity 11 7] 6 [2, 2, 2] [4, 1, 1] 8 18 = true := by decide +kernel
theorem characteristic_48 : firstCollision [.characteristic 2, .nullity 9 7] 6 [2, 2, 2] [4, 1, 1] 8 19 = true := by decide +kernel
theorem characteristic_49 : firstCollision [.characteristic 2, .nullity 9 4] 6 [1, 1, 1, 1, 1, 1] [4, 2] 8 15 = true := by decide +kernel
theorem characteristic_50 : firstCollision [.characteristic 2, .nullity 5 10] 6 [2, 2, 2] [4, 1, 1] 8 19 = true := by decide +kernel

end A
