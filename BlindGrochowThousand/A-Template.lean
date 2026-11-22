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
