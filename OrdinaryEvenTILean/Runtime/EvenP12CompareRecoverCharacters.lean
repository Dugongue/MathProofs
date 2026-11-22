import EvenP12CompareRecoverLinear
import EvenP8ReferencePullback

namespace EvenTI.P12Compare

open scoped BigOperators Matrix
open EvenTI.Part8
open Mathproof.P15NetworkDefs20261007

variable {M m n : ℕ} [NeZero M]

/-- Compute each character row via coordinate fixing against the transposed
system. Its output only depends on Smith's physically stored B and U. -/
def recoverCharacterRows (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ) :
    Option (Matrix (Fin n) (Fin m) (ZMod M)) :=
  sequenceFinOptions (fun i : Fin n =>
    recoverLinear A.transpose (fun j => if i = j then (h : ZMod M) else 0))

theorem recoverCharacterRows_sound (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ)
    {C : Matrix (Fin n) (Fin m) (ZMod M)} (hc : recoverCharacterRows A h = some C) :
    C*A = (h : ZMod M) • (1 : Matrix (Fin n) (Fin n) (ZMod M)) := by
  unfold recoverCharacterRows sequenceFinOptions at hc
  split at hc
  · rename_i hs
    obtain rfl := Option.some.inj hc
    apply (characterRows_mul_iff A h _).mpr
    intro i
    exact recoverLinear_sound A.transpose _ (Option.some_get (hs i)).symm
  · contradiction

theorem recoverCharacterRows_complete (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ)
    {C : Matrix (Fin n) (Fin m) (ZMod M)}
    (hc : C*A = (h : ZMod M) • (1 : Matrix (Fin n) (Fin n) (ZMod M))) :
    (recoverCharacterRows A h).isSome = true := by
  have hs (i : Fin n) :
      (recoverLinear A.transpose (fun j => if i = j then (h : ZMod M) else 0)).isSome = true :=
    recoverLinear_complete A.transpose _ ⟨C i,(characterRows_mul_iff A h C).mp hc i⟩
  unfold recoverCharacterRows sequenceFinOptions
  rw [dif_pos hs]
  rfl

private theorem npowBinRec_eq {G : Type*} [Monoid G] (x : G) (h : ℕ) :
    npowBinRec h x = x^h := by
  induction h with
  | zero => simp [npowBinRec_zero]
  | succ h ih => rw [npowBinRec_succ,ih,pow_succ]

def recoverCharacterValues {G : Type*} [CommGroup G]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ) (y : Fin m → G) :
    Option (Fin n → G) :=
  (recoverCharacterRows A h).map (fun C i => ∏ j, npowBinRec (C i j).val (y j))

/-- Use the exact Part 8 values on any feasible RHS, even when the two
implementations return different character rows. They reject exactly the
same unavailable character systems. -/
theorem recoverCharacterValues_eq {G : Type*} [CommGroup G]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (h : ℕ) (x : Fin n → G)
    (hx : ∀ j, x j ^ M = 1) (y : Fin m → G) (hy : matPowZ A x = y) :
    recoverCharacterValues A h y = smithPowerValues A h y := by
  rw [recoverCharacterValues,smithPowerValues]
  rcases hs : smithPowerRows A h with _ | C
  · have hh : recoverCharacterRows A h = none := by
      cases hr : recoverCharacterRows A h with
      | none => rfl
      | some D =>
        have hz := (smithLeftSolve_isSome_iff A _).mpr
          ⟨D,recoverCharacterRows_sound A h hr⟩
        change (smithPowerRows A h).isSome = true at hz
        simp [hs] at hz
    rw [hh]
  · have hc := smithLeftSolve_sound hs
    obtain ⟨D,hD⟩ := Option.isSome_iff_exists.mp (recoverCharacterRows_complete A h hc)
    rw [hD]
    simp only [Option.map_some,npowBinRec_eq]
    exact congrArg some
      (characterRows_values_eq A D C ((recoverCharacterRows_sound A h hD).trans hc.symm)
        x hx y hy)

#print axioms recoverCharacterRows_sound
#print axioms recoverCharacterRows_complete
#print axioms recoverCharacterValues_eq

end EvenTI.P12Compare
