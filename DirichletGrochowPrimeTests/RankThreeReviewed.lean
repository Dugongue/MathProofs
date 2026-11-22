import Mathlib.Tactic.Ring

namespace JointPrimeRankThree

/-- Coordinates are the multiplicities of the transitive orbits of (F₂)³.
Index 0 is the whole stabilizer. Indices 1 through 7 are planes with the
corresponding binary normal, 8 through 14 are lines with binary vectors
1 through 7, and 15 is the zero stabilizer. -/
def degree (x : Fin 16 → Nat) : Nat :=
  x 0 + 2 * (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7) + 4 * (x 8 + x 9 + x 10 + x 11 + x 12 + x 13 + x 14) + 8 * x 15

def planes (x : Fin 16 → Nat) : List Nat :=
  [x 0 + 2 * x 1,
   x 0 + 2 * x 2,
   x 0 + 2 * x 3,
   x 0 + 2 * x 4,
   x 0 + 2 * x 5,
   x 0 + 2 * x 6,
   x 0 + 2 * x 7]

def lines (x : Fin 16 → Nat) : List Nat :=
  [x 0 + 2 * (x 2 + x 4 + x 6) + 4 * x 8,
   x 0 + 2 * (x 1 + x 4 + x 5) + 4 * x 9,
   x 0 + 2 * (x 3 + x 4 + x 7) + 4 * x 10,
   x 0 + 2 * (x 1 + x 2 + x 3) + 4 * x 11,
   x 0 + 2 * (x 2 + x 5 + x 7) + 4 * x 12,
   x 0 + 2 * (x 1 + x 6 + x 7) + 4 * x 13,
   x 0 + 2 * (x 3 + x 5 + x 6) + 4 * x 14]

private def pTotal (x : Fin 16 → Nat) := x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7
private def lTotal (x : Fin 16 → Nat) := x 8 + x 9 + x 10 + x 11 + x 12 + x 13 + x 14

private theorem sumP (x : Fin 16 → Nat) :
    (planes x).sum = 7 * x 0 + 2 * pTotal x := by
  simp [planes, pTotal]
  <;> ring

private theorem sumL (x : Fin 16 → Nat) :
    (lines x).sum = 7 * x 0 + 6 * pTotal x + 4 * lTotal x := by
  simp [lines, pTotal, lTotal]
  <;> ring

private theorem mass (a b c d e f g h u v : Nat)
    (sd : a + 2*b + 4*c + 8*d = e + 2*f + 4*g + 8*h)
    (sp : 7*a + 2*b = 7*e + 2*f)
    (sl : 7*a + 6*b + 4*c = 7*e + 6*f + 4*g)
    (one : a + 2*u = e + 2*v) (ne : a ≠ e) :
    30 ≤ a + 2*b + 4*c + 8*d := by
  have balance : 14*a + 4*g = 14*e + 4*c := by omega
  have gap : a + 2 ≤ e ∨ e + 2 ≤ a := by omega
  rcases gap with l | r <;> omega

theorem sharpLower (x y : Fin 16 → Nat)
    (hd : degree x = degree y) (hp : planes x = planes y)
    (hl : lines x = lines y) (ht : x 0 ≠ y 0) :
    30 ≤ degree x := by
  have p := congrArg List.sum hp
  have l := congrArg List.sum hl
  rw [sumP, sumP] at p
  rw [sumL, sumL] at l
  have one := congrArg (fun L : List Nat => L.headD 0) hp
  change x 0 + 2 * x 1 = y 0 + 2 * y 1 at one
  exact mass (x 0) (pTotal x) (lTotal x) (x 15)
    (y 0) (pTotal y) (lTotal y) (y 15) (x 1) (y 1) hd p l one ht

/-- A pair attaining the lower bound in the elementary group of rank three. -/
def leftSide (i : Fin 16) : Nat :=
  if i.val = 0 then 2 else if 8 ≤ i.val ∧ i.val ≤ 14 then 1 else 0

def rightSide (i : Fin 16) : Nat :=
  if i.val = 15 then 2 else if 1 ≤ i.val ∧ i.val ≤ 7 then 1 else 0

theorem realized : degree leftSide = 30 ∧ degree rightSide = 30 ∧
    planes leftSide = planes rightSide ∧ lines leftSide = lines rightSide ∧
    leftSide 0 ≠ rightSide 0 := by decide

end JointPrimeRankThree
