import Mathlib

/-!
# A circular Florentine rectangle with five rows of order 25

We encode a row by the position of each symbol in `ZMod n`. Thus a family
`position` is circular Florentine when every row is a permutation and no ordered
pair of distinct symbols has the same circular displacement in two different rows.
-/

namespace CFR525

/--
A circular Florentine rectangle encoded by symbol-position maps.

Pairwise bijectivity of `x ↦ position i x - position j x` says precisely that
an ordered pair of symbols cannot have the same circular displacement in two rows.
-/
def IsCircularFlorentine {r n : ℕ} [NeZero n]
    (position : Fin r → ZMod n → ZMod n) : Prop :=
  (∀ i, Function.Bijective (position i)) ∧
    ∀ i j, i ≠ j →
      Function.Bijective fun x => position i x - position j x

theorem no_repeated_displacement {r n : ℕ} [NeZero n]
    {position : Fin r → ZMod n → ZMod n}
    (h : IsCircularFlorentine position) {i j : Fin r} (hij : i ≠ j)
    {a b : ZMod n} (hab : a ≠ b) :
    position i b - position i a ≠ position j b - position j a := by
  intro same
  apply hab
  apply (h.2 i j hij).1
  dsimp
  linear_combination -same

abbrev Residue := ZMod 25

private def table (values : Fin 25 → Residue) (x : Residue) : Residue :=
  values ⟨x.val, x.val_lt⟩

def theta₁ : Residue → Residue := table ![
  0, 7, 14, 21, 3, 10, 17, 24, 6, 13, 20, 2, 9, 16, 23, 5, 12, 19, 1, 8, 15,
  22, 4, 11, 18]

def theta₂ : Residue → Residue := table ![
  0, 18, 6, 14, 2, 15, 13, 1, 9, 22, 5, 8, 21, 4, 17, 20, 3, 16, 24, 12, 10,
  23, 11, 19, 7]

def theta₃ : Residue → Residue := table ![
  0, 4, 9, 15, 20, 24, 8, 3, 19, 14, 18, 12, 2, 23, 13, 7, 11, 6, 22, 17, 1,
  5, 10, 16, 21]

def theta₄ : Residue → Residue := table ![
  0, 19, 22, 11, 23, 7, 15, 8, 20, 12, 24, 21, 16, 9, 4, 1, 13, 5, 17, 10, 18,
  2, 14, 3, 6]

/-- The five rows, represented by their symbol-position permutations. -/
def witness : Fin 5 → Residue → Residue := ![id, theta₁, theta₂, theta₃, theta₄]

private theorem bijective_of_injective {f : Residue → Residue}
    (h : Function.Injective f) : Function.Bijective f :=
  Finite.injective_iff_bijective.mp h

theorem witness_isCircularFlorentine : IsCircularFlorentine witness := by
  constructor
  · intro i
    fin_cases i
    · exact Function.bijective_id
    all_goals exact bijective_of_injective (by decide)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact bijective_of_injective (by decide)

/-- A circular Florentine rectangle with five rows of order 25 exists. -/
theorem exists_cfr_5_25 :
    ∃ position : Fin 5 → ZMod 25 → ZMod 25, IsCircularFlorentine position :=
  ⟨witness, witness_isCircularFlorentine⟩

end CFR525
