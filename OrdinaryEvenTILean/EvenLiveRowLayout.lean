import EvenCellsPrefix
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Field.Defs

/-! The variable-order prefix construction in the existing three-slot signed
field-unit row format. The auxiliary addresses and row indices are dense. -/
namespace EvenOrdinaryTI.LiveRows
open scoped BigOperators
open EvenOrdinaryTI.CellPrefix

abbrev Aux (t d : Nat) := Fin t × Fin (d + 1)
abbrev Var (s t d : Nat) := Fin s ⊕ Aux t d
abbrev Row (t d : Nat) := Fin t × (Fin d ⊕ Fin 2)

variable {s t d : Nat}

def varIndex : Var s t d ≃ Fin (s + t * (d + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def rowIndex : Row t d ≃ Fin (t * (d + 2)) :=
  (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv).trans finProdFinEquiv

def prefixVar (j : Fin t) (k : Fin (d + 1)) : Var s t d := .inr (j, k)

def pinIndex (p : Fin 2) : Fin (d + 1) := if p.val = 0 then 0 else Fin.last d

def src (orig : Fin t → Fin d → Fin s) (r : Row t d) (e : Fin 3) : Var s t d :=
  match r.2 with
  | .inl i =>
    if e.val = 0 then prefixVar r.1 i.succ
    else if e.val = 1 then prefixVar r.1 i.castSucc
    else .inl (orig r.1 i)
  | .inr p => prefixVar r.1 (pinIndex p)

def varField (X : Fin s → Type) (Y : Fin t → Type) : Var s t d → Type
  | .inl i => X i
  | .inr (j, _) => Y j

variable (X : Fin s → Type) (Y : Fin t → Type) [∀ i, Field (X i)] [∀ j, Field (Y j)]
  (orig : Fin t → Fin d → Fin s) (embed : ∀ j i, X (orig j i) →+* Y j)

instance fieldVar (v : Var s t d) : Field (varField X Y v) := by
  cases v with
  | inl i => exact inferInstanceAs (Field (X i))
  | inr q => exact inferInstanceAs (Field (Y q.1))

def incidence (r : Row t d) (e : Fin 3) : varField X Y (src orig r e) →+* Y r.1 := by
  rcases r with ⟨j, i | p⟩
  · induction e using Fin.cases with
    | zero => exact RingHom.id _
    | succ e =>
      induction e using Fin.cases with
      | zero => exact RingHom.id _
      | succ e => exact embed j i
  · exact RingHom.id _

def pack (x : ∀ i, (X i)ˣ) (y : ∀ j, Fin (d + 1) → (Y j)ˣ) :
    ∀ v : Var s t d, (varField X Y v)ˣ
  | .inl i => x i
  | .inr (j, k) => y j k

def original (a : ∀ v : Var s t d, (varField X Y v)ˣ) : ∀ i, (X i)ˣ :=
  fun i => a (.inl i)

def auxiliary (a : ∀ v : Var s t d, (varField X Y v)ˣ) : ∀ j, Fin (d + 1) → (Y j)ˣ :=
  fun j k => a (prefixVar j k)

def rightSide (c : ∀ j, (Y j)ˣ) (r : Row t d) : (Y r.1)ˣ :=
  match r.2 with
  | .inl _ => 1
  | .inr p => if p.val = 0 then 1 else (c r.1)⁻¹

def signedValue (a : ∀ v : Var s t d, (varField X Y v)ˣ) (r : Row t d) : (Y r.1)ˣ :=
  ternary
    (Units.map (incidence X Y orig embed r 0).toMonoidHom (a (src orig r 0)))
    (Units.map (incidence X Y orig embed r 1).toMonoidHom (a (src orig r 1)))
    (Units.map (incidence X Y orig embed r 2).toMonoidHom (a (src orig r 2)))

def factors (x : ∀ i, (X i)ˣ) (j : Fin t) (i : Nat) : (Y j)ˣ :=
  if h : i < d then
    Units.map (embed j ⟨i,h⟩).toMonoidHom (x (orig j ⟨i,h⟩))
  else 1

@[simp] theorem factors_fin (x : ∀ i, (X i)ˣ) (j : Fin t) (i : Fin d) :
    factors X Y orig embed x j i.val = Units.map (embed j i).toMonoidHom (x (orig j i)) := by
  exact dif_pos i.isLt

theorem signedValue_step (a : ∀ v : Var s t d, (varField X Y v)ˣ)
    (j : Fin t) (i : Fin d) :
    signedValue X Y orig embed a (j, .inl i) =
      ternary (auxiliary X Y a j i.succ) (auxiliary X Y a j i.castSucc)
        (factors X Y orig embed (original X Y a) j i.val) := by
  rw [factors_fin]
  rfl

theorem signedValue_pin (a : ∀ v : Var s t d, (varField X Y v)ˣ)
    (j : Fin t) (p : Fin 2) :
    signedValue X Y orig embed a (j, .inr p) =
      ternary (auxiliary X Y a j (pinIndex p)) (auxiliary X Y a j (pinIndex p))
        (auxiliary X Y a j (pinIndex p)) := rfl

def extend (y : Fin (d + 1) → (Y j)ˣ) (k : Nat) : (Y j)ˣ :=
  if h : k < d + 1 then y ⟨k, h⟩ else 1

theorem signedValue_iff_rows (a : ∀ v : Var s t d, (varField X Y v)ˣ)
    (c : ∀ j, (Y j)ˣ) :
    (∀ r, signedValue X Y orig embed a r = rightSide Y c r) ↔
      ∀ j, Rows (factors X Y orig embed (original X Y a) j) d (c j)
        (extend Y (auxiliary X Y a j)) := by
  constructor
  · intro h j
    constructor
    · simpa [signedValue_pin, pinIndex, rightSide, extend, Nat.zero_lt_succ] using h (j, .inr 0)
    · simpa [signedValue_pin, pinIndex, rightSide, extend, Nat.lt_succ_self, Fin.last] using h (j, .inr 1)
    · intro i hi
      simpa [signedValue_step, rightSide, extend, Nat.lt_succ_of_lt hi, Nat.succ_lt_succ hi]
        using h (j, .inl ⟨i, hi⟩)
  · intro h r
    rcases r with ⟨j, i | p⟩
    · simpa [signedValue_step, rightSide, extend, Nat.lt_succ_of_lt i.isLt,
        Nat.succ_lt_succ i.isLt, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] using (h j).step i i.isLt
    · by_cases hp : p.val = 0
      · simpa [signedValue_pin, pinIndex, extend, rightSide, hp, Nat.zero_lt_succ] using (h j).start
      · simpa [signedValue_pin, pinIndex, extend, rightSide, hp, Nat.lt_succ_self, Fin.last] using (h j).finish

def liftOriginal (x : ∀ i, (X i)ˣ) :
    ∀ v : Var s t d, (varField X Y v)ˣ :=
  pack X Y x (fun j k => prefixProd (factors X Y orig embed x j) k.val)

theorem liftOriginal_solves (x : ∀ i, (X i)ˣ) (c : ∀ j, (Y j)ˣ)
    (h : ∀ j, prefixProd (factors X Y orig embed x j) d = c j) :
    ∀ r, signedValue X Y orig embed (liftOriginal X Y orig embed x) r = rightSide Y c r := by
  intro r
  rcases r with ⟨j, i | p⟩
  · rw [signedValue_step]
    exact (prefix_rows _ d _ (h j)).step i i.isLt
  · rw [signedValue_pin]
    by_cases hp : p.val = 0
    · simpa [pinIndex, rightSide, hp, liftOriginal, auxiliary, prefixVar, pack] using (prefix_rows _ d _ (h j)).start
    · simpa [pinIndex, rightSide, hp, liftOriginal, auxiliary, prefixVar, pack] using
        (prefix_rows _ d _ (h j)).finish

theorem signedValue_solves_iff (c : ∀ j, (Y j)ˣ) :
    (∃ a, ∀ r, signedValue X Y orig embed a r = rightSide Y c r) ↔
      ∃ x, ∀ j, prefixProd (factors X Y orig embed x j) d = c j := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨original X Y a, fun j =>
      (rows_iff_product _ d (c j)).mp ⟨_, (signedValue_iff_rows X Y orig embed a c).mp h j⟩⟩
  · rintro ⟨x, h⟩
    exact ⟨liftOriginal X Y orig embed x, liftOriginal_solves X Y orig embed x c h⟩

theorem liftOriginal_unique (a : ∀ v : Var s t d, (varField X Y v)ˣ)
    (c : ∀ j, (Y j)ˣ) (h : ∀ r, signedValue X Y orig embed a r = rightSide Y c r) :
    liftOriginal X Y orig embed (original X Y a) = a := by
  funext v
  rcases v with i | ⟨j, k⟩
  · rfl
  · have hk := rows_unique_on_prefix _ d (c j)
      ((signedValue_iff_rows X Y orig embed a c).mp h j) k.val (Nat.le_of_lt_succ k.isLt)
    have hkeq : prefixProd (factors X Y orig embed (original X Y a) j) k.val =
        auxiliary X Y a j k := by simpa [extend, k.isLt] using hk.symm
    exact hkeq

#print axioms signedValue_solves_iff
#print axioms liftOriginal_unique

end EvenOrdinaryTI.LiveRows
