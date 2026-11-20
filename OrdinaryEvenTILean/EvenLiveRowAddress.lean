import EvenLiveRowLayout
import Mathlib.Algebra.BigOperators.Fin
import Init.Data.Vector.OfFn

/-! Reindex the prefix network to the dense `Fin` banks of the existing
three-incidence CRT solver, retaining the same field bases and slot numbers. -/
namespace EvenOrdinaryTI.LiveRows

open scoped BigOperators
open EvenOrdinaryTI.CellPrefix

variable {s t d : Nat}

abbrev VarCount (s t d : Nat) := s + t * (d + 1)
abbrev RowCount (t d : Nat) := t * (d + 2)

def physicalSrc (orig : Fin t → Fin d → Fin s) (r : Fin (RowCount t d)) (e : Fin 3) :
    Fin (VarCount s t d) :=
  varIndex (src orig (rowIndex.symm r) e)

def slotIndex (r : Fin (RowCount t d)) (e : Fin 3) : Fin (RowCount t d * 3) :=
  finProdFinEquiv (r, e)

theorem slotIndex_val (r : Fin (RowCount t d)) (e : Fin 3) :
    (slotIndex r e).val = 3 * r.val + e.val := by
  change e.val + 3 * r.val = _
  exact Nat.add_comm _ _

def sourceWord (orig : Fin t → Fin d → Fin s) (i : Nat) : Nat :=
  if h : i < RowCount t d * 3 then
    let slot : Fin (RowCount t d) × Fin 3 := finProdFinEquiv.symm ⟨i, h⟩
    (physicalSrc orig slot.1 slot.2).val
  else 0

theorem sourceWord_correct (orig : Fin t → Fin d → Fin s)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    sourceWord orig (3 * r.val + e.val) = (physicalSrc orig r e).val := by
  rw [← slotIndex_val r e]
  unfold sourceWord
  rw [dif_pos (slotIndex r e).isLt]
  change (physicalSrc orig (finProdFinEquiv.symm (slotIndex r e)).1
    (finProdFinEquiv.symm (slotIndex r e)).2).val = _
  rw [slotIndex, finProdFinEquiv.symm_apply_apply]

/-- The incidence table has exactly three address words per physical row. -/
def sourceTable (orig : Fin t → Fin d → Fin s) : Vector Nat (RowCount t d * 3) :=
  Vector.ofFn fun i => sourceWord orig i.val

theorem sourceTable_correct (orig : Fin t → Fin d → Fin s)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    (sourceTable orig).get (slotIndex r e) = (physicalSrc orig r e).val := by
  change (Vector.ofFn (fun i : Fin (RowCount t d * 3) => sourceWord orig i.val))[
    (slotIndex r e).val] = _
  rw [Vector.getElem_ofFn, slotIndex_val, sourceWord_correct]

theorem sourceWord_lt (orig : Fin t → Fin d → Fin s)
    (r : Fin (RowCount t d)) (e : Fin 3) :
    sourceWord orig (3 * r.val + e.val) < VarCount s t d := by
  rw [sourceWord_correct]
  exact (physicalSrc orig r e).isLt
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ i, Field (X i)] [∀ j, Field (Y j)]
  (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →+* Y j)

abbrev physicalVarField (v : Fin (VarCount s t d)) : Type :=
  varField X Y (varIndex.symm v)

abbrev physicalRowField (r : Fin (RowCount t d)) : Type :=
  Y (rowIndex.symm r).1

private def fieldMove {A : Type} (F : A → Type) [∀ z, Field (F z)] {u v : A} (h : u = v) :
    F u →+* F v := by
  subst v
  exact RingHom.id _

private theorem fieldMove_eval {A : Type} (F : A → Type) [∀ z, Field (F z)]
    {u v : A} (h : u = v) (a : ∀ z, (F z)ˣ) :
    Units.map (fieldMove F h).toMonoidHom (a u) = a v := by
  subst v
  apply Units.ext
  rfl

def physicalInc (r : Fin (RowCount t d)) (e : Fin 3) :
    physicalVarField X Y (physicalSrc orig r e) →+* physicalRowField Y r :=
  (incidence X Y orig emb (rowIndex.symm r) e).comp
    (fieldMove (varField X Y) (varIndex.symm_apply_apply (src orig (rowIndex.symm r) e)))

def fromPhysical (a : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ)
    (v : Var s t d) : (varField X Y v)ˣ :=
  Units.map (fieldMove (varField X Y) (varIndex.symm_apply_apply v)).toMonoidHom (a (varIndex v))

def toPhysical (a : ∀ v : Var s t d, (varField X Y v)ˣ)
    (v : Fin (VarCount s t d)) : (physicalVarField X Y v)ˣ := a (varIndex.symm v)

@[simp] theorem from_toPhysical (a : ∀ v : Var s t d, (varField X Y v)ˣ) :
    fromPhysical X Y (toPhysical X Y a) = a := by
  funext v
  exact fieldMove_eval (varField X Y) (varIndex.symm_apply_apply v) a

def physicalRHS (c : ∀ j, (Y j)ˣ) (r : Fin (RowCount t d)) : (physicalRowField Y r)ˣ :=
  rightSide Y c (rowIndex.symm r)

def physicalValue (a : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ)
    (r : Fin (RowCount t d)) : (physicalRowField Y r)ˣ :=
  ternary
    (Units.map (physicalInc X Y orig emb r 0).toMonoidHom (a (physicalSrc orig r 0)))
    (Units.map (physicalInc X Y orig emb r 1).toMonoidHom (a (physicalSrc orig r 1)))
    (Units.map (physicalInc X Y orig emb r 2).toMonoidHom (a (physicalSrc orig r 2)))

theorem physicalValue_eq (a : ∀ v : Fin (VarCount s t d), (physicalVarField X Y v)ˣ)
    (r : Fin (RowCount t d)) :
    physicalValue X Y orig emb a r =
      signedValue X Y orig emb (fromPhysical X Y a) (rowIndex.symm r) := by
  have h (e : Fin 3) :
      Units.map (physicalInc X Y orig emb r e).toMonoidHom (a (physicalSrc orig r e)) =
        Units.map (incidence X Y orig emb (rowIndex.symm r) e).toMonoidHom
          (fromPhysical X Y a (src orig (rowIndex.symm r) e)) := by
    apply Units.ext
    rfl
  unfold physicalValue signedValue
  rw [h 0, h 1, h 2]

theorem product_fin (x : ∀ i, (X i)ˣ) (j : Fin t) :
    prefixProd (factors X Y orig emb x j) d =
      ∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i)) := by
  rw [prefixProd, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => factors_fin X Y orig emb x j i

theorem physical_solves_iff (c : ∀ j, (Y j)ˣ) :
    (∃ a, ∀ r, physicalValue X Y orig emb a r = physicalRHS Y c r) ↔
      ∃ x : ∀ i, (X i)ˣ, ∀ j,
        (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j := by
  have hProd : (∃ x : ∀ i, (X i)ˣ, ∀ j, prefixProd (factors X Y orig emb x j) d = c j) ↔
      ∃ x : ∀ i, (X i)ˣ, ∀ j,
        (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j :=
    exists_congr fun x => forall_congr' fun j => by rw [product_fin]
  rw [← hProd]
  rw [← signedValue_solves_iff X Y orig emb c]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fromPhysical X Y a, fun r => ?_⟩
    have hh := ha (rowIndex r)
    rw [physicalValue_eq] at hh
    change signedValue X Y orig emb (fromPhysical X Y a) (rowIndex.symm (rowIndex r)) =
      rightSide Y c (rowIndex.symm (rowIndex r)) at hh
    rw [rowIndex.symm_apply_apply] at hh
    exact hh
  · rintro ⟨a, ha⟩
    refine ⟨toPhysical X Y a, fun r => ?_⟩
    simpa only [physicalValue_eq, physicalRHS, from_toPhysical] using
      ha (rowIndex.symm r)

#print axioms sourceTable_correct
#print axioms sourceWord_lt
#print axioms physical_solves_iff

end EvenOrdinaryTI.LiveRows
