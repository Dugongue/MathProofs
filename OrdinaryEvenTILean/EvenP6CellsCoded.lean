import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.Fintype.Pi

/-! Executable coefficient arithmetic for a represented commutative
algebra. The model supplies proofs of the laws, while all operations
read the given tables. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

structure WordTable (K ι : Type) where
  one : ι → K
  multiply : (ι → K) → (ι → K) → (ι → K)

namespace WordTable

variable {K ι : Type} [Field K]

class Laws (T : WordTable K ι) : Prop where
  assoc : ∀ a b c, T.multiply (T.multiply a b) c = T.multiply a (T.multiply b c)
  comm : ∀ a b, T.multiply a b = T.multiply b a
  one_mul : ∀ a, T.multiply T.one a = a
  zero_mul : ∀ a, T.multiply 0 a = 0
  add_mul : ∀ a b c, T.multiply (a+b) c = T.multiply a c + T.multiply b c
  smul_mul : ∀ (r : K) a b, T.multiply (r • a) b = r • T.multiply a b

theorem laws_of_model (T : WordTable K ι)
    {A : Type} [CommRing A] [Algebra K A] (D : (ι → K) ≃ₗ[K] A)
    (hOne : D T.one = 1) (hMul : ∀ a b, D (T.multiply a b) = D a * D b) :
    Laws T := by
  constructor
  · intro a b c
    apply D.injective
    simp only [hMul, mul_assoc]
  · intro a b
    apply D.injective
    simp only [hMul, mul_comm]
  · intro a
    apply D.injective
    simp only [hMul, hOne, one_mul]
  · intro a
    apply D.injective
    simp only [hMul, map_zero, zero_mul]
  · intro a b c
    apply D.injective
    simp only [hMul, map_add, add_mul]
  · intro r a b
    apply D.injective
    simp only [hMul, map_smul, smul_mul_assoc]

end WordTable

/-- A value stored in the same indexed scalar array used by its table. -/
structure TableWord {K ι : Type} (T : WordTable K ι) where
  val : ι → K

namespace TableWord

variable {K ι : Type} [Field K] (T : WordTable K ι)

def wordEquiv : TableWord T ≃ (ι → K) where
  toFun := TableWord.val
  invFun := TableWord.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

instance [Fintype ι] [DecidableEq K] : DecidableEq (TableWord T) :=
  fun a b => decidable_of_iff (a.val = b.val)
    ⟨fun e => (wordEquiv T).injective e, congrArg TableWord.val⟩

instance : AddCommGroup (TableWord T) := (wordEquiv T).addCommGroup

instance : SMul K (TableWord T) := ⟨fun a x => ⟨a • x.val⟩⟩

instance [h : WordTable.Laws T] : CommRing (TableWord T) where
  __ := (wordEquiv T).addCommGroup
  one := ⟨T.one⟩
  mul a b := ⟨T.multiply a.val b.val⟩
  mul_assoc a b c := congrArg TableWord.mk (h.assoc a.val b.val c.val)
  mul_comm a b := congrArg TableWord.mk (h.comm a.val b.val)
  one_mul a := (wordEquiv T).injective (h.one_mul a.val)
  mul_one a := (wordEquiv T).injective ((h.comm a.val T.one).trans (h.one_mul a.val))
  zero_mul a := (wordEquiv T).injective (h.zero_mul a.val)
  mul_zero a := (wordEquiv T).injective ((h.comm a.val 0).trans (h.zero_mul a.val))
  left_distrib a b c := (wordEquiv T).injective (by
    change T.multiply a.val (b.val + c.val) = T.multiply a.val b.val + T.multiply a.val c.val
    rw [h.comm a.val _, h.add_mul, h.comm b.val a.val, h.comm c.val a.val])
  right_distrib a b c := (wordEquiv T).injective (h.add_mul a.val b.val c.val)

@[simp] theorem val_mul [WordTable.Laws T] (a b : TableWord T) :
    (a * b).val = T.multiply a.val b.val := rfl

@[simp] theorem val_one [WordTable.Laws T] : (1 : TableWord T).val = T.one := rfl

instance [h : WordTable.Laws T] : Algebra K (TableWord T) where
  algebraMap :=
    { toFun := fun r => ⟨r • T.one⟩
      map_one' := congrArg TableWord.mk (one_smul K T.one)
      map_zero' := congrArg TableWord.mk (zero_smul K T.one)
      map_add' := fun r s => congrArg TableWord.mk (add_smul r s T.one)
      map_mul' := fun r s => (wordEquiv T).injective (by
        change (r * s) • T.one = T.multiply (r • T.one) (s • T.one)
        rw [h.smul_mul, h.one_mul, mul_smul]) }
  commutes' _ _ := mul_comm _ _
  smul_def' r a := (wordEquiv T).injective (by
    change r • a.val = T.multiply (r • T.one) a.val
    rw [h.smul_mul, h.one_mul])

/-- Reindex the actual storage words onto the numeric basis of the splitter. -/
def coordinates [WordTable.Laws T] {d : ℕ} (e : Fin d ≃ ι) :
    TableWord T ≃ₗ[K] (Fin d → K) where
  toFun a i := a.val (e i)
  invFun x := ⟨fun i => x (e.symm i)⟩
  left_inv a := (wordEquiv T).injective (funext fun i => by simp)
  right_inv x := funext fun i => by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The checked model is an algebra equivalence. Its decoding routine
does not occur in the storage arithmetic. -/
def modelEquiv [WordTable.Laws T] {A : Type} [CommRing A] [Algebra K A]
    (D : (ι → K) ≃ₗ[K] A) (hOne : D T.one = 1)
    (hMul : ∀ a b, D (T.multiply a b) = D a * D b) :
    TableWord T ≃ₐ[K] A where
  toEquiv := (wordEquiv T).trans D.toEquiv
  map_mul' a b := hMul a.val b.val
  map_add' a b := D.map_add a.val b.val
  commutes' r := by
    change D (r • T.one) = algebraMap K A r
    rw [map_smul, hOne, Algebra.smul_def, mul_one]

#print axioms val_mul
#print axioms coordinates
#print axioms modelEquiv

end TableWord

end EvenTI.CellProducer
