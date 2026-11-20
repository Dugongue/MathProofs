import EvenP6CellsCoded
import EvenP6CellsSemantics

/-! Compact field words. Their inverse is implemented by the checked
linear solve in the real field corner. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped BigOperators

variable {K A : Type} [Field K] [DecidableEq K] [CommRing A] [Algebra K A] {d : ℕ}

def compactTable (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    WordTable K (Fin (rawCellDegree C e)) where
  one := cellCoefficients C e e
  multiply u v := cellCoefficients C e (cellDecode C e u * cellDecode C e v)

abbrev CompactCell (C : A ≃ₗ[K] (Fin d → K)) (e : A) := TableWord (compactTable C e)

/-- The proof certificate of the live field. The payload stores only its
idempotent and compact coordinates. -/
class CellFieldCertificate (C : A ≃ₗ[K] (Fin d → K)) (e : A) : Prop where
  idem : e * e = e
  nonzero : e ≠ 0
  inverse_exists : ∀ x : A, e * x ≠ 0 → ∃ y : A, (e * x) * y = e

def cellDecoder (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    (Fin (rawCellDegree C e) → K) →ₗ[K] A :=
  C.symm.toLinearMap.comp (Fintype.linearCombination K (fun i => ((rawCellRows C e).get i).2))

@[simp] theorem cellDecoder_apply (C : A ≃ₗ[K] (Fin d → K)) (e : A)
    (x : Fin (rawCellDegree C e) → K) : cellDecoder C e x = cellDecode C e x := rfl

private theorem cellDecoder_injective (C : A ≃ₗ[K] (Fin d → K)) (e : A) (he : e * e = e) :
    Function.Injective (cellDecoder C e) := by
  intro x y h
  simp only [cellDecoder_apply] at h
  rw [← cellCoefficients_decode C he x, h, cellCoefficients_decode C he y]

theorem cellDecoder_one (C : A ≃ₗ[K] (Fin d → K)) (e : A) (he : e * e = e) :
    cellDecoder C e (compactTable C e).one = e := by
  rw [cellDecoder_apply]
  exact (cellDecode_coefficients C e e).trans he

theorem cellDecoder_mul (C : A ≃ₗ[K] (Fin d → K)) (e : A) (he : e * e = e)
    (x y : Fin (rawCellDegree C e) → K) :
    cellDecoder C e ((compactTable C e).multiply x y) = cellDecoder C e x * cellDecoder C e y := by
  simp only [compactTable, cellDecoder_apply, cellDecode_coefficients]
  rw [← mul_assoc, cellDecode_fixed C he x]

instance compactTable_laws (C : A ≃ₗ[K] (Fin d → K)) (e : A) [h : CellFieldCertificate C e] :
    WordTable.Laws (compactTable C e) := by
  let D := cellDecoder C e
  have hm := cellDecoder_mul C e h.idem
  have h1 := cellDecoder_one C e h.idem
  constructor
  · intro a b c
    apply cellDecoder_injective C e h.idem
    simp only [hm, mul_assoc]
  · intro a b
    apply cellDecoder_injective C e h.idem
    simp only [hm, mul_comm]
  · intro a
    apply cellDecoder_injective C e h.idem
    rw [hm, h1, cellDecoder_apply, cellDecode_fixed C h.idem a]
  · intro a
    apply cellDecoder_injective C e h.idem
    simpa only [hm, map_zero, zero_mul] using (rfl : (0 : A) = 0)
  · intro a b c
    apply cellDecoder_injective C e h.idem
    simp only [hm, map_add, add_mul]
  · intro r a b
    apply cellDecoder_injective C e h.idem
    simp only [hm, map_smul, smul_mul_assoc]

def compactInv (C : A ≃ₗ[K] (Fin d → K)) (e : A) [CellFieldCertificate C e]
    (x : CompactCell C e) : CompactCell C e :=
  if x = 0 then 0 else
    ((rawCellDivision C e (cellDecode C e x.val) e).map
      (fun z => TableWord.mk (cellCoefficients C e z))).getD 0

theorem compactDecode_injective (C : A ≃ₗ[K] (Fin d → K)) (e : A)
    [h : CellFieldCertificate C e] :
    Function.Injective (fun x : CompactCell C e => cellDecoder C e x.val) :=
  (cellDecoder_injective C e h.idem).comp (TableWord.wordEquiv _).injective

private theorem compact_inv_cancel (C : A ≃ₗ[K] (Fin d → K)) (e : A)
    [h : CellFieldCertificate C e] (x : CompactCell C e) (hx : x ≠ 0) :
    x * compactInv C e x = 1 := by
  let t := cellDecode C e x.val
  have ht : e * t = t := cellDecode_fixed C h.idem x.val
  have ht0 : e * t ≠ 0 := by
    rw [ht]
    intro hz
    apply hx
    apply compactDecode_injective C e
    change cellDecoder C e x.val = cellDecoder C e 0
    rw [map_zero]
    exact hz
  obtain ⟨w, hw⟩ := h.inverse_exists _ ht0
  have hs := rawCellDivision_isSome C e t e ⟨w, hw.trans h.idem.symm⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have hR := rawCellDivision_sound C h.idem hr
  apply compactDecode_injective C e
  simp only [TableWord.val_mul, TableWord.val_one, cellDecoder_mul C e h.idem,
    cellDecoder_one C e h.idem]
  unfold compactInv
  rw [if_neg hx]
  change cellDecoder C e x.val *
      cellDecoder C e (((rawCellDivision C e t e).map
        (fun z => TableWord.mk (cellCoefficients C e z))).getD (0 : CompactCell C e)).val = e
  rw [hr, Option.map_some, Option.getD_some, cellDecoder_apply, cellDecoder_apply,
    cellDecode_coefficients, hR.1]
  calc
    t * r = (e * t) * r := by rw [ht]
    _ = e * e := hR.2
    _ = e := h.idem

instance compactField (C : A ≃ₗ[K] (Fin d → K)) (e : A)
    [h : CellFieldCertificate C e] : Field (CompactCell C e) where
  __ := (inferInstance : CommRing (CompactCell C e))
  inv := compactInv C e
  inv_zero := if_pos rfl
  mul_inv_cancel := compact_inv_cancel C e
  nnqsmul := _
  qsmul := _
  exists_pair_ne := ⟨0, 1, fun he => h.nonzero (by
    have hh := congrArg (fun x : CompactCell C e => cellDecoder C e x.val) he
    change cellDecoder C e 0 = cellDecoder C e (compactTable C e).one at hh
    rw [map_zero, cellDecoder_one C e h.idem] at hh
    exact hh.symm)⟩

/-- Install an ambient operand in the stored field corner. -/
def compactPack (C : A ≃ₗ[K] (Fin d → K)) (e x : A) : CompactCell C e :=
  ⟨cellCoefficients C e x⟩

@[simp] theorem compactPack_decode (C : A ≃ₗ[K] (Fin d → K)) (e x : A) :
    cellDecoder C e (compactPack C e x).val = e * x := cellDecode_coefficients C e x

/-- Map a real mode-field value into its field cell. -/
def compactAlgebraMap {B : Type} [Semiring B] [Algebra K B]
    (C : A ≃ₗ[K] (Fin d → K)) (e : A) [h : CellFieldCertificate C e]
    (f : B →ₐ[K] A) : B →ₐ[K] CompactCell C e where
  toFun x := compactPack C e (f x)
  map_one' := by
    apply compactDecode_injective C e
    simp only [compactPack_decode, map_one, mul_one, TableWord.val_one,
      cellDecoder_one C e h.idem]
  map_zero' := by
    apply compactDecode_injective C e
    change cellDecoder C e (compactPack C e (f 0)).val = cellDecoder C e 0
    simp only [compactPack_decode, map_zero, mul_zero]
  map_add' a b := by
    apply compactDecode_injective C e
    change cellDecoder C e (compactPack C e (f (a+b))).val =
      cellDecoder C e ((compactPack C e (f a)).val + (compactPack C e (f b)).val)
    simp only [compactPack_decode, map_add, mul_add]
  map_mul' a b := by
    apply compactDecode_injective C e
    simp only [TableWord.val_mul, cellDecoder_mul C e h.idem, compactPack_decode, map_mul]
    calc
      e * (f a * f b) = (e * e) * (f a * f b) := by rw [h.idem]
      _ = _ := by ac_rfl
  commutes' r := by
    apply compactDecode_injective C e
    change cellDecoder C e (compactPack C e (f (algebraMap K B r))).val =
      cellDecoder C e (r • (compactTable C e).one)
    rw [compactPack_decode, AlgHom.commutes, map_smul, cellDecoder_one C e h.idem,
      Algebra.smul_def, mul_comm]

section Model

variable {J : Type} [DecidableEq J]
  {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

theorem cellField_of_coordinate (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e : A} (he : E e = Pi.single j 1) :
    CellFieldCertificate C e := by
  refine ⟨idempotent_of_field_projection E j he, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at he
    have hz : (0 : F j) = 1 := by simpa using congrFun he j
    exact zero_ne_one hz
  · intro x hx
    have hx' : E x j ≠ 0 := by
      intro h
      apply hx
      apply E.injective
      rw [project_to_field E j he, h, Pi.single_zero, map_zero]
    obtain ⟨r, hr, _⟩ := rawCellDivision_exact C E j (target := e) he hx'
    exact ⟨r, ((rawCellDivision_sound C
      (idempotent_of_field_projection E j he) hr).2).trans
        (idempotent_of_field_projection E j he)⟩

end Model

section Produced

variable [Fintype K] [DecidableEq A] {J : Type} [Fintype J] [DecidableEq J]
  {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

theorem rawCell_field_certificate (enum : Fin (Fintype.card K) ≃ K)
    (C : A ≃ₗ[K] (Fin d → K)) (E : A ≃ₐ[K] (∀ j, F j))
    (i : Fin (rawCells enum C).length) :
    CellFieldCertificate C ((rawCells enum C).get i) := by
  obtain ⟨order, h⟩ := rawCells_exact enum C E
  exact cellField_of_coordinate C E (order i) (h i)

instance compactFintype (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    Fintype (CompactCell C e) :=
  Fintype.ofEquiv _ (TableWord.wordEquiv _).symm

theorem compact_card (C : A ≃ₗ[K] (Fin d → K)) (e : A) :
    Fintype.card (CompactCell C e) = Fintype.card K ^ rawCellDegree C e := by
  rw [Fintype.card_congr (TableWord.wordEquiv _), Fintype.card_fun, Fintype.card_fin]

end Produced

#print axioms compact_inv_cancel
#print axioms cellField_of_coordinate
#print axioms compactAlgebraMap
#print axioms rawCell_field_certificate

end EvenTI.CellProducer
