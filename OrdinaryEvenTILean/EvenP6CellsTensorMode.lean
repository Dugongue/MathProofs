import EvenP6CellsTensor

/-! Actual mode-to-joint inclusions on coefficient words. The tensor and
the local table models occur only in the proof of the ring-map laws. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped TensorProduct
open Module

variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]
  {N : I → Type} [∀ i, Fintype (N i)]
  {A : I → Type} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]

/-- The actual inclusion of one mode into the tensor table. Its value is
built directly by inserting the words and the units of the other modes. -/
def modeWordHom (B : ∀ i, Basis (N i) K (A i))
    (u : ∀ i, N i → K) (m : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable u m)]
    (hU : ∀ i p, u i p = (B i).repr 1 p)
    (hM : ∀ i p r q, m i p r q = (B i).repr (B i r * B i q) p)
    (i : I) (L : WordTable K (N i)) [WordTable.Laws L]
    (hL1 : (B i).equivFun.symm L.one = 1)
    (hLM : ∀ x y, (B i).equivFun.symm (L.multiply x y) =
      (B i).equivFun.symm x * (B i).equivFun.symm y) :
    TableWord L →ₐ[K] TableWord (tensorTable u m) := by
  let put : TableWord L → TableWord (tensorTable u m) := fun x => modeWord u m i x.val
  have laws : put 0 = 0 ∧ put 1 = 1 ∧
      (∀ x y, put (x + y) = put x + put y) ∧
      (∀ x y, put (x * y) = put x * put y) ∧
      (∀ r : K, put (algebraMap K (TableWord L) r) =
        algebraMap K (TableWord (tensorTable u m)) r) := by
    let G := tensorTable_decode B u m hU hM
    let H := TableWord.modelEquiv L (B i).equivFun.symm hL1 hLM
    let J := (PiTensorProduct.singleAlgHom (R := K) i (A := A)).comp H.toAlgHom
    have h (x : TableWord L) : G (put x) = J x := modeWord_decode B u m hU i x.val
    refine ⟨G.injective (by rw [h, map_zero, map_zero]),
      G.injective (by rw [h, map_one, map_one]), ?_, ?_, ?_⟩
    · intro x y
      exact G.injective (by rw [h, map_add, map_add, h, h])
    · intro x y
      exact G.injective (by rw [h, map_mul, map_mul, h, h])
    · intro x
      exact G.injective (by rw [h, AlgHom.commutes, AlgEquiv.commutes])
  exact
    { toFun := put
      map_zero' := laws.1
      map_one' := laws.2.1
      map_add' := laws.2.2.1
      map_mul' := laws.2.2.2.1
      commutes' := laws.2.2.2.2 }
@[simp] theorem modeWordHom_apply (B : ∀ i, Basis (N i) K (A i))
    (u : ∀ i, N i → K) (m : ∀ i, N i → N i → N i → K)
    [WordTable.Laws (tensorTable u m)]
    (hU : ∀ i p, u i p = (B i).repr 1 p)
    (hM : ∀ i p r q, m i p r q = (B i).repr (B i r * B i q) p)
    (i : I) (L : WordTable K (N i)) [WordTable.Laws L]
    (hL1 : (B i).equivFun.symm L.one = 1)
    (hLM : ∀ x y, (B i).equivFun.symm (L.multiply x y) =
      (B i).equivFun.symm x * (B i).equivFun.symm y)
    (x : TableWord L) :
    modeWordHom B u m hU hM i L hL1 hLM x = modeWord u m i x.val := rfl

#print axioms modeWordHom

end EvenTI.CellProducer
