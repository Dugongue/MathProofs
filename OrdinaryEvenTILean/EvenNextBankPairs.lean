import EvenNextSourceChoice
import EvenNextKernelBank

namespace EvenTI.Contract

open Action

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l r n : Nat}

/-- Read one kernel basis from the row-major output bank. The coordinate
ordering is the same one used to install the input columns. -/
def cutBankBasis {I : Type} {c : Nat} (ord : I ≃ Fin n)
    (read : Nat → K) (out : Nat) : Fin c → I → K :=
  fun a i => readBasis (m := n) read out a (ord i)

def bankForms {I : Type} [Fintype I] [DecidableEq I] {c : Nat}
    (F : FieldEncoding K) (ord : I ≃ Fin n)
    (read : Nat → K) (out budget : Nat) (good : (I → K) → Bool) : List (I → K) :=
  (linearChoices F (cutBankBasis (c := c) ord read out) budget).filter
    (fun v => decide (v ≠ 0) && good v)

theorem bankForms_eq {I W : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module K W] {c : Nat}
    (F : FieldEncoding K) (ord : I ≃ Fin n)
    (read : Nat → K) (out budget : Nat) (good : (I → K) → Bool)
    (f : (I → K) →ₗ[K] W) (xs : Fin c → I → K)
    (hRead : ∀ i j, read (out + (i.val * n + (ord j).val)) = xs i j)
    (hInd : LinearIndependent K xs) (hSpan : Submodule.span K (Set.range xs) = f.ker) :
    bankForms (c := c) F ord read out budget good =
      kernelForms F f (frameFromVectors f xs hInd hSpan) budget good := by
  have hBank : cutBankBasis ord read out = xs := funext fun i => funext (hRead i)
  unfold bankForms kernelForms
  rw [hBank, linearChoices_eq_kernel F f xs hInd hSpan]

/-- Produce the two-sided kernel trials directly from the basis words. -/
def bankCutFormPairs {c e a b : Nat} (F : FieldEncoding K)
    (leftOrder : Coord l n ≃ Fin a) (rightOrder : Coord r n ≃ Fin b)
    (leftRead rightRead : Nat → K) (leftOut rightOut : Nat)
    (leftGood : (Coord l n → K) → Bool) (rightGood : (Coord r n → K) → Bool) :
    List (CutFormPair K l r n) :=
  (bankForms (c := c) F leftOrder leftRead leftOut n leftGood).product
    (bankForms (c := e) F rightOrder rightRead rightOut n rightGood)

theorem bankCutFormPairs_eq {c e a b : Nat} (F : FieldEncoding K)
    (T : Tensor K (l + r) n)
    (leftOrder : Coord l n ≃ Fin a) (rightOrder : Coord r n ≃ Fin b)
    (leftRead rightRead : Nat → K) (leftOut rightOut : Nat)
    (leftGood : (Coord l n → K) → Bool) (rightGood : (Coord r n → K) → Bool)
    (L : Fin c → Coord l n → K) (R : Fin e → Coord r n → K)
    (hL : ∀ i j, leftRead (leftOut + (i.val * a + (leftOrder j).val)) = L i j)
    (hR : ∀ i j, rightRead (rightOut + (i.val * b + (rightOrder j).val)) = R i j)
    (hLI : LinearIndependent K L) (hRI : LinearIndependent K R)
    (hLS : Submodule.span K (Set.range L) = (leftCutKernel T).ker)
    (hRS : Submodule.span K (Set.range R) = (rightCutKernel T).ker) :
    bankCutFormPairs (c := c) (e := e) F leftOrder rightOrder
        leftRead rightRead leftOut rightOut leftGood rightGood =
      cutFormPairs F T
        ⟨c, e, frameFromVectors _ L hLI hLS, frameFromVectors _ R hRI hRS⟩
        leftGood rightGood := by
  unfold bankCutFormPairs cutFormPairs
  rw [bankForms_eq F _ _ _ _ _ (leftCutKernel T) L hL hLI hLS,
      bankForms_eq F _ _ _ _ _ (rightCutKernel T) R hR hRI hRS]

#print axioms bankForms_eq
#print axioms bankCutFormPairs_eq

end EvenTI.Contract
