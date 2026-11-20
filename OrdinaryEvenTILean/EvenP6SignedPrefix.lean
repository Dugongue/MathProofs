import EvenP6Numbered
import EvenP6Install
import Mathlib.Tactic.FinCases

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenOrdinaryTI.LiveRows

private def boolOrder : Fin 2 ≃ Bool where
  toFun i := decide (i.val = 1)
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> decide
  right_inv b := by cases b <;> decide

def signedVariableOrder (s : ℕ) : Fin (s * 2 + 1) ≃ Option (Fin s × Bool) :=
  (finSuccEquiv (s * 2)).trans
    (Equiv.optionCongr (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) boolOrder)))

def signedCellOrder (t s : ℕ) : Fin (t + s + 1) ≃ Option (Fin t ⊕ Fin s) :=
  (finSuccEquiv (t + s)).trans (Equiv.optionCongr finSumFinEquiv.symm)

variable {K : Type} [Field K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ v, Algebra K (X v)]
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin (d + 2) → Option (Fin s))
variable (emb : ∀ j i, withBase (K := K) X (orig j i) →ₐ[K] Y j)
variable (neg : Fin t → Fin (d + 2) → Bool)

def signedPrefixOrigin : Fin (t + s + 1) → Fin (d + 2) → Fin (s * 2 + 1) :=
  numberedOrigin (signedVariableOrder s) (signedCellOrder t s)
    (filledOrigin (extendedOrigin orig neg))

theorem signedPrefix_iff (c : ∀ j, (Y j)ˣ) :
    let V := withBase (K := K) (twinField X)
    let C := withBase (K := K) (extendedField X Y)
    let ev := signedVariableOrder s
    let ec := signedCellOrder t s
    let e := numberedEmbedding V C ev ec (filledOrigin (extendedOrigin orig neg))
      (fun j i => (filledEmbedding (twinField X) (extendedField X Y)
        (extendedOrigin orig neg) (extendedEmbedding X Y orig emb neg) j i).toRingHom)
    let rhs := filledRatio (K := K) (extendedField X Y) (extendedRatio X Y c)
    (∃ a, ∀ r, physicalValue (fun v => V (ev v)) (fun j => C (ec j))
        (signedPrefixOrigin orig neg) e a r =
      physicalRHS (fun j => C (ec j)) (fun j => rhs (ec j)) r) ↔
    ∃ x : ∀ v, (X v)ˣ, ∀ j,
      (∏ i : Fin (d + 2), signedFactor X Y orig emb neg x j i) = c j := by
  dsimp only
  exact (numberedPrefix_iff _ _ _ _ _ _ _).trans (extended_rows_iff X Y orig emb neg c)

def installSignedPrefix
    (twist : Fin (t + s + 1) → Fin (d + 2) → ℕ)
    (order : Fin (VarCount (s * 2 + 1) (t + s + 1) (d + 2)) → ℕ) (modulus : ℕ) :
    PrefixBanks :=
  installPrefixBanks (signedPrefixOrigin orig neg) twist order modulus

/-- One dummy variable and one opposite copy per shared variable suffice,
with one extra inverse row per variable and one base pin row. -/
theorem signedPrefix_size_bound (N : ℕ) (hs : s ≤ N) (ht : t ≤ N) (hd : d ≤ N)
    (twist : Fin (t + s + 1) → Fin (d + 2) → ℕ)
    (order : Fin (VarCount (s * 2 + 1) (t + s + 1) (d + 2)) → ℕ) (modulus : ℕ) :
    let B := installSignedPrefix orig neg twist order modulus
    B.source.length + B.gauge.length + B.orders.length ≤ 14 * (2 * N + 3) ^ 2 :=
  installPrefixBanks_polynomial _ _ _ _ (2 * N + 2) (by omega) (by omega) (by omega)

#print axioms signedPrefix_iff
#print axioms signedPrefix_size_bound

end EvenTI.CellPreparation
