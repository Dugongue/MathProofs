import EvenP6ReferenceOrders

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenOrdinaryTI.LiveRows EvenOrdinaryTI.LCMProjection

variable {K : Type} [Field K] {s t d : ℕ}

abbrev SignedSource (X : Fin s → Type) (v : Fin (s * 2 + 1)) : Type :=
  withBase (K := K) (twinField X) (signedVariableOrder s v)

abbrev SignedTarget (X : Fin s → Type) (Y : Fin t → Type) (j : Fin (t + s + 1)) : Type :=
  withBase (K := K) (extendedField X Y) (signedCellOrder t s j)

variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ v, Algebra K (X v)] [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin (d + 2) → Option (Fin s))
variable (emb : ∀ j i, withBase (K := K) X (orig j i) →ₐ[K] Y j)
variable (neg : Fin t → Fin (d + 2) → Bool)

def signedPrefixMaps (j : Fin (t + s + 1)) (i : Fin (d + 2)) :
    SignedSource (K := K) X (signedPrefixOrigin orig neg j i) →+*
      SignedTarget (K := K) X Y j :=
  numberedEmbedding _ _ (signedVariableOrder s) (signedCellOrder t s)
    (filledOrigin (extendedOrigin orig neg))
    (fun j i => (filledEmbedding (twinField X) (extendedField X Y)
      (extendedOrigin orig neg) (extendedEmbedding X Y orig emb neg) j i).toRingHom) j i

def signedPrefixRatios (c : ∀ j, (Y j)ˣ) (j : Fin (t + s + 1)) :
    (SignedTarget (K := K) X Y j)ˣ :=
  filledRatio (K := K) (extendedField X Y) (extendedRatio X Y c) (signedCellOrder t s j)

abbrev SignedReferences (s t d : ℕ) :=
  Fin (VarCount (s * 2 + 1) (t + s + 1) (d + 2)) ⊕ Fin (RowCount (t + s + 1) (d + 2))

/-- Install the computed shared addresses, orders, and LCM quotients before
entering the reference-specific field transport and Smith commands. -/
structure PreparedPrefix where
  source : List ℕ
  variableOrders : List ℕ
  referenceOrders : List ℕ
  referenceExponents : List ℕ
  modulus : ℕ

def preparePrefix (q : ℕ) (shared : Fin s → ℕ) (cell : Fin t → ℕ) : PreparedPrefix :=
  let a := signedVarDegrees shared
  let b := signedCellDegrees cell shared
  let m := numericalRefOrders (d := d + 2) q a b
  let M := commonOrder m
  ⟨SmithSourceBank (signedPrefixOrigin orig neg),
    SmithOrderBank (fun v : Fin _ => q ^ prefixVarDegrees (d := d + 2) a b v - 1),
    List.ofFn (fun i : Fin _ => m (finSumFinEquiv.symm i)),
    List.ofFn (fun i : Fin _ => M / m (finSumFinEquiv.symm i)), M⟩

theorem preparePrefix_sizes (q : ℕ) (shared : Fin s → ℕ) (cell : Fin t → ℕ) :
    let B := preparePrefix orig neg q shared cell
    let V := VarCount (s * 2 + 1) (t + s + 1) (d + 2)
    let J := RowCount (t + s + 1) (d + 2)
    B.source.length = J * 3 ∧ B.variableOrders.length = V ∧
      B.referenceOrders.length = V + J ∧ B.referenceExponents.length = V + J := by
  simp only [preparePrefix, SmithSourceBank, SmithOrderBank, List.length_ofFn, and_self]

theorem preparePrefix_words_le (q N : ℕ) (shared : Fin s → ℕ) (cell : Fin t → ℕ)
    (hs : s ≤ N) (ht : t ≤ N) (hd : d ≤ N) :
    let B := preparePrefix orig neg q shared cell
    B.source.length + B.variableOrders.length + B.referenceOrders.length +
      B.referenceExponents.length ≤ 8 * (2 * N + 3) ^ 2 := by
  dsimp only
  obtain ⟨hf, hv, hr, he⟩ := preparePrefix_sizes orig neg q shared cell
  rw [hf, hv, hr, he]
  have hR : RowCount (t + s + 1) (d + 2) ≤ (2 * N + 1) * (N + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hV : VarCount (s * 2 + 1) (t + s + 1) (d + 2) ≤
      (2 * N + 1) + (2 * N + 1) * (N + 3) :=
    Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega) (by omega))
  nlinarith

theorem preparePrefix_shared (q : ℕ) (shared : Fin s → ℕ) (cell : Fin t → ℕ)
    (j k : Fin (t + s + 1)) (i u : Fin (d + 2))
    (h : signedPrefixOrigin orig neg j i = signedPrefixOrigin orig neg k u) :
    (preparePrefix orig neg q shared cell).source.getD (3 * (rowIndex (j, .inl i)).val + 2) 0 =
      (preparePrefix orig neg q shared cell).source.getD (3 * (rowIndex (k, .inl u)).val + 2) 0 :=
  installPrefixBanks_shared (signedPrefixOrigin orig neg) (fun _ _ => 1) (fun _ => 0) 1 j k i u h

variable [∀ v, Fintype (SignedSource (K := K) X v)]
  [∀ j, Fintype (SignedTarget (K := K) X Y j)]

/-- These are precisely the reference components for the already verified
ternary Smith specification, with signed copies and base-field pins intact. -/
theorem signedPrefix_references_iff (c : ∀ j, (Y j)ˣ) :
    (∀ i : SignedReferences s t d, PrefixReferenceSolvable
      (SignedSource (K := K) X) (SignedTarget (K := K) X Y)
      (signedPrefixOrigin orig neg) (signedPrefixMaps X Y orig emb neg)
      (signedPrefixRatios X Y c) i) ↔
    ∃ x : ∀ v, (X v)ˣ, ∀ j, (∏ i, signedFactor X Y orig emb neg x j i) = c j := by
  exact (prefixReferenceSolvable_iff _ _ _ _ _).trans
    ((physical_solves_iff _ _ _ _ _).symm.trans (signedPrefix_iff X Y orig emb neg c))

#print axioms preparePrefix_sizes
#print axioms preparePrefix_words_le
#print axioms preparePrefix_shared
#print axioms signedPrefix_references_iff

end EvenTI.CellPreparation
