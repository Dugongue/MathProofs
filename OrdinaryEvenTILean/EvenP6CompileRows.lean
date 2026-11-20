import EvenP6SignedRows
import EvenP6PreparedPrefix

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.CellProducer EvenOrdinaryTI.LiveRows

variable {K Q : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing Q] [Algebra K Q] [DecidableEq Q] {N d s : ℕ}
variable {width : Fin (d + 2) → ℕ}
variable {X : (i : Fin (d + 2)) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
variable (enum : Fin (Fintype.card K) ≃ K) (C : Q ≃ₗ[K] (Fin N → K))
variable [∀ i : Fin (rawCells enum C).length, CellFieldCertificate C ((rawCells enum C).get i)]
variable (mode : ∀ i, Modes X i →ₐ[K] Q)
variable (U : Fin s → Type) [∀ v, Field (U v)] [∀ v, Algebra K (U v)]
variable (key : ∀ i, Fin (width i) → Option (Fin s))
variable (link : ∀ i v, withBase (K := K) U (key i v) →ₐ[K] X i v)
variable (negative : ∀ i, Fin (width i) → Bool)

abbrev RawPrefixOutput (T : Q) :=
  (∀ r : Active enum C T, (ActiveField enum C T r)ˣ) × PreparedPrefix

/-- Form the actual ratio and address banks together. If support differs,
the checked ratio scan produces none and no branch is installed. -/
def compileRawPrefix (T S : Q) (sharedDegree : Fin s → ℕ)
    (cellDegree : Active enum C T → ℕ) : Option (RawPrefixOutput enum C T) :=
  (rawRatios enum C T S).map fun ratios =>
    (ratios, preparePrefix (joinedOrigin enum C mode key T)
      (joinedNegative enum C mode negative T) (Fintype.card K) sharedDegree cellDegree)

theorem compileRawPrefix_length (T S : Q) (sharedDegree : Fin s → ℕ)
    (cellDegree : Active enum C T → ℕ) (out : RawPrefixOutput enum C T)
    (ho : compileRawPrefix enum C mode key negative T S sharedDegree cellDegree = some out)
    (bound : ℕ) (hs : s ≤ bound) (ht : (activeCells (compactProductPack enum C T)).card ≤ bound)
    (hd : d ≤ bound) :
    out.2.source.length + out.2.variableOrders.length + out.2.referenceOrders.length +
      out.2.referenceExponents.length ≤ 8 * (2 * bound + 3) ^ 2 := by
  unfold compileRawPrefix at ho
  cases h : rawRatios enum C T S with
  | none => simp [h] at ho
  | some c =>
    simp only [h, Option.map_some, Option.some.injEq] at ho
    subst out
    apply preparePrefix_words_le _ _ _ _ _ _ hs ht hd

abbrev rawRefsHold (T : Q) (out : RawPrefixOutput enum C T)
    [∀ v, Fintype (SignedSource (K := K) U v)]
    [∀ j, Fintype (SignedTarget (K := K) U (ActiveField enum C T) j)] : Prop :=
  ∀ i : SignedReferences s (activeCells (compactProductPack enum C T)).card d,
    PrefixReferenceSolvable (SignedSource (K := K) U)
      (SignedTarget (K := K) U (ActiveField enum C T))
      (signedPrefixOrigin (joinedOrigin enum C mode key T)
        (joinedNegative enum C mode negative T))
      (signedPrefixMaps U (ActiveField enum C T)
        (joinedOrigin enum C mode key T) (joinedEmbedding enum C mode U key link T)
        (joinedNegative enum C mode negative T))
      (signedPrefixRatios U (ActiveField enum C T) out.1) i
/-- Exact feasibility of one signed compiled branch. Shared field labels
and opposite copies are the very same ones used by the executable caller. -/
theorem compileRawPrefix_iff (T S : Q) (sharedDegree : Fin s → ℕ)
    (cellDegree : Active enum C T → ℕ)
    [∀ v, Fintype (SignedSource (K := K) U v)]
    [∀ j, Fintype (SignedTarget (K := K) U (ActiveField enum C T) j)] :
    (∃ out, compileRawPrefix enum C mode key negative T S sharedDegree cellDegree = some out ∧
      rawRefsHold enum C mode U key link negative T out) ↔
    ∃ x : ∀ v, (U v)ˣ,
      (∏ i : Fin (d + 2), mode i (fun v => (sharedUnits U key link negative x i v : X i v))) * T = S := by
  constructor
  · rintro ⟨out, ho, h⟩
    have hr : rawRatios enum C T S = some out.1 := by
      simpa only [compileRawPrefix, Option.map_map, Function.comp_def, Option.map_id_fun', id_eq, Option.map_some] using
        congrArg (Option.map Prod.fst) ho
    obtain ⟨x, hx⟩ := (signedPrefix_references_iff U (ActiveField enum C T)
      (joinedOrigin enum C mode key T) (joinedEmbedding enum C mode U key link T)
      (joinedNegative enum C mode negative T) out.1).mp h
    exact ⟨x, (rawSignedRows_iff enum C mode U key link negative T S x).mpr ⟨out.1, hr, hx⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hm⟩ := (rawSignedRows_iff enum C mode U key link negative T S x).mp hx
    let bank := preparePrefix (joinedOrigin enum C mode key T)
      (joinedNegative enum C mode negative T) (Fintype.card K) sharedDegree cellDegree
    refine ⟨(c, bank), ?_, ?_⟩
    · simp only [compileRawPrefix, hc, Option.map_some, bank]
    · exact (signedPrefix_references_iff U (ActiveField enum C T)
        (joinedOrigin enum C mode key T) (joinedEmbedding enum C mode U key link T)
        (joinedNegative enum C mode negative T) c).mpr ⟨x, hm⟩

#print axioms compileRawPrefix_length
#print axioms compileRawPrefix_iff

end EvenTI.CellPreparation
