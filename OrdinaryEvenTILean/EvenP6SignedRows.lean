import EvenP6RawRows
import EvenP6SignedPrefix

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

abbrev Active (T : Q) :=
  Fin (activeCells (compactProductPack enum C T)).card

abbrev ActiveField (T : Q) (r : Active enum C T) :=
  ProducedCell enum C (activeIndex (compactProductPack enum C T) r)

def pickedBlock (T : Q) (r : Active enum C T) (i : Fin (d + 2)) : Fin (width i) :=
  activeBlock (rawModeIncidence enum C mode (activeIndex (compactProductPack enum C T) r) i)

def joinedOrigin (T : Q) (r : Active enum C T) (i : Fin (d + 2)) :=
  key i (pickedBlock enum C mode T r i)

def joinedNegative (T : Q) (r : Active enum C T) (i : Fin (d + 2)) :=
  negative i (pickedBlock enum C mode T r i)

def joinedEmbedding (T : Q) (r : Active enum C T) (i : Fin (d + 2)) :
    withBase (K := K) U (joinedOrigin enum C mode key T r i) →ₐ[K] ActiveField enum C T r :=
  (activeFieldEmbedding (rawModeIncidence enum C mode
    (activeIndex (compactProductPack enum C T) r) i)).comp
      (link i (pickedBlock enum C mode T r i))

/-- Map a shared variable into each of its occurrences. A missing label
represents a coordinate already acted on by the fixed branch. -/
def sharedUnits (x : ∀ v, (U v)ˣ) : ∀ i v, (X i v)ˣ :=
  fun i v =>
    let a := pinBase (K := K) U x (key i v)
    Units.map (link i v).toRingHom.toMonoidHom (if negative i v then a⁻¹ else a)

def rawSignedSourceBank (T : Q) : List ℕ :=
  SmithSourceBank (signedPrefixOrigin
    (joinedOrigin enum C mode key T) (joinedNegative enum C mode negative T))

theorem rawSignedRows_iff (T S : Q) (x : ∀ v, (U v)ˣ) :
    (∏ i : Fin (d + 2), mode i (fun v =>
      (sharedUnits U key link negative x i v : X i v))) * T = S ↔
      ∃ c : ∀ r : Active enum C T, (ActiveField enum C T r)ˣ,
        rawRatios enum C T S = some c ∧
        ∀ r, (∏ i : Fin (d + 2), signedFactor U (ActiveField enum C T)
          (joinedOrigin enum C mode key T) (joinedEmbedding enum C mode U key link T)
          (joinedNegative enum C mode negative T) x r i) = c r := by
  rw [rawRows_iff enum C mode T S (sharedUnits U key link negative x)]
  have h (r : Active enum C T) (i : Fin (d + 2)) :
      selectedValue (rawModeIncidence enum C mode) (sharedUnits U key link negative x)
          (activeIndex (compactProductPack enum C T) r) i =
        signedFactor U (ActiveField enum C T)
          (joinedOrigin enum C mode key T) (joinedEmbedding enum C mode U key link T)
          (joinedNegative enum C mode negative T) x r i := by
    unfold selectedValue sharedUnits signedFactor joinedNegative joinedEmbedding
    simp only [pickedBlock, joinedOrigin]
    split <;> simp_all only [map_inv] <;> apply Units.ext <;> rfl
  simp only [h]

#print axioms rawSignedRows_iff

end EvenTI.CellPreparation
