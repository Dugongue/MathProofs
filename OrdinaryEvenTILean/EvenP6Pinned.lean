import EvenLiveRowAddress
import Mathlib.Algebra.Algebra.Hom

namespace EvenTI.CellPreparation

open scoped BigOperators

variable {K V C : Type} [Field K] {d : ℕ}
variable (X : V → Type) (Y : C → Type)
  [∀ i, Field (X i)] [∀ i, Algebra K (X i)]
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]

abbrev withBase (A : V → Type) : Option (V) → Type
  | none => K
  | some i => A i

instance withBaseField (i : Option (V)) : Field (withBase (K := K) X i) := by
  cases i <;> infer_instance

instance withBaseAlgebra (i : Option (V)) : Algebra K (withBase (K := K) X i) := by
  cases i <;> infer_instance

def baseUnit {A : Type} [Field A] [Algebra K A] (a : Kˣ) : Aˣ :=
  Units.map (algebraMap K A).toMonoidHom a

theorem map_baseUnit {A B : Type} [Field A] [Algebra K A] [Field B] [Algebra K B]
    (e : A →ₐ[K] B) (a : Kˣ) :
    Units.map e.toRingHom.toMonoidHom (baseUnit a) = baseUnit a := by
  apply Units.ext
  exact e.commutes (a : K)

variable (orig : C → Fin d → Option (V))
variable (emb : ∀ j i, withBase (K := K) X (orig j i) →ₐ[K] Y j)

def filledOrigin : Option (C) → Fin d → Option (V)
  | none, _ => none
  | some j, i => orig j i

def filledEmbedding (j : Option (C)) (i : Fin d) :
    withBase (K := K) X (filledOrigin orig j i) →ₐ[K] withBase (K := K) Y j :=
  match j with
  | none => AlgHom.id K K
  | some j => emb j i

def filledRatio (c : ∀ j, (Y j)ˣ) : ∀ j, (withBase (K := K) Y j)ˣ
  | none => 1
  | some j => c j

def slotValue (x : ∀ v, (withBase (K := K) X v)ˣ) (j : Option (C)) (i : Fin d) :
    (withBase (K := K) Y j)ˣ :=
  Units.map (filledEmbedding X Y orig emb j i).toRingHom.toMonoidHom
    (x (filledOrigin orig j i))

def pinBase (x : ∀ v : V, (X v)ˣ) : ∀ v, (withBase (K := K) X v)ˣ
  | none => 1
  | some v => x v

private theorem slotValue_dummy (x : ∀ v, (withBase (K := K) X v)ˣ) (i : Fin d) :
    slotValue X Y orig emb x none i = x none := by
  apply Units.ext
  rfl

private theorem pin_normalized (x : ∀ v, (withBase (K := K) X v)ˣ)
    (v : Option (V)) :
    pinBase (K := K) X (fun i => x (some i) * baseUnit (x none)⁻¹) v =
      x v * baseUnit (x none)⁻¹ := by
  cases v with
  | some i => rfl
  | none =>
    change (1 : Kˣ) = x none * baseUnit (x none)⁻¹
    have h (a : Kˣ) : (baseUnit (K := K) (A := K) a) = a := by
      apply Units.ext
      simp [baseUnit]
    rw [h, mul_inv_cancel]

/-- One extra base-field row lets the existing fixed-arity prefix layout
handle pinned slots. The extra row forces the dummy unit to have d-th
power one, so normalizing by that unit preserves every real row. -/
theorem filled_rows_iff (c : ∀ j, (Y j)ˣ) :
    (∃ x : ∀ v, (withBase (K := K) X v)ˣ, ∀ j : Option (C),
      (∏ i : Fin d, slotValue X Y orig emb x j i) = filledRatio (K := K) Y c j) ↔
    (∃ x : ∀ v : V, (X v)ˣ, ∀ j : C,
      (∏ i : Fin d, slotValue X Y orig emb (pinBase (K := K) X x) (some j) i) = c j) := by
  constructor
  · rintro ⟨x, hx⟩
    have hd : x none ^ d = 1 := by
      simpa [slotValue_dummy, filledRatio] using hx none
    let y := fun v : V => x (some v) * baseUnit (x none)⁻¹
    refine ⟨y, fun j => ?_⟩
    have hfactor (i : Fin d) :
        slotValue X Y orig emb (pinBase (K := K) X y) (some j) i =
          slotValue X Y orig emb x (some j) i * baseUnit (x none)⁻¹ := by
      unfold slotValue
      rw [pin_normalized, map_mul, map_baseUnit]
    simp only [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow : (baseUnit (K := K) (A := Y j) (x none)⁻¹) ^ d = 1 := by
      simp only [baseUnit, ← map_pow, inv_pow, hd, inv_one, map_one]
    rw [hpow, mul_one]
    exact hx (some j)
  · rintro ⟨x, hx⟩
    refine ⟨pinBase (K := K) X x, ?_⟩
    rintro (_ | j)
    · simp [slotValue_dummy, pinBase, filledRatio]
    · exact hx j

#print axioms filled_rows_iff

end EvenTI.CellPreparation
