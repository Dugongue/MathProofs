import EvenP6Gauge
import EvenP6Install

namespace EvenTI.CellPreparation

open EvenOrdinaryTI.LiveRows Module

/-- Apply the q-power map k times. This never asks the field's default
power operation to iterate over the exponentially large exponent q^k. -/
def repeatedFrobenius {A : Type} [Monoid A] (q : ℕ) (k : ℕ) (x : A) : A :=
  match k with
  | 0 => x
  | k+1 => repeatedFrobenius q k x ^ q

theorem repeatedFrobenius_eq {A : Type} [Monoid A] (q k : ℕ) (x : A) :
    repeatedFrobenius q k x = x ^ (q ^ k) := by
  induction k with
  | zero => simp [repeatedFrobenius]
  | succ k ih => rw [repeatedFrobenius, ih, ← pow_mul, pow_succ]

section FastGauge

variable {K A C : Type} [Field K] [Fintype K] [Field A] [Field C]
  [Algebra K A] [Algebra K C] [Finite A] [Finite C] [DecidableEq C] {r : ℕ}

def fastGaugeIndex (word : Fin r → A) (ref actual : A →ₐ[K] C) : Option (Fin r) :=
  (List.finRange r).find? fun k =>
    (List.finRange r).all fun i => decide (actual (word i) =
      repeatedFrobenius (Fintype.card K) k.val (ref (word i)))

theorem fastGaugeIndex_eq (word : Fin r → A) (ref actual : A →ₐ[K] C) :
    fastGaugeIndex word ref actual = gaugeIndex word ref actual := by
  unfold fastGaugeIndex gaugeIndex
  simp only [repeatedFrobenius_eq]

end FastGauge
variable {K : Type} [Field K] [Fintype K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ v, Algebra K (X v)] [∀ v, Finite (X v)]
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)] [∀ j, Finite (Y j)]
  [∀ j, DecidableEq (Y j)]
variable (orig : Fin t → Fin d → Fin s) (degree : Fin s → ℕ)
variable (B : ∀ v, Basis (Fin (degree v)) K (X v))
variable (word : ∀ v, Fin (degree v) → X v)
variable (hWord : ∀ v, word v = B v)
variable (reference live : ∀ j i, X (orig j i) →ₐ[K] Y j)

def liveGauge (j : Fin t) (i : Fin d) : Fin (degree (orig j i)) :=
  (fastGaugeIndex (word (orig j i)) (reference j i) (live j i)).get
    (by rw [fastGaugeIndex_eq, hWord]; exact gaugeIndex_total (B (orig j i)) (reference j i) (live j i))

theorem liveGauge_spec (j : Fin t) (i : Fin d) :
    ∀ x, live j i x =
      reference j i x ^ (Fintype.card K ^ (liveGauge X Y orig degree B word hWord reference live j i).val) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
    (gaugeIndex_total (B (orig j i)) (reference j i) (live j i))
  have hk' : fastGaugeIndex (word (orig j i)) (reference j i) (live j i) = some k := by
    rw [fastGaugeIndex_eq, hWord]
    exact hk
  have h : liveGauge X Y orig degree B word hWord reference live j i = k := by
    unfold liveGauge
    exact Option.get_of_eq_some _ hk'
  rw [h]
  exact gaugeIndex_sound (B (orig j i)) (reference j i) (live j i) k hk
def installGaugeBanks (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ) : PrefixBanks :=
  installPrefixBanks orig
    (fun j i => Fintype.card K ^ (liveGauge X Y orig degree B word hWord reference live j i).val)
    order modulus

theorem gaugeBank_main_slot (order : Fin (VarCount s t d) → ℕ) (modulus : ℕ)
    (j : Fin t) (i : Fin d) :
    (installGaugeBanks X Y orig degree B word hWord reference live order modulus).gauge.getD
        (3 * (rowIndex (j, .inl i)).val + 2) 0 =
      (Fintype.card K ^ (liveGauge X Y orig degree B word hWord reference live j i).val) % modulus := by
  let w (j : Fin t) (i : Fin d) :=
    Fintype.card K ^ (liveGauge X Y orig degree B word hWord reference live j i).val
  change (SmithGaugeBank modulus (extendSmithGauge w)).getD
    (3 * (rowIndex (j, .inl i)).val + (2 : Fin 3).val) 0 = _
  rw [gaugeBank_at_slot, extendSmithGauge_step]
  rfl

#print axioms fastGaugeIndex_eq
#print axioms liveGauge_spec
#print axioms gaugeBank_main_slot

end EvenTI.CellPreparation
