import EvenP6Pinned

namespace EvenTI.CellPreparation

open scoped BigOperators

variable {K : Type} [Field K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ v, Algebra K (X v)]
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Option (Fin s))
variable (emb : ∀ j i, withBase (K := K) X (orig j i) →ₐ[K] Y j)
variable (negative : Fin t → Fin d → Bool)

def chooseCopy (x : ∀ v : Fin s, Bool → (X v)ˣ) (v : Option (Fin s)) (b : Bool) :
    (withBase (K := K) X v)ˣ :=
  match v with
  | none => 1
  | some v => x v b

def copiedFactor (x : ∀ v : Fin s, Bool → (X v)ˣ) (j : Fin t) (i : Fin d) : (Y j)ˣ :=
  Units.map (emb j i).toRingHom.toMonoidHom
    (chooseCopy (K := K) X x (orig j i) (negative j i))

def signedFactor (x : ∀ v : Fin s, (X v)ˣ) (j : Fin t) (i : Fin d) : (Y j)ˣ :=
  let a := Units.map (emb j i).toRingHom.toMonoidHom (pinBase (K := K) X x (orig j i))
  if negative j i then a⁻¹ else a

private theorem copiedFactor_eq (x : ∀ v : Fin s, Bool → (X v)ˣ)
    (hx : ∀ v, x v false * x v true = 1) (j : Fin t) (i : Fin d) :
    copiedFactor X Y orig emb negative x j i =
      signedFactor X Y orig emb negative (fun v => x v false) j i := by
  have h (v : Option (Fin s)) (b : Bool) (e : withBase (K := K) X v →ₐ[K] Y j) :
      Units.map e.toRingHom.toMonoidHom (chooseCopy (K := K) X x v b) =
        let a := Units.map e.toRingHom.toMonoidHom (pinBase (K := K) X (fun v => x v false) v)
        if b then a⁻¹ else a := by
    cases v with
    | none => cases b <;> simp [chooseCopy, pinBase]
    | some v =>
      have hv := eq_inv_of_mul_eq_one_right (hx v)
      cases b <;> simp [chooseCopy, pinBase, hv]
  exact h (orig j i) (negative j i) (emb j i)

/-- Reuse the unsigned field-unit solver for a signed tensor action by
assigning one inverse copy to each shared variable. One product-one row
per variable enforces the reciprocal relation. -/
theorem copied_rows_iff (c : ∀ j, (Y j)ˣ) :
    (∃ x : ∀ v : Fin s, Bool → (X v)ˣ,
      (∀ v, x v false * x v true = 1) ∧
      (∀ j, (∏ i : Fin d, copiedFactor X Y orig emb negative x j i) = c j)) ↔
    (∃ x : ∀ v : Fin s, (X v)ˣ,
      ∀ j, (∏ i : Fin d, signedFactor X Y orig emb negative x j i) = c j) := by
  constructor
  · rintro ⟨x, hinv, hc⟩
    exact ⟨fun v => x v false, fun j => by
      simpa only [copiedFactor_eq X Y orig emb negative x hinv] using hc j⟩
  · rintro ⟨x, hx⟩
    let y (v : Fin s) (b : Bool) := if b then (x v)⁻¹ else x v
    have hy (v : Fin s) : y v false * y v true = 1 := by simp [y]
    refine ⟨y, hy, fun j => ?_⟩
    simpa only [copiedFactor_eq X Y orig emb negative y hy, y,
      Bool.false_eq_true, if_false] using hx j

#print axioms copied_rows_iff

end EvenTI.CellPreparation
