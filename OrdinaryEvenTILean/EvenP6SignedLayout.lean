import EvenP6Signed

namespace EvenTI.CellPreparation

open scoped BigOperators

variable {K : Type} [Field K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ v, Algebra K (X v)]
  [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin (d + 2) → Option (Fin s))
variable (emb : ∀ j i, withBase (K := K) X (orig j i) →ₐ[K] Y j)
variable (neg : Fin t → Fin (d + 2) → Bool)

abbrev twinField (v : Fin s × Bool) := X v.1

abbrev extendedField : (Fin t ⊕ Fin s) → Type
  | .inl j => Y j
  | .inr v => X v

instance extendedFieldField (j : Fin t ⊕ Fin s) : Field (extendedField X Y j) := by
  cases j <;> infer_instance

instance extendedFieldAlgebra (j : Fin t ⊕ Fin s) : Algebra K (extendedField X Y j) := by
  cases j <;> infer_instance

private def twinOrigin (o : Option (Fin s)) (b : Bool) : Option (Fin s × Bool) :=
  o.map (fun v => (v,b))

def oppositeOrigin (v : Fin s) (i : Fin (d + 2)) : Option (Fin s × Bool) :=
  Fin.cases (some (v,false)) (Fin.cases (some (v,true)) (fun _ => none)) i

def extendedOrigin (j : Fin t ⊕ Fin s) (i : Fin (d + 2)) : Option (Fin s × Bool) :=
  match j with
  | .inl j => twinOrigin (orig j i) (neg j i)
  | .inr v => oppositeOrigin v i

private def twinEmbedding {B : Type} [Field B] [Algebra K B] (o : Option (Fin s))
    (b : Bool) (e : withBase (K := K) X o →ₐ[K] B) :
    withBase (K := K) (twinField X) (twinOrigin o b) →ₐ[K] B := by
  cases o <;> exact e

private def oppositeEmbedding (v : Fin s) (i : Fin (d + 2)) :
    withBase (K := K) (twinField X) (oppositeOrigin v i) →ₐ[K] X v := by
  induction i using Fin.cases with
  | zero => exact AlgHom.id _ _
  | succ i =>
    induction i using Fin.cases with
    | zero => exact AlgHom.id _ _
    | succ i => exact Algebra.ofId _ _

def extendedEmbedding (j : Fin t ⊕ Fin s) (i : Fin (d + 2)) :
    withBase (K := K) (twinField X) (extendedOrigin orig neg j i) →ₐ[K] extendedField X Y j :=
  match j with
  | .inl j => twinEmbedding X (orig j i) (neg j i) (emb j i)
  | .inr v => oppositeEmbedding X v i

def extendedRatio (c : ∀ j, (Y j)ˣ) : ∀ j, (extendedField X Y j)ˣ
  | .inl j => c j
  | .inr _ => 1

private theorem twin_eval {B : Type} [Field B] [Algebra K B] (o : Option (Fin s)) (b : Bool)
    (e : withBase (K := K) X o →ₐ[K] B) (x : ∀ v : Fin s × Bool, (twinField X v)ˣ) :
    Units.map (twinEmbedding X o b e).toRingHom.toMonoidHom
        (pinBase (K := K) (twinField X) x (twinOrigin o b)) =
      Units.map e.toRingHom.toMonoidHom (chooseCopy (K := K) X (fun v b => x (v,b)) o b) := by
  cases o <;> rfl

private theorem opposite_eval (x : ∀ v : Fin s × Bool, (twinField X v)ˣ)
    (v : Fin s) :
    (∏ i : Fin (d + 2),
      Units.map (oppositeEmbedding X v i).toRingHom.toMonoidHom
        (pinBase (K := K) (twinField X) x (oppositeOrigin v i))) =
      x (v,false) * x (v,true) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h (i : Fin d) :
      Units.map (oppositeEmbedding X v i.succ.succ).toRingHom.toMonoidHom
        (pinBase (K := K) (twinField X) x (oppositeOrigin v i.succ.succ)) = 1 := by
    change Units.map (Algebra.ofId K (X v)).toRingHom.toMonoidHom (1 : Kˣ) = 1
    exact map_one _
  simp only [h, Finset.prod_const_one, mul_one]
  rfl

/-- The live unsigned incidence layout for signed rows. It contains the
original active cells, one inverse equation per shared variable, and one
base dummy equation. All rows use the original fixed arity. -/
theorem extended_rows_iff (c : ∀ j, (Y j)ˣ) :
    (∃ x : ∀ v, (withBase (K := K) (twinField X) v)ˣ, ∀ j : Option (Fin t ⊕ Fin s),
      (∏ i : Fin (d + 2),
        slotValue (twinField X) (extendedField X Y) (extendedOrigin orig neg)
          (extendedEmbedding X Y orig emb neg) x j i) =
        filledRatio (K := K) (extendedField X Y) (extendedRatio X Y c) j) ↔
    (∃ x : ∀ v : Fin s, (X v)ˣ, ∀ j, (∏ i : Fin (d + 2),
      signedFactor X Y orig emb neg x j i) = c j) := by
  rw [filled_rows_iff]
  apply Iff.trans _ (copied_rows_iff X Y orig emb neg c)
  have hReal (x : ∀ v : Fin s × Bool, (twinField X v)ˣ) (j : Fin t)
      (i : Fin (d + 2)) :
      slotValue (twinField X) (extendedField X Y) (extendedOrigin orig neg)
          (extendedEmbedding X Y orig emb neg) (pinBase (K := K) (twinField X) x) (some (.inl j)) i =
        copiedFactor X Y orig emb neg (fun v b => x (v,b)) j i :=
    twin_eval X (orig j i) (neg j i) (emb j i) x
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun v b => x (v,b), fun v => ?_, fun j => ?_⟩
    · exact (opposite_eval X x v).symm.trans (hx (.inr v))
    · simpa only [hReal, extendedRatio] using hx (.inl j)
  · rintro ⟨x, hi, hx⟩
    let y (v : Fin s × Bool) := x v.1 v.2
    refine ⟨y, fun j => ?_⟩
    rcases j with j | v
    · simp only [hReal]
      exact hx j
    · exact (opposite_eval X y v).trans (hi v)

#print axioms extended_rows_iff

end EvenTI.CellPreparation
