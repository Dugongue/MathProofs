import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic

namespace Mathproof.EvenOrdinaryTISingular

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Retain the last `b` columns, dropping a prescribed number of earlier columns. -/
def suffix {b : ℕ} : (t : ℕ) → (Fin (b + t) → V) → Fin b → V
  | 0, x => x
  | t+1, x => suffix t (Fin.tail x)

abbrev Independent (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    (b : ℕ) := {x : Fin b → V // LinearIndependent K x}

abbrev completion {b : ℕ} (y : Independent K V b) (t : ℕ) :=
  {x : Independent K V (b + t) // suffix t x.val = y.val}

theorem suffix_independent {b : ℕ} (t : ℕ) (x : Independent K V (b+t)) :
    LinearIndependent K (suffix t x.val) := by
  induction t with
  | zero => exact x.property
  | succ t ih =>
    exact ih ⟨Fin.tail x.val, (linearIndependent_finSucc.mp x.property).1⟩

private theorem subtype_heq_of_pred_eq {A : Type*} {P Q : A → Prop} (h : P = Q)
    {x : Subtype P} {y : Subtype Q} (hv : x.val = y.val) : HEq x y := by
  subst Q
  exact heq_of_eq (Subtype.ext hv)

private def completionSuccEquiv {b : ℕ} (y : Independent K V b) (t : ℕ) :
    completion y (t+1) ≃ Σ x : completion y t,
      ((Submodule.span K (Set.range (x.val.val)))ᶜ : Set V) where
  toFun z :=
    let hz := linearIndependent_finSucc.mp z.val.property
    ⟨⟨⟨Fin.tail z.val.val, hz.1⟩, z.property⟩, ⟨z.val.val 0, hz.2⟩⟩
  invFun z :=
    ⟨⟨Fin.cons (α:=fun _ => V) z.2.val z.1.val.val,
      linearIndependent_finCons.mpr ⟨z.1.val.property, z.2.property⟩⟩, by
      change suffix t (Fin.tail (Fin.cons (α:=fun _ => V) z.2.val z.1.val.val)) = y.val
      rw [Fin.tail_cons]
      exact z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Fin.cons_self_tail (α:=fun _ => V) _
  right_inv := by
    rintro ⟨x, v⟩
    have hx : Fin.tail (Fin.cons (α:=fun _ => V) v.val x.val.val) = x.val.val := Fin.tail_cons (α:=fun _ => V) _ _
    have hV : Fin.cons (α:=fun _ => V) v.val x.val.val 0 = v.val := Fin.cons_zero (α:=fun _ => V) _ _
    apply Sigma.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact hx
    · apply subtype_heq_of_pred_eq
      · funext a
        change (a ∉ Submodule.span K (Set.range (Fin.tail (Fin.cons (α:=fun _ => V) v.val x.val.val)))) =
          (a ∉ Submodule.span K (Set.range x.val.val))
        rw [hx]
      · exact hV

section Finite

variable [Fintype K] [Fintype V]

private theorem completion_zero_card {b : ℕ} (y : Independent K V b) :
    Nat.card (completion y 0) = 1 := by
  letI : Subsingleton (completion y 0) :=
    ⟨fun z w => Subtype.ext (Subtype.ext (z.property.trans w.property.symm))⟩
  letI : Unique (completion y 0) := uniqueOfSubsingleton ⟨y, rfl⟩
  exact Nat.card_unique

private theorem outside_span_card {k : ℕ} (x : Independent K V k) :
    Nat.card ((Submodule.span K (Set.range x.val))ᶜ : Set V) =
      Fintype.card V - Fintype.card K ^ k := by
  classical
  let U : Submodule K V := Submodule.span K (Set.range x.val)
  letI : Fintype U := Fintype.ofFinite _
  letI : Fintype (↥((U : Set V)ᶜ)) := Fintype.ofFinite _
  change Nat.card (↥((U : Set V)ᶜ)) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  congr 1
  change Fintype.card U = _
  rw [Module.card_eq_pow_finrank (K:=K) (V:=U)]
  exact congrArg (fun j : ℕ => Fintype.card K ^ j)
    ((finrank_span_eq_card x.property).trans (Fintype.card_fin k))

/-- Every independent suffix has exactly the same number of independent
completions. At full length these completions are invertible matrices. -/
theorem completion_card {b : ℕ} (y : Independent K V b) (t : ℕ) :
    Nat.card (completion y t) = ∏ i : Fin t, (Fintype.card V - Fintype.card K ^ (b + i.val)) := by
  classical
  induction t with
  | zero => simpa using completion_zero_card y
  | succ t ih =>
    rw [Nat.card_congr (completionSuccEquiv y t), Nat.card_sigma]
    have h (x : completion y t) :
        Nat.card ((Submodule.span K (Set.range x.val.val))ᶜ : Set V) =
          Fintype.card V - Fintype.card K ^ (b + t) := outside_span_card x.val
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ih]
    rw [Fin.prod_univ_castSucc]
    rfl

/-- Cross-multiplied event law for projecting full independent families
to an independent suffix. -/
theorem independent_suffix_event {b t : ℕ} (P : Independent K V b → Prop) :
    Nat.card {x : Independent K V (b+t) // P ⟨suffix t x.val, suffix_independent t x⟩} *
        Nat.card (Independent K V b) =
      Nat.card (Independent K V (b+t)) * Nat.card {y : Independent K V b // P y} := by
  classical
  let C := ∏ i : Fin t, (Fintype.card V - Fintype.card K ^ (b + i.val))
  let e (A : Independent K V b → Prop) :
      {x : Independent K V (b+t) // A ⟨suffix t x.val, suffix_independent t x⟩} ≃
        Σ y : {y : Independent K V b // A y}, completion y.val t :=
    { toFun := fun x => ⟨⟨⟨suffix t x.val.val, suffix_independent t x.val⟩, x.property⟩, ⟨x.val, rfl⟩⟩
      invFun := fun y => ⟨y.2.val, by
        have h : (⟨suffix t y.2.val.val, suffix_independent t y.2.val⟩ : Independent K V b) =
            y.1.val := Subtype.ext y.2.property
        rw [h]
        exact y.1.property⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨y, x⟩
        apply Sigma.ext
        · exact Subtype.ext (Subtype.ext x.property)
        · apply subtype_heq_of_pred_eq
          · funext z
            change (suffix t z.val = suffix t x.val.val) = (suffix t z.val = y.val.val)
            rw [x.property]
          · rfl }
  have he (A : Independent K V b → Prop) :
      Nat.card {x : Independent K V (b+t) // A ⟨suffix t x.val, suffix_independent t x⟩} =
        Nat.card {y : Independent K V b // A y} * C := by
    rw [Nat.card_congr (e A), Nat.card_sigma]
    simp only [completion_card, C, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
    first | rfl | simp
  have hall := he (fun _ => True)
  simp only [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at hall
  rw [he P, hall]
  ac_rfl

end Finite
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.completion_card
#print axioms Mathproof.EvenOrdinaryTISingular.independent_suffix_event
