import EvenP6SignedLayout
import EvenLiveRowAddress

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenOrdinaryTI.LiveRows

variable {J V : Type} {s t d : ℕ}
variable (X : V → Type) (Y : J → Type) [∀ v, Field (X v)] [∀ j, Field (Y j)]
variable (ev : Fin s ≃ V) (ej : Fin t ≃ J)
variable (orig : J → Fin d → V)
variable (emb : ∀ j i, X (orig j i) →+* Y j)

def numberedOrigin (j : Fin t) (i : Fin d) : Fin s :=
  ev.symm (orig (ej j) i)

private def moveField {a b : V} (h : a = b) : X a →+* X b := by
  subst b
  exact RingHom.id _

def numberedEmbedding (j : Fin t) (i : Fin d) :
    X (ev (numberedOrigin ev ej orig j i)) →+* Y (ej j) :=
  (emb (ej j) i).comp (moveField X (ev.apply_symm_apply (orig (ej j) i)))

private def fromNumbered (x : ∀ v, (X (ev v))ˣ) (v : V) : (X v)ˣ :=
  Units.map (moveField X (ev.apply_symm_apply v)).toMonoidHom (x (ev.symm v))

private theorem fromNumbered_of (x : ∀ v, (X v)ˣ) :
    fromNumbered X ev (fun i => x (ev i)) = x := by
  funext v
  let w := ev (ev.symm v)
  have h : w = v := ev.apply_symm_apply _
  change Units.map (moveField X h).toMonoidHom (x w) = x v
  generalize w = u at h ⊢
  cases h
  apply Units.ext
  rfl

private theorem numberedFactor (x : ∀ v, (X (ev v))ˣ) (j : Fin t) (i : Fin d) :
    Units.map (numberedEmbedding X Y ev ej orig emb j i).toMonoidHom
        (x (numberedOrigin ev ej orig j i)) =
      Units.map (emb (ej j) i).toMonoidHom (fromNumbered X ev x (orig (ej j) i)) := by
  apply Units.ext
  rfl

/-- Actual field-unit row semantics are preserved by the layout's
variable numbering and row numbering. -/
theorem numberedRows_iff (c : ∀ j, (Y j)ˣ) :
    (∃ x : ∀ v, (X (ev v))ˣ, ∀ j : Fin t,
      (∏ i : Fin d, Units.map (numberedEmbedding X Y ev ej orig emb j i).toMonoidHom
        (x (numberedOrigin ev ej orig j i))) = c (ej j)) ↔
    (∃ x : ∀ v, (X v)ˣ, ∀ j : J,
      (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fromNumbered X ev x, ?_⟩
    intro j
    obtain ⟨k, rfl⟩ := ej.surjective j
    simpa only [numberedFactor X Y ev ej orig emb x] using hx k
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x (ev i), fun j => ?_⟩
    calc
      _ = ∏ i : Fin d, Units.map (emb (ej j) i).toMonoidHom
          (fromNumbered X ev (fun v => x (ev v)) (orig (ej j) i)) :=
        Finset.prod_congr rfl fun i _ =>
          numberedFactor X Y ev ej orig emb (fun v => x (ev v)) j i
      _ = _ := by rw [fromNumbered_of]; exact hx (ej j)

/-- Run the existing physical address layout on any exactly numbered field
network, including the layouts containing base pins and inverse copies. -/
theorem numberedPrefix_iff (c : ∀ j, (Y j)ˣ) :
    (∃ a, ∀ r, physicalValue (fun v => X (ev v)) (fun j => Y (ej j))
      (numberedOrigin ev ej orig) (numberedEmbedding X Y ev ej orig emb) a r =
      physicalRHS (fun j => Y (ej j)) (fun j => c (ej j)) r) ↔
    (∃ x : ∀ v, (X v)ˣ, ∀ j : J,
      (∏ i : Fin d, Units.map (emb j i).toMonoidHom (x (orig j i))) = c j) :=
  (physical_solves_iff _ _ _ _ _).trans (numberedRows_iff X Y ev ej orig emb c)

#print axioms numberedRows_iff
#print axioms numberedPrefix_iff

end EvenTI.CellPreparation
