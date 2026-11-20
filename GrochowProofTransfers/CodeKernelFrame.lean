import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Abel

namespace CodeKernelFrame

/-- Coset relations generated from coordinate fibers by intersection and composition. -/
inductive RelationTerm (I : Type*) where
  | generator (i : I)
  | meet (s t : RelationTerm I)
  | compose (s t : RelationTerm I)

def RelationTerm.eval {I X : Type*} (R : I → X → X → Prop) :
    RelationTerm I → X → X → Prop
  | .generator i, x, y => R i x y
  | .meet s t, x, y => s.eval R x y ∧ t.eval R x y
  | .compose s t, x, z => ∃ y, s.eval R x y ∧ t.eval R y z

/-- A bijection transporting coordinate relations transports every generated term. -/
theorem transports_terms {I X Y : Type*} (R : I → X → X → Prop) (S : I → Y → Y → Prop)
    (e : X ≃ Y) (h : ∀ i x y, R i x y ↔ S i (e x) (e y)) (t : RelationTerm I)
    (x y : X) : t.eval R x y ↔ t.eval S (e x) (e y) := by
  induction t generalizing x y with
  | generator i => exact h i x y
  | meet u v hu hv => exact and_congr (hu x y) (hv x y)
  | compose u v hu hv =>
    constructor
    · rintro ⟨z, hz₁, hz₂⟩
      exact ⟨e z, (hu x z).mp hz₁, (hv z y).mp hz₂⟩
    · rintro ⟨z, hz₁, hz₂⟩
      refine ⟨e.symm z, (hu x _).mpr ?_, (hv _ y).mpr ?_⟩
      · simpa only [e.apply_symm_apply] using hz₁
      · simpa only [e.apply_symm_apply] using hz₂

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- On an abelian group, composition of two coset relations represents the subgroup sum. -/
theorem compose_coset_fibers (P Q : AddSubgroup G) (x z : G) :
    (∃ y, x - y ∈ P ∧ y - z ∈ Q) ↔ x - z ∈ P ⊔ Q := by
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨y, hp, hq⟩
    exact ⟨x - y, hp, y - z, hq, by abel⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨x - u, ?_, ?_⟩
    · simpa only [sub_sub_cancel] using hu
    · have h : x - u - z = (x - z) - u := by abel
      rw [h, ← huv, add_comm u v, add_sub_cancel_right]
      exact hv

def RelationTerm.subgroup {I : Type*} (K : I → AddSubgroup G) :
    RelationTerm I → AddSubgroup G
  | .generator i => K i
  | .meet s t => s.subgroup K ⊓ t.subgroup K
  | .compose s t => s.subgroup K ⊔ t.subgroup K

/-- A term built from coset relations is the coset relation of the matching
meet and join term in the subgroup lattice. -/
theorem eval_coset_iff {I : Type*} (K : I → AddSubgroup G) (t : RelationTerm I)
    (x y : G) :
    t.eval (fun i u v => u - v ∈ K i) x y ↔ x - y ∈ t.subgroup K := by
  induction t generalizing x y with
  | generator i => rfl
  | meet s t hs ht =>
    change (s.eval _ x y ∧ t.eval _ x y) ↔ x - y ∈ s.subgroup K ⊓ t.subgroup K
    exact and_congr (hs x y) (ht x y)
  | compose s t hs ht =>
    change (∃ z, s.eval _ x z ∧ t.eval _ z y) ↔ x - y ∈ s.subgroup K ⊔ t.subgroup K
    simpa only [hs, ht] using compose_coset_fibers (s.subgroup K) (t.subgroup K) x y
/-- Preserving the three projection fibers of a product group forces additivity. -/
theorem additive_of_three_projections (f : G × G → H × H)
    (hzero : f (0, 0) = (0, 0))
    (hfirst : ∀ u v w, (f (u, v)).1 = (f (u, w)).1)
    (hsecond : ∀ u v w, (f (u, v)).2 = (f (w, v)).2)
    (hsum : ∀ u v, (f (u, v)).1 + (f (u, v)).2 =
      (f (u + v, 0)).1 + (f (u + v, 0)).2) :
    ∀ x y, f (x + y) = f x + f y := by
  let a (u : G) := (f (u, 0)).1
  let b (v : G) := (f (0, v)).2
  have hs (u v : G) : f (u, v) = (a u, b v) :=
    Prod.ext (hfirst u v 0) (hsecond u v 0)
  have ha0 : a 0 = 0 := congrArg Prod.fst hzero
  have hb0 : b 0 = 0 := congrArg Prod.snd hzero
  have heq (u v : G) : a u + b v = a (u + v) := by
    simpa only [hs, hb0, Prod.fst, Prod.snd, add_zero] using hsum u v
  have hb (v : G) : b v = a v := by
    simpa only [ha0, zero_add] using heq 0 v
  have ha (u v : G) : a (u + v) = a u + a v := by
    rw [← hb v]
    exact (heq u v).symm
  rintro ⟨u, v⟩ ⟨w, z⟩
  change f (u + w, v + z) = f (u, v) + f (w, z)
  simp only [hs, hb, ha, Prod.mk_add_mk]

private def firstFiber (x y : G × G) : Prop := x.1 = y.1
private def secondFiber (x y : G × G) : Prop := x.2 = y.2
private def sumFiber (x y : G × G) : Prop := x.1 + x.2 = y.1 + y.2

/-- Intrinsically recovered fibers suffice to turn a normalized symbol
equivalence into an additive equivalence on the codeword spaces. -/
def additiveEquivOfGeneratedFrame {I : Type*}
    (R : I → G × G → G × G → Prop) (S : I → H × H → H × H → Prop)
    (e : G × G ≃ H × H) (hzero : e (0, 0) = (0, 0))
    (h : ∀ i x y, R i x y ↔ S i (e x) (e y))
    (a b c : RelationTerm I)
    (haR : ∀ x y, a.eval R x y ↔ firstFiber x y)
    (hbR : ∀ x y, b.eval R x y ↔ secondFiber x y)
    (hcR : ∀ x y, c.eval R x y ↔ sumFiber x y)
    (haS : ∀ x y, a.eval S x y ↔ firstFiber x y)
    (hbS : ∀ x y, b.eval S x y ↔ secondFiber x y)
    (hcS : ∀ x y, c.eval S x y ↔ sumFiber x y) :
    G × G ≃+ H × H where
  toEquiv := e
  map_add' := additive_of_three_projections e hzero
    (fun u v w => (haS _ _).mp ((transports_terms R S e h a _ _).mp
      ((haR (u, v) (u, w)).mpr rfl)))
    (fun u v w => (hbS _ _).mp ((transports_terms R S e h b _ _).mp
      ((hbR (u, v) (w, v)).mpr rfl)))
    (fun u v => (hcS _ _).mp ((transports_terms R S e h c _ _).mp
      ((hcR (u, v) (u + v, 0)).mpr (by simp [sumFiber]))))

end CodeKernelFrame
