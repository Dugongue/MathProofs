import EvenP6SignedRows

namespace EvenTI.CellPreparation

open scoped BigOperators

variable {K : Type} [Field K] {d c : ℕ}
variable {width : Fin c → ℕ}

/-- Number each physical block once. Dual sites refer to the same block and
do not have a separate field variable. -/
def sharedSlot (i : Fin c) (v : Fin (width i)) : Fin (∑ j, width j) :=
  finSigmaFinEquiv ⟨i, v⟩

abbrev SharedField (F : ∀ i : Fin c, Fin (width i) → Type) (a : Fin (∑ j, width j)) :=
  F (finSigmaFinEquiv.symm a).1 (finSigmaFinEquiv.symm a).2

variable (F : ∀ i : Fin c, Fin (width i) → Type)
  [∀ i v, Field (F i v)] [∀ i v, Algebra K (F i v)]
variable (physical : Fin d → Fin c) (free : ∀ i, Fin (width i) → Bool)

instance sharedFieldField (v : Fin (∑ j, width j)) : Field (SharedField F v) :=
  inferInstanceAs (Field (F (finSigmaFinEquiv.symm v).1 (finSigmaFinEquiv.symm v).2))

instance sharedFieldAlgebra (v : Fin (∑ j, width j)) : Algebra K (SharedField F v) :=
  inferInstanceAs (Algebra K (F (finSigmaFinEquiv.symm v).1 (finSigmaFinEquiv.symm v).2))

def commonKey (i : Fin d) (v : Fin (width (physical i))) : Option (Fin (∑ j, width j)) :=
  if free (physical i) v then some (sharedSlot (physical i) v) else none

private def coordinateCast {p q : (i : Fin c) × Fin (width i)} (h : p = q) :
    F p.1 p.2 →ₐ[K] F q.1 q.2 := by
  subst q
  exact AlgHom.id K _

private def sharedLinkAt (i : Fin c) (v : Fin (width i)) (b : Bool) :
    withBase (K := K) (SharedField F) (if b then some (sharedSlot i v) else none) →ₐ[K] F i v :=
  match b with
  | true => coordinateCast F (finSigmaFinEquiv.symm_apply_apply ⟨i, v⟩)
  | false => Algebra.ofId K _

def sharedLink (i : Fin d) (v : Fin (width (physical i))) :
    withBase (K := K) (SharedField F) (commonKey physical free i v) →ₐ[K] F (physical i) v :=
  sharedLinkAt F (physical i) v (free (physical i) v)
theorem commonKey_same (i j : Fin d) (h : physical i = physical j)
    (v : Fin (width (physical i))) (w : Fin (width (physical j)))
    (hw : Fin.cast (congrArg width h) v = w) :
    commonKey physical free i v = commonKey physical free j w := by
  have e : (⟨physical i, v⟩ : (a : Fin c) × Fin (width a)) = ⟨physical j, w⟩ := by
    apply Sigma.ext h
    apply (Fin.heq_ext_iff (congrArg width h)).mpr
    exact congrArg Fin.val hw
  exact congrArg (fun p : (a : Fin c) × Fin (width a) =>
    if free p.1 p.2 then some (sharedSlot p.1 p.2) else none) e

theorem sharedUnits_pinned (physical : Fin (d + 2) → Fin c) (sign : Fin (d + 2) → Bool)
    (x : ∀ a, (SharedField F a)ˣ) (i : Fin (d + 2)) (v : Fin (width (physical i)))
    (hFree : free (physical i) v = false) :
    sharedUnits (K := K) (SharedField F) (commonKey physical free) (sharedLink (K := K) F physical free)
      (fun j _ => sign j) x i v = 1 := by
  unfold sharedUnits
  have hk : commonKey physical free i v = none := by simp [commonKey, hFree]
  have hp (z : Option (Fin (∑ j, width j))) (h : z = none) :
      pinBase (K := K) (SharedField F) x z = 1 := by
    subst z
    rfl
  dsimp only
  rw [hp _ hk, inv_one, ite_self, map_one]

#print axioms commonKey_same
#print axioms sharedUnits_pinned

def collectSharedUnits (a : ∀ i v, (F i v)ˣ) :
    ∀ k : Fin (∑ j, width j), (SharedField F k)ˣ :=
  fun k => a (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2

private theorem coordinateCast_unit (a : ∀ i v, (F i v)ˣ)
    {p q : (i : Fin c) × Fin (width i)} (h : p = q) :
    Units.map (coordinateCast (K := K) F h).toRingHom.toMonoidHom (a p.1 p.2) = a q.1 q.2 := by
  subst q
  apply Units.ext
  rfl

theorem sharedUnits_free (physical : Fin (d + 2) → Fin c) (sign : Fin (d + 2) → Bool)
    (a : ∀ i v, (F i v)ˣ) (i : Fin (d + 2)) (v : Fin (width (physical i)))
    (hf : free (physical i) v = true) :
    sharedUnits (K := K) (SharedField F) (commonKey physical free) (sharedLink (K := K) F physical free)
      (fun j _ => sign j) (collectSharedUnits F a) i v =
        if sign i then (a (physical i) v)⁻¹ else a (physical i) v := by
  have h (p : Fin c) (v : Fin (width p)) (b z : Bool) (hb : b = true) :
      let q := if b then some (sharedSlot p v) else none
      let x := pinBase (K := K) (SharedField F) (collectSharedUnits F a) q
      Units.map (sharedLinkAt (K := K) F p v b).toRingHom.toMonoidHom
        (if z then x⁻¹ else x) = if z then (a p v)⁻¹ else a p v := by
    subst b
    cases z
    · exact coordinateCast_unit F a (finSigmaFinEquiv.symm_apply_apply ⟨p,v⟩)
    · simp only [Bool.true_eq, if_true, map_inv]
      exact congrArg Inv.inv (coordinateCast_unit F a (finSigmaFinEquiv.symm_apply_apply ⟨p,v⟩))
  exact h (physical i) v (free (physical i) v) (sign i) hf

#print axioms sharedUnits_free
end EvenTI.CellPreparation
