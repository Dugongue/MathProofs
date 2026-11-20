import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness
import Mathproof.Meta.Problem18SubspaceCountNarrow20260929
import Mathproof.Meta.Problem18IrreducibleOperatorCard20260930

namespace Mathproof.Problem17PrimaryTail
open Module LinearMap Matrix Polynomial
noncomputable section

variable {K V W U : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup U] [Module K U]

def upper (A : End K W) (B : U →ₗ[K] W) (D : End K U) : End K (W × U) :=
  (A.comp (LinearMap.fst K W U) + B.comp (LinearMap.snd K W U)).prod
    (D.comp (LinearMap.snd K W U))

@[simp] theorem upper_apply (A : End K W) (B : U →ₗ[K] W) (D : End K U) (x : W × U) :
    upper A B D x = (A x.1 + B x.2, D x.2) := rfl

theorem upper_charpoly [FiniteDimensional K W] [FiniteDimensional K U]
    (A : End K W) (B : U →ₗ[K] W) (D : End K U) :
    (upper A B D).charpoly = A.charpoly * D.charpoly := by
  classical
  let b := Module.finBasis K W
  let c := Module.finBasis K U
  rw [← charpoly_toMatrix _ (b.prod c), ← charpoly_toMatrix A b, ← charpoly_toMatrix D c]
  have h : toMatrix (b.prod c) (b.prod c) (upper A B D) =
      Matrix.fromBlocks (toMatrix b b A) (toMatrix c b B) 0 (toMatrix c c D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, b, c, upper_apply]
  rw [h, Matrix.charpoly_fromBlocks_zero₂₁]

def firstBlock (T : End K (W × U)) : End K W :=
  (LinearMap.fst K W U).comp (T.comp (LinearMap.inl K W U))

def middleBlock (T : End K (W × U)) : U →ₗ[K] W :=
  (LinearMap.fst K W U).comp (T.comp (LinearMap.inr K W U))

def lastBlock (T : End K (W × U)) : End K U :=
  (LinearMap.snd K W U).comp (T.comp (LinearMap.inr K W U))

theorem eq_upper_of_invariant (T : End K (W × U)) (hT : ∀ x, (T (x, 0)).2 = 0) :
    upper (firstBlock T) (middleBlock T) (lastBlock T) = T := by
  apply LinearMap.ext
  intro x
  have h : T ((x.1, 0) + (0, x.2)) = T (x.1, 0) + T (0, x.2) := map_add T _ _
  have hx : ((x.1, 0) + (0, x.2) : W × U) = x := by ext <;> simp
  rw [hx] at h
  rw [h]
  apply Prod.ext <;> simp [firstBlock, middleBlock, lastBlock, hT]

/-- A fixed invariant summand contributes one freely chosen off-diagonal map. -/
def upperEquiv (P : End K W → Prop) (Q : End K U → Prop) :
    {T : End K (W × U) // (∀ x, (T (x, 0)).2 = 0) ∧ P (firstBlock T) ∧ Q (lastBlock T)}
      ≃ {A : End K W // P A} × (U →ₗ[K] W) × {D : End K U // Q D} := by
  have hA (A : End K W) (B : U →ₗ[K] W) (D : End K U) :
      firstBlock (upper A B D) = A := by ext; simp [firstBlock]
  have hB (A : End K W) (B : U →ₗ[K] W) (D : End K U) :
      middleBlock (upper A B D) = B := by ext; simp [middleBlock]
  have hD (A : End K W) (B : U →ₗ[K] W) (D : End K U) :
      lastBlock (upper A B D) = D := by ext; simp [lastBlock]
  refine {
    toFun := fun T => (⟨firstBlock T.val, T.property.2.1⟩,
      middleBlock T.val, ⟨lastBlock T.val, T.property.2.2⟩)
    invFun := fun z => ⟨upper z.1.val z.2.1 z.2.2.val, by
      refine ⟨fun x => ?_, ?_, ?_⟩
      · simp
      · rw [hA]; exact z.1.property
      · rw [hD]; exact z.2.2.property⟩
    left_inv := fun T => Subtype.ext (eq_upper_of_invariant T.val T.property.1)
    right_inv := ?_ }
  rintro ⟨⟨A, hPA⟩, B, ⟨D, hQD⟩⟩
  apply Prod.ext
  · exact Subtype.ext (hA A B D)
  · exact Prod.ext (hB A B D) (Subtype.ext (hD A B D))

def Preserves (T : End K V) (S : Submodule K V) : Prop :=
  ∀ x ∈ S, T x ∈ S

def quotientBlock (T : End K V) (S : Submodule K V) (h : Preserves T S) :
    End K (V ⧸ S) := S.mapQ S T h

theorem conjugated_first (T : End K V) (S C : Submodule K V) (hc : IsCompl S C)
    (h : Preserves T S) :
    firstBlock ((S.prodEquivOfIsCompl C hc).symm.conj T) = T.restrict h := by
  let e := S.prodEquivOfIsCompl C hc
  apply LinearMap.ext
  intro x
  have he (y : S) : e (y, 0) = y.val := by simp [e]
  have hy : e.symm (T x.val) = (⟨T x.val, h _ x.property⟩, 0) :=
    e.symm_apply_eq.mpr (he ⟨T x.val, h _ x.property⟩).symm
  change (e.symm (T (e (x, 0)))).1 = _
  rw [he, hy]
  rfl

theorem conjugated_invariant (T : End K V) (S C : Submodule K V) (hc : IsCompl S C)
    (h : Preserves T S) (x : S) : ((S.prodEquivOfIsCompl C hc).symm.conj T (x, 0)).2 = 0 := by
  let e := S.prodEquivOfIsCompl C hc
  have he (y : S) : e (y, 0) = y.val := by simp [e]
  have hy : e.symm (T x.val) = (⟨T x.val, h _ x.property⟩, 0) :=
    e.symm_apply_eq.mpr (he ⟨T x.val, h _ x.property⟩).symm
  change (e.symm (T (e (x, 0)))).2 = _
  rw [he, hy]

theorem conjugated_last (T : End K V) (S C : Submodule K V) (hc : IsCompl S C)
    (h : Preserves T S) :
    (S.quotientEquivOfIsCompl C hc).conj (quotientBlock T S h) =
      lastBlock ((S.prodEquivOfIsCompl C hc).symm.conj T) := by
  let e := S.prodEquivOfIsCompl C hc
  let q := S.quotientEquivOfIsCompl C hc
  apply LinearMap.ext
  intro x
  have he : e (0, x) = x.val := by simp [e]
  have hq (y : V) : q (S.mkQ y) = (e.symm y).2 := by
    obtain ⟨⟨u, v⟩, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply]
    change q (S.mkQ (u.val + v.val)) = v
    rw [map_add]
    have hu : S.mkQ u.val = 0 := (Submodule.Quotient.mk_eq_zero S).mpr u.property
    rw [hu, zero_add]
    exact Submodule.quotientEquivOfIsCompl_apply_mk_right hc v
  have hqx : q.symm x = S.mkQ x.val := by
    apply q.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (Submodule.quotientEquivOfIsCompl_apply_mk_right hc x).symm
  change q (quotientBlock T S h (q.symm x)) = (e.symm (T (e (0, x)))).2
  rw [he, hqx]
  have hh : quotientBlock T S h (S.mkQ x.val) = S.mkQ (T x.val) :=
    LinearMap.congr_fun (Submodule.mapQ_mkQ S S T (h := h)) x.val
  rw [hh, hq]

theorem invariant_charpoly_split [FiniteDimensional K V]
    (T : End K V) (S : Submodule K V) (h : Preserves T S) :
    T.charpoly = (T.restrict h).charpoly * (quotientBlock T S h).charpoly := by
  obtain ⟨C, hc⟩ := Submodule.exists_isCompl S
  let e := S.prodEquivOfIsCompl C hc
  let T' := e.symm.conj T
  have ht := eq_upper_of_invariant T' (conjugated_invariant T S C hc h)
  have ha := conjugated_first T S C hc h
  have hd := conjugated_last T S C hc h
  calc
    T.charpoly = T'.charpoly := (LinearEquiv.charpoly_conj _ _).symm
    _ = (upper (firstBlock T') (middleBlock T') (lastBlock T')).charpoly :=
      congrArg LinearMap.charpoly ht.symm
    _ = (firstBlock T').charpoly * (lastBlock T').charpoly := upper_charpoly _ _ _
    _ = _ := by rw [ha, ← hd, LinearEquiv.charpoly_conj]

def SplitPred (S : Submodule K V) (P : End K S → Prop)
    (Q : End K (V ⧸ S) → Prop) (T : End K V) : Prop :=
  ∃ h : Preserves T S, P (T.restrict h) ∧ Q (quotientBlock T S h)

theorem conjugated_invariant_iff (T : End K V) (S C : Submodule K V) (hc : IsCompl S C) :
    (∀ x, ((S.prodEquivOfIsCompl C hc).symm.conj T (x, 0)).2 = 0) ↔ Preserves T S := by
  refine ⟨?_, fun h => conjugated_invariant T S C hc h⟩
  intro h x hx
  let e := S.prodEquivOfIsCompl C hc
  have he : e (⟨x, hx⟩, 0) = x := by simp [e]
  specialize h ⟨x, hx⟩
  change (e.symm (T (e (⟨x, hx⟩, 0)))).2 = 0 at h
  rw [he] at h
  have h1 := e.apply_symm_apply (T x)
  have hs : e.symm (T x) = ((e.symm (T x)).1, 0) := Prod.ext rfl h
  rw [hs] at h1
  have h2 (y : S) : e (y, 0) = y.val := by simp [e]
  rw [h2] at h1
  rw [← h1]
  exact (e.symm (T x)).1.property

/-- Uniform coordinates for an arbitrary invariant subspace and its quotient. -/
def invariantSplitEquiv (S C : Submodule K V) (hc : IsCompl S C)
    (P : End K S → Prop) (Q : End K (V ⧸ S) → Prop) :
    {T : End K V // SplitPred S P Q T} ≃
      {A : End K S // P A} × (C →ₗ[K] S) × {D : End K (V ⧸ S) // Q D} := by
  let e := S.prodEquivOfIsCompl C hc
  let q := S.quotientEquivOfIsCompl C hc
  let Q' : End K C → Prop := fun D => Q (q.symm.conj D)
  have hQ (T : End K V) (h : Preserves T S) :
      q.symm.conj (lastBlock (e.symm.conj T)) = quotientBlock T S h := by
    rw [← conjugated_last T S C hc h]
    apply LinearMap.ext
    intro x
    simp [q]
  let e₁ := e.symm.conj.toEquiv.subtypeEquiv
    (p := SplitPred S P Q) (q := fun T =>
      (∀ x, (T (x, 0)).2 = 0) ∧ P (firstBlock T) ∧ Q' (lastBlock T))
    (fun T => by
      change SplitPred S P Q T ↔ (∀ x, (e.symm.conj T (x, 0)).2 = 0) ∧
        P (firstBlock (e.symm.conj T)) ∧ Q' (lastBlock (e.symm.conj T))
      constructor
      · rintro ⟨h, hp, hq⟩
        exact ⟨conjugated_invariant T S C hc h,
          (conjugated_first T S C hc h).symm ▸ hp, by dsimp [Q']; rwa [hQ T h]⟩
      · rintro ⟨hi, hp, hq⟩
        let h := (conjugated_invariant_iff T S C hc).mp hi
        refine ⟨h, (conjugated_first T S C hc h) ▸ hp, ?_⟩
        dsimp [Q'] at hq
        rwa [hQ T h] at hq)
  let e₃ : {D : End K C // Q' D} ≃ {D : End K (V ⧸ S) // Q D} :=
    q.symm.conj.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e₁.trans ((upperEquiv P Q').trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) e₃)))

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.upper_charpoly
#print axioms Mathproof.Problem17PrimaryTail.upperEquiv

#print axioms Mathproof.Problem17PrimaryTail.invariant_charpoly_split


#print axioms Mathproof.Problem17PrimaryTail.invariantSplitEquiv
