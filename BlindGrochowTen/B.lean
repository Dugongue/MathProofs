import Mathlib

namespace BlindTenMatrix

section Certificates

variable {R : Type*} [CommRing R]
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The trace discrepancy is an explicit degree-two certificate in the unknown
transporter and inverse. The matrices being compared are constant. -/
theorem trace_certificate (X : Matrix m n R) (Y : Matrix n m R)
    (P : Matrix n n R) (Q : Matrix m m R) :
    Matrix.trace (Y * (X * P - Q * X)) +
      Matrix.trace ((1 - Y * X) * P) +
      Matrix.trace ((X * Y - 1) * Q) = Matrix.trace P - Matrix.trace Q := by
  have htrace : Matrix.trace (Y * (Q * X)) = Matrix.trace ((X * Y) * Q) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, ← Matrix.mul_assoc, htrace]
  abel

/-- If transported maps admit split image factorizations, their image dimensions
agree in the base ring. This version allows rectangular transporters and free
image modules of different ranks, and assumes intertwining in both directions. -/
theorem split_image_dimension {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix m n R) (Y : Matrix n m R)
    (I₁ : Matrix n a R) (L₁ : Matrix a n R) (S₁ : Matrix a n R) (T₁ : Matrix n a R)
    (I₂ : Matrix m b R) (L₂ : Matrix b m R) (S₂ : Matrix b m R) (T₂ : Matrix m b R)
    (left₁ : L₁ * I₁ = 1) (right₁ : S₁ * T₁ = 1)
    (left₂ : L₂ * I₂ = 1) (right₂ : S₂ * T₂ = 1)
    (hx : X * (I₁ * S₁) = (I₂ * S₂) * X)
    (hy : Y * (I₂ * S₂) = (I₁ * S₁) * Y)
    (hYX : Y * X = 1) (hXY : X * Y = 1) :
    (Fintype.card a : R) = (Fintype.card b : R) := by
  let U := S₂ * (X * T₁)
  let V := S₁ * (Y * T₂)
  have hu : X * I₁ = I₂ * U := by
    simpa only [Matrix.mul_assoc, right₁, Matrix.mul_one, U] using
      congrArg (· * T₁) hx
  have hv : Y * I₂ = I₁ * V := by
    simpa only [Matrix.mul_assoc, right₂, Matrix.mul_one, V] using
      congrArg (· * T₂) hy
  have hVU : V * U = 1 := by
    have h : I₁ * (V * U) = I₁ := by
      calc
        I₁ * (V * U) = Y * (X * I₁) := by rw [← Matrix.mul_assoc, ← hv, Matrix.mul_assoc, ← hu]
        _ = I₁ := by rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
    simpa only [← Matrix.mul_assoc, left₁, Matrix.one_mul] using
      congrArg (L₁ * ·) h
  have hUV : U * V = 1 := by
    have h : I₂ * (U * V) = I₂ := by
      calc
        I₂ * (U * V) = X * (Y * I₂) := by rw [← Matrix.mul_assoc, ← hu, Matrix.mul_assoc, ← hv]
        _ = I₂ := by rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
    simpa only [← Matrix.mul_assoc, left₂, Matrix.one_mul] using
      congrArg (L₂ * ·) h
  simpa only [hVU, hUV, Matrix.trace_one] using Matrix.trace_mul_comm V U

end Certificates

section Cyclic

open Module

variable {K V W A I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Evaluate a generator word by acting with its letters from right to left. -/
def word {M : Type*} [AddCommGroup M] [Module K M]
    (S : A → M →ₗ[K] M) (w : List A) (x : M) : M :=
  w.foldr (fun a y => S a y) x

/-- A common set of words furnishing bases at two cyclic vectors reduces pointed
simultaneous conjugacy to equality of all the one-letter transition coordinates.
The pointed transporter, when it exists, is unique. -/
theorem pointed_conjugacy_from_word_coordinates
    (S : A → V →ₗ[K] V) (T : A → W →ₗ[K] W) (v : V) (w : W)
    (words : I → List A) (b : Basis I K V) (c : Basis I K W)
    (hb : ∀ i, b i = word S (words i) v) (hc : ∀ i, c i = word T (words i) w)
    (i₀ : I) (hi₀ : words i₀ = []) :
    (∃! E : V ≃ₗ[K] W, E v = w ∧
      ∀ a x, E (S a x) = T a (E x)) ↔
      ∀ a i, b.repr (S a (b i)) = c.repr (T a (c i)) := by
  let E := b.equiv c (Equiv.refl I)
  have he (i) : E (b i) = c i := by simp [E, Basis.equiv_apply]
  have hcoords (x : V) : c.repr (E x) = b.repr x := by
    simp [E, Basis.equiv]
  have hu (F : V ≃ₗ[K] W) (hF : F v = w ∧ ∀ a x, F (S a x) = T a (F x)) :
      F = E := by
    have hw (u : List A) : F (word S u v) = word T u w := by
      induction u with
      | nil => exact hF.1
      | cons a u ih =>
        change F (S a (word S u v)) = T a (word T u w)
        rw [hF.2, ih]
    apply b.ext'
    intro i
    rw [he, hb i, hc i, hw]
  constructor
  · intro ⟨F, hF, _⟩ a i
    have hf := hF.2 a (b i)
    rw [hu F hF, he] at hf
    rw [← hf, hcoords]
  · intro H
    refine ⟨E, ⟨?_, ?_⟩, hu⟩
    · simpa only [hb i₀, hc i₀, hi₀, word, List.foldr_nil] using he i₀
    · intro a
      have hm : E.toLinearMap.comp (S a) = (T a).comp E.toLinearMap := by
        apply b.ext
        intro i
        change E (S a (b i)) = T a (E (b i))
        rw [he]
        exact c.repr.injective ((hcoords _).trans (H a i))
      intro x
      exact DFunLike.congr_fun hm x

end Cyclic

end BlindTenMatrix
