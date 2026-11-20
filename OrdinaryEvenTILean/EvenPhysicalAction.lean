import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace EvenTI.Action

abbrev Coord (d n : Nat) := Fin d → Fin n
abbrev Tensor (K : Type*) (d n : Nat) := Coord d n → K
abbrev Changes (K : Type*) [Field K] (d n : Nat) :=
  Fin d → (Matrix (Fin n) (Fin n) K)ˣ

variable {K : Type*} [Field K] {d n : Nat}

/-- Matrix of the product action, indexed by physical multi-indices. -/
def productMatrix (g : Changes K d n) : Matrix (Coord d n) (Coord d n) K :=
  fun x y => ∏ i, (g i).val (x i) (y i)

theorem productMatrix_one :
    productMatrix (1 : Changes K d n) = 1 := by
  ext x y
  simp only [productMatrix, Pi.one_apply, Units.val_one, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem productMatrix_mul (g h : Changes K d n) :
    productMatrix (g * h) = productMatrix g * productMatrix h := by
  ext x y
  simp only [productMatrix, Pi.mul_apply, Units.val_mul, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

def act (g : Changes K d n) (T : Tensor K d n) : Tensor K d n :=
  (productMatrix g).mulVec T

@[simp] theorem act_one (T : Tensor K d n) : act 1 T = T := by
  simp [act, productMatrix_one]

theorem act_mul (g h : Changes K d n) (T : Tensor K d n) :
    act (g * h) T = act g (act h T) := by
  rw [act, productMatrix_mul, ← Matrix.mulVec_mulVec]
  rfl

/-- Scalar units in the physical matrix group. -/
def scalar (u : Kˣ) : (Matrix (Fin n) (Fin n) K)ˣ :=
  Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom u

theorem scalar_val (u : Kˣ) :
    (scalar (n := n) u).val = (u : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  exact Algebra.algebraMap_eq_smul_one _

def scalars (u : Fin d → Kˣ) : Changes K d n := fun i => scalar (u i)

theorem productMatrix_scalars (u : Fin d → Kˣ) :
    productMatrix (scalars (n := n) u) =
      (∏ i, (u i : K)) • (1 : Matrix (Coord d n) (Coord d n) K) := by
  ext x y
  simp only [productMatrix, scalars, scalar_val, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib]
  congr 1
  exact congrFun (congrFun (productMatrix_one (K := K) (d := d) (n := n)) x) y

theorem act_scalars (u : Fin d → Kˣ) (T : Tensor K d n) :
    act (scalars u) T = (∏ i, (u i : K)) • T := by
  rw [act, productMatrix_scalars, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem scalars_fix_iff {T : Tensor K d n} (hT : T ≠ 0) (u : Fin d → Kˣ) :
    act (scalars u) T = T ↔ (∏ i, u i) = 1 := by
  rw [act_scalars]
  constructor
  · intro h
    obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := Function.ne_iff.mp hT
    have hv : (∏ i, (u i : K)) * T x = T x := congrFun h x
    have hf : (∏ i, (u i : K)) = 1 := by
      apply mul_right_cancel₀ hx
      simpa using hv
    apply Units.ext
    simpa using hf
  · intro h
    have hf : (∏ i, (u i : K)) = 1 := by
      simpa using congrArg (fun z : Kˣ => (z : K)) h
    rw [hf, one_smul]

theorem scalar_injective (hn : 0 < n) :
    Function.Injective (scalar (K := K) (n := n)) := by
  let i : Fin n := ⟨0, hn⟩
  intro u v h
  apply Units.ext
  have hv := congrArg (fun m : (Matrix (Fin n) (Fin n) K)ˣ => m.val i i) h
  simpa [scalar_val] using hv

/-- An explicit transporter identifies all filtered transporters with scalar
tuples of product one, once the raw source stabilizer has been certified. -/
noncomputable def filteredTransportEquiv (hn : 0 < n) {T S : Tensor K d n} (hT : T ≠ 0)
    (g : Changes K d n) (hg : act g T = S)
    (scalarOnly : ∀ a : Changes K d n, act a T = T → ∃ u, a = scalars u)
    (allowed : (Matrix (Fin n) (Fin n) K)ˣ → Fin d → Prop) :
    {u : Fin d → Kˣ // (∀ i, allowed (g i * scalar (u i)) i) ∧ (∏ i, u i) = 1} ≃
      {a : Changes K d n // (∀ i, allowed (a i) i) ∧ act a T = S} :=
  Equiv.ofBijective
    (fun u => ⟨g * scalars u.val, u.property.1, by
      rw [act_mul, (scalars_fix_iff hT _).mpr u.property.2, hg]⟩)
    ⟨fun u v h => Subtype.ext (funext fun i => scalar_injective hn
        (mul_left_cancel (congrFun (congrArg Subtype.val h) i))),
      fun a => by
        have ha : act (g⁻¹ * a.val) T = T := by
          rw [act_mul, a.property.2, ← hg, ← act_mul, inv_mul_cancel, act_one]
        obtain ⟨u, hu⟩ := scalarOnly _ ha
        have eqA : g * scalars u = a.val := by rw [← hu, ← mul_assoc, mul_inv_cancel, one_mul]
        have hfilter : ∀ i, allowed (g i * scalar (u i)) i := by
          intro i
          change allowed ((g * scalars u : Changes K d n) i) i
          rw [eqA]
          exact a.property.1 i
        exact ⟨⟨u, hfilter, (scalars_fix_iff hT u).mp (hu ▸ ha)⟩, Subtype.ext eqA⟩⟩

theorem det_scalar_mul (u : Kˣ) (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    ((g * scalar u).val).det = (u : K) ^ n * g.val.det := by
  simp [scalar_val]

#print axioms productMatrix_mul
#print axioms scalars_fix_iff
#print axioms filteredTransportEquiv
#print axioms det_scalar_mul

end EvenTI.Action
