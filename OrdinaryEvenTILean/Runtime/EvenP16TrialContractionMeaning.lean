import EvenP15TrialAnchorProduct
import EvenP16TrialCrossShuffle

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace EvenTI.P16Trial

open EvenTI.TrialProducer EvenTI.P15Trial Matrix
open scoped Matrix

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def literalProjectionProduct {l r m k : ℕ}
    (A : Matrix I J K) (L : (I → K) →ₗ[K] Matrix (Fin l) (Fin l) K)
    (R : (J → K) →ₗ[K] Matrix (Fin r) (Fin r) K) (eI : Fin m ≃ I) (eJ : Fin k ≃ J) :
    Matrix (Fin (l*l)) (Fin (r*r)) K :=
  (projectionCoefficients L).submatrix finProdFinEquiv.symm eI *
    ((A.submatrix eI eJ) * (((projectionCoefficients R)ᵀ).submatrix eJ finProdFinEquiv.symm))

private theorem productEntry {l r m k : ℕ}
    (A : Matrix I J K) (L : (I → K) →ₗ[K] Matrix (Fin l) (Fin l) K)
    (R : (J → K) →ₗ[K] Matrix (Fin r) (Fin r) K) (eI : Fin m ≃ I) (eJ : Fin k ≃ J)
    (u u' : Fin l) (v v' : Fin r) :
    literalProjectionProduct A L R eI eJ (finProdFinEquiv (u,u')) (finProdFinEquiv (v,v')) =
      coordinateProjection L R A (u,v) (u',v') := by
  unfold literalProjectionProduct
  rw [submatrix_mul_equiv,submatrix_mul_equiv]
  simp only [submatrix_apply,Equiv.symm_apply_apply]
  exact (coordinateProjection_eq_rectangular L R A u u' v v').symm

private theorem pair_quot {l r : ℕ} (x : Fin l) (y : Fin r) :
    (x.val*r+y.val)/r=x.val := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt y.isLt),
    Nat.div_eq_of_lt y.isLt,zero_add]

private theorem pair_rem {l r : ℕ} (x : Fin l) (y : Fin r) :
    (x.val*r+y.val)%r=y.val := by
  simp [Nat.add_mod,Nat.mod_eq_of_lt y.isLt]

private theorem pair_lt {l r : ℕ} (x : Fin l) (y : Fin r) :
    x.val*r+y.val < l*r := by
  have h := Mathproof.P15RecogIMPGrid20261007.out_lt (o0 := 0) x.isLt y.isLt
  simpa only [Nat.zero_add] using h

/-- The paid product and shuffle have the exact tensor-contraction semantics,
independently of how the coefficient banks and input coordinate maps arose. -/
theorem nativeProjectionContraction_meaning {l r m k : ℕ}
    (A : Matrix I J K) (L : (I → K) →ₗ[K] Matrix (Fin l) (Fin l) K)
    (R : (J → K) →ₗ[K] Matrix (Fin r) (Fin r) K) (eI : Fin m ≃ I) (eJ : Fin k ≃ J)
    (read out : ℕ → K)
    (hProduct : ∀ (x : Fin (l*l)) (y : Fin (r*r)),
      read (x.val*(r*r)+y.val)=literalProjectionProduct A L R eI eJ x y)
    (hShuffle : ∀ x < l*r, ∀ y < l*r,
      out (x*(l*r)+y)=read (crossShuffleIndex 0 l r x y)) :
    ∀ (u u' : Fin l) (v v' : Fin r),
      out ((u.val*r+v.val)*(l*r)+(u'.val*r+v'.val)) =
        coordinateProjection L R A (u,v) (u',v') := by
  intro u u' v v'
  rw [hShuffle _ (pair_lt u v) _ (pair_lt u' v'),crossShuffleIndex,Nat.zero_add,
    pair_quot u v,pair_quot u' v',pair_rem u v,pair_rem u' v']
  have h : read ((u.val*l+u'.val)*(r*r)+(v.val*r+v'.val)) =
      literalProjectionProduct A L R eI eJ (finProdFinEquiv (u,u')) (finProdFinEquiv (v,v')) := by
    simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using hProduct (finProdFinEquiv (u,u')) (finProdFinEquiv (v,v'))
  exact h.trans (productEntry A L R eI eJ u u' v v')

#print axioms nativeProjectionContraction_meaning
end EvenTI.P16Trial