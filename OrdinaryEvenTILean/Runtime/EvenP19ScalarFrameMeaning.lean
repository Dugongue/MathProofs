import EvenP18ScalarChartMeaning

set_option autoImplicit false
set_option maxHeartbeats 180000

namespace EvenTI.P19Scalar

open scoped Matrix
open Matrix

variable {K : Type} [Field K] {I : Type} {r p : ℕ}

/-- Exact residue congruences imply the required right eigenaction on every
supported row. This works for full primary powers, without squarefreeness or
splitting the base field. The residue condition is an ordinary polynomial
congruence, not an assumed eigenbasis. -/
theorem supported_eigen_of_polynomial_residue
    (S X : Matrix (Fin r) (Fin r) K) (f g : Polynomial K) (a : K)
    (hSupport : X*Polynomial.aeval S f=0)
    (hResidue : f ∣ g-Polynomial.C a) :
    X*Polynomial.aeval S g=a • X := by
  obtain ⟨h,hh⟩ := hResidue
  have hg : g=Polynomial.C a+f*h := by rw [← hh]; ring
  rw [hg,map_add,map_mul,Matrix.mul_add,← Matrix.mul_assoc,hSupport,
    Matrix.zero_mul,add_zero]
  simp only [Polynomial.aeval_C,Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul,Matrix.mul_one]
/-- A supported-centralizer spanning family replaces an inverse eigenbasis.
Every rectangular restriction is allowed, including the padded order-four case.
No simultaneous diagonalization or chosen left inverse of the family is needed. -/
theorem scalarCrop_iff_supportedFrame
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (N : Matrix (Fin r) (Fin r) K) (X : I → Matrix (Fin r) (Fin r) K)
    (eigenvalue : I → K) (a : K)
    (hLeft : Q*P=1) (hInvariant : N*P=P*(Q*N*P))
    (hSpan : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hEigen : ∀ i, X i*N=eigenvalue i • X i) :
    Q*N*P=a • (1 : Matrix (Fin p) (Fin p) K) ↔
      ∀ i, X i*P ≠ 0 → eigenvalue i=a := by
  classical
  constructor
  · intro hCrop i hNonzero
    have hNP : N*P=a • P := by
      rw [hInvariant,hCrop,Matrix.mul_smul,Matrix.mul_one]
    have heq : eigenvalue i • (X i*P)=a • (X i*P) := by
      calc
        eigenvalue i • (X i*P) = (X i*N)*P := by rw [hEigen,Matrix.smul_mul]
        _ = X i*(N*P) := Matrix.mul_assoc _ _ _
        _ = a • (X i*P) := by rw [hNP,Matrix.mul_smul]
    have hEntry : ∃ u v, (X i*P) u v ≠ 0 := by
      by_contra hh
      push_neg at hh
      apply hNonzero
      ext u v
      exact hh u v
    obtain ⟨u,v,hv⟩ := hEntry
    have hh := congrFun (congrFun heq u) v
    exact mul_right_cancel₀ hv (by simpa only [Matrix.smul_apply,smul_eq_mul] using hh)
  · intro hScalars
    let V : Submodule K (Matrix (Fin r) (Fin r) K) :=
      { carrier := {Z | Z*(N*P)=a • (Z*P)}
        zero_mem' := by simp
        add_mem' := by
          intro A B hA hB
          change (A+B)*(N*P)=a • ((A+B)*P)
          rw [Matrix.add_mul,Matrix.add_mul,hA,hB,smul_add]
        smul_mem' := by
          intro c A hA
          change (c • A)*(N*P)=a • ((c • A)*P)
          rw [Matrix.smul_mul,Matrix.smul_mul,hA,smul_comm c a] }
    have hGenerators : Submodule.span K (Set.range X) ≤ V := by
      apply Submodule.span_le.mpr
      rintro Z ⟨i,rfl⟩
      change X i*(N*P)=a • (X i*P)
      rw [← Matrix.mul_assoc,hEigen,Matrix.smul_mul]
      by_cases hZero : X i*P=0
      · rw [hZero]; simp
      · rw [hScalars i hZero]
    have hOne := hGenerators hSpan
    change (1 : Matrix (Fin r) (Fin r) K)*(N*P)=a • ((1 : Matrix (Fin r) (Fin r) K)*P) at hOne
    have hNP : N*P=a • P := by simpa only [Matrix.one_mul] using hOne
    calc
      Q*N*P = Q*(N*P) := Matrix.mul_assoc _ _ _
      _ = a • (Q*P) := by rw [hNP,Matrix.mul_smul]
      _ = a • (1 : Matrix (Fin p) (Fin p) K) := by rw [hLeft]

/-- The capped base-unit CRT words can be consumed directly through a
supported-centralizer frame; constructing each candidate action is unnecessary. -/
theorem scalarCrop_iff_supportedFrameWords [Fintype K] [DecidableEq K]
    (P : Matrix (Fin r) (Fin p) K) (Q : Matrix (Fin p) (Fin r) K)
    (N : Matrix (Fin r) (Fin r) K) (X : I → Matrix (Fin r) (Fin r) K)
    (L : EvenTI.Part8.BaseUnitLog K) {c : ℕ} (site : I → Fin c)
    (x : Fin c → ZMod (Fintype.card K-1)) (reference : I)
    (hRef : X reference*P ≠ 0)
    (hLeft : Q*P=1) (hInvariant : N*P=P*(Q*N*P))
    (hSpan : (1 : Matrix (Fin r) (Fin r) K) ∈ Submodule.span K (Set.range X))
    (hEigen : ∀ i, X i*N=(L.decode (x (site i)) : K) • X i) :
    (∃ a : K, Q*N*P=a • (1 : Matrix (Fin p) (Fin p) K)) ↔
      ∀ i, X i*P ≠ 0 → (x (site i)).val=(x (site reference)).val := by
  letI : NeZero (Fintype.card K-1) :=
    ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩
  have hDecode : Function.Injective (fun z : ZMod (Fintype.card K-1) =>
      (L.decode z : K)) := by
    intro u v huv
    have he : L.decode u=L.decode v := Units.ext huv
    have hz := L.mulEquiv.injective he
    exact congrArg Multiplicative.toAdd hz
  constructor
  · rintro ⟨a,ha⟩ i hi
    have hAll := (scalarCrop_iff_supportedFrame P Q N X
      (fun i => (L.decode (x (site i)) : K)) a hLeft hInvariant hSpan hEigen).mp ha
    exact congrArg ZMod.val (hDecode ((hAll i hi).trans (hAll reference hRef).symm))
  · intro h
    refine ⟨(L.decode (x (site reference)) : K),?_⟩
    apply (scalarCrop_iff_supportedFrame P Q N X
      (fun i => (L.decode (x (site i)) : K))
      (L.decode (x (site reference)) : K) hLeft hInvariant hSpan hEigen).mpr
    intro i hi
    exact congrArg (fun z => (L.decode z : K)) (ZMod.val_injective _ (h i hi))

#print axioms supported_eigen_of_polynomial_residue
#print axioms scalarCrop_iff_supportedFrameWords
#print axioms scalarCrop_iff_supportedFrame
end EvenTI.P19Scalar