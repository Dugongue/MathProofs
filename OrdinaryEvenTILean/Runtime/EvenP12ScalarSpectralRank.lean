import EvenP11SpectralGate

namespace EvenTI.P12Scalar

open scoped BigOperators Matrix
open Matrix EvenTI.Action EvenTI.Contract EvenTI.TrialProducer
open Mathproof.EvenTI.GlobalCoverage Mathproof.EvenTI.Singular.Coverage
open Mathproof.EvenTI.OrderFour Mathproof.EvenTI.Reciprocal.Coverage

set_option autoImplicit false
set_option maxHeartbeats 550000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {a b s d n : ℕ}

private theorem cutUpdateLeft (x : Coord a n) (y : Coord b n) (p : Fin a) (j : Fin n) :
    Function.update (cutEquiv (x, y)) (p.castAdd b) j =
      cutEquiv (Function.update x p j, y) := by
  funext i
  refine Fin.addCases (fun u => ?_) (fun v => ?_) i
  · by_cases hu : u = p
    · subst u
      simp [cutEquiv, Fin.append_left]
    · have hu' : u.castAdd b ≠ p.castAdd b := by
        intro he
        apply hu
        exact Fin.ext (congrArg (fun w : Fin (a+b) => w.val) he)
      simp [cutEquiv, Fin.append_left, hu, hu']
  · have hv : v.natAdd a ≠ p.castAdd b := by
      intro he
      have h := congrArg Fin.val he
      change a + v.val = p.val at h
      have hp := p.isLt
      omega
    simp [cutEquiv, Fin.append_right, hv]

private theorem cutUpdateRight (x : Coord a n) (y : Coord b n) (p : Fin b) (j : Fin n) :
    Function.update (cutEquiv (x, y)) (p.natAdd a) j =
      cutEquiv (x, Function.update y p j) := by
  funext i
  refine Fin.addCases (fun u => ?_) (fun v => ?_) i
  · have hu : u.castAdd b ≠ p.natAdd a := by
      intro he
      have h := congrArg Fin.val he
      change u.val = a + p.val at h
      have hl := u.isLt
      omega
    simp [cutEquiv, Fin.append_left, hu]
  · by_cases hv : v = p
    · subst v
      simp [cutEquiv, Fin.append_right]
    · have hv' : v.natAdd a ≠ p.natAdd a := by
        intro he
        apply hv
        apply Fin.ext
        have h := congrArg Fin.val he
        change a + v.val = a + p.val at h
        omega
      simp [cutEquiv, Fin.append_right, hv, hv']

private theorem retainedModeUpdate (p : Fin (s+1)) (a b : Fin n) (u : Coord s n) :
    Function.update (retainedMode p (a,u)) p b = retainedMode p (b,u) := by
  change Function.update (Fin.insertNth (α := fun _ => Fin n) p a u) p b =
    Fin.insertNth (α := fun _ => Fin n) p b u
  exact Fin.update_insertNth (α := fun _ => Fin n) p a b u

private theorem retainedContract_update (T : Tensor K (d+1) n) (p : Fin (d+1))
    (c : Fin n → K) (hc : c ∈ ((retainedForm p T)ᵀ.mulVecLin).ker) (z : Coord (d+1) n) :
    ∑ j : Fin n, c j * T (Function.update z p j) = 0 := by
  have h := congrFun (LinearMap.mem_ker.mp hc) ((retainedMode p).symm z).2
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, transpose_apply,
    retainedForm, Pi.zero_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  symm
  apply congrArg T
  change p.insertNth j (p.removeNth z) = _
  exact Fin.insertNth_removeNth p j z

private theorem cutKernelLift {J : Type} [Fintype J] [DecidableEq J]
    (M : Matrix (Coord (s+1) n) J K) (p : Fin (s+1))
    (c : Fin n → K) (hc : c ≠ 0)
    (hzero : ∀ u : Coord s n, ∀ y : J,
      ∑ j : Fin n, c j * M (retainedMode p (j,u)) y = 0) :
    n^s ≤ Module.finrank K (Mᵀ.mulVecLin).ker := by
  classical
  let e : Fin n × Coord s n ≃ Coord (s+1) n := retainedMode p
  let S : (Coord s n → K) →ₗ[K] (Coord (s+1) n → K) :=
    { toFun := fun f x => c (e.symm x).1 * f (e.symm x).2
      map_add' := by intros; ext x; simp [mul_add]
      map_smul' := by intros; ext x; simp [mul_left_comm] }
  have hs f : S f ∈ (Mᵀ.mulVecLin).ker := by
    apply LinearMap.mem_ker.mpr
    funext y
    change (∑ x : Coord (s+1) n, M x y * (c (e.symm x).1 * f (e.symm x).2)) = 0
    rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro u _
    simp only [e.symm_apply_apply]
    calc
      (∑ j : Fin n, M (e (j,u)) y * (c j * f u)) =
          ∑ j : Fin n, (c j * M (e (j,u)) y) * f u := by
        apply Finset.sum_congr rfl
        intro j _
        ac_rfl
      _ = 0 := by rw [← Finset.sum_mul, hzero u y, zero_mul]
  let H := S.codRestrict _ hs
  have hS : Function.Injective H := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    intro f g he
    funext u
    have hx := congrFun (congrArg Subtype.val he) (e (j,u))
    change c (e.symm (e (j,u))).1 * f (e.symm (e (j,u))).2 =
      c (e.symm (e (j,u))).1 * g (e.symm (e (j,u))).2 at hx
    rw [e.symm_apply_apply] at hx
    exact mul_left_cancel₀ hj hx
  simpa [Module.finrank_fintype_fun_eq_card, cut_side_card] using
    LinearMap.finrank_le_finrank_of_injective hS

private theorem balancedKernelDims (T : Dense K s n) :
    Module.finrank K (leftCutKernel T).ker = Module.finrank K (rightCutKernel T).ker := by
  have hL : (flatten T).rank + Module.finrank K (leftCutKernel T).ker =
      Module.finrank K (Coord (s+1) n → K) := by
    rw [← Matrix.rank_transpose]
    exact (leftCutKernel T).finrank_range_add_finrank_ker
  have hR : (flatten T).rank + Module.finrank K (rightCutKernel T).ker =
      Module.finrank K (Coord (s+1) n → K) :=
    (rightCutKernel T).finrank_range_add_finrank_ker
  omega

/-- If the balanced-cut kernel has smaller dimension than the product of
one half's other physical modes, every one-mode flattening has full row rank. -/
theorem retainedFullRank_of_cutCorank (T : Dense K s n)
    (hSmall : Module.finrank K (rightCutKernel T).ker < n^s) :
    rawRetainedFullRank (l := (s+1)+s) T = true := by
  apply (rawRetainedFullRank_spec T).mpr
  intro i
  have hbot : ((retainedForm i T)ᵀ.mulVecLin).ker = ⊥ := by
    refine le_antisymm (fun c hc => ?_) bot_le
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨j0, _⟩ := Function.ne_iff.mp hne
    revert hc
    refine Fin.addCases
      (motive := fun pos : Fin ((s+1)+(s+1)) => c ∈ ((retainedForm pos T)ᵀ.mulVecLin).ker → False)
      (fun (p : Fin (s+1)) hc => ?_) (fun (p : Fin (s+1)) hc => ?_) i
    · have H : n^s ≤ Module.finrank K (leftCutKernel T).ker := by
        apply cutKernelLift (flatten T) p c hne
        intro u y
        have hz := retainedContract_update T (p.castAdd (s+1)) c hc
          (cutEquiv (l := s+1) (r := s+1) (retainedMode p (j0, u), y))
        simpa only [cutUpdateLeft, retainedModeUpdate, flatten] using hz
      rw [balancedKernelDims T] at H
      omega
    · have H : n^s ≤ Module.finrank K (rightCutKernel T).ker := by
        have hz : ∀ u : Coord s n, ∀ x : Coord (s+1) n,
            ∑ j : Fin n, c j * (flatten T)ᵀ (retainedMode p (j,u)) x = 0 := by
          intro u x
          have h := retainedContract_update T (p.natAdd (s+1)) c hc
            (cutEquiv (l := s+1) (r := s+1) (x, retainedMode p (j0, u)))
          simpa only [cutUpdateRight, retainedModeUpdate, transpose_apply, flatten] using h
        have h := cutKernelLift (flatten T)ᵀ p c hne hz
        exact h
      omega
  have h := ((retainedForm i T)ᵀ.mulVecLin).finrank_range_add_finrank_ker
  change (retainedForm i T)ᵀ.rank + Module.finrank K ((retainedForm i T)ᵀ.mulVecLin).ker =
    Module.finrank K (Fin n → K) at h
  rw [rank_transpose, hbot] at h
  simpa using h

private theorem rightKernelExact (T : Dense K s n) :
    (rightCutKernel T).ker = (exactKernels T).1 := by
  simp only [exactKernels, rightCutKernel, Matrix.toLin'_apply']

private theorem rightKernelUnit (T : Dense K s n) (h : IsUnit (flatten T)) :
    (rightCutKernel T).ker = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  rw [Submodule.mem_bot]
  by_contra hne
  have hz : (flatten T).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨v, hne, by simpa only [rightCutKernel, Matrix.mulVecLin_apply] using LinearMap.mem_ker.mp hv⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h).ne_zero hz

private theorem rightKernel_small_of_budget (T : Dense K s n) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (h : Fintype.card K ^ Module.finrank K (rightCutKernel T).ker ≤ n) :
    Module.finrank K (rightCutKernel T).ker < n^s := by
  have hcard : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h2 := Nat.lt_two_pow_self (n := Module.finrank K (rightCutKernel T).ker)
  have hq := Nat.pow_le_pow_left hcard (Module.finrank K (rightCutKernel T).ker)
  have hp : n ≤ n^s := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n) hs
  exact h2.trans_le (hq.trans (h.trans hp))

/-- Every source passing the existing spectral gate is already full-rank in
all physical modes. This removes a separate retained-rank machine from the
spectrally guarded recognizer. -/
theorem retainedFullRank_of_spectral (T : Dense K s n)
    (h : sourceSpectralAccepted T) :
    rawRetainedFullRank (l := (s+1)+s) T = true := by
  have hheader : (s = 1 ∧ 5 ≤ n) ∨ (2 ≤ s ∧ 1 ≤ n) := by
    rcases h with ⟨hd,hn,_⟩ | ⟨l,hl,hd,hn,_⟩
    · exact Or.inl ⟨by omega, hn⟩
    · exact Or.inr ⟨by omega, hn⟩
  apply retainedFullRank_of_cutCorank T
  rcases hheader with ⟨rfl, hn⟩ | ⟨hs, hn⟩
  · rcases (four_spectral_iff hn T).mp h with ⟨_,hl⟩ | ⟨hu,_⟩
    · apply rightKernel_small_of_budget T (by decide) (by omega)
      rw [rightKernelExact]
      rcases hl with ⟨_,_,_,_,_,_,hb,_⟩
      exact hb
    · rw [rightKernelUnit T hu]
      simpa using (show 0 < n by omega)
  · rcases (higher_spectral_iff hs hn T).mp h with ⟨_,hl⟩ | ⟨hu,_⟩
    · apply rightKernel_small_of_budget T (by omega) hn
      rw [rightKernelExact]
      rcases hl with ⟨k,A,hA,hb,_⟩
      have hker := A.property.1
      change (flatten A.val).toLin'.ker = k.1 at hker
      rw [hA] at hker
      rw [exactKernels, hker]
      exact hb
    · rw [rightKernelUnit T hu]
      simpa using (show 0 < n^s by positivity)

#print axioms retainedFullRank_of_cutCorank
#print axioms retainedFullRank_of_spectral

end EvenTI.P12Scalar
