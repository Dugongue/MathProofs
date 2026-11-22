import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

theorem mem_of_positive_pow_of_diagonal_stable
    {K ι : Type*} [Field K] [Finite ι]
    (W : Submodule K (ι → K)) (z : ι → K) (d : ℕ)
    (stable : ∀ x ∈ W, z * x ∈ W)
    (h : z ^ (d + 1) ∈ W) :
    z ∈ W := by
  classical
  let V : Submodule K (ι → K) :=
    { carrier := {x | x ∈ W ∧ ∀ i, z i = 0 → x i = 0}
      zero_mem' := ⟨W.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨hx, hxs⟩ ⟨hy, hys⟩
        exact ⟨W.add_mem hx hy, fun i hi => by simp [hxs i hi, hys i hi]⟩
      smul_mem' := by
        rintro a x ⟨hx, hxs⟩
        exact ⟨W.smul_mem a hx, fun i hi => by simp [hxs i hi]⟩ }
  let F : V →ₗ[K] V :=
    { toFun := fun x => ⟨z * (x : ι → K), stable _ x.property.1, by simp_all⟩
      map_add' := fun x y => Subtype.ext (by exact mul_add z _ _)
      map_smul' := fun a x => Subtype.ext (by
        change z * (a • (x : ι → K)) = a • (z * (x : ι → K))
        ext i
        simp [mul_left_comm]) }
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : z i = 0
    · exact (x.property.2 i hi).trans (y.property.2 i hi).symm
    · exact mul_left_cancel₀ hi (congrArg (fun t : V => (t : ι → K) i) hxy)
  have hs : Function.Surjective F := LinearMap.surjective_of_injective hinj
  have hstep (k : ℕ) (hp : z ^ (k + 1 + 1) ∈ V) : z ^ (k + 1) ∈ V := by
    obtain ⟨v, hv⟩ := hs ⟨_, hp⟩
    have he : (v : ι → K) = z ^ (k + 1) := by
      funext i
      by_cases hi : z i = 0
      · simpa [Pi.pow_apply, hi] using v.property.2 i hi
      · apply mul_left_cancel₀ hi
        have hh := congrArg (fun t : V => (t : ι → K) i) hv
        change z i * (v : ι → K) i = (z ^ (k + 1 + 1)) i at hh
        simpa [Pi.pow_apply, pow_succ'] using hh
    rw [← he]
    exact v.property
  have hV : z ^ (d + 1) ∈ V := ⟨h, fun i hi => by simp [Pi.pow_apply, hi]⟩
  have hbase : ∀ n : ℕ, z ^ (n + 1) ∈ V → z ∈ V := by
    intro n
    induction n with
    | zero => simpa
    | succ n ihn => exact fun hn => ihn (hstep n hn)
  exact (hbase d hV).1
