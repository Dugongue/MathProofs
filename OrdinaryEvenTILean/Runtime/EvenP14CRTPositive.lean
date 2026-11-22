import EvenP14CRTReference

set_option autoImplicit false

namespace EvenTI.P14Recovery

open EvenTI.P12Compare

/-- With at least one variable, successful coordinate recovery already
certifies the final equation. The reference verification is thus redundant
in positive dimension. The zero-column verification is a separate case. -/
theorem fixPaddedCoordinates_eq_recoverLinear {M m n : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (hn : 0 < n) :
    fixPaddedCoordinates A b (List.finRange n) 0 0 = recoverLinear A b := by
  rw [fixPaddedCoordinates_start]
  by_cases h : ∃ x, A.mulVec x = b
  · obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (recoverLinear_complete A b h)
    unfold recoverLinear at hx
    obtain ⟨y,hy,he⟩ := Option.bind_eq_some_iff.mp hx
    split at he
    · obtain rfl := Option.some.inj he
      rw [hy]
      exact hx.symm
    · contradiction
  · have hlist : List.finRange n ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp at hl
      omega
    obtain ⟨i,is,hi⟩ := List.exists_cons_of_ne_nil hlist
    have hzero : recoverCoordinate A b i = none := by
      cases hr : recoverCoordinate A b i with
      | none => rfl
      | some v =>
        obtain ⟨x,hx,_⟩ := recoverCoordinate_sound A b i hr
        exact (h ⟨x,hx⟩).elim
    unfold recoverLinear
    rw [hi,fixCoordinates,hzero]
    rfl

#print axioms fixPaddedCoordinates_eq_recoverLinear
end EvenTI.P14Recovery