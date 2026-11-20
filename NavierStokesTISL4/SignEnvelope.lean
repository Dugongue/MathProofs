import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel

namespace HeldActionSignProfiles

/-- Inside a certified sign envelope, equality of residual probes suffices
    to correct one actual transporter to the requested sign. -/
theorem exact_sign_of_projection
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (corrections allowed : AddSubgroup G) (read : G →+ R)
    (found target reference : G)
    (hfound : found - reference ∈ allowed)
    (htarget : target - reference ∈ allowed)
    (hread : read found = read target)
    (hkernel : ∀ d ∈ allowed, read d = 0 → d ∈ corrections) :
    ∃ change ∈ corrections, found + change = target := by
  have hd : target - found ∈ allowed := by
    have h : (target - reference) - (found - reference) ∈ allowed :=
      allowed.sub_mem htarget hfound
    have heq : target - found = (target - reference) - (found - reference) := by
      abel
    rwa [heq]
  have hc : target - found ∈ corrections :=
    hkernel _ hd (by rw [map_sub, hread, sub_self])
  refine ⟨target - found, hc, ?_⟩
  abel

end HeldActionSignProfiles
