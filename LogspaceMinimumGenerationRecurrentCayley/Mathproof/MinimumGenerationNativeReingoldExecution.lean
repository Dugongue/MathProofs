import Mathproof.MinimumGenerationNativeReingoldCayley
import Complexity.Computability.USTCON.SpaceKernel

namespace Mathproof.MinimumGeneration.NativeReingoldCayley

open Cslib.Complexity Turing.MultiTapeTM

/-- A native binary Reingold machine on the exact USTCON input encoding. -/
theorem nativeBinaryCertificate : NativeCertificate := by
  obtain ⟨time, C, h⟩ := Cslib.USTCON.nativeComputableInBigO_decide
  refine ⟨fun I => C * (time I + 1), 2 * C, h.mono (fun _ => le_rfl) ?_⟩
  intro I
  change C * (Nat.log2 (encUSTCON I).length + 1 + 1) ≤
    (2 * C) * (Nat.log2 (encUSTCON I).length + 1)
  rw [Nat.mul_comm 2 C, Nat.mul_assoc]
  exact Nat.mul_le_mul_left C (by omega)

/-- An actual finite binary machine with the single literal answer bit. -/
theorem nativeEncodedRun : ∃ M C, EncodedRunCertificate M C :=
  liftEncodedRun nativeBinaryCertificate

/-- The native Reingold binary machine decides all three Cayley graph queries
with logarithmic work space in the original input size and stores the decision
in one finite-control state of the callback controller. -/
theorem nativeCallbackCertificate : ∃ M C, CallbackCertificate M C :=
  liftCertificate nativeBinaryCertificate

end Mathproof.MinimumGeneration.NativeReingoldCayley
