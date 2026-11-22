import EvenP11RawKernelMachine
import EvenP11InputCoordOrder
import EvenP5KernelScan

namespace EvenTI.LiveSpectral

open EvenTI.Action EvenTI.Contract Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 Mathproof.P15RecogIMPProgram20261007
open Mathproof.P15DecideIMPKerBasis20261007 Mathproof.P15DecideIMPRowKer20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {d n AM OUT Z Sn B RB : ℕ}

theorem retainedRankCost_le (FP : FieldPresentation K) (hd : 1 ≤ d)
    (hn : 2 ≤ n) (L : Nat) (hL : n ^ (d + 1) ≤ L) :
    rkCost FP (n^d) n ≤ 34500 * (macroBudget FP * (6 * L)^5) := by
  have hn0 : 0 < n := by omega
  have hn_d : n ≤ n^d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hn0 hd
  have hnd : n^d ≤ n^(d+1) := Nat.pow_le_pow_right hn0 (by omega)
  have hp : 1 ≤ n^(d+1) := Nat.one_le_pow _ _ hn0
  have hnL : n ≤ L := hn_d.trans (hnd.trans hL)
  have hndL : n^d ≤ L := hnd.trans hL
  have hnn : n*n ≤ n^(d+1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ hn_d
  have hprod : n * (n^d + n) ≤ L + L := by
    rw [Nat.mul_add, ← pow_succ']
    exact Nat.add_le_add hL (hnn.trans hL)
  exact Mathproof.P15DecideIMPCost20261007.rkCost_le FP
    (show n * (n^d + n) + n^d + n + 2 ≤ 6 * L by omega)

/-- Run the physical rank test in the scalar recognizer's retained mode.
The incoming bank is the indicated transpose of the retained flattening.
The zero-kernel bit agrees with the exact native scan, independently of
the elimination basis or its coordinate order. -/
theorem paidRetainedRank_run (F : FieldEncoding K) (FP : FieldPresentation K)
    (T : Tensor K (d+1) n) (i : Fin (d+1))
    (hd : 1 ≤ d) (hn : 2 ≤ n) (L : Nat) (hL : n^(d+1) ≤ L)
    (layout : KBLay (n^d) n AM OUT Z Sn B) {σ : Env}
    (hS : Slots FP canonical qN.WS Sn B σ)
    (hR : σ.vars tNR = n^d) (hD : σ.vars tD = n) (hRBv : σ.vars tRB = RB)
    (hAM : σ.vars kAM = AM) (hOUT : σ.vars kOUT = OUT)
    (hZ : σ.vars dZ = Z) (hO : σ.vars rOs = Z + 1)
    (hT : σ.vars dT = Z + 2) (hU : σ.vars dU = Z + 3)
    (hws : σ.vars qN.WS = FP.e + 1)
    (hlo : (n + 1) * XBs (n^d) n ≤ RB) (hhi : RB + n^d * n ≤ AM)
    (hRows : ∀ (t : Fin (n^d)) (j : Fin n),
      val FP canonical qN.WS σ (RB + (t.val * n + j.val)) =
        (retainedForm i T).transpose ((inputCoordOrder n d).symm t) j)
    (hz : val FP canonical qN.WS σ Z = 0)
    (ho : val FP canonical qN.WS σ (Z + 1) = 1) :
    ∃ τ, Run B rkProg σ τ (34500 * (macroBudget FP * (6 * L)^5)) ∧
      Slots FP canonical qN.WS Sn B τ ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      (τ.vars kK = 0 ↔
        (rawKernelVectors (retainedForm i T).transpose (cutOrder d n) (Equiv.refl (Fin n))).isEmpty
          = true) := by
  obtain ⟨τ, hRun, hSlots, hDim, _, hIn, hOut⟩ :=
    physicalRawKernelForms_run FP F (retainedForm i T).transpose (inputCoordOrder n d)
      (Equiv.refl (Fin n)) 0 (fun _ => true) layout hS hR hD hRBv hAM hOUT hZ hO hT hU hws
      hlo hhi hRows hz ho
  refine ⟨τ, hRun.mono (retainedRankCost_le FP hd hn L hL), hSlots, hIn, hOut, ?_⟩
  rw [hDim, List.isEmpty_iff_length_eq_zero, rawKernelVectors_length]

#print axioms paidRetainedRank_run
end EvenTI.LiveSpectral
