import EvenP15ScalarProbeReset
import EvenP15ScalarProbeCheck
import EvenP15ScalarProbeSuffix

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option maxRecDepth 48000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

private def scalarProbeActive : Cond := .eq (.var crtActive) (.lit 1)
private def finishScalarProbe : Com := .ite scalarProbeActive recoverRemainingCoordinates .skip

def runScalarKernelProbe : Com :=
  .seq resetScalarProbeBank (.seq installKernelProbePrefix
    (.seq checkScalarProbeFeasibility finishScalarProbe))

def runScalarKernelProbeCost (M m n : ℕ) : ℕ :=
  resetScalarProbeCost m n+(64*n+8)+checkScalarProbeCost M m n+
    (recoverRoundCost M m n+54)*n+10

/-- Starting with the immutable incidence bank, recover any genuine
completion of a homogeneous prefix. Every step uses the same-sized CRT
workspace. A previous probe can leave arbitrary canonical constraints. -/
theorem runScalarKernelProbe_run {M W m n : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCap : (s.arrs constraintMatrix).length < W) (hRhs : (s.arrs crtRhsBank).length = m+n)
    (hIndex : s.vars probeIndex = i.val) (hValue : s.vars probeValue = a.val) :
    let A := incidenceMatrix M src
    let C := fixedCoordinateMatrix A (i.val+1)
    let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M) (Function.update 0 i a) (i.val+1)
    ∃ t, Run W runScalarKernelProbe s t (runScalarKernelProbeCost M m n) ∧
      Frame runScalarKernelProbe s t ∧ RecoveryLayout M m n t ∧
      Canonical M (t.arrs constraintMatrix) ∧ t.vars crtActive ≤ 1 ∧
      (t.vars crtActive = 1 ↔ ∃ x, C.mulVec x = rhs) ∧
      (t.vars crtActive = 1 → ∃ x, C.mulVec x = rhs ∧
        ∀ j, (t.arrs coordinateBank).getD j.val 0 = (x j).val) := by
  let A := incidenceMatrix M src
  let p := i.val+1
  let f := Function.update (0 : Fin n → ZMod M) i a
  let C := fixedCoordinateMatrix A p
  let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M) f p
  have hp : p ≤ n := Nat.succ_le_of_lt i.isLt
  have hN : M < W := by
    have hStrong : M ≤ 4*M*M+4*M+10 := by omega
    omega
  obtain ⟨u,r0,f0,hu,huData,huSlot⟩ :=
    resetScalarProbeBank_run src (by omega) hRows hL hs hSrc hCanonical hCap hRhs
  have huIndex : u.vars probeIndex = i.val := (f0.vars _ (by decide)).trans hIndex
  have huVal : u.vars probeValue = a.val := (f0.vars _ (by decide)).trans hValue
  obtain ⟨v,r1,hv,_,hvData,hvPrefix⟩ := installKernelProbePrefix_run (W:=W) A i a (by omega) (by omega)
    hu huData huSlot huIndex huVal
  have hvIndex : v.vars probeIndex = i.val :=
    ((Frame.of_run r1).vars _ (by decide)).trans huIndex
  obtain ⟨w,r2,f2,hw,hwData,hwPrefix,hwSlot,hwBit,hwFeasible⟩ :=
    checkScalarProbeFeasibility_run A i a hW hL hv hvData hvPrefix hvIndex
  have h1 : 1 < W := by omega
  have hB1 := Nat.mul_le_mul_left 64 hp
  have hB2 := Nat.mul_le_mul_left (recoverRoundCost M m n+54) (Nat.sub_le n p)
  by_cases hActive : w.vars crtActive = 1
  · have hExists : ∃ x, C.mulVec x = rhs := hwFeasible.mp hActive
    obtain ⟨x,hx,hxSound⟩ := probeSuffix_feasible A (0 : Fin m → ZMod M) f hExists
    obtain ⟨t,r3,ht,_,_,hOut⟩ := recoverRemainingCoordinates_run A (0 : Fin m → ZMod M) f hW hL
      hw hp hwSlot hActive hwData hwPrefix
    have hTrue : scalarProbeActive.evalB W w = some true :=
      evalB_condEq (ev_var hActive h1) (evalB_lit h1)
    have r4 : Run W finishScalarProbe w t ((recoverRoundCost M m n+54)*(n-p)+8) :=
      (Run.ite_true (d:=.skip) hTrue r3).mono (by
        simp [scalarProbeActive,Cond.size,Expr.size] <;> omega)
    have r : Run W runScalarKernelProbe s t (runScalarKernelProbeCost M m n) :=
      (r0.seq (r1.seq (r2.seq r4))).mono (by
        unfold runScalarKernelProbeCost
        change resetScalarProbeCost m n+((64*p+8)+
          (checkScalarProbeCost M m n+((recoverRoundCost M m n+54)*(n-p)+8)))
          ≤ _
        omega)
    rw [hx] at hOut
    exact ⟨t,r,Frame.of_run r,ht,hOut.2.2,by omega,
      ⟨fun _ => hExists,fun _ => hOut.1⟩,fun _ => ⟨x,hxSound,hOut.2.1⟩⟩
  · have hZero : w.vars crtActive = 0 := by omega
    have hFalse : scalarProbeActive.evalB W w = some false :=
      evalB_condEq (ev_var hZero (by omega)) (evalB_lit (n:=1) h1)
    have r4 : Run W finishScalarProbe w w 5 := Run.ite_false (c:=recoverRemainingCoordinates) hFalse Run.skip
    have r : Run W runScalarKernelProbe s w (runScalarKernelProbeCost M m n) :=
      (r0.seq (r1.seq (r2.seq r4))).mono (by
        unfold runScalarKernelProbeCost
        change resetScalarProbeCost m n+((64*p+8)+(checkScalarProbeCost M m n+5)) ≤ _
        omega)
    exact ⟨w,r,Frame.of_run r,hw,hwData.canonical,hwBit,hwFeasible,
      fun h => False.elim (hActive h)⟩

/-- The full RAM probe from signed incidence words has a polynomial
execution bound in the field bit-width and live row and column counts. -/
theorem runScalarKernelProbeCost_le (M m n : ℕ) :
    runScalarKernelProbeCost M m n ≤
      1700000*(Nat.size M+m+n+2)^5 := by
  let X := Nat.size M+m+n+2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hmn : m+n+1 ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hm : m ≤ X := by dsimp [X]; omega
  have hS := (smithRecoverAndCommitCost_le M (m+n) n).trans
    (Nat.mul_le_mul_left 52000 (Nat.pow_le_pow_left
      (show Nat.size M+(m+n)+n+2 ≤ 2*X by dsimp [X]; omega) 4))
  rw [show 52000*(2*X)^4=832000*X^4 by ring] at hS
  have hT : (m+n+1)*n ≤ X^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hmn hn
  have h24 : X^2 ≤ X^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h25 : X^2 ≤ X^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h45 : X^4 ≤ X^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h14 : 1 ≤ X^4 := one_le_pow₀ hx
  have h15 : 1 ≤ X^5 := one_le_pow₀ hx
  have hX5 : X ≤ X^5 := by
    simpa using Nat.pow_le_pow_right hx (show 1 ≤ 5 by decide)
  have hRound : recoverRoundCost M m n+54 ≤ 832104*X^4 := by
    unfold recoverRoundCost
    omega
  have hLoop := Nat.mul_le_mul hRound hn
  rw [show 832104*X^4*X = 832104*X^5 by ring] at hLoop
  have hCheck : checkScalarProbeCost M m n ≤ 832104*X^4 := by
    unfold checkScalarProbeCost
    omega
  have hReset : resetScalarProbeCost m n ≤ 225*X^5 := by
    unfold resetScalarProbeCost buildIncidenceCost
    omega
  change runScalarKernelProbeCost M m n ≤ 1700000*X^5
  unfold runScalarKernelProbeCost
  omega

#print axioms runScalarKernelProbeCost_le

#print axioms runScalarKernelProbe_run
end EvenTI.P15Scalar