import EvenP13SpectralAnchorBody
import Mathproof.Meta.Problem18P34Machine20261002Layout
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 6500000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Mathproof.IMPAuto20261004 Mathproof.Problem18IMPPolynomialCompiler20261001
open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Compare
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.Problem17RecognizerWorkspace (wordScale wordLimit reserve)
open Mathproof.Problem17RecognizerAllocation (width)
open Mathproof.P15FactorIMP20261007 (Snf)
open Mathproof.Problem17CharpolyExec (configCost fromBankFactor)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def anchorBinaryCode (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.read rawPairIO.limit) <| .seq rawPairLoad <|
  .seq (.assign anchorLength (.var rawPairIO.limit)) (anchorBody D F rawPairIO.array)

def anchorExtent (F : FieldPresentation K) (ws : List Nat) : String → Nat :=
  canonicalInitExt F (Snf (width (min (ws.headD 0) ws.length)))
    (fun name => if name = rawPairIO.array then ws.length else 0)

theorem OneAnchorLayout.enlarge {N B B' t : Nat} (h : OneAnchorLayout N B t) (hb : B ≤ B') :
    OneAnchorLayout N B' t :=
  ⟨h.low,h.high,h.word.trans_le hb,h.wide.trans_le hb,h.budget.trans_le hb,h.degree,h.minimum⟩

theorem anchorBinaryCode_run (D : FieldEncoding K) (F : FieldPresentation K) (ws : List Nat)
    {B C : Nat} (hLen : ws.length*ws.length+2 < B) (hWords : ∀ a ∈ ws, a < B)
    (hq : Fintype.card K < B) (hp : (F.p+1)^2 < B) (he : (F.p+1)^(F.e+1) < B)
    (hReady : ∀ t xs, ws = (t+1)::xs → xs.length = (t+1)*(t+1) →
      OneAnchorLayout (width (t+1)) B t ∧ width (t+1) < B ∧
      F.e+1+Snf (width (t+1))*F.e < B ∧ 16*(F.e+1) < B ∧ loadedAnchorCost F t ≤ C) :
    ∃ τ, Run B (anchorBinaryCode D F) (initEnv (anchorExtent F ws) (ws.length::ws)) τ
      (36*ws.length+C+100) ∧ τ.out = anchorWordResult D ws := by
  let σ := initEnv (anchorExtent F ws) (ws.length::ws)
  let σ₁ := {σ.setVar rawPairIO.limit ws.length with inp := ws}
  have r₁ : Run B (.read rawPairIO.limit) σ σ₁ 1 := Run.read rfl
  have hL : ws.length < B := (Nat.le_mul_self _).trans_lt (by omega)
  have hLenRaw : (σ₁.arrs rawPairIO.array).length = ws.length := by
    simp [σ₁,σ,initEnv,anchorExtent,canonicalInitExt,rawPairIO,canonical]
  obtain ⟨ρ,r₂,hRaw,hOther,hVars,_,hOut⟩ :=
    rawPairLoad_run ws [] (σ := σ₁) (by simp [σ₁]) rfl (by simp [σ₁]) hLenRaw hL hWords
  have hrL : ρ.vars rawPairIO.limit = ws.length := by
    rw [hVars _ (by decide) (by decide)]
    simp [σ₁]
  let ρ' := ρ.setVar anchorLength ws.length
  have er : (Expr.var rawPairIO.limit).evalB B ρ = some ws.length := by
    have h := evalB_var (B := B) (σ := ρ) (x := rawPairIO.limit) (by rwa [hrL])
    rw [hrL] at h
    exact h
  have r₃ : Run B (.assign anchorLength (.var rawPairIO.limit)) ρ ρ' 2 := Run.assign er
  have hReady' : ∀ t xs, ws = (t+1)::xs → xs.length = (t+1)*(t+1) →
      AnchorInputs F t B ρ' ∧ loadedAnchorCost F t ≤ C := by
    intro t xs hw hx
    obtain ⟨hFit,hWidth,hMemB,hScrB,hC⟩ := hReady t xs hw hx
    have hmin : min (ws.headD 0) ws.length = t+1 := by
      rw [hw]
      simp only [List.headD_cons,List.length_cons]
      exact min_eq_left ((Nat.le_mul_self (t+1)).trans (by omega))
    have hMem : ρ'.arrs canonical.mem = List.replicate (F.e+1+Snf (width (t+1))*F.e) 0 := by
      change ρ.arrs canonical.mem = _
      rw [hOther _ (by decide)]
      change List.replicate (anchorExtent F ws canonical.mem) 0 = _
      simp only [anchorExtent,canonicalInitExt,hmin,if_true]
    have hScr : (ρ'.arrs canonical.scratch).length = 16*(F.e+1) := by
      change (ρ.arrs canonical.scratch).length = _
      rw [hOther _ (by decide)]
      simp [ρ',σ₁,σ,initEnv,anchorExtent,canonicalInitExt,canonical]
    exact ⟨⟨hFit,hWidth,hMem,hScr,hMemB,hScrB⟩,hC⟩
  obtain ⟨τ,r₄,hτ⟩ := anchorBody_run D F rawPairIO.array ws (σ := ρ')
    (by decide) hRaw (by simp [ρ',vars_setVar]) hLen hWords hq hp he hReady'
  refine ⟨τ,(r₁.seq (r₂.seq (r₃.seq r₄))).mono (by omega),?_⟩
  rw [hτ,show ρ'.out = ρ.out from rfl,hOut]
  rfl

theorem anchorWordResult_turingPolytime (D : FieldEncoding K) (F : FieldPresentation K) :
    TuringPolytime (anchorWordResult D) := by
  let a : Polynomial Nat := (Polynomial.X+Polynomial.C (F.e+macroBudget F+12))^2
  let f : Nat := Fintype.card K+(F.p+1)^2+(F.p+1)^(F.e+1)+20
  let g : Nat := 3*F.e+222+encodedBankLoadStepCost F contiguousAddress+configCost false+
    fromBankFactor+5000000
  let P : Polynomial Nat := Polynomial.C wordScale*a^20+a+Polynomial.C f
  let T : Polynomial Nat := Polynomial.C 36*Polynomial.X+
    Polynomial.C g*(Polynomial.C 10000000*a^5)^7+Polynomial.C 100
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp
    (Mathproof.Problem18P34Machine20261002Layout.layout (anchorBinaryCode D F))
    (anchorBinaryCode D F) (anchorWordResult D) P T
    (Mathproof.Problem18P34Machine20261002Layout.layout_ok _)
  intro ws
  let b := bitSize ws
  let x := anchorInputScale F b
  let B := 2^(P.eval b+b+1)
  have ha : a.eval b = x := by
    dsimp only [a,x,anchorInputScale]
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
      Nat.add_assoc]
  have hP : P.eval b = wordScale*x^20+x+f := by simp [P,ha]
  have hT : T.eval b = 36*b+g*(reserve x)^7+100 := by simp [T,ha,reserve]
  have hB : wordLimit x ≤ B := by
    unfold wordLimit B
    rw [hP]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hFit : ws.length ≤ b := Lax51Proofs.Encoding.length_le_bitSize ws
  have hX : ws.length*ws.length ≤ x := by
    unfold x anchorInputScale
    rw [pow_two]
    apply Nat.mul_le_mul <;> omega
  have hCap : x+2 < B := (Nat.lt_two_pow_self (n := x+2)).trans_le
    (Nat.pow_le_pow_right (by decide) (by show x+2 ≤ P.eval b+b+1; rw [hP]; dsimp [f]; omega))
  have hf : f < B := (Nat.lt_two_pow_self (n := f)).trans_le
    (Nat.pow_le_pow_right (by decide) (by show f ≤ P.eval b+b+1; rw [hP]; omega))
  have hDigits (v : Nat) (hv : v ∈ ws) : v < B :=
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hv).trans_le
      (Nat.pow_le_pow_right (by decide) (by show b+1 ≤ P.eval b+b+1; omega))
  have hReady (t : Nat) (xs : List Nat) (hw : ws = (t+1)::xs) (hl : xs.length = (t+1)*(t+1)) :
      OneAnchorLayout (width (t+1)) B t ∧ width (t+1) < B ∧
      F.e+1+Snf (width (t+1))*F.e < B ∧ 16*(F.e+1) < B ∧
      loadedAnchorCost F t ≤ g*(reserve x)^7 := by
    have hz : (t+1)*(t+1)+1 ≤ b := by
      rw [hw,List.length_cons,hl] at hFit
      exact hFit
    obtain ⟨hA,hM,hS,hW,_⟩ := anchorFits F hz
    exact ⟨hA.enlarge hB,hW.trans_le hB,hM.trans_le hB,hS.trans_le hB,loadedAnchorCost_le F hz⟩
  obtain ⟨τ,h,ho⟩ := anchorBinaryCode_run D F ws (B := B)
    (show ws.length*ws.length+2 < B by omega) hDigits
    (by dsimp [f] at hf; omega) (by dsimp [f] at hf; omega) (by dsimp [f] at hf; omega) hReady
  refine ⟨anchorExtent F ws,τ,h.mono ?_,ho⟩
  rw [show bitSize ws = b from rfl,hT]
  omega

#print axioms anchorBinaryCode_run
#print axioms anchorWordResult_turingPolytime
end EvenTI.P13Spectral
