import EvenP16TrialNativeProjection
import EvenP16TrialRectangularCall

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace EvenTI.P19Trial

open EvenTI.P16TrialNative

open EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames NoVar)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.P15RecogIMPDot20261007 (qN dI dO dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut gU gV Written)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)

structure ProjectionWords where
  width : String
  stride : String
  columns : String
  form : String
  output : String

def ProjectionWords.regs (R : ProjectionWords) : List String := [R.width,R.stride,R.columns,R.form,R.output]

def projectionTargets : List String :=
  [dL,gRows,gCols,gOut,nativeProjectionWidth,nativeProjectionStride,nativeProjectionForm]

private def projectionArgs (R : ProjectionWords) : List (String × Expr) :=
  [(dL,.lit 1),(gRows,.mul (.var R.width) (.var R.width)),(gCols,.var R.columns),
    (gOut,.var R.output),(nativeProjectionWidth,.var R.width),
    (nativeProjectionStride,.var R.stride),(nativeProjectionForm,.var R.form)]

private theorem projectionArgs_safe (R : ProjectionWords)
    (h : ∀ r∈R.regs,r∉projectionTargets) :
    ∀ p∈projectionArgs R, ∀ q∈projectionArgs R, NoVar p.1 q.2 := by
  intro p hp q hq
  have hp' : p.1∈projectionTargets := List.mem_map.mpr ⟨p,hp,rfl⟩
  have hfl (x : String) (hx : x∈R.regs) : p.1≠x := fun ee => h x hx (ee ▸ hp')
  have h₁ : p.1≠R.width := hfl _ (by simp [ProjectionWords.regs])
  have h₂ : p.1≠R.stride := hfl _ (by simp [ProjectionWords.regs])
  have h₃ : p.1≠R.columns := hfl _ (by simp [ProjectionWords.regs])
  have h₄ : p.1≠R.form := hfl _ (by simp [ProjectionWords.regs])
  have h₅ : p.1≠R.output := hfl _ (by simp [ProjectionWords.regs])
  simp only [projectionArgs,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [NoVar,Expr.mul,h₁,h₂,h₃,h₄,h₅,Ne.symm h₁,Ne.symm h₂,Ne.symm h₃,Ne.symm h₄,Ne.symm h₅]

variable {K : Type} [Field K] [Fintype K]

noncomputable def nativeProjectionCall (F : FieldPresentation K) (R : ProjectionWords) : Com :=
  .seq (commands (projectionArgs R)) (nativeProjectionGrid F)

/-- Install the retained-mode grid arguments from a saved caller state
and execute the actual projection on its current form bank. -/
theorem nativeProjectionCall_run (F : FieldPresentation K) (R : ProjectionWords)
    {n s p src dst z t u Sn B : ℕ} {σ : Env}
    (hSafe : ∀ r∈R.regs,r∉projectionTargets)
    (hn : 0 < n) (hs : 0 < s) (hp : 0 < p) (hWide : 2*n < B)
    (hRows : n*n+1 < B) (hCols : (p*n)*s+1 < B)
    (hSrc : src+(p*n)*s ≤ dst) (hFit : dst+(n*n)*((p*n)*s) ≤ Sn)
    (ht : t < Sn) (hu : u < Sn) (htu : t ≠ u)
    (htDst : dst+(n*n)*((p*n)*s) ≤ t) (huDst : dst+(n*n)*((p*n)*s) ≤ u)
    (hOneFit : z+1 < Sn)
    (hz : ¬ Written dst (n*n) ((p*n)*s) t u z) (ho : ¬ Written dst (n*n) ((p*n)*s) t u (z+1))
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hZero : val F canonical qN.WS σ z=0) (hOne : val F canonical qN.WS σ (z+1)=1)
    (hRegT : σ.vars dT=t) (hRegU : σ.vars dU=u) (hRegZ : σ.vars dZ=z)
    (hWidth : σ.vars R.width=n) (hStride : σ.vars R.stride=s) (hColumns : σ.vars R.columns=((p*n)*s))
    (hForm : σ.vars R.form=src) (hOutput : σ.vars R.output=dst) :
    ∃ τ, Run B (nativeProjectionCall F R) σ τ (17+nativeProjectionGridCost F n s p) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ i < n*n, ∀ j < (p*n)*s,
        val F canonical qN.WS τ (dst+(i*((p*n)*s)+j)) =
          if i/n=j/s%n then val F canonical qN.WS σ (src+changedDigit n s j (i%n)) else 0) ∧
      (∀ k < Sn, ¬ Written dst (n*n) ((p*n)*s) t u k →
        val F canonical qN.WS τ k = val F canonical qN.WS σ k) ∧
      (∀ x, x ∉ projectionTargets → x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x = σ.vars x) ∧
      (∀ a, a ≠ canonical.mem → a ≠ canonical.scratch → τ.arrs a = σ.arrs a) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let A := [(dL,1),(gRows,n*n),(gCols,(p*n)*s),(gOut,dst),(nativeProjectionWidth,n),
    (nativeProjectionStride,s),(nativeProjectionForm,src)]
  let ρ := install A σ
  have hB := hSlots.slots_word
  have hnB : n<B := by omega
  have hsB : s<B := (Nat.le_mul_of_pos_left s (Nat.mul_pos hp hn)).trans_lt (by omega)
  have e := ev_var hWidth hnB
  have r₀ : Run B (commands (projectionArgs R)) σ ρ 17 :=
    commands_run (projectionArgs R) [1,n*n,(p*n)*s,dst,n,s,src] σ rfl
      (.cons (evalB_lit (by omega)) (.cons (ev_mul e e (by omega))
        (.cons (ev_var hColumns (by omega)) (.cons (ev_var hOutput (by omega))
          (.cons e (.cons (ev_var hStride hsB) (.cons (ev_var hForm (by omega)) .nil)))))))
      (projectionArgs_safe R hSafe)
  have hField : ∀ x∈projectionTargets,
      canonical.e≠x ∧ canonical.p≠x ∧ canonical.modBase≠x ∧ canonical.exp≠x ∧ qN.WS≠x := by decide
  have hKeep (x : String) (hx : x ∉ projectionTargets) : ρ.vars x = σ.vars x :=
    installed_scalar A σ x (fun q hq eq => hx (List.mem_map.mpr ⟨q,hq,eq.symm⟩))
  have hA := (installed_arrays A σ).1
  have hV (k : ℕ) : val F canonical qN.WS ρ k=val F canonical qN.WS σ k := by
    unfold val slice
    rw [hKeep _ (by decide),hA]
  have hS := installed_slots F A σ hSlots (fun q hq => hField q.1 (List.mem_map.mpr ⟨q,hq,rfl⟩))
  obtain ⟨τ,r,hSlots',hOut,hMem,hVars,hArr,hIn,hO⟩ :=
    nativeProjectionGrid_run F hn hs hp hWide hRows hCols hSrc hFit ht hu htu htDst huDst hOneFit hz ho
      hS ((hV _).trans hZero) ((hV _).trans hOne)
      (by rfl)
      ((hKeep _ (by decide)).trans hRegT) ((hKeep _ (by decide)).trans hRegU)
      ((hKeep _ (by decide)).trans hRegZ)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  refine ⟨τ,r₀.seq r,hSlots',?_,fun k hk hf => (hMem k hk hf).trans (hV k),
    fun x hs ha h₁ h₂ h₃ h₄ => (hVars x ha h₁ h₂ h₃ h₄).trans (hKeep x hs),
    fun a ha hb => (hArr a ha hb).trans (congrFun hA a),hIn,hO⟩
  intro i hi j hj
  rw [hOut i hi j hj,hV]

#print axioms nativeProjectionCall_run
end EvenTI.P19Trial
