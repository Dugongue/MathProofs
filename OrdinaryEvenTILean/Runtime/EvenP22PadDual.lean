import EvenP22PadAssembly
import EvenP21PadInverseCall

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000

namespace EvenTI.P22Pad

open EvenTI.Contract EvenTI.P20Sweep EvenTI.P21Pad EvenTI.P15Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul ev_add)
open Mathproof.Problem17Primary46ModePadding (start stop)
open EvenTI.P19Scalar.PrefixStencil (stencilChartBank)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def installDualLabelBounds (lower : Bool) : Com :=
  .seq (.assign (start lower) (.var frameTemp))
    (.assign (stop lower) (.add (.var frameTemp)
      (.mul (.var savedAmbientSize) (.var savedAmbientSize))))

noncomputable def exportArchivedDualLabels (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) : Com :=
  .seq (installDualLabelBounds lower)
    (EvenTI.P19Scalar.LiveChart.materializeSweptChart D F lower)

/-- The archive's column-major frame already stores the dual chart in
row-major order, so the existing label exporter can consume it directly. -/
theorem exportArchivedDualLabels_run (D : FieldEncoding K) (F : FieldPresentation K)
    (lower : Bool) {B S n src : ℕ} {s : Env} (U : Matrix (Fin n) (Fin n) K)
    (hs : Slots F canonical qN.WS S B s)
    (hN : s.vars savedAmbientSize=n) (hSrc : s.vars frameTemp=src)
    (hn : n < B) (hOne : 1<B) (hFit : src+n*n ≤ S)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hDst : n*n ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < B)
    (hStored : ∀ r c, val F canonical qN.WS s (src+inverseAddress c r)=U r c) :
    ∃ t, Run B (exportArchivedDualLabels D F lower) s t (8+(8+installScalarLabelsCost F (n*n))) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ r c, (t.arrs stencilChartBank).getD (inverseAddress r c) 0=(D (U c r)).val) ∧
      Frame (exportArchivedDualLabels D F lower) s t := by
  have hS := hs.slots_word
  let u := s.setVar (start lower) src
  let v := u.setVar (stop lower) (src+n*n)
  have r₀ : Run B (.assign (start lower) (.var frameTemp)) s u 2 :=
    Run.assign (ev_var hSrc (by omega))
  have uN : u.vars savedAmbientSize=n := by
    have hSep : savedAmbientSize≠start lower := by cases lower <;> decide
    simpa only [u,vars_setVar,if_neg hSep] using hN
  have uSrc : u.vars frameTemp=src := by
    have hSep : frameTemp≠start lower := by cases lower <;> decide
    simpa only [u,vars_setVar,if_neg hSep] using hSrc
  have r₁ : Run B (.assign (stop lower) (.add (.var frameTemp)
      (.mul (.var savedAmbientSize) (.var savedAmbientSize)))) u v 6 :=
    Run.assign (ev_add (ev_var uSrc (by omega))
      (ev_mul (ev_var uN hn) (ev_var uN hn) (by omega)) (by omega))
  have r : Run B (installDualLabelBounds lower) s v 8 := r₀.seq r₁
  have hu : Slots F canonical qN.WS S B u := Slots.setVar F canonical hs
    (by cases lower <;> decide) (by cases lower <;> decide) _
  have hv : Slots F canonical qN.WS S B v := Slots.setVar F canonical hu
    (by cases lower <;> decide) (by cases lower <;> decide) _
  have huStart : u.vars (start lower)=src := by simp [u]
  have hStart : v.vars (start lower)=src := by
    have hSep : start lower≠stop lower := by cases lower <;> decide
    simpa only [v,vars_setVar,if_neg hSep] using huStart
  have hStop : v.vars (stop lower)=src+n*n := by simp [v]
  have hFrame : ∀ r c, val F canonical qN.WS v (src+inverseAddress r c)=U.transpose r c := by
    intro r c
    rw [val_setVar F canonical (by cases lower <;> decide),
      val_setVar F canonical (by cases lower <;> decide)]
    exact hStored c r
  obtain ⟨t,rt,ht,hLabels,_,_,_⟩ := materializeInverseGaugeLabels_run D F lower U.transpose
    hv hQ hP hOne hStart hStop hFit hDst hWord hFrame
  have rr : Run B (exportArchivedDualLabels D F lower) s t
      (8+(8+installScalarLabelsCost F (n*n))) := r.seq rt
  exact ⟨t,rr,ht,hLabels,Frame.of_run rr⟩

#print axioms exportArchivedDualLabels_run
end EvenTI.P22Pad

