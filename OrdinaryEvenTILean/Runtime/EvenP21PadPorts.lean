import EvenP21PadClosure
import EvenP8ChartPair

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace EvenTI.P21Pad

open scoped Matrix
open Matrix EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.CellPreparation EvenTI.LiveAlgebra

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A width cast neither moves field words nor changes row-major addresses. -/
theorem transportInverseLabels {u v : ℕ} (h : u=v)
    (D : FieldEncoding K) (U : (Matrix (Fin u) (Fin u) K)ˣ) (bank : List ℕ)
    (hBank : ∀ r c, bank.getD (inverseAddress r c) 0=(D (U.inv r c)).val) :
    ∀ r c, bank.getD (inverseAddress r c) 0=
      (D ((transportMatrixUnit (finCongr h) U).inv r c)).val := by
  cases h
  exact hBank

/-- The actual inverse output of the selected site's source chart
is the numeric support input, through both proved width identifications. -/
theorem transportedInverseGaugeBank_labels (w : TrialWords K)
    (m : Fin w.modeCount → PreparedMode K) (hw : ∀ p, (m p).n=w.width p)
    (U : SiteUnits w m) (i : Fin (w.sites+2)) {width : ℕ}
    (hWidth : w.width (w.mode i)=width) (D : FieldEncoding K) (bank : List ℕ)
    (hBank : ∀ r c, bank.getD (inverseAddress r c) 0=(D ((U i).inv r c)).val) :
    ∀ r c, bank.getD (inverseAddress r c) 0=
      (D ((transportMatrixUnit (finCongr hWidth) (physicalSourceChartUnit w m hw U i)).inv r c)).val :=
  transportInverseLabels hWidth D (physicalSourceChartUnit w m hw U i) bank
    (transportInverseLabels (hw (w.mode i)) D (U i) bank hBank)

/-- Identify the source gauge picked by the checked chart choice. -/
theorem allModeCharts_sourceGauge
    (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K) (h : ∀ p, ModeLayout (m p))
    (c : AllModeChoices w m) (U V : SiteUnits w m) (i : Fin (w.sites+2))
    (hRead : allModeCharts w m h c=some (U,V))
    (hSource : IsUnit (modeSourceFrame (m (w.mode i)) (h (w.mode i))))
    (hTarget : IsUnit (modeTargetFrame (m (w.mode i)) (h (w.mode i)) (c (w.mode i))))
    (hFields : ∀ b ∈ (m (w.mode i)).blocks, b.HasFieldModel) :
    (U i).val =
      if w.minus i then ((modeSourceFrame (m (w.mode i)) (h (w.mode i)))⁻¹)ᵀ *
          modeGramMatrix (m (w.mode i)) (h (w.mode i))
      else modeSourceFrame (m (w.mode i)) (h (w.mode i)) := by
  have hSite := allModeCharts_read w m h c U V hRead i
  cases hs : w.minus i with
  | false =>
    simp only [hs] at hSite
    obtain ⟨P,Q,hr,hP,_⟩ := makeSiteChart_primal (m (w.mode i)) (h (w.mode i))
      (c (w.mode i)) hSource hTarget
    have he : (P,Q)=(U i,V i) := Option.some.inj (hr.symm.trans hSite)
    exact (congrArg (fun z => z.1.val) he).symm.trans hP
  | true =>
    simp only [hs] at hSite
    obtain ⟨P,Q,hr,hP,_⟩ := makeSiteChart_dual (m (w.mode i)) (h (w.mode i))
      (c (w.mode i)) hSource hTarget (modeGramMatrix_isUnit _ _ hFields)
    have he : (P,Q)=(U i,V i) := Option.some.inj (hr.symm.trans hSite)
    exact (congrArg (fun z => z.1.val) he).symm.trans hP

#print axioms transportedInverseGaugeBank_labels
#print axioms allModeCharts_sourceGauge
end EvenTI.P21Pad
