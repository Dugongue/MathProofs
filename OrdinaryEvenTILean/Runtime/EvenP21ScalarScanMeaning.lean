import EvenP21ScalarScanModes

set_option autoImplicit false

namespace EvenTI.P21ScalarScan

open scoped Matrix
open EvenTI.P15Recover

/-- The physical nonzero chart entries and active source blocks cover the
same site addresses. Several entries or blocks may share one address. -/
theorem ScanModeInput.scalar_iff_supportedSites {M W m n : ℕ} {B : Type}
    (p : ScanModeInput W n) (src : Fin m → Fin 3 → Fin n)
    (slot : B → Fin n) (active : B → Prop)
    (fromChart : ∀ k : Fin p.L, p.chart.getD k.val 0 ≠ p.zero →
      ∃ b, active b ∧ p.site k = slot b)
    (toChart : ∀ b, active b → ∃ k : Fin p.L, p.chart.getD k.val 0 ≠ p.zero ∧ p.site k = slot b)
    (refChart : ∀ k : Fin p.L, p.chart.getD k.val 0 ≠ p.zero →
      ∃ b, active b ∧ p.reference = slot b) :
    p.scalar (M:=M) src ↔
      ∀ z, (incidenceMatrix M src).mulVec z = 0 →
        ∀ b c, active b → active c → z (slot b) = z (slot c) := by
  change (∀ z, (incidenceMatrix M src).mulVec z = 0 →
      ∀ k : Fin p.L, p.chart.getD k.val 0 ≠ p.zero → z (p.site k) = z p.reference) ↔ _
  constructor
  · intro h z hz b c hb hc
    obtain ⟨i,hi,ei⟩ := toChart b hb
    obtain ⟨j,hj,ej⟩ := toChart c hc
    rw [←ei,←ej]
    exact (h z hz i hi).trans (h z hz j hj).symm
  · intro h z hz i hi
    obtain ⟨b,hb,eb⟩ := fromChart i hi
    obtain ⟨c,hc,ec⟩ := refChart i hi
    rw [eb,ec]
    exact h z hz b c hb hc

#print axioms ScanModeInput.scalar_iff_supportedSites
end EvenTI.P21ScalarScan
