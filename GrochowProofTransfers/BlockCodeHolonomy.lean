import Mathlib.Tactic.Group

namespace BlockCodeHolonomy

variable {I J K : Type*} [Group K]

/-- Holonomy of the rectangle from the two fixed coordinate indices. -/
def cycleGain (A : I → J → K) (i₀ : I) (j₀ : J) (i : I) (j : J) : K :=
  (A i₀ j)⁻¹ * A i j * (A i j₀)⁻¹ * A i₀ j₀

/-- All compatible input and output gauges. Group multiplication is composition. -/
def GaugeWitness (A B : I → J → K) :=
  { p : (I → K) × (J → K) // ∀ i j, p.2 j * A i j = B i j * p.1 i }

/-- The common intertwiners of all anchored rectangles. -/
def RootWitness (A B : I → J → K) (i₀ : I) (j₀ : J) :=
  { t : K // ∀ i j, t * cycleGain A i₀ j₀ i j = cycleGain B i₀ j₀ i j * t }

private def outputGauge (A B : I → J → K) (i₀ : I) (t : K) (j : J) : K :=
  B i₀ j * t * (A i₀ j)⁻¹

private def inputGauge (A B : I → J → K) (i₀ : I) (j₀ : J) (t : K) (i : I) : K :=
  (B i j₀)⁻¹ * B i₀ j₀ * t * (A i₀ j₀)⁻¹ * A i j₀

private theorem transported_edge_iff (A B : I → J → K)
    (i₀ : I) (j₀ : J) (t : K) (i : I) (j : J) :
    outputGauge A B i₀ t j * A i j = B i j * inputGauge A B i₀ j₀ t i ↔
      t * cycleGain A i₀ j₀ i j = cycleGain B i₀ j₀ i j * t := by
  constructor
  · intro h
    calc
      _ = (B i₀ j)⁻¹ * (outputGauge A B i₀ t j * A i j) *
          ((A i j₀)⁻¹ * A i₀ j₀) := by unfold outputGauge cycleGain; group
      _ = (B i₀ j)⁻¹ * (B i j * inputGauge A B i₀ j₀ t i) *
          ((A i j₀)⁻¹ * A i₀ j₀) := by rw [h]
      _ = _ := by unfold inputGauge cycleGain; group
  · intro h
    calc
      _ = B i₀ j * (t * cycleGain A i₀ j₀ i j) * ((A i₀ j₀)⁻¹ * A i j₀) := by
        unfold outputGauge cycleGain
        group
      _ = B i₀ j * (cycleGain B i₀ j₀ i j * t) * ((A i₀ j₀)⁻¹ * A i j₀) := by rw [h]
      _ = _ := by unfold inputGauge cycleGain; group

private theorem recover_output (A B : I → J → K)
    (i₀ : I) (p : GaugeWitness A B) (j : J) :
    p.val.2 j = outputGauge A B i₀ (p.val.1 i₀) j := by
  calc
    _ = (p.val.2 j * A i₀ j) * (A i₀ j)⁻¹ := by group
    _ = _ := by rw [p.property i₀ j]; rfl

private theorem recover_input (A B : I → J → K)
    (i₀ : I) (j₀ : J) (p : GaugeWitness A B) (i : I) :
    p.val.1 i = inputGauge A B i₀ j₀ (p.val.1 i₀) i := by
  calc
    _ = (B i j₀)⁻¹ * (B i j₀ * p.val.1 i) := by group
    _ = (B i j₀)⁻¹ * (p.val.2 j₀ * A i j₀) := by rw [p.property i j₀]
    _ = _ := by rw [recover_output A B i₀ p j₀]; unfold outputGauge inputGauge; group

/-- Evaluation at one input coordinate bijects all full witnesses with the
simultaneous intertwiners. In particular every root witness recovers all coordinates. -/
def gaugeEquivRoot (A B : I → J → K) (i₀ : I) (j₀ : J) :
    GaugeWitness A B ≃ RootWitness A B i₀ j₀ where
  toFun p := ⟨p.val.1 i₀, fun i j => (transported_edge_iff A B i₀ j₀ (p.val.1 i₀) i j).mp
    (by rw [← recover_input A B i₀ j₀ p i, ← recover_output A B i₀ p j]; exact p.property i j)⟩
  invFun t := ⟨(inputGauge A B i₀ j₀ t.val, outputGauge A B i₀ t.val),
    fun i j => (transported_edge_iff A B i₀ j₀ t.val i j).mpr (t.property i j)⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (funext fun i => (recover_input A B i₀ j₀ p i).symm)
      (funext fun j => (recover_output A B i₀ p j).symm)
  right_inv t := by
    apply Subtype.ext
    change inputGauge A B i₀ j₀ t.val i₀ = t.val
    unfold inputGauge
    group

/-- Fixed-coordinate existence is exactly simultaneous conjugacy of cycle gains. -/
theorem gauge_iff_cycle_intertwiner (A B : I → J → K) (i₀ : I) (j₀ : J) :
    Nonempty (GaugeWitness A B) ↔ Nonempty (RootWitness A B i₀ j₀) :=
  ⟨fun ⟨p⟩ => ⟨gaugeEquivRoot A B i₀ j₀ p⟩,
   fun ⟨t⟩ => ⟨(gaugeEquivRoot A B i₀ j₀).symm t⟩⟩

end BlockCodeHolonomy
