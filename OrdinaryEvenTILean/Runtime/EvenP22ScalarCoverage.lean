import EvenP22ScalarController
import EvenP21PadSite

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace EvenTI.P22Scalar

open Matrix EvenTI.Contract EvenTI.P20Pad EvenTI.P21Pad EvenTI.P21ScalarScan

variable {K : Type} [Field K] [Fintype K]

/-- Exact coverage on a padded chart loaded with the masked inverse-frame
digits. Every occupied cell can be traced to one native field block. -/
theorem inverseChartCoverage {W N width blocks : ℕ} {C : Fin blocks → Type}
    (D : FieldEncoding K) (hw : 0 < width) (right : Bool) (cutoff : ℕ)
    (order : (Σ j, C j) ≃ Fin width) (V : Matrix (Fin width) (Fin width) K)
    (slot : Fin blocks → Fin N) (plan : ScanModeInput W N)
    (hL : plan.L=width*width) (hZero : plan.zero=(D 0).val)
    (hChart : ∀ r c : Fin width, plan.chart.getD (inverseAddress r c) 0 =
      if columnKept right cutoff c.val then (D (V r c)).val else plan.zero)
    (hSite : ∀ k : Fin plan.L, plan.site k=inverseBankSite hw order slot (Fin.cast hL k))
    (reference : Fin plan.L)
    (hReference : plan.chart.getD reference.val 0≠plan.zero)
    (hSelected : plan.reference=plan.site reference) :
    ChartCoverage plan slot (inverseBlockSupported right cutoff order V) := by
  have atAddress (k : Fin plan.L) :
      plan.chart.getD k.val 0≠plan.zero ↔
      columnKept right cutoff (inverseCol hw (Fin.cast hL k)).val=true ∧
        V (inverseRow hw (Fin.cast hL k)) (inverseCol hw (Fin.cast hL k))≠0 := by
    let r := inverseRow hw (Fin.cast hL k)
    let c := inverseCol hw (Fin.cast hL k)
    have hk : inverseAddress r c=k.val := inverseAddress_indices hw (Fin.cast hL k)
    change _ ↔ columnKept right cutoff c.val=true ∧ V r c≠0
    rw [← hk,hChart]
    by_cases hKeep : columnKept right cutoff c.val=true
    · simp only [hKeep,if_true,true_and]
      rw [hZero]
      constructor
      · intro h hz
        exact h (congrArg (fun a => (D a).val) hz)
      · intro h hz
        exact h (D.injective (Fin.ext hz))
    · have hFalse := Bool.eq_false_iff.mpr hKeep
      simp [hFalse]
  have first (k : Fin plan.L) (hk : plan.chart.getD k.val 0≠plan.zero) :
      ∃ j, inverseBlockSupported right cutoff order V j ∧ plan.site k=slot j := by
    let r := inverseRow hw (Fin.cast hL k)
    let c := inverseCol hw (Fin.cast hL k)
    let a := order.symm r
    obtain ⟨hKeep,hNZ⟩ := (atAddress k).mp hk
    refine ⟨a.1,⟨a.2,c,hKeep,?_⟩,hSite k⟩
    simpa only [a,Sigma.eta,Equiv.apply_symm_apply] using hNZ
  refine ⟨first,?_,?_⟩
  · rintro j ⟨a,c,hKeep,hNZ⟩
    let r := order ⟨j,a⟩
    let k : Fin plan.L := Fin.cast hL.symm ⟨inverseAddress r c,inverseAddress_lt r c⟩
    have hc : Fin.cast hL k = ⟨inverseAddress r c,inverseAddress_lt r c⟩ := by
      apply Fin.ext
      rfl
    have hFlat : k.val=inverseAddress r c := rfl
    refine ⟨k,?_,?_⟩
    · rw [hFlat,hChart,if_pos hKeep,hZero]
      exact fun e => hNZ (D.injective (Fin.ext e))
    · rw [hSite,hc,inverseBankSite,inverseAddress_row]
      simp [r]
  · intro _ _
    obtain ⟨j,hj,hr⟩ := first reference hReference
    exact ⟨j,hj,hSelected.trans hr⟩


/-- Charts and original blocks need agree on the set of active addresses.
In particular, several repeated origins can all use the normalization pin. -/
theorem ChartCoverage.of_sameSites {W N : ℕ} {J J' : Type}
    {plan : ScanModeInput W N} {slot : J → Fin N} {active : J → Prop}
    (original : ChartCoverage plan slot active)
    (slot' : J' → Fin N) (active' : J' → Prop)
    (same : ∀ j : Fin N, (∃ b, active b ∧ slot b=j) ↔ (∃ b, active' b ∧ slot' b=j)) :
    ChartCoverage plan slot' active' := by
  constructor
  · intro k hk
    obtain ⟨b,hb,eq⟩ := original.fromChart k hk
    obtain ⟨b',hb',eq'⟩ := (same (plan.site k)).mp ⟨b,hb,eq.symm⟩
    exact ⟨b',hb',eq'.symm⟩
  · intro b' hb'
    obtain ⟨b,hb,eq⟩ := (same (slot' b')).mpr ⟨b',hb',rfl⟩
    obtain ⟨k,hk,heq⟩ := original.toChart b hb
    exact ⟨k,hk,heq.trans eq⟩
  · intro k hk
    obtain ⟨b,hb,eq⟩ := original.reference k hk
    obtain ⟨b',hb',eq'⟩ := (same plan.reference).mp ⟨b,hb,eq.symm⟩
    exact ⟨b',hb',eq'.symm⟩

#print axioms ChartCoverage.of_sameSites
#print axioms inverseChartCoverage
end EvenTI.P22Scalar


