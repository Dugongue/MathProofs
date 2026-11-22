import EvenP14CutDot

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dI dL dO dT dU dZ)

variable {K : Type} [Field K] [Fintype K]

def cutNextEntry : Com := .assign cutEntry (.add (.var cutEntry) (.lit 1))
def cutDotGuard : Cond := .lt (.var cutEntry) (.var shapePower.out)

noncomputable def cutRecombineBody (F : FieldPresentation K) : Com :=
  .seq (cutDotProgram F) cutNextEntry

noncomputable def cutRecombineProgram (F : FieldPresentation K) : Com :=
  .seq (.assign cutEntry (.lit 0)) (.while cutDotGuard (cutRecombineBody F))

noncomputable def cutRecombineCost (F : FieldPresentation K) (c m : ℕ) : ℕ :=
  (cutDotCost F c+8)*m+6

noncomputable def cutFormEntry (F : FieldPresentation K) (σ : Env) (a b c m j : ℕ) : K :=
  ∑ i ∈ Finset.range c, val F canonical qN.WS σ (a+i) * val F canonical qN.WS σ (b+(i*m+j))

structure CutRecombineInput {B Sn : ℕ} (F : FieldPresentation K)
    (σ : Env) (a b o c m z t u : ℕ) : Prop where
  slots : Slots F canonical qN.WS Sn B σ
  layout : CutDotLayout a b o c m z t u Sn
  count_word : c+1 < B
  coeff_start : σ.vars cutCoeffStart = a
  basis_start : σ.vars cutBasisStart = b
  form_start : σ.vars cutFormStart = o
  side : σ.vars shapePower.out = m
  count : σ.vars dL = c
  zero : σ.vars dZ = z
  scratch₁ : σ.vars dT = t
  scratch₂ : σ.vars dU = u
  zero_value : val F canonical qN.WS σ z = 0

private structure RecombineInvariant (F : FieldPresentation K)
    (σ τ : Env) (B Sn a b o c m t u : ℕ) : Prop where
  slots : Slots F canonical qN.WS Sn B τ
  cursor : τ.vars cutEntry ≤ m
  sameRegs : ∀ r, r ∉ regNames canonical → r ≠ dI → r ≠ dO → r ≠ cutEntry → τ.vars r = σ.vars r
  sameMem : ∀ s < Sn, (s < o ∨ o+m ≤ s) → s ≠ t → s ≠ u →
    val F canonical qN.WS τ s = val F canonical qN.WS σ s
  entries : ∀ j < τ.vars cutEntry, val F canonical qN.WS τ (o+j) = cutFormEntry F σ a b c m j
  sameArrays : ∀ x, x ≠ canonical.mem → x ≠ canonical.scratch → τ.arrs x = σ.arrs x
  input : τ.inp = σ.inp
  output : τ.out = σ.out

/-- The live form bank is the exact coefficient combination of the live
cut basis at every coordinate. Each physical dot costs linear time in the
live nullity; its writes are framed out of all four basis banks. -/
theorem cutRecombineProgram_run (F : FieldPresentation K)
    {B Sn a b o c m z t u : ℕ} {σ : Env}
    (h : CutRecombineInput (Sn := Sn) (B := B) F σ a b o c m z t u) :
    ∃ τ, Run B (cutRecombineProgram F) σ τ (cutRecombineCost F c m) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ j < m, val F canonical qN.WS τ (o+j) = cutFormEntry F σ a b c m j) ∧
      (∀ s < Sn, (s < o ∨ o+m ≤ s) → s ≠ t → s ≠ u →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, r ∉ regNames canonical → r ≠ dI → r ≠ dO → r ≠ cutEntry → τ.vars r = σ.vars r) ∧
      (∀ x, x ≠ canonical.mem → x ≠ canonical.scratch → τ.arrs x = σ.arrs x) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hm := h.layout.output_before
  have hz := h.layout.basis_before
  have hzt := h.layout.zero_before
  have htu := h.layout.scratch_order
  have hfit := h.layout.fit
  have hc := h.layout.nullity
  have hao := h.layout.coefficient_before
  have hB := h.slots.slots_word
  have hOne : 1 < B := by have := h.count_word; omega
  have eVar {ρ : Env} {r : String} {v : ℕ} (hv : ρ.vars r = v) (hb : v < B) :
      (Expr.var r).evalB B ρ = some v := evalB_var_iff.mpr ⟨hv.symm,hv ▸ hb⟩
  let σ₀ := σ.setVar cutEntry 0
  let I (ρ : Env) := RecombineInvariant F σ ρ B Sn a b o c m t u
  let V (ρ : Env) := m - ρ.vars cutEntry
  have eqW : cutEntry ≠ qN.WS := by decide
  have h₀ : Run B (.assign cutEntry (.lit 0)) σ σ₀ 2 := Run.assign (evalB_lit (by omega))
  have e₀ : σ₀.vars cutEntry = 0 := by simp [σ₀]
  have I₀ : I σ₀ := by
    refine ⟨Slots.setVar F canonical h.slots (by decide) eqW 0,by rw [e₀]; omega,
      fun r _ _ _ hr => by simp [σ₀,vars_setVar,hr],
      fun s _ _ _ _ => val_setVar F canonical eqW σ 0 s,?_,fun _ _ _ => rfl,rfl,rfl⟩
    intro j hj
    omega
  have guard (ρ : Env) (hρ : I ρ) : cutDotGuard.evalB B ρ = some (decide (ρ.vars cutEntry < m)) := by
    have hs := (hρ.sameRegs shapePower.out (by decide) (by decide) (by decide) (by decide)).trans h.side
    exact evalB_condLt (evalB_var (hρ.cursor.trans_lt (by omega))) (eVar hs (by omega))
  have each (ρ : Env) (hρ : I ρ) (bg : cutDotGuard.evalB B ρ = some true) :
      ∃ ν, Run B (cutRecombineBody F) ρ ν (cutDotCost F c+4) ∧ I ν ∧ V ν < V ρ := by
    let j := ρ.vars cutEntry
    have hj : j < m := by rw [guard ρ hρ] at bg; simpa [j] using bg
    have hz0 := (hρ.sameMem z (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans h.zero_value
    obtain ⟨τ,hr,hs,hv,hMem,hRegs,hArr,hIn,hOut⟩ :=
      cutDotProgram_run F hρ.slots h.layout hj h.count_word
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.coeff_start)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.basis_start)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.form_start)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.side) rfl
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.count)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.zero)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.scratch₁)
        ((hρ.sameRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.scratch₂) hz0
    have hRead : cutFormEntry F ρ a b c m j = cutFormEntry F σ a b c m j := by
      unfold cutFormEntry
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hiw : i*m+j < m*m := by
        have hl := Nat.mul_le_mul_right m (show i+1 ≤ m from hi'.trans_le hc)
        rw [Nat.succ_mul] at hl
        omega
      rw [hρ.sameMem (a+i) (by omega) (Or.inl (by omega)) (by omega) (by omega),
        hρ.sameMem (b+(i*m+j)) (by omega) (Or.inr (by omega)) (by omega) (by omega)]
    have hValue : val F canonical qN.WS τ (o+j) = cutFormEntry F σ a b c m j := hv.trans hRead
    have hJ : τ.vars cutEntry = j := hRegs _ (by decide) (by decide) (by decide)
    let ν := τ.setVar cutEntry (j+1)
    have hInc : Run B cutNextEntry τ ν 4 :=
      Run.assign (evalB_bin (op := .add) (eVar hJ (by omega))
        (evalB_lit hOne) (by change j+1 < B; omega))
    have hν : ν.vars cutEntry = j+1 := by simp [ν]
    have hNv (s : ℕ) : val F canonical qN.WS ν s = val F canonical qN.WS τ s :=
      val_setVar F canonical eqW τ _ s
    refine ⟨ν,hr.seq hInc,⟨Slots.setVar F canonical hs (by decide) eqW _,by omega,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · intro r h1 h2 h3 h4
      simpa [ν,vars_setVar,h4] using (hRegs r h1 h2 h3).trans (hρ.sameRegs r h1 h2 h3 h4)
    · intro s hs hsOut ht hu
      rw [hNv,hMem s hs (by rcases hsOut with hsOut|hsOut <;> omega) ht hu]
      exact hρ.sameMem s hs hsOut ht hu
    · intro i hi
      rw [hNv]
      by_cases he : i=j
      · simpa only [he] using hValue
      · have hip : i < j := by omega
        exact (hMem (o+i) (by omega) (by omega) (by omega) (by omega)).trans (hρ.entries i hip)
    · exact fun x hx hy => (hArr x hx hy).trans (hρ.sameArrays x hx hy)
    · exact hIn.trans hρ.input
    · exact hOut.trans hρ.output
    · change m-ν.vars cutEntry < m-j
      omega
  obtain ⟨τ,hLoop,hτ,hEnd⟩ := Run.while_count I V (cutDotCost F c+4)
    (fun ρ hρ => ⟨_,guard ρ hρ⟩) each I₀
  rw [guard _ hτ] at hEnd
  have he : τ.vars cutEntry = m := by
    have hnot : ¬ τ.vars cutEntry < m := by simpa using hEnd
    exact le_antisymm hτ.cursor (by omega)
  refine ⟨τ,(h₀.seq hLoop).mono ?_,hτ.slots,?_,hτ.sameMem,hτ.sameRegs,
    hτ.sameArrays,hτ.input,hτ.output⟩
  · simp [cutRecombineCost,V,e₀,cutDotGuard,Cond.size]
    rw [show 4 + (cutDotCost F c + 4) = cutDotCost F c + 8 by omega]
    omega
  · intro j hj
    exact hτ.entries j (by rwa [he])

#print axioms cutRecombineProgram_run
end EvenTI.P12ComparePrep
