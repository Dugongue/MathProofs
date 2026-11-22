import EvenP8Dechart
import Mathproof.Meta.Problem18P34AssemblyMatrixProduct20261003
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldPrimitives20261001
open Mathproof.Problem18IMPFieldPresentation20261001 (decode slice)
open Mathproof.Problem18IMPMatrixMemory20261001 (address matrix index_lt)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots NoVar)
open Mathproof.Problem18IMPRectangularProductLayout20261002 (Packed)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false

open Mathproof.Problem18IMPMatrixProductLoop20261001
open Mathproof.Problem18IMPMatrixDot20261001 (count)

-- These saved control words are part of the caller's stable frame.
def triLeft : String := "even.scalar.product.left"
def triInner : String := "even.scalar.product.inner"
def triHeight : String := "even.scalar.product.height"
def triTemp : String := "even.scalar.product.temp"
def triOut : String := "even.scalar.product.out"
def triWork : String := "even.scalar.product.work"

def triSwitchBindings : List (String × Expr) := [
  (canonical.aBase,.var triLeft), (canonical.bBase,.var triTemp),
  (canonical.outBase,.var triOut), (rows,.var triHeight),
  (count,.var triInner), (workBase,.var triWork)]

private def triSaved : List String := [triLeft,triInner,triHeight,triTemp,triOut,triWork]
private def triTouched : List String := [canonical.aBase,canonical.bBase,canonical.outBase,
  rows,count,workBase]

private theorem triSaved_frame : ∀ x ∈ triSaved, x ∉ scalarWrites routine := by
  intro x hx
  simp only [triSaved,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem triTouched_fields : ∀ x ∈ triTouched,
    canonical.e ≠ x ∧ canonical.p ≠ x ∧ canonical.modBase ≠ x ∧
      canonical.exp ≠ x ∧ "even.scalar.ws" ≠ x := by
  intro x hx
  simp only [triTouched,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The first paid matrix multiplication computes `C * D`. The second
uses a different caller-held left matrix and the same actual output bank. -/
def triProduct : Com := .seq routine (.seq (commands triSwitchBindings) routine)

variable {K : Type} [Field K] [Fintype K] (F : FieldPresentation K)

structure TriProductInput (B S m r k p : ℕ) (σ : Env) : Prop where
  first : Packed F B r k p σ
  slots : Slots F canonical "even.scalar.ws" S B σ
  in_temp : σ.vars triTemp = σ.vars canonical.outBase
  in_inner : σ.vars triInner = r
  in_height : σ.vars triHeight = m
  height_pos : 0 < m
  height_word : m < B
  output_word : m*p < B
  target_modulus : σ.vars canonical.modBase+F.e ≤ σ.vars triLeft
  target_left : σ.vars triLeft+F.e*(m*r) ≤ σ.vars triTemp
  target_middle : σ.vars triTemp+F.e*(r*p) ≤ σ.vars triOut
  target_output : σ.vars triOut+F.e*(m*p) ≤ σ.vars triWork
  target_work : σ.vars triWork+3*F.e ≤ (σ.arrs canonical.mem).length

private theorem matrix_of_cell_frame {σ τ : Env} {base m n : ℕ}
    (h : ∀ i, base ≤ i → i < base+F.e*(m*n) →
      (τ.arrs canonical.mem).getD i 0 = (σ.arrs canonical.mem).getD i 0) :
    matrix F τ base m n = matrix F σ base m n := by
  ext i j
  change decode F (slice F τ canonical (address F base n i.val j.val)) =
    decode F (slice F σ canonical (address F base n i.val j.val))
  apply congrArg (decode F)
  funext c
  apply h
  · simp [address, slice]; omega
  · have hidx := index_lt i j
    have hc := c.isLt
    have hm := Nat.mul_le_mul_left F.e (show i.val*n+j.val+1 ≤ m*n by omega)
    simp [address, slice]; nlinarith

/-- The two verified Problem 1.8 matrix calls implement the exact
three-matrix product, preserving every bank outside their destinations and
work slices. The shapes cover ordinary chart conjugation and rectangular
cropping in the order-four branch. -/
theorem triProduct_run {B S m r k p : ℕ} {σ : Env}
    (h : TriProductInput F B S m r k p σ) :
    ∃ τ, Run B triProduct σ τ (cost F.e r k p + 13 + cost F.e m r p) ∧
      ValidMemory F B τ ∧ Slots F canonical "even.scalar.ws" S B τ ∧
      matrix F τ (σ.vars triOut) m p =
        matrix F σ (σ.vars triLeft) m r *
          (matrix F σ (σ.vars canonical.aBase) r k * matrix F σ (σ.vars canonical.bBase) k p) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hws : "even.scalar.ws" ∉ scalarWrites routine := by decide
  obtain ⟨α,ha,hv,hs,hProd,hFrame,hRegs,hSizes,hIn,hOut⟩ :=
    Mathproof.Problem18P34AssemblyMatrixProduct20261003.run F σ h.first h.slots hws
  have hvar (x : String) (hx : x ∈ triSaved) : α.vars x = σ.vars x :=
    hRegs x (triSaved_frame x hx)
  have hmem := h.first.valid.memory_word
  have hse := F.degree_pos
  have hfit := h.target_work
  have hb := h.target_left
  have ht := h.target_middle
  have ho := h.target_output
  have hA : σ.vars triLeft < B := by omega
  have hT : σ.vars triTemp < B := by omega
  have hO : σ.vars triOut < B := by omega
  have hW : σ.vars triWork < B := by omega
  have get (x : String) (hx : x ∈ triSaved) (z : ℕ) (he : σ.vars x = z) (hb : z < B) :
      (Expr.var x).evalB B α = some z := by
    have hh := (hvar x hx).trans he
    simpa only [hh] using evalB_var (σ := α) (x := x) (by rw [hh]; exact hb)
  let vals := [σ.vars triLeft,σ.vars triTemp,σ.vars triOut,m,r,σ.vars triWork]
  have heval : List.Forall₂ (fun z w => z.2.evalB B α = some w) triSwitchBindings vals := by
    simp only [triSwitchBindings,vals,List.forall₂_cons]
    exact ⟨get triLeft (by decide) _ rfl hA,
      get triTemp (by decide) _ rfl hT,
      get triOut (by decide) _ rfl hO,
      get triHeight (by decide) _ h.in_height h.height_word,
      get triInner (by decide) _ h.in_inner h.first.rows_word,
      get triWork (by decide) _ rfl hW,List.Forall₂.nil⟩
  let bindings := List.zip (triSwitchBindings.map Prod.fst) vals
  let β := install bindings α
  have hsw : Run B (commands triSwitchBindings) α β 13 := by
    exact commands_run triSwitchBindings vals α rfl heval (by
      intro p hp r hr
      simp only [triSwitchBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hr
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [NoVar,canonical,rows,count,workBase,triLeft,triTemp,triOut,triHeight,triInner,triWork])
  have hio := installed_arrays bindings α
  have hkeep : ∀ q ∈ bindings, canonical.e ≠ q.1 ∧ canonical.p ≠ q.1 ∧
      canonical.modBase ≠ q.1 ∧ canonical.exp ≠ q.1 ∧ "even.scalar.ws" ≠ q.1 := by
    intro q hq
    apply triTouched_fields q.1
    simp only [bindings,triSwitchBindings,vals,List.map_cons,List.map_nil,List.zip_cons_cons,List.zip_nil_left,
      List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [triTouched]
  have hvs := installed_valid F bindings α hv (fun q hq =>
    ⟨(hkeep q hq).1,(hkeep q hq).2.1,(hkeep q hq).2.2.1⟩)
  have hss := installed_slots F bindings α hs hkeep
  have hvB : β.vars canonical.bBase = σ.vars triTemp := by
    simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
  have hvA : β.vars canonical.aBase = σ.vars triLeft := by
    simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
  have hvO : β.vars canonical.outBase = σ.vars triOut := by
    simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
  have hvW : β.vars workBase = σ.vars triWork := by
    simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
  have hvMod : β.vars canonical.modBase = σ.vars canonical.modBase := by
    have hh := installed_scalar bindings α canonical.modBase (fun q hq => (hkeep q hq).2.2.1)
    exact hh.trans (hRegs canonical.modBase (by decide))
  have hf₂ : Packed F B m r p β := {
    valid := hvs
    rows_eq := by simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
    inner_eq := by simp [β,bindings,triSwitchBindings,vals,install,canonical,rows,count,workBase]
    cols_eq := by
      rw [installed_scalar bindings α columns (by simp [bindings,triSwitchBindings,vals,canonical,
        columns,rows,count,workBase])]
      exact (hRegs columns (by decide)).trans h.first.cols_eq
    rows_pos := h.height_pos
    inner_pos := h.first.rows_pos
    cols_pos := h.first.cols_pos
    rows_word := h.height_word
    inner_word := h.first.rows_word
    cols_word := h.first.cols_word
    output_word := h.output_word
    exponent := hss.base.exp_word
    modulus_before := by simpa only [hvMod,hvA] using h.target_modulus
    left_before := by simpa only [hvA,hvB] using h.target_left
    right_before := by simpa only [hvB,hvO] using h.target_middle
    output_before := by simpa only [hvO,hvW] using h.target_output
    work_fit := by rw [hvW,hio.1,hSizes]; exact h.target_work }
  obtain ⟨τ,hr,htv,hts,hPr,_,_,_,hi,ho'⟩ :=
    Mathproof.Problem18P34AssemblyMatrixProduct20261003.run F β hf₂ hss hws
  refine ⟨τ,?_,htv,hts,?_,hi.trans (hio.2.1.trans hIn),ho'.trans (hio.2.2.trans hOut)⟩
  · simpa only [triProduct,Nat.add_assoc] using ha.seq (hsw.seq hr)
  have hLeft : matrix F β (σ.vars triLeft) m r = matrix F σ (σ.vars triLeft) m r := by
    apply matrix_of_cell_frame F
    intro i _ hj
    have hStart : i < σ.vars canonical.outBase := by
      rw [← h.in_temp]
      exact hj.trans_le h.target_left
    have hbefore := h.first.output_before
    have hfitFirst := h.first.work_fit
    rw [hio.1]
    exact hFrame i (by omega) (Or.inl hStart) (Or.inl (by omega))
  have hTemp : matrix F β (σ.vars triTemp) r p = matrix F α (σ.vars canonical.outBase) r p := by
    rw [h.in_temp]
    apply matrix_of_cell_frame F
    intro i _ _
    rw [hio.1]
  simpa only [hvA,hvB,hvO,hLeft,hTemp,hProd] using hPr

#print axioms triProduct_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPMatrixProductLoop20261001 (cost)
open EvenTI.CellPreparation EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.LiveAlgebra

set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Execute the chart sandwich at one live trial site from the three installed
matrix banks. The resulting row-major bank is the literal trial transporter. -/
theorem recoverTrialSite_run (F : FieldPresentation K)
    (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K) (h : ∀ p, ModeLayout (m p))
    (hw : ∀ p, (m p).n = w.width p)
    [∀ p j, Fact (((m p).blocks.get j).HasFieldModel)]
    (U V : ModeUnits K (fun i => Fin (ModeSize w m i))) (x : BranchAssignment w m)
    (i : Fin (w.sites+2)) {B S : ℕ} {s : Env}
    (hIn : TriProductInput F B S (ModeSize w m i) (ModeSize w m i) (ModeSize w m i) (ModeSize w m i) s)
    (hV : matrix F s (s.vars triLeft) (ModeSize w m i) (ModeSize w m i) = (V i).val)
    (hM : matrix F s (s.vars canonical.aBase) (ModeSize w m i) (ModeSize w m i) =
      (recoveredChartUnits w m h x i).val)
    (hU : matrix F s (s.vars canonical.bBase) (ModeSize w m i) (ModeSize w m i) = (U i).inv) :
    ∃ t, Run B triProduct s t (cost F.e (ModeSize w m i) (ModeSize w m i) (ModeSize w m i) + 13 +
        cost F.e (ModeSize w m i) (ModeSize w m i) (ModeSize w m i)) ∧
      ValidMemory F B t ∧ Slots F canonical "even.scalar.ws" S B t ∧
      (∀ j k : Fin (ModeSize w m i),
        matrix F t (s.vars triOut) (ModeSize w m i) (ModeSize w m i) j k =
          (recoverTrialSites w m h hw U V x i).val (finCongr (hw (w.mode i)) j) (finCongr (hw (w.mode i)) k)) ∧
      t.inp = s.inp ∧ t.out = s.out := by
  obtain ⟨t,hr,hMem,hS,hP,hI,hO⟩ := triProduct_run F hIn
  refine ⟨t,hr,hMem,hS,?_,hI,hO⟩
  intro j k
  rw [hP,hV,hM,hU]
  unfold recoverTrialSites
  rw [transportMatrixUnit_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  change ((V i).val * ((recoveredChartUnits w m h x i).val * (U i).inv)) j k =
    (((V i).val * (recoveredChartUnits w m h x i).val) * (U i).inv) j k
  rw [mul_assoc]

#print axioms recoverTrialSite_run
end EvenTI.P16Recover
