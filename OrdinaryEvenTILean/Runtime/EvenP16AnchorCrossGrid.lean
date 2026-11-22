import EvenP16DigitAddress
import EvenP15ReciprocalProducts
import Mathproof.Meta.P15RecogIMPGrid20261007

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul ev_add ev_div)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

def crossN : String := "even.cross.n"
def crossA : String := "even.cross.a"
def crossStride : String := "even.cross.stride"
def crossSource : String := "even.cross.source"
def crossInverse : String := "even.cross.inverse"
private def crossRegs : List String :=
  [dL,dT,dU,dZ,gRows,gCols,gOut,crossN,crossA,crossStride,crossSource,crossInverse]

private def crossNExpr : Expr := .var crossN
private def crossAExpr : Expr := .var crossA
private def crossWidth : Expr := .mul crossNExpr crossAExpr
private def crossLeftExpr (x : Expr) : Expr :=
  .add (.mul (.div x crossNExpr) crossAExpr) (.div (.var dI) crossAExpr)
private def crossRightExpr (x : Expr) : Expr :=
  digitInsertExpr crossNExpr (.var crossStride) (remainderExpr x crossNExpr)
    (remainderExpr (.var dI) crossAExpr)

private def crossFrontExpr (mirror : Bool) : Expr :=
  orientedIndexExpr mirror (.var crossSource) crossWidth (crossLeftExpr (.var gU)) (crossRightExpr (.var gU))
private def crossBackExpr (mirror : Bool) : Expr :=
  orientedIndexExpr mirror (.var crossInverse) crossWidth (crossRightExpr (.var gV)) (crossLeftExpr (.var gV))

def crossLeftIndex (n a i k : ℕ) : ℕ := i/n*a+k/a
def crossRightIndex (n a b i k : ℕ) : ℕ := insertWordIndex n b (i%n) (k%a)

def crossFrontIndex (mirror : Bool) (n a b src i k : ℕ) : ℕ :=
  orientedIndex mirror src (n*a) (crossLeftIndex n a i k) (crossRightIndex n a b i k)
def crossBackIndex (mirror : Bool) (n a b src j k : ℕ) : ℕ :=
  orientedIndex mirror src (n*a) (crossRightIndex n a b j k) (crossLeftIndex n a j k)

noncomputable def crossGrid (F : FieldPresentation K) (mirror : Bool) : Com :=
  gridProg (fieldMacros F) (crossFrontExpr mirror) (crossBackExpr mirror)
noncomputable def crossGridCost (F : FieldPresentation K) (mirror : Bool) (n a : ℕ) : ℕ :=
  gridCost (fieldMacros F) (crossFrontExpr mirror) (crossBackExpr mirror) (a*a) (n*n) (n*n)

private theorem leftBound {n a i k : ℕ} (hi : i < n*n) (hk : k < a*a) : crossLeftIndex n a i k < n*a := by
  have hi' : i/n < n := Nat.div_lt_of_lt_mul hi
  have hk' : k/a < a := Nat.div_lt_of_lt_mul hk
  simpa [crossLeftIndex] using (out_lt (o0:=0) hi' hk')

private theorem rightBound {n l i k : ℕ} (hn : 0 < n) (m : Fin (l+1)) :
    crossRightIndex n (n^l) (n^(l-m.val)) i k < n*n^l := by
  rw [Nat.mul_comm n (n^l),←pow_succ]
  exact insertWordIndex_lt n l hn m (Nat.mod_lt _ hn) (Nat.mod_lt _ (pow_pos hn _))

private theorem slotBound (mirror : Bool) {a width i j cap : ℕ} (hi : i < width) (hj : j < width)
    (hFit : a+width*width ≤ cap) : orientedIndex mirror a width i j < cap := by
  cases mirror
  · exact (out_lt (o0:=a) hi hj).trans_le hFit
  · exact (out_lt (o0:=a) hj hi).trans_le hFit

/-- Existing slot-grid engine applied directly to the original and reciprocal
flattenings. The mixed-radix expressions implement the two crossed reads. -/
theorem crossGrid_run (F : FieldPresentation K) (mirror : Bool) {l n B S src inv o tt uu z : ℕ}
    {s : Env} (m : Fin (l+1)) (hn : 0 < n) (hS : Slots F canonical qN.WS S B s)
    (hWidth : n*n+1 < B) (hInner : (n^l)*(n^l)+1 < B)
    (hSrc : src+(n*n^l)*(n*n^l) ≤ S) (hInv : inv+(n*n^l)*(n*n^l) ≤ S)
    (hSrcSep : src+(n*n^l)*(n*n^l) ≤ o) (hInvSep : inv+(n*n^l)*(n*n^l) ≤ o)
    (hOut : o+(n*n)*(n*n) ≤ S) (hT : tt < S) (hU : uu < S) (hZ : z < S) (hTU : tt≠uu)
    (hTlo : tt < src ∧ tt < inv) (hUlo : uu < src ∧ uu < inv)
    (hZkeep : ¬ Written o (n*n) (n*n) tt uu z)
    (hZero : val F canonical qN.WS s z=0)
    (hR : s.vars gRows=n*n) (hC : s.vars gCols=n*n) (hL : s.vars dL=(n^l)*(n^l))
    (hO : s.vars gOut=o) (hT' : s.vars dT=tt) (hU' : s.vars dU=uu) (hZ' : s.vars dZ=z)
    (hN : s.vars crossN=n) (hA : s.vars crossA=n^l) (hStride : s.vars crossStride=n^(l-m.val))
    (hSrc' : s.vars crossSource=src) (hInv' : s.vars crossInverse=inv) :
    ∃ t, Run B (crossGrid F mirror) s t (crossGridCost F mirror n (n^l)) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i < n*n, ∀ j < n*n, val F canonical qN.WS t (o+(i*(n*n)+j)) =
        ∑ k ∈ Finset.range ((n^l)*(n^l)),
          val F canonical qN.WS s (crossFrontIndex mirror n (n^l) (n^(l-m.val)) src i k) *
          val F canonical qN.WS s (crossBackIndex mirror n (n^l) (n^(l-m.val)) inv j k)) ∧
      (∀ k < S, ¬ Written o (n*n) (n*n) tt uu k → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO → t.vars x=s.vars x) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let a := n^l
  let b := n^(l-m.val)
  have hS_B := hS.slots_word
  have ha0 : 0 < a := pow_pos hn _
  have hb0 : 0 < b := pow_pos hn _
  have hab : b ≤ a := Nat.pow_le_pow_right hn (Nat.sub_le _ _)
  have hnB : n < B := (Nat.le_mul_of_pos_right n hn).trans_lt (by omega)
  have haB : a < B := (Nat.le_mul_of_pos_right a ha0).trans_lt (by change a*a+1 < B at hInner; omega)
  have hwB : n*a < B := by
    have hp := Nat.mul_pos hn ha0
    have h := Nat.le_mul_of_pos_right (n*a) hp
    change src+(n*a)*(n*a) ≤ S at hSrc
    omega
  have hAB (r : Env) (hf : ∀ x ∈ crossRegs, r.vars x=s.vars x)
      {x : Expr} {i k : ℕ} (hi : i < n*n) (hk : k < a*a) (evI : x.evalB B r=some i)
      (hK : r.vars dI=k) :
      crossWidth.evalB B r=some (n*a) ∧
      (crossLeftExpr x).evalB B r=some (crossLeftIndex n a i k) ∧
      (crossRightExpr x).evalB B r=some (crossRightIndex n a b i k) := by
    have en := ev_var ((hf crossN (by simp [crossRegs])).trans hN) hnB
    have ea := ev_var ((hf crossA (by simp [crossRegs])).trans hA) haB
    have eb := ev_var ((hf crossStride (by simp [crossRegs])).trans hStride) (hab.trans_lt haB)
    have iB : i < B := by omega
    have kB : k < B := by change a*a+1 < B at hInner; omega
    have eK := ev_var hK kB
    have hn' : i/n < n := Nat.div_lt_of_lt_mul hi
    have ha' : k/a < a := Nat.div_lt_of_lt_mul hk
    have hLw := (leftBound hi hk).trans hwB
    have hRw := (rightBound (i:=i) (k:=k) hn m).trans hwB
    refine ⟨ev_mul en ea hwB,?_,?_⟩
    · exact ev_add (ev_mul (ev_div evI en (hn'.trans hnB)) ea (show i / n * a < B from (Nat.le_add_right _ _).trans_lt hLw))
        (ev_div eK ea (ha'.trans haB)) hLw
    · exact digitInsertExpr_eval en eb (remainderExpr_eval evI en iB) (remainderExpr_eval eK ea kB)
        hn hb0 ((Nat.mod_le _ _).trans_lt kB) hRw
  let f := crossFrontIndex mirror n a b src
  let g := crossBackIndex mirror n a b inv
  have fS {i k : ℕ} (hi : i < n*n) (hk : k < a*a) : f i k < S :=
    slotBound mirror (leftBound hi hk) (rightBound hn m) hSrc
  have gS {j k : ℕ} (hj : j < n*n) (hk : k < a*a) : g j k < S :=
    slotBound mirror (rightBound hn m) (leftBound hj hk) hInv
  have fO {i k : ℕ} (hi : i < n*n) (hk : k < a*a) : f i k < o :=
    slotBound mirror (leftBound hi hk) (rightBound hn m) hSrcSep
  have gO {j k : ℕ} (hj : j < n*n) (hk : k < a*a) : g j k < o :=
    slotBound mirror (rightBound hn m) (leftBound hj hk) hInvSep
  have fLo (i k : ℕ) : src ≤ f i k := by cases mirror <;> simp [f,crossFrontIndex,orientedIndex]
  have gLo (i k : ℕ) : inv ≤ g i k := by cases mirror <;> simp [g,crossBackIndex,orientedIndex]
  obtain ⟨t,hr,hs,hv,hf,hregs,_,hi,ho⟩ := grid_run (fieldMacros F) crossRegs (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (crossFrontExpr mirror) (crossBackExpr mirror)
    (by cases mirror <;> simp [crossFrontExpr,orientedIndexExpr,crossWidth,crossLeftExpr,crossRightExpr,
      crossNExpr,crossAExpr,digitInsertExpr,remainderExpr,crossRegs,VarsIn])
    (by cases mirror <;> simp [crossBackExpr,orientedIndexExpr,crossWidth,crossLeftExpr,crossRightExpr,
      crossNExpr,crossAExpr,digitInsertExpr,remainderExpr,crossRegs,VarsIn])
    (fa:=fun i _ k => f i k) (fb:=fun _ j k => g j k) hS hL hT' hU' hZ' hR hC hO
    (fun r h i hi _ _ k hk hri _ hrk => by
      obtain ⟨ew,el,er⟩ := hAB r h hi hk (ev_var hri (by omega)) hrk
      exact orientedIndexExpr_eval mirror (ev_var ((h _ (by decide)).trans hSrc') (by omega))
        ew el er ((fS hi hk).trans hS_B))
    (fun r h _ _ j hj k hk _ hrj hrk => by
      obtain ⟨ew,el,er⟩ := hAB r h hj hk (ev_var hrj (by omega)) hrk
      exact orientedIndexExpr_eval mirror (ev_var ((h _ (by decide)).trans hInv') (by omega))
        ew er el ((gS hj hk).trans hS_B))
    (fun i hi _ _ k hk => ⟨fS hi hk,by have := fLo i k; have := fO hi hk; unfold Written; omega⟩)
    (fun _ _ j hj k hk => ⟨gS hj hk,by have := gLo j k; have := gO hj hk; unfold Written; omega⟩)
    hOut hT hU hZ hTU hZkeep (by omega) (by omega) hZero hInner hWidth hWidth (hOut.trans_lt hS_B)
  exact ⟨t,hr,hs,hv,hf,hregs,hi,ho⟩

#print axioms crossGrid_run
end EvenTI.P16Execution