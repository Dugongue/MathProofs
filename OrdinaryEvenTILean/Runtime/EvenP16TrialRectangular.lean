import Mathproof.Meta.P15DecideIMPEGens20261007

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P16Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)

def rectangularLeftBase : String := "even.trial.rectangular.left"
def rectangularRightBase : String := "even.trial.rectangular.right"

private def matrixAddress (base row width col : String) : Expr :=
  (Expr.var base).add (((Expr.var row).mul (.var width)).add (.var col))

private def leftExpr : Expr := matrixAddress rectangularLeftBase gU dL dI

private def rightExpr (transpose : Bool) : Expr :=
  if transpose then matrixAddress rectangularRightBase gV dL dI
  else matrixAddress rectangularRightBase dI gCols gV

def rightIndex (transpose : Bool) (base k r t j : ℕ) : ℕ :=
  base+(if transpose then j*k+t else t*r+j)

variable {K : Type} [Field K] [Fintype K]

noncomputable def rectangularProduct (F : FieldPresentation K) (transpose : Bool) : Com :=
  gridProg (fieldMacros F) leftExpr (rightExpr transpose)

noncomputable def rectangularCost (F : FieldPresentation K) (transpose : Bool)
    (rows inner cols : ℕ) : ℕ :=
  gridCost (fieldMacros F) leftExpr (rightExpr transpose) inner rows cols

private def keep : List String := [dL,dT,dU,dZ,gRows,gCols,gOut,rectangularLeftBase,rectangularRightBase]

private theorem matrixAddress_eval {B a i n j : ℕ} {σ : Env} {ra ri rn rj : String}
    (ha : σ.vars ra=a) (hi : σ.vars ri=i) (hn : σ.vars rn=n) (hj : σ.vars rj=j)
    (hnB : n < B) (hiB : i < B) (hB : a+(i*n+j) < B) :
    (matrixAddress ra ri rn rj).evalB B σ=some (a+(i*n+j)) := by
  have ei := ev_var hi hiB
  have en := ev_var hn hnB
  have ej := ev_var hj (show j < B by omega)
  have ea := ev_var ha (show a < B by omega)
  exact ev_add ea (ev_add (ev_mul ei en (by omega)) ej (by omega)) hB

/-- Paid normal and transpose-right matrix products with the same field-slot
ABI as the kernel and projection machinery. The two input banks persist. -/
theorem rectangularProduct_run (F : FieldPresentation K) (transpose : Bool)
    {m k r a b o z t u Sn B : ℕ} {σ : Env}
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hLeft : a+m*k ≤ o)
    (hRight : b+(if transpose then r*k else k*r) ≤ o)
    (hFit : o+m*r ≤ Sn)
    (hT : t < Sn) (hU : u < Sn) (hTU : t ≠ u)
    (hTS : o+m*r ≤ t ∨ (t < a ∧ t < b)) (hUS : o+m*r ≤ u ∨ (u < a ∧ u < b))
    (hZ : z < Sn) (hZguard : ¬ Written o m r t u z)
    (hZero : val F canonical qN.WS σ z=0)
    (hWords : m+1 < B ∧ k+1 < B ∧ r+1 < B)
    (hl : σ.vars dL=k) (ht : σ.vars dT=t) (hu : σ.vars dU=u)
    (hz : σ.vars dZ=z) (hm : σ.vars gRows=m) (hr : σ.vars gCols=r)
    (ho : σ.vars gOut=o)
    (ha : σ.vars rectangularLeftBase=a) (hb : σ.vars rectangularRightBase=b) :
    ∃ τ, Run B (rectangularProduct F transpose) σ τ (rectangularCost F transpose m k r) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ i < m, ∀ j < r,
        val F canonical qN.WS τ (o+(i*r+j)) =
          ∑ x ∈ Finset.range k, val F canonical qN.WS σ (a+(i*k+x)) *
            val F canonical qN.WS σ (rightIndex transpose b k r x j)) ∧
      (∀ s < Sn, ¬ Written o m r t u s → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO → τ.vars x=σ.vars x) ∧
      (∀ x, x ≠ canonical.mem → x ≠ canonical.scratch → τ.arrs x=σ.arrs x) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
  have hMem := hSlots.slots_word
  have hAStart : a ≤ o := by omega
  have hBStart : b ≤ o := by cases transpose <;> simpa using Nat.le_trans (Nat.le_add_right b _) hRight
  have hLeft' (i x : ℕ) (hi : i < m) (hx : x < k) : a+(i*k+x) < o :=
    (out_lt hi hx).trans_le hLeft
  have hRight' (x j : ℕ) (hx : x < k) (hj : j < r) : rightIndex transpose b k r x j < o := by
    cases transpose
    · exact (out_lt hx hj).trans_le hRight
    · exact (out_lt hj hx).trans_le hRight
  apply grid_run (fieldMacros F) keep (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) leftExpr (rightExpr transpose)
    (by simp [leftExpr,matrixAddress,VarsIn,keep])
    (by cases transpose <;> simp [rightExpr,matrixAddress,VarsIn,keep])
    hSlots hl ht hu hz hm hr ho
    (fa := fun i _ x => a+(i*k+x)) (fb := fun _ j x => rightIndex transpose b k r x j)
  · intro τ hk i hi j hj x hx hi' hj' hx'
    apply matrixAddress_eval ((hk _ (by decide)).trans ha) hi' ((hk _ (by decide)).trans hl) hx'
      (by omega) (by omega)
    have h := hLeft' i x hi hx
    omega
  · intro τ hk i hi j hj x hx hi' hj' hx'
    have hh := hRight' x j hx hj
    cases transpose
    · exact matrixAddress_eval ((hk _ (by decide)).trans hb) hx' ((hk _ (by decide)).trans hr) hj'
        (by omega) (by omega) (show rightIndex false b k r x j < B by omega)
    · exact matrixAddress_eval ((hk _ (by decide)).trans hb) hj' ((hk _ (by decide)).trans hl) hx'
        (by omega) (by omega) (show rightIndex true b k r x j < B by omega)
  · intro i hi j hj x hx
    have hh := hLeft' i x hi hx
    refine ⟨by omega,?_⟩
    rintro (⟨_,_⟩ | he | he) <;> omega
  · intro i hi j hj x hx
    have hh := hRight' x j hx hj
    have hLow : b ≤ rightIndex transpose b k r x j := by unfold rightIndex; omega
    refine ⟨by omega,?_⟩
    rintro (⟨_,_⟩ | he | he) <;> omega
  · exact hFit
  · exact hT
  · exact hU
  · exact hZ
  · exact hTU
  · exact hZguard
  · omega
  · omega
  · exact hZero
  · exact hWords.2.1
  · exact hWords.1
  · exact hWords.2.2
  · omega

#print axioms rectangularProduct_run
end EvenTI.P16Trial