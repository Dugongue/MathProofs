import EvenP12RecognizeRetainedRank
import Mathproof.Meta.P15DecideIMPCost20261007

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.LiveSpectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.P15RecogIMPDot20261007 Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15RecogIMPProgram20261007 Mathproof.P15RecogIMPTail20261007
open Mathproof.P15DecideIMPEGens20261007 (hmdg ev_var ev_add ev_mul ev_div)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def retainedSrc : String := "even.retained.source"
def retainedStride : String := "even.retained.stride"

def retainedIndex : Expr :=
  let quotient := Expr.bin .div (v gU) (v retainedStride)
  let rest := Expr.bin .sub (v gU) (mul quotient (v retainedStride))
  add (v retainedSrc) <|
    add (mul (add (mul quotient (v gCols)) (v gV)) (v retainedStride)) rest

def retainedOffset (s n u j : Nat) : Nat :=
  (u / s * n + j) * s + u % s

theorem retainedOffset_lt {a s n u j : Nat} (hs : 0 < s)
    (hu : u < a*s) (hj : j < n) : retainedOffset s n u j < (a*s)*n := by
  have hq : u/s < a := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hu)
  have hrow := out_lt (o0 := 0) hq hj
  have hrem : u%s < s := Nat.mod_lt _ hs
  have hnext : (u/s*n+j+1)*s ≤ a*n*s := Nat.mul_le_mul_right _ (by omega)
  have hadd : (u/s*n+j)*s + u%s < (u/s*n+j+1)*s := by
    calc
      _ < (u/s*n+j)*s + s := Nat.add_lt_add_left hrem _
      _ = _ := by ring
  unfold retainedOffset
  exact (hadd.trans_le hnext).trans_eq (by ring)

theorem retainedIndex_eval {B a s n u j src : Nat} {τ : Env}
    (hs : 0 < s) (hu : u < a*s) (hj : j < n)
    (hsize : src + (a*s)*n < B)
    (hsrc : τ.vars retainedSrc = src) (hstride : τ.vars retainedStride = s)
    (hcols : τ.vars gCols = n) (hrow : τ.vars gU = u) (hcol : τ.vars gV = j) :
    retainedIndex.evalB B τ = some (src + retainedOffset s n u j) := by
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at hu
  have hn : 0 < n := by omega
  have has : 0 < a*s := by positivity
  have hU : a*s ≤ (a*s)*n := Nat.le_mul_of_pos_right _ hn
  have hS : s ≤ a*s := Nat.le_mul_of_pos_left _ ha
  have hN : n ≤ (a*s)*n := Nat.le_mul_of_pos_left _ has
  have hdiv : u/s ≤ u := Nat.div_le_self _ _
  have hmul : u/s*s ≤ u := Nat.div_mul_le_self _ _
  have hoff := retainedOffset_lt hs hu hj
  unfold retainedOffset at hoff
  have hm : u/s*n+j ≤ (u/s*n+j)*s := Nat.le_mul_of_pos_right _ hs
  have eu := ev_var hrow (show u < B by omega)
  have es := ev_var hstride (show s < B by omega)
  have eq := ev_div eu es (show u/s < B by omega)
  have er := ev_sub eu (ev_mul eq es (by omega)) (by omega)
  have en := ev_var hcols (show n < B by omega)
  have ej := ev_var hcol (show j < B by omega)
  have ex := ev_mul eq en (show u/s*n < B by omega)
  have eth := ev_add ex ej (show u/s*n+j < B by omega)
  have eb := ev_mul eth es (show (u/s*n+j)*s < B by omega)
  rw [hmdg] at er
  unfold retainedIndex retainedOffset
  exact ev_add (ev_var hsrc (by omega)) (ev_add eb er (by omega)) (by omega)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Move all entries from original dense order to the retained-mode row bank,
using the actual certified IMP grid and leaving the other banks intact. -/
theorem paidRetainedLoad_run (FP : FieldPresentation K)
    {a s n src dst z Sn B L : Nat} {σ : Env}
    (hs : 0 < s) (hn : 0 < n) (ha : 0 < a)
    (hLength : (a*s)*n ≤ L) (hSrcFit : src+(a*s)*n ≤ dst)
    (hDstFit : dst+(a*s)*n ≤ z) (hScratch : z+4 ≤ Sn)
    (hBound : Sn+3 < B) (hS : Slots FP canonical qN.WS Sn B σ)
    (hsrc : σ.vars retainedSrc = src) (hstride : σ.vars retainedStride = s)
    (hL : σ.vars dL = 1) (hT : σ.vars dT = z+2) (hU : σ.vars dU = z+3)
    (hZ : σ.vars dZ = z) (hOne : σ.vars rOs = z+1)
    (hRows : σ.vars gRows = a*s) (hCols : σ.vars gCols = n) (hOut : σ.vars gOut = dst)
    (hz : val FP canonical qN.WS σ z = 0)
    (ho : val FP canonical qN.WS σ (z+1) = 1) :
    ∃ τ, Run B (gridProg Mac copyAE retainedIndex) σ τ (300 * (macroBudget FP * (L+2)^4)) ∧
      Slots FP canonical qN.WS Sn B τ ∧
      (∀ u < a*s, ∀ j < n,
        val FP canonical qN.WS τ (dst + (u*n+j)) =
          val FP canonical qN.WS σ (src + retainedOffset s n u j)) ∧
      (∀ t < Sn, ¬ Written dst (a*s) n (z+2) (z+3) t →
        val FP canonical qN.WS τ t = val FP canonical qN.WS σ t) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO →
        τ.vars x = σ.vars x) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let keep := [dL,dT,dU,dZ,gRows,gCols,gOut,rOs,retainedSrc,retainedStride]
  have hk : ∀ x ∈ keep, x ∉ regNames canonical ∧ x ≠ dI ∧ x ≠ gU ∧ x ≠ gV ∧ x ≠ dO := by decide
  have has : 0 < a*s := by positivity
  have hrows : a*s ≤ (a*s)*n := Nat.le_mul_of_pos_right _ hn
  have hcols : n ≤ (a*s)*n := Nat.le_mul_of_pos_left _ has
  obtain ⟨τ,hRun,hSlots,hcopy,hframe,hvars,_,hin,hout⟩ :=
    grid_run (Mf FP) keep hk (by simp [keep]) (by simp [keep]) (by simp [keep])
      (by simp [keep]) (by simp [keep]) (by simp [keep]) (by simp [keep])
      copyAE retainedIndex (by simp [copyAE,v,VarsIn,keep])
      (by simp [retainedIndex,add,mul,v,VarsIn,keep])
      (σ := σ) (fa := fun _ _ _ => z+1) (fb := fun u j _ => src + retainedOffset s n u j)
      hS hL hT hU hZ hRows hCols hOut
      (fun σ' h _ _ _ _ _ _ _ _ _ => ev_var (by rw [h rOs (by simp [keep]),hOne]) (by omega))
      (fun σ' h _ hu _ hj _ _ hrow hcol _ =>
        retainedIndex_eval hs hu hj (by omega) (by rw [h retainedSrc (by simp [keep]),hsrc])
          (by rw [h retainedStride (by simp [keep]),hstride])
          (by rw [h gCols (by simp [keep]),hCols]) hrow hcol)
      (by intro u hu j hj t ht; refine ⟨by omega, ?_⟩; rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by intro u hu j hj t ht; have := retainedOffset_lt hs hu hj
          refine ⟨by omega, ?_⟩; rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rintro (⟨h₁,h₂⟩ | h | h) <;> omega)
      (by rintro ⟨h₁,h₂⟩; omega) (by rintro ⟨h₁,h₂⟩; omega)
      hz (by omega) (by omega) (by omega) (by omega)
  have hcost := Mathproof.P15DecideIMPCost20261007.grid4' FP copyAE retainedIndex
    (by decide) (by decide) (L := 1) (U := a*s) (V := n) (X := L+2)
    (by omega) (by omega) (by omega)
  refine ⟨τ,hRun.mono hcost,hSlots,?_,hframe,hvars,hin,hout⟩
  intro u hu j hj
  simpa only [Finset.sum_range_one,ho,one_mul] using hcopy u hu j hj

#print axioms paidRetainedLoad_run
end EvenTI.LiveSpectral
