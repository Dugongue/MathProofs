import EvenP20SweepArchive
import Primary46FactorCursor
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P20Sweep

open EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)
open Mathproof.Problem17Primary46FactorCursor (cursor)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A fixed-capacity recovery row can be used across any later call that
preserves its two blocks and its width word. -/
theorem SavedChart.frame (F : FieldPresentation K) {n row outX outR : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {s t : Env}
    (h : SavedChart F A f row outX outR s)
    (keepWidth : (t.arrs savedWidths)[row]?=(s.arrs savedWidths)[row]?)
    (keepX : ∀ k < n*n, val F canonical qN.WS t (outX+k)=val F canonical qN.WS s (outX+k))
    (keepR : ∀ k < n*n, val F canonical qN.WS t (outR+k)=val F canonical qN.WS s (outR+k)) :
    SavedChart F A f row outX outR t := by
  obtain ⟨w,xs,hw,hs,hInd,hSpan,hX,hR⟩ := h
  have idx (q : ℕ) (hq : q ≤ n) (j : Fin w) (k : Fin q) : j.val*q+k.val<n*n := by
    have hrow : j.val+1 ≤ n := (Nat.succ_le_iff.mpr j.isLt).trans hw
    have hmul := Nat.mul_le_mul hrow hq
    rw [Nat.succ_mul] at hmul
    omega
  refine ⟨w,xs,hw,keepWidth.trans hs,hInd,hSpan,?_,?_⟩
  · intro j k
    exact (keepX _ (idx n le_rfl j k)).trans (hX j k)
  · intro j hj
    rw [← hR j hj]
    apply Finset.sum_congr rfl
    intro i _
    rw [keepR _ (idx w hw j i)]

theorem SavedChart.setVar (F : FieldPresentation K) {n row outX outR : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {s : Env} {r : String}
    (h : SavedChart F A f row outX outR s) (hr : r≠qN.WS) (v : ℕ) :
    SavedChart F A f row outX outR (s.setVar r v) :=
  h.frame F rfl (fun _ _ => val_setVar F canonical hr s v _) (fun _ _ => val_setVar F canonical hr s v _)

/-- Actual factor loop, with a preserved prefix of durable chart rows.
A single per-row machine is used for every entry. -/
theorem chartFactorLoop_run (F : FieldPresentation K) {n B P m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : ℕ → Polynomial K)
    (rows bases charts : ℕ → ℕ) (count : String) (hcount : cursor≠count)
    (body : Com) (Ready : Env → Prop) {s : Env}
    (hm : s.vars count=m) (hmB : m<B) (hs : Ready s)
    (readyCursor : ∀ t i, Ready t → Ready (t.setVar cursor i))
    (step : ∀ i < m, ∀ u, Ready u → u.vars cursor=i → u.vars count=m →
      ∃ v, Run B body u v P ∧ Ready v ∧ v.vars cursor=i ∧ v.vars count=m ∧
        SavedChart F A (f i) (rows i) (bases i) (charts i) v ∧
        (∀ j < i, (v.arrs savedWidths)[rows j]?=(u.arrs savedWidths)[rows j]?) ∧
        (∀ j < i, ∀ k < n*n, val F canonical qN.WS v (bases j+k)=val F canonical qN.WS u (bases j+k)) ∧
        (∀ j < i, ∀ k < n*n, val F canonical qN.WS v (charts j+k)=val F canonical qN.WS u (charts j+k))) :
    ∃ t, Run B (forLoop cursor count body) s t ((P+8)*m+6) ∧ Ready t ∧ t.vars cursor=m ∧
      (∀ i < m, SavedChart F A (f i) (rows i) (bases i) (charts i) t) := by
  let Inv (i : ℕ) (t : Env) := Ready t ∧
    ∀ j < i, SavedChart F A (f j) (rows j) (bases j) (charts j) t
  have h0 : Inv 0 (s.setVar cursor 0) := ⟨readyCursor _ _ hs, by simp⟩
  have hstep : ∀ i < m, ∀ u, Inv i u → u.vars cursor=i → u.vars count=m →
      ∃ v, Run B body u v P ∧ v.vars cursor=i ∧ v.vars count=m ∧ Inv (i+1) (v.setVar cursor (i+1)) := by
    intro i hi u hInv hidx hlen
    obtain ⟨v,hv,hvReady,hvi,hvlen,hNew,hW,hX,hR⟩ := step i hi u hInv.1 hidx hlen
    refine ⟨v,hv,hvi,hvlen,readyCursor _ _ hvReady,?_⟩
    intro j hj
    have hcur : cursor≠qN.WS := by decide
    have hGot : SavedChart F A (f j) (rows j) (bases j) (charts j) v := by
      by_cases h : j=i
      · subst j
        exact hNew
      · have hji : j < i := by omega
        exact (hInv.2 j hji).frame F (hW j hji) (hX j hji) (hR j hji)
    exact hGot.setVar F hcur _
  obtain ⟨t,hr,hInv,hidx⟩ := forLoop_run cursor count body hcount Inv hm hmB h0 hstep
  exact ⟨t,hr,hInv.1,hidx,hInv.2⟩

end EvenTI.P20Sweep


