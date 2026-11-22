import EvenP22PadAppend
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 1250000

namespace EvenTI.P22Pad

open EvenTI.P20Sweep
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Widths in literal archived order, with the physical column start of each. -/
def columnStart (width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => columnStart width i + width i

theorem columnStart_mono (width : ℕ → ℕ) : Monotone (columnStart width) :=
  monotone_nat_of_le_succ (fun _ => Nat.le_add_right _ _)

noncomputable def packArchiveColumns : Com :=
  .seq (.assign framePrefix (.lit 0)) (forLoop frameCursor frameCount appendFrameBlock)

noncomputable def packArchiveColumnsCost (F : FieldPresentation K) (n m : ℕ) : ℕ :=
  2+((appendFrameBlockCost F (n*n)+8)*m+6)

theorem appendFrameBlockCost_mono (F : FieldPresentation K) :
    Monotone (appendFrameBlockCost F) := by
  intro a b hab
  unfold appendFrameBlockCost Mathproof.P15DecideIMPCopy20261007.copyCost
    Mathproof.P15RecogIMPGrid20261007.gridCost Mathproof.P15RecogIMPGrid20261007.rowStep
  gcongr

structure ArchivePorts (s : Env) (n off m base stride target Z : ℕ) : Prop where
  size : s.vars savedAmbientSize=n
  start : s.vars savedOffset=off
  count : s.vars frameCount=m
  bank : s.vars savedBank=base
  step : s.vars savedStride=stride
  dest : s.vars frameTemp=target
  zero : s.vars dZ=Z
  one : s.vars rOs=Z+1
  tmp₀ : s.vars dT=Z+2
  tmp₁ : s.vars dU=Z+3

private theorem ArchivePorts.ofAppendFrame {s t : Env} {n off m base stride target Z : ℕ}
    (p : ArchivePorts s n off m base stride target Z)
    (h : Frame appendFrameBlock s t) : ArchivePorts t n off m base stride target Z :=
  ⟨(h.vars _ (by decide)).trans p.size, (h.vars _ (by decide)).trans p.start,
   (h.vars _ (by decide)).trans p.count, (h.vars _ (by decide)).trans p.bank,
   (h.vars _ (by decide)).trans p.step, (h.vars _ (by decide)).trans p.dest,
   (h.vars _ (by decide)).trans p.zero, (h.vars _ (by decide)).trans p.one,
   (h.vars _ (by decide)).trans p.tmp₀, (h.vars _ (by decide)).trans p.tmp₁⟩

private theorem ArchivePorts.cursor {s : Env} {n off m base stride target Z : ℕ}
    (p : ArchivePorts s n off m base stride target Z) (j : ℕ) :
    ArchivePorts (s.setVar frameCursor j) n off m base stride target Z :=
  ⟨p.size,p.start,p.count,p.bank,p.step,p.dest,p.zero,p.one,p.tmp₀,p.tmp₁⟩

private theorem ArchivePorts.prefix {s : Env} {n off m base stride target Z : ℕ}
    (p : ArchivePorts s n off m base stride target Z) (j : ℕ) :
    ArchivePorts (s.setVar framePrefix j) n off m base stride target Z :=
  ⟨p.size,p.start,p.count,p.bank,p.step,p.dest,p.zero,p.one,p.tmp₀,p.tmp₁⟩

/-- Reads and copies every archived factor basis. The literal concatenation
uses the widths found in memory, in the unchanged archived row order. -/
theorem packArchiveColumns_run (F : FieldPresentation K)
    {W S n off m base stride target Z : ℕ} {s : Env} (width : ℕ → ℕ)
    (hs : Slots F canonical qN.WS S W s)
    (p : ArchivePorts s n off m base stride target Z)
    (hw : ∀ i < m, (s.arrs savedWidths)[off+i]?=some (width i))
    (hSum : columnStart width m=n) (hn : n < W) (hm : m < W)
    (hi : ∀ i < m, off+i < W) (hst : stride < W)
    (hSource : ∀ i < m, base+(off+i)*stride+width i*n ≤ target)
    (hTarget : target+n*n ≤ Z) (hZ : Z+4 ≤ S) (hW : S+10 < W)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t cost, Run W packArchiveColumns s t cost ∧ cost ≤ packArchiveColumnsCost F n m ∧
      Slots F canonical qN.WS S W t ∧ ArchivePorts t n off m base stride target Z ∧
      t.vars framePrefix=n ∧ (t.arrs savedWidths)=(s.arrs savedWidths) ∧
      (∀ j < m, ∀ k < width j*n, val F canonical qN.WS t (target+columnStart width j*n+k)=
        val F canonical qN.WS s (base+(off+j)*stride+k)) ∧
      (∀ k < S, (k < target ∨ target+n*n ≤ k) → k≠Z+2 → k≠Z+3 →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame packArchiveColumns s t := by
  let s₀ := s.setVar framePrefix 0
  have r₀ : Run W (.assign framePrefix (.lit 0)) s s₀ 2 :=
    Run.assign (evalB_lit (show 0 < W by omega))
  have hCur : frameCursor≠qN.WS := by decide
  let Inv (i : ℕ) (u : Env) :=
    Slots F canonical qN.WS S W u ∧ ArchivePorts u n off m base stride target Z ∧
      u.vars framePrefix=columnStart width i ∧ u.arrs savedWidths=s.arrs savedWidths ∧
      (∀ j < i, ∀ k < width j*n,
        val F canonical qN.WS u (target+columnStart width j*n+k)=
          val F canonical qN.WS s (base+(off+j)*stride+k)) ∧
      (∀ k < S, (k < target ∨ target+columnStart width i*n ≤ k) → k≠Z+2 → k≠Z+3 →
        val F canonical qN.WS u k=val F canonical qN.WS s k)
  have h₀ : Inv 0 (s₀.setVar frameCursor 0) := by
    refine ⟨Slots.setVar F canonical (Slots.setVar F canonical hs (by decide) (by decide) 0)
      (by decide) (by decide) 0,(p.prefix 0).cursor 0,rfl,rfl,?_,?_⟩
    · simp
    · intro k _ _ _ _
      rw [val_setVar F canonical hCur,val_setVar F canonical (by decide)]
  have hstep : ∀ i < m, ∀ u, Inv i u → u.vars frameCursor=i → u.vars frameCount=m →
      ∃ v, Run W appendFrameBlock u v (appendFrameBlockCost F (n*n)) ∧
        v.vars frameCursor=i ∧ v.vars frameCount=m ∧ Inv (i+1) (v.setVar frameCursor (i+1)) := by
    intro i him u hInv hidx _
    obtain ⟨hU,pu,hpr,hwr,hMade,hKeep⟩ := hInv
    have hCol : columnStart width (i+1) ≤ n := by
      rw [← hSum]
      apply columnStart_mono width
      omega
    have hCol' : columnStart width i ≤ n :=
      (columnStart_mono width (Nat.le_succ _)).trans hCol
    have hColW : columnStart width i+width i < W := lt_of_le_of_lt hCol hn
    have hWid : width i ≤ n := (Nat.le_add_left _ _).trans hCol
    have hT : target+(columnStart width i+width i)*n ≤ Z :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCol) _).trans hTarget
    have hT' : target+columnStart width i*n ≤ Z :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hCol') _).trans hTarget
    have hZu : val F canonical qN.WS u Z=0 :=
      (hKeep _ (by omega) (Or.inr hT') (by omega) (by omega)).trans hz
    have hOu : val F canonical qN.WS u (Z+1)=1 :=
      (hKeep _ (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans ho
    obtain ⟨v,r,hV,hpr',hCopy,hOutside,hFr⟩ := appendFrameBlock_run F hU
      ⟨pu.size,pu.start,hidx,pu.bank,pu.step,pu.dest,hpr,pu.zero,pu.one,pu.tmp₀,pu.tmp₁⟩
      (by rw [hwr]; exact hw i him) hn (hi i him) hst (hWid.trans_lt hn) hColW (hSource i him)
      hT hZ hW hZu hOu
    have pv := pu.ofAppendFrame hFr
    refine ⟨v,r.mono (appendFrameBlockCost_mono F (Nat.mul_le_mul_right _ hWid)),
      (hFr.vars _ (by decide)).trans hidx,pv.count,
      Slots.setVar F canonical hV (by decide) (by decide) _,pv.cursor _,hpr',
      (hFr.arrs _ (by decide)).trans hwr,?_,?_⟩
    · intro j hj k hk
      rw [val_setVar F canonical hCur]
      by_cases eq : j=i
      · subst j
        have hsAddr : base+(off+i)*stride+k < target := by have := hSource i him; omega
        exact (hCopy k hk).trans (hKeep _ (by omega) (Or.inl hsAddr) (by omega) (by omega))
      · have hji : j < i := by omega
        have hlo : columnStart width (j+1) ≤ columnStart width i := columnStart_mono width (by omega)
        have hm' := Nat.mul_le_mul_right n hlo
        change (columnStart width j+width j)*n ≤ columnStart width i*n at hm'
        rw [Nat.add_mul] at hm'
        have hCopyAddr : target+columnStart width j*n+k < target+columnStart width i*n := by omega
        exact (hOutside _ (by omega) (Or.inl hCopyAddr) (by omega) (by omega)).trans (hMade j hji k hk)
    · intro k hk hOut hk₀ hk₁
      rw [val_setVar F canonical hCur]
      have hGrow : target+columnStart width i*n ≤ target+columnStart width (i+1)*n :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (columnStart_mono width (Nat.le_succ _))) _
      have hOut' : k < target+columnStart width i*n ∨ target+(columnStart width i+width i)*n ≤ k := by
        change k < target ∨ target+(columnStart width i+width i)*n ≤ k at hOut
        omega
      have hKeep' : k < target ∨ target+columnStart width i*n ≤ k :=
        hOut.elim Or.inl (fun h => Or.inr (hGrow.trans h))
      exact (hOutside k hk hOut' hk₀ hk₁).trans (hKeep k hk hKeep' hk₀ hk₁)
  obtain ⟨t,r,hI,_⟩ := forLoop_run frameCursor frameCount appendFrameBlock (by decide)
    Inv (show s₀.vars frameCount=m from (p.prefix 0).count) hm h₀ hstep
  obtain ⟨ht,pt,hPr,hSaved,hCopy,hKeep⟩ := hI
  have hr := r₀.seq r
  exact ⟨t,_,hr,le_rfl,ht,pt,hPr.trans hSum,hSaved,hCopy,
    fun k hk hout h1 h2 => hKeep k hk (by rw [hSum]; exact hout) h1 h2,Frame.of_run hr⟩

#print axioms packArchiveColumns_run
end EvenTI.P22Pad

