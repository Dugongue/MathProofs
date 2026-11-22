import EvenP21SiteUniformBanks

namespace EvenTI.P21Site.Mode
open scoped BigOperators
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P21Site EvenTI.P20Scalar
open EvenTI.P18Scalar (stencilSitesBank)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)

set_option autoImplicit false
set_option maxHeartbeats 650000

def rowPrefix (f : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, f j

@[simp] theorem prefix_zero (f : ℕ → ℕ) : rowPrefix f 0 = 0 := by simp [rowPrefix]
@[simp] theorem prefix_succ (f : ℕ → ℕ) (i : ℕ) : rowPrefix f (i+1) = rowPrefix f i+f i :=
  Finset.sum_range_succ f i

theorem prefix_mono (f : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : rowPrefix f i ≤ rowPrefix f j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

theorem interval_cover (f : ℕ → ℕ) (m k : ℕ) (hk : k < rowPrefix f m) :
    ∃ j < m, rowPrefix f j ≤ k ∧ k < rowPrefix f j+f j := by
  induction m with
  | zero => simp at hk
  | succ m ih =>
    by_cases h : k < rowPrefix f m
    · obtain ⟨j,hj,hl,hr⟩ := ih h
      exact ⟨j,by omega,hl,hr⟩
    · exact ⟨m,by omega,by omega,by simpa only [prefix_succ] using hk⟩

def modeBlockLimit : String := "even.site.mode.block.limit"

def advanceBlock (mult : String) : Com :=
  .seq (.assign originStart (.add (.var originStart) (.var originCount)))
    (.seq (.ite (.eq (.get mult (.var physicalBlockRow)) (.lit 1))
      (.assign globalStart (.add (.var globalStart) (.lit 1)))
      (.assign globalStart (.add (.var globalStart) (.var originCount))))
      (.assign physicalBlockRow (.add (.var physicalBlockRow) (.lit 1))))

def modeBody (widths mult : String) : Com :=
  .seq (uniformFromBanks widths mult) (advanceBlock mult)

def modeMetadata (widths mult : String) : Com :=
  .seq (.assign physicalBlockRow (.lit 0))
    (.seq (.assign originStart (.lit 0))
      (.while (.lt (.var physicalBlockRow) (.var modeBlockLimit)) (modeBody widths mult)))

/-- Single final conversion after all physical block intervals are appended. -/
def modeSites (widths mult : String) : Com :=
  .seq (modeMetadata widths mult)
    (.seq (.assign positiveSiteCount (.var originStart)) installPositiveSites)

theorem advanceBlock_run {W row width start base e : ℕ} (mult : String) (s : Env)
    (hTwo : 2 < W) (hRow : s.vars physicalBlockRow = row) (hCount : s.vars originCount = width)
    (hStart : s.vars originStart = start) (hBase : s.vars globalStart = base)
    (hRowFit : row < (s.arrs mult).length) (hMult : (s.arrs mult).getD row 0 = e)
    (hE : e < W) (hRowWord : row+1 < W) (hWidthWord : width < W)
    (hEndWord : start+width < W) (hBaseWord : base+(if e = 1 then 1 else width) < W) :
    ∃ u, Run W (advanceBlock mult) s u 30 ∧
      u.vars physicalBlockRow = row+1 ∧ u.vars originStart = start+width ∧
      u.vars globalStart = base+(if e = 1 then 1 else width) ∧ u.arrs = s.arrs ∧
      Frame (advanceBlock mult) s u := by
  by_cases he : e = 1
  · simp only [he,if_true] at hBaseWord ⊢
    imp_vcgen [advanceBlock,hRow,hCount,hStart,hBase,hMult,he]
    all_goals simp_all [he]
    all_goals omega
  · simp only [he,if_false] at hBaseWord ⊢
    imp_vcgen [advanceBlock,hRow,hCount,hStart,hBase,hMult,he]
    all_goals simp_all [he]
    all_goals omega
def nativeCount (w e : ℕ → ℕ) (j : ℕ) : ℕ := if e j = 1 then 1 else w j

structure ModePrefix (s u : Env) (w e : ℕ → ℕ) (base i : ℕ) : Prop where
  start : u.vars originStart = rowPrefix w i
  global : u.vars globalStart = base+rowPrefix (nativeCount w e) i
  done : ∀ j < i, ∀ k < w j,
    (u.arrs nativeSourceLabelBank).getD (rowPrefix w j+k) 0 = base+rowPrefix (nativeCount w e) j ∧
    (u.arrs nativeFreeBank).getD (rowPrefix w j+k) 0 = if e j = 1 then 1 else 0

/-- Complete chronological physical-block metadata loop. The input order is
literal: the width/multiplicity rows must describe the same source block order.
Native prefixes advance by one for a free block and by width for a pinned block. -/
theorem modeMetadata_run {W M off base S : ℕ} (widths mult : String) (s : Env)
    (w e : ℕ → ℕ) (hTwo : 2 < W) (hM : M < W) (hR : rowPrefix w M < W) (hS : S < W)
    (hBaseCap : base+rowPrefix (nativeCount w e) M ≤ S)
    (hOff : off+M < W)
    (hWidthFit : off+M ≤ (s.arrs widths).length) (hMultFit : M ≤ (s.arrs mult).length)
    (hWidthData : ∀ j < M, (s.arrs widths).getD (off+j) 0 = w j)
    (hMultData : ∀ j < M, (s.arrs mult).getD j 0 = e j)
    (hEWord : ∀ j < M, e j < W)
    (hL : rowPrefix w M ≤ (s.arrs nativeSourceLabelBank).length)
    (hF : rowPrefix w M ≤ (s.arrs nativeFreeBank).length)
    (hWLabel : widths ≠ nativeSourceLabelBank) (hWFlag : widths ≠ nativeFreeBank)
    (hELabel : mult ≠ nativeSourceLabelBank) (hEFlag : mult ≠ nativeFreeBank)
    (hLimit : s.vars modeBlockLimit = M) (hBase : s.vars globalStart = base)
    (hOffset : s.vars physicalWidthOffset = off) :
    ∃ u, Run W (modeMetadata widths mult) s u ((40*rowPrefix w M+104)*M+20) ∧
      ModePrefix s u w e base M ∧ Frame (modeMetadata widths mult) s u := by
  have writes : arrayWrites (modeBody widths mult) ⊆ {nativeSourceLabelBank,nativeFreeBank} := by
    change arrayWrites (modeBody "" "") ⊆ {nativeSourceLabelBank,nativeFreeBank}
    decide
  have noW : widths∉arrayWrites (modeBody widths mult) := by
    intro h
    have h' := writes h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h'
    exact h'.elim hWLabel hWFlag
  have noE : mult∉arrayWrites (modeBody widths mult) := by
    intro h
    have h' := writes h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h'
    exact h'.elim hELabel hEFlag
  imp_vcgen [modeMetadata]
  refine wp_for_var M (40*rowPrefix w M+100) (fun i u => ModePrefix s u w e base i)
    hM (by simp) ?_ (by change modeBlockLimit ∉ scalarWrites (modeBody "" ""); decide) ?_ ?_ ?_
  · simpa only [vars_setVar,show modeBlockLimit ≠ originStart by decide,
      show modeBlockLimit ≠ physicalBlockRow by decide,if_false] using hLimit
  · refine ⟨by simp,?_,?_⟩
    · simpa only [vars_setVar,show globalStart ≠ originStart by decide,
        show globalStart ≠ physicalBlockRow by decide,if_false,prefix_zero,Nat.add_zero] using hBase
    · intro j hj
      omega
  · intro i hi u inv hIndex frame
    have hiM : i+1 ≤ M := by omega
    have hWP := prefix_mono w hiM
    have hNP := prefix_mono (nativeCount w e) hiM
    have hWI : w i ≤ rowPrefix w M := by rw [prefix_succ] at hWP; omega
    have arrW : u.arrs widths = s.arrs widths := by simpa using frame.arrs widths noW
    have arrE : u.arrs mult = s.arrs mult := by simpa using frame.arrs mult noE
    have hOffU : u.vars physicalWidthOffset = off :=
      (frame.vars _ (by change physicalWidthOffset ∉ scalarWrites (modeBody "" ""); decide)).trans (by
        simpa only [vars_setVar,show physicalWidthOffset ≠ originStart by decide,
          show physicalWidthOffset ≠ physicalBlockRow by decide,if_false] using hOffset)
    have lenL : (u.arrs nativeSourceLabelBank).length = (s.arrs nativeSourceLabelBank).length := by simpa using frame.len nativeSourceLabelBank
    have lenF : (u.arrs nativeFreeBank).length = (s.arrs nativeFreeBank).length := by simpa using frame.len nativeFreeBank
    have gBound : base+rowPrefix (nativeCount w e) i ≤ S :=
      (Nat.add_le_add_left (prefix_mono (nativeCount w e) (Nat.le_of_lt hi)) base).trans hBaseCap
    obtain ⟨v,r₀,block,count⟩ := uniformFromBanks_run (width:=w i) (start:=rowPrefix w i)
      (base:=base+rowPrefix (nativeCount w e) i) (row:=i) (off:=off) (e:=e i) widths mult u
      (by omega) (hWI.trans_lt hR)
      ((prefix_mono w (Nat.le_of_lt hi)).trans_lt hR) (gBound.trans_lt hS)
      (by simpa only [prefix_succ] using hWP.trans_lt hR)
      (by rw [lenL]; exact (show rowPrefix w i+w i ≤ rowPrefix w M from by simpa only [prefix_succ] using hWP).trans hL)
      (by rw [lenF]; exact (show rowPrefix w i+w i ≤ rowPrefix w M from by simpa only [prefix_succ] using hWP).trans hF)
      inv.start inv.global hIndex hOffU (by omega) (hi.trans hM) (hEWord i hi)
      (by rw [arrW]; omega) (by rw [arrE]; omega)
      (by rw [arrW]; exact hWidthData i hi) (by rw [arrE]; exact hMultData i hi)
    have fr₀ := Frame.of_run r₀
    have vi : v.vars physicalBlockRow = i := (fr₀.vars _ (by change physicalBlockRow ∉ scalarWrites (uniformFromBanks "" ""); decide)).trans hIndex
    have vs : v.vars originStart = rowPrefix w i := (fr₀.vars _ (by change originStart ∉ scalarWrites (uniformFromBanks "" ""); decide)).trans inv.start
    have vg : v.vars globalStart = base+rowPrefix (nativeCount w e) i := (fr₀.vars _ (by change globalStart ∉ scalarWrites (uniformFromBanks "" ""); decide)).trans inv.global
    have ve : v.arrs mult = s.arrs mult := by
      have hNo : mult∉arrayWrites (uniformFromBanks widths mult) := by
        intro h
        exact noE (Finset.mem_union_left _ h)
      exact (fr₀.arrs mult hNo).trans arrE
    obtain ⟨z,r₁,zi,zs,zg,za,_⟩ := advanceBlock_run mult v hTwo vi count vs vg
      (by rw [ve]; omega) (by rw [ve]; exact hMultData i hi)
      (hEWord i hi) (hiM.trans_lt hM) (hWI.trans_lt hR)
      (by simpa only [prefix_succ] using hWP.trans_lt hR)
      (by
        have h := (Nat.add_le_add_left hNP base).trans hBaseCap
        simpa only [prefix_succ,nativeCount,Nat.add_assoc] using h.trans_lt hS)
    have bodyRun : Run W (modeBody widths mult) u z (40*rowPrefix w M+100) :=
      (r₀.seq r₁).mono (by omega)
    apply vc_of_run bodyRun
    intro cost hCost
    refine ⟨?_,zi,hCost⟩
    refine ⟨by simpa only [prefix_succ] using zs,?_,?_⟩
    · simpa only [prefix_succ,nativeCount,Nat.add_assoc] using zg
    · intro j hj k hk
      by_cases heq : j = i
      · subst j
        have hl := block.labels.inside k hk
        have hf := block.flags.inside k hk
        rw [za]
        exact ⟨hl,hf⟩
      · have hj' : j < i := by omega
        have hBefore : rowPrefix w j+k < rowPrefix w i := by
          have h := prefix_mono w (by omega : j+1 ≤ i)
          rw [prefix_succ] at h
          omega
        have hl := block.labels.outside (rowPrefix w j+k) (Or.inl hBefore)
        have hf := block.flags.outside (rowPrefix w j+k) (Or.inl hBefore)
        rw [za,hl,hf]
        exact inv.done j hj' k hk
  · intro u cost inv _ _ hCost
    have hClock : 40*rowPrefix w M+100+4 = 40*rowPrefix w M+104 := by omega
    rw [hClock] at hCost
    exact ⟨by omega,fun fr => ⟨inv,fr⟩⟩

/-- Full physical mode pass followed by one signed-site conversion. The theorem
keeps the literal archive row order; reference-order transport is a separate bridge. -/
theorem modeSites_run {W M off base S : ℕ} (widths mult : String) (s : Env)
    (w e : ℕ → ℕ) (hTwo : 2 < W) (hM : M < W) (hR : rowPrefix w M < W)
    (hBaseCap : base+rowPrefix (nativeCount w e) M ≤ S) (hSlots : 2*S+1 < W)
    (hOff : off+M < W)
    (hWidthFit : off+M ≤ (s.arrs widths).length) (hMultFit : M ≤ (s.arrs mult).length)
    (hWidthData : ∀ j < M, (s.arrs widths).getD (off+j) 0 = w j)
    (hMultData : ∀ j < M, (s.arrs mult).getD j 0 = e j)
    (hEWord : ∀ j < M, e j < W)
    (hL : rowPrefix w M ≤ (s.arrs nativeSourceLabelBank).length)
    (hF : rowPrefix w M ≤ (s.arrs nativeFreeBank).length)
    (hT : rowPrefix w M ≤ (s.arrs stencilSitesBank).length)
    (hWLabel : widths ≠ nativeSourceLabelBank) (hWFlag : widths ≠ nativeFreeBank)
    (hELabel : mult ≠ nativeSourceLabelBank) (hEFlag : mult ≠ nativeFreeBank)
    (hLimit : s.vars modeBlockLimit = M) (hBase : s.vars globalStart = base)
    (hOffset : s.vars physicalWidthOffset = off) :
    ∃ u, Run W (modeSites widths mult) s u
      ((40*rowPrefix w M+104)*M+30*rowPrefix w M+40) ∧
      (∀ j < M, ∀ k < w j, (u.arrs stencilSitesBank).getD (rowPrefix w j+k) 0 = 
        if e j = 1 then 2*(base+rowPrefix (nativeCount w e) j)+1 else 0) ∧
      u.vars positiveSiteCount = rowPrefix w M ∧
      u.vars globalStart = base+rowPrefix (nativeCount w e) M ∧
      (∀ k, rowPrefix w M ≤ k → (u.arrs stencilSitesBank).getD k 0 = (s.arrs stencilSitesBank).getD k 0) ∧
      Frame (modeSites widths mult) s u := by
  obtain ⟨u,r₀,inv,fr₀⟩ := modeMetadata_run widths mult s w e hTwo hM hR (by omega)
    hBaseCap hOff hWidthFit hMultFit hWidthData hMultData hEWord hL hF
    hWLabel hWFlag hELabel hEFlag hLimit hBase hOffset
  let R := rowPrefix w M
  let v := u.setVar positiveSiteCount R
  have r₁ : Run W (.assign positiveSiteCount (.var originStart)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨inv.start.symm,by rw [inv.start]; exact hR⟩)
  have labels : R ≤ (v.arrs nativeSourceLabelBank).length := by
    change R ≤ (u.arrs nativeSourceLabelBank).length
    rw [fr₀.len]; exact hL
  have flags : R ≤ (v.arrs nativeFreeBank).length := by
    change R ≤ (u.arrs nativeFreeBank).length
    rw [fr₀.len]; exact hF
  have sites : R ≤ (v.arrs stencilSitesBank).length := by
    change R ≤ (u.arrs stencilSitesBank).length
    rw [fr₀.len]; exact hT
  have data (k : ℕ) (hk : k < R) :
      ∃ j < M, (v.arrs nativeSourceLabelBank).getD k 0 = base+rowPrefix (nativeCount w e) j ∧
        (v.arrs nativeFreeBank).getD k 0 = if e j = 1 then 1 else 0 := by
    obtain ⟨j,hj,hl,hr⟩ := interval_cover w M k hk
    have hLocal : k-rowPrefix w j < w j := by omega
    have h := inv.done j hj (k-rowPrefix w j) hLocal
    have hi : rowPrefix w j+(k-rowPrefix w j) = k := by omega
    rw [hi] at h
    exact ⟨j,hj,h⟩
  have hFlagWords : ∀ k < R, (v.arrs nativeFreeBank).getD k 0 < W := by
    intro k hk
    obtain ⟨j,_,_,hf⟩ := data k hk
    rw [hf]
    split <;> omega
  have hLabelBounds : ∀ k < R, (v.arrs nativeFreeBank).getD k 0 ≠ 0 →
      (v.arrs nativeSourceLabelBank).getD k 0 < S := by
    intro k hk hn
    obtain ⟨j,hj,hl,hf⟩ := data k hk
    rw [hf] at hn
    have he : e j = 1 := by by_contra he; exact hn (if_neg he)
    have hp := prefix_mono (nativeCount w e) (by omega : j+1 ≤ M)
    rw [prefix_succ] at hp
    have hc : nativeCount w e j = 1 := if_pos he
    rw [hc] at hp
    rw [hl]
    omega
  obtain ⟨z,r₂,hValues,hTail,_,_,hVars,_,_⟩ := installPositiveSites_run v hTwo hR
    (by simp [v,R]) labels sites flags hFlagWords hLabelBounds hSlots
  have r : Run W (modeSites widths mult) s z
      ((40*rowPrefix w M+104)*M+30*rowPrefix w M+40) :=
    (r₀.seq (r₁.seq r₂)).mono (by omega)
  refine ⟨z,r,?_,?_,?_,?_,Frame.of_run r⟩
  · intro j hj k hk
    have hp := prefix_mono w (by omega : j+1 ≤ M)
    rw [prefix_succ] at hp
    have hi : rowPrefix w j+k < R := by dsimp [R]; omega
    have hd := inv.done j hj k hk
    rw [hValues _ hi]
    change (if (u.arrs nativeFreeBank).getD (rowPrefix w j+k) 0 = 0 then 0 else
      2*(u.arrs nativeSourceLabelBank).getD (rowPrefix w j+k) 0+1) = _
    rw [hd.1,hd.2]
    by_cases he : e j = 1 <;> simp only [he,if_true,if_false,Nat.one_ne_zero]

  · simpa only [v,vars_setVar,if_true] using hVars positiveSiteCount (by decide)
  · calc
      z.vars globalStart = v.vars globalStart := hVars globalStart (by decide)
      _ = u.vars globalStart := by simp only [v,vars_setVar,show globalStart ≠ positiveSiteCount by decide,if_false]
      _ = base+rowPrefix (nativeCount w e) M := inv.global
  · intro k hk
    have ht := hTail k hk
    have hs : u.arrs stencilSitesBank = s.arrs stencilSitesBank := fr₀.arrs _ (by change stencilSitesBank ∉ arrayWrites (modeMetadata "" ""); decide)
    change (z.arrs stencilSitesBank).getD k 0 = (u.arrs stencilSitesBank).getD k 0 at ht
    rw [hs] at ht
    exact ht
#print axioms modeSites_run
#print axioms modeMetadata_run
#print axioms advanceBlock_run
end EvenTI.P21Site.Mode
