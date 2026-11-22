import EvenP21SiteUniform

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P21Site
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P20Scalar
open EvenTI.P18Scalar (stencilSitesBank)

def physicalBlockRow : String := "even.site.physical.row"
def physicalWidthOffset : String := "even.site.physical.width.offset"

/-- Read raw primary width and archive multiplicity. Every physical block row
gets the same source address; multiplicity one makes it free, otherwise pinned. -/
def uniformFromBanks (widths mult : String) : Com :=
  .seq (.assign originCount (.get widths (.add (.var physicalWidthOffset) (.var physicalBlockRow))))
    (.seq (.ite (.eq (.get mult (.var physicalBlockRow)) (.lit 1))
      (.assign freeValue (.lit 1)) (.assign freeValue (.lit 0))) appendUniform)

theorem uniformFromBanks_run {W width start base row off e : ℕ} (widths mult : String) (s : Env)
    (hOne : 1 < W) (hWidthWord : width < W) (hs : start < W) (hb : base < W)
    (hEndWord : start+width < W)
    (hLabels : start+width ≤ (s.arrs nativeSourceLabelBank).length)
    (hFlags : start+width ≤ (s.arrs nativeFreeBank).length)
    (hStart : s.vars originStart=start) (hBase : s.vars globalStart=base)
    (hRow : s.vars physicalBlockRow=row) (hOffset : s.vars physicalWidthOffset=off)
    (hWidthIndex : off+row < W) (hRowWord : row < W) (hEWord : e < W)
    (hWidthFit : off+row < (s.arrs widths).length) (hMultFit : row < (s.arrs mult).length)
    (hWidth : (s.arrs widths).getD (off+row) 0=width) (hMult : (s.arrs mult).getD row 0=e) :
    ∃ u, Run W (uniformFromBanks widths mult) s u (40*width+40) ∧
      UniformPrefix s u start width base (if e=1 then 1 else 0) ∧
      u.vars originCount=width := by
  let v := s.setVar originCount width
  let u := v.setVar freeValue (if e=1 then 1 else 0)
  have ex : (Expr.var physicalWidthOffset).evalB W s=some off :=
    evalB_var_iff.mpr ⟨hOffset.symm,by omega⟩
  have er : (Expr.var physicalBlockRow).evalB W s=some row :=
    evalB_var_iff.mpr ⟨hRow.symm,by rw [hRow]; exact hRowWord⟩
  have getWidth : (s.arrs widths)[off+row]?=some width := by
    simpa only [List.getElem?_eq_getElem hWidthFit,List.getD_eq_getElem _ _ hWidthFit] using congrArg some hWidth
  have r₀ : Run W (.assign originCount
      (.get widths (.add (.var physicalWidthOffset) (.var physicalBlockRow)))) s v 5 :=
    Run.assign (evalB_get (evalB_bin (op:=.add) ex er hWidthIndex) getWidth hWidthWord)
  have er' : (Expr.var physicalBlockRow).evalB W v=some row :=
    evalB_var_iff.mpr ⟨by simpa only [v,vars_setVar,show physicalBlockRow ≠ originCount by decide,if_false] using hRow.symm,by simpa only [v,vars_setVar,show physicalBlockRow ≠ originCount by decide,if_false,hRow] using hRowWord⟩
  have getMult : (v.arrs mult)[row]?=some e := by
    change (s.arrs mult)[row]?=some e
    simpa only [List.getElem?_eq_getElem hMultFit,List.getD_eq_getElem _ _ hMultFit] using congrArg some hMult
  have eg := evalB_condEq (evalB_get er' getMult hEWord) (evalB_lit hOne)
  have r₁ : Run W (.ite (.eq (.get mult (.var physicalBlockRow)) (.lit 1))
      (.assign freeValue (.lit 1)) (.assign freeValue (.lit 0))) v u 7 := by
    by_cases he : e=1
    · have guard : (Cond.eq (.get mult (.var physicalBlockRow)) (.lit 1)).evalB W v=some true := by
        simpa [he] using eg
      simpa only [u,he,if_true] using
        (Run.ite_true (d:=.assign freeValue (.lit 0)) guard
          (Run.assign (x:=freeValue) (evalB_lit hOne))).mono (by simp [Cond.size,Expr.size])
    · have guard : (Cond.eq (.get mult (.var physicalBlockRow)) (.lit 1)).evalB W v=some false := by
        simpa [he,beq_iff_eq] using eg
      simpa only [u,he,if_false] using
        (Run.ite_false (c:=.assign freeValue (.lit 1)) guard
          (Run.assign (x:=freeValue) (evalB_lit (by omega : 0<W)))).mono (by simp [Cond.size,Expr.size])
  obtain ⟨z,r₂,hPrefix,_,_,hVars,_,_,_⟩ :=
    appendUniform_run (n:=width) (start:=start) (base:=base) (flag:=if e=1 then 1 else 0) u
      hOne hWidthWord hs hb hEndWord (by split <;> omega) hLabels hFlags
      (by simpa only [u,v,vars_setVar,show originStart ≠ freeValue by decide,show originStart ≠ originCount by decide,if_false] using hStart)
      (by simpa only [u,v,vars_setVar,show globalStart ≠ freeValue by decide,show globalStart ≠ originCount by decide,if_false] using hBase)
      (by simp [u,v,vars_setVar,originCount,freeValue])
      (by simp [u,vars_setVar])
  refine ⟨z,(r₀.seq (r₁.seq r₂)).mono (by omega),⟨hPrefix.labels,hPrefix.flags⟩,?_⟩
  exact (hVars originCount (by decide)).trans (by simp [u,v,vars_setVar,originCount,freeValue])
def uniformBlockSites (widths mult : String) : Com :=
  .seq (uniformFromBanks widths mult)
    (.seq (.assign positiveSiteCount (.var originCount)) installPositiveSites)

/-- End-to-end physical block site production: raw width and multiplicity
banks are read, both metadata arrays are generated, and signed CRT site words
are installed. No supplied per-row label/free/site equality is required. -/
theorem uniformBlockSites_run {W width base row off e S : ℕ} (widths mult : String) (s : Env)
    (hTwo : 2 < W) (hWidthWord : width < W) (hb : base < W)
    (hLabels : width ≤ (s.arrs nativeSourceLabelBank).length)
    (hFlags : width ≤ (s.arrs nativeFreeBank).length)
    (hSites : width ≤ (s.arrs stencilSitesBank).length)
    (hStart : s.vars originStart=0) (hBase : s.vars globalStart=base)
    (hRow : s.vars physicalBlockRow=row) (hOffset : s.vars physicalWidthOffset=off)
    (hWidthIndex : off+row < W) (hRowWord : row < W) (hEWord : e < W)
    (hWidthFit : off+row < (s.arrs widths).length) (hMultFit : row < (s.arrs mult).length)
    (hWidth : (s.arrs widths).getD (off+row) 0=width) (hMult : (s.arrs mult).getD row 0=e)
    (hBaseBound : e=1 → base<S) (hSlots : 2*S+1 < W) :
    ∃ u, Run W (uniformBlockSites widths mult) s u (70*width+52) ∧
      (∀ k < width, (u.arrs stencilSitesBank).getD k 0=if e=1 then 2*base+1 else 0) ∧
      Frame (uniformBlockSites widths mult) s u := by
  obtain ⟨u,r₀,hPrefix,hCount⟩ := uniformFromBanks_run widths mult s (by omega) hWidthWord
    (by omega) hb (by simpa using hWidthWord) (by simpa using hLabels) (by simpa using hFlags)
    hStart hBase hRow hOffset hWidthIndex hRowWord hEWord hWidthFit hMultFit hWidth hMult
  have fr₀ := Frame.of_run r₀
  let v := u.setVar positiveSiteCount width
  have r₁ : Run W (.assign positiveSiteCount (.var originCount)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hCount.symm,by rw [hCount]; exact hWidthWord⟩)
  have hL : width ≤ (v.arrs nativeSourceLabelBank).length := by
    change width ≤ (u.arrs nativeSourceLabelBank).length
    rw [fr₀.len]; exact hLabels
  have hF : width ≤ (v.arrs nativeFreeBank).length := by
    change width ≤ (u.arrs nativeFreeBank).length
    rw [fr₀.len]; exact hFlags
  have hS : width ≤ (v.arrs stencilSitesBank).length := by
    change width ≤ (u.arrs stencilSitesBank).length
    rw [fr₀.len]; exact hSites
  have labels (k : ℕ) (hk : k<width) :
      (v.arrs nativeSourceLabelBank).getD k 0=base := by
    simpa only [v,arrs_setVar,Nat.zero_add] using hPrefix.labels.inside k hk
  have flags (k : ℕ) (hk : k<width) :
      (v.arrs nativeFreeBank).getD k 0=if e=1 then 1 else 0 := by
    simpa only [v,arrs_setVar,Nat.zero_add] using hPrefix.flags.inside k hk
  have hBounds : ∀ k < width, (v.arrs nativeFreeBank).getD k 0≠0 →
      (v.arrs nativeSourceLabelBank).getD k 0<S := by
    intro k hk hn
    rw [flags k hk] at hn
    have he : e=1 := by
      by_contra he
      exact hn (if_neg he)
    rw [labels k hk]
    exact hBaseBound he
  obtain ⟨z,r₂,hValues,_,_,_,_,_,_⟩ := installPositiveSites_run v hTwo hWidthWord
    (by simp [v]) hL hS hF (fun k hk => by rw [flags k hk]; split <;> omega) hBounds hSlots
  have r : Run W (uniformBlockSites widths mult) s z (70*width+52) :=
    (r₀.seq (r₁.seq r₂)).mono (by omega)
  refine ⟨z,r,?_,Frame.of_run r⟩
  intro k hk
  rw [hValues k hk,flags k hk,labels k hk]
  by_cases he : e=1 <;> simp only [he,if_true,if_false,Nat.one_ne_zero]

#print axioms uniformBlockSites_run
#print axioms uniformFromBanks_run
end EvenTI.P21Site
