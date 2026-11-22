import EvenP21SiteAppend
import Mathproof.Meta.IMPAutoTactics20261004

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P21Site
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P20Scalar (nativeSourceLabelBank nativeFreeBank)

private def uniformBody : Com :=
  .seq (.store nativeSourceLabelBank (.add (.var originStart) (.var originCursor))
      (.var globalStart))
    (.seq (.store nativeFreeBank (.add (.var originStart) (.var originCursor)) (.var freeValue))
      (.assign originCursor (.add (.var originCursor) (.lit 1))))

def appendUniform : Com :=
  .seq (.assign originCursor (.lit 0))
    (.while (.lt (.var originCursor) (.var originCount)) uniformBody)

structure UniformPrefix (s u : Env) (start n base flag : ℕ) : Prop where
  labels : SegInv (s.arrs nativeSourceLabelBank) (u.arrs nativeSourceLabelBank)
    start n (fun _ => base)
  flags : SegInv (s.arrs nativeFreeBank) (u.arrs nativeFreeBank) start n (fun _ => flag)

/-- Repeat one native label and fixed/free word across the physical rows of a
block. A simple block has one free field origin; repeated-block rows are pinned.
Existing records outside the append interval and every raw bank survive. -/
theorem appendUniform_run {W n start base flag : ℕ} (s : Env)
    (hOne : 1 < W) (hn : n < W) (hs : start < W) (hb : base < W)
    (hEndWord : start+n < W) (hFlag : flag < W)
    (hLabels : start+n ≤ (s.arrs nativeSourceLabelBank).length)
    (hFlags : start+n ≤ (s.arrs nativeFreeBank).length)
    (hStart : s.vars originStart=start) (hBase : s.vars globalStart=base)
    (hCount : s.vars originCount=n) (hFree : s.vars freeValue=flag) :
    ∃ u, Run W appendUniform s u (40*n+10) ∧ UniformPrefix s u start n base flag ∧
      (∀ a, a ≠ nativeSourceLabelBank → a ≠ nativeFreeBank → u.arrs a=s.arrs a) ∧
      (∀ a, (u.arrs a).length=(s.arrs a).length) ∧
      (∀ x, x ≠ originCursor → u.vars x=s.vars x) ∧
      u.inp=s.inp ∧ u.out=s.out ∧ u.vars originCursor=n := by
  imp_vcgen [appendUniform]
  refine wp_for_var n 30 (fun i u => UniformPrefix s u start i base flag)
    hn (by simp) ?_ (by imp_frame [uniformBody])
    ⟨SegInv.zero _ _ _,SegInv.zero _ _ _⟩ ?_ ?_
  · simpa only [vars_setVar,show originCount ≠ originCursor by decide,if_false] using hCount
  · intro i hi u hSeg hIndex hFrame
    have hS : u.vars originStart=start := (hFrame.vars _ (by imp_frame [uniformBody])).trans
      (by simpa only [vars_setVar,show originStart ≠ originCursor by decide,if_false] using hStart)
    have hB : u.vars globalStart=base := (hFrame.vars _ (by imp_frame [uniformBody])).trans
      (by simpa only [vars_setVar,show globalStart ≠ originCursor by decide,if_false] using hBase)
    have hF : u.vars freeValue=flag := (hFrame.vars _ (by imp_frame [uniformBody])).trans
      (by simpa only [vars_setVar,show freeValue ≠ originCursor by decide,if_false] using hFree)
    have hLL : (u.arrs nativeSourceLabelBank).length=(s.arrs nativeSourceLabelBank).length := by simpa using hFrame.len nativeSourceLabelBank
    have hFL : (u.arrs nativeFreeBank).length=(s.arrs nativeFreeBank).length := by simpa using hFrame.len nativeFreeBank
    imp_vcgen [uniformBody,hIndex,hS,hB,hF,hLL,hFL]
    refine ⟨?_,?_⟩
    · exact hSeg.labels.step (by omega) rfl
    · exact hSeg.flags.step (by omega) rfl
  · intro u cost hSeg hIndex _ hCost
    refine ⟨by omega,fun hFrame => ⟨hSeg,?_,?_,?_,?_,?_,hIndex⟩⟩
    · intro a h₁ h₂
      exact hFrame.arrs a (by imp_frame [uniformBody])
    · exact hFrame.len
    · intro x hx
      exact hFrame.vars x (by imp_frame [uniformBody])
    · exact hFrame.inp (by imp_frame [uniformBody])
    · exact hFrame.out (by imp_frame [uniformBody])


#print axioms appendUniform_run
end EvenTI.P21Site
