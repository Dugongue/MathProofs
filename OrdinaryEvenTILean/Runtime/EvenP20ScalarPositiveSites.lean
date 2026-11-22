import EvenP20ScalarNativeIndex
import EvenP18ScalarStencil
import Mathproof.Meta.IMPAutoTactics20261004

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P20Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P18Scalar (stencilSitesBank)
/-- Same fixed array identity as the checked legacy source4 producer. -/
def nativeSourceLabelBank : String := "CellCRT.source4"

def nativeFreeBank : String := "even.scalar.native.free.flags"

def positiveSiteCursor : String := "even.scalar.native.positive.cursor"
def positiveSiteCount : String := "even.scalar.native.positive.count"

private def positiveSiteBody : Com :=
  .seq (.ite (.eq (.get nativeFreeBank (.var positiveSiteCursor)) (.lit 0))
    (.store stencilSitesBank (.var positiveSiteCursor) (.lit 0))
    (.store stencilSitesBank (.var positiveSiteCursor)
      (.add (.mul (.lit 2) (.get nativeSourceLabelBank (.var positiveSiteCursor))) (.lit 1))))
    (.assign positiveSiteCursor (.add (.var positiveSiteCursor) (.lit 1)))

def installPositiveSites : Com :=
  .seq (.assign positiveSiteCursor (.lit 0))
    (.while (.lt (.var positiveSiteCursor) (.var positiveSiteCount)) positiveSiteBody)

/-- Compile actual native source labels to the literal positive-copy slots
used by signed CRT recovery, while pinned blocks receive slot 0. Unused destination capacity stays unchanged. -/
theorem installPositiveSites_run {W L S : ℕ} (s : Env)
    (hTwo : 2 < W) (hL : L < W) (hCount : s.vars positiveSiteCount=L)
    (hSrc : L ≤ (s.arrs nativeSourceLabelBank).length) (hDst : L ≤ (s.arrs stencilSitesBank).length)
    (hFlags : L ≤ (s.arrs nativeFreeBank).length)
    (hFlagWords : ∀ k < L, (s.arrs nativeFreeBank).getD k 0 < W)
    (hLabels : ∀ k < L, (s.arrs nativeFreeBank).getD k 0 ≠ 0 → (s.arrs nativeSourceLabelBank).getD k 0 < S)
    (hSlots : 2*S+1 < W) :
    ∃ t, Run W installPositiveSites s t (30*L+10) ∧
      (∀ k < L, (t.arrs stencilSitesBank).getD k 0=if (s.arrs nativeFreeBank).getD k 0=0 then 0 else 2*(s.arrs nativeSourceLabelBank).getD k 0+1) ∧
      (∀ k, L ≤ k → (t.arrs stencilSitesBank).getD k 0=(s.arrs stencilSitesBank).getD k 0) ∧
      (∀ a, a ≠ stencilSitesBank → t.arrs a=s.arrs a) ∧
      (t.arrs stencilSitesBank).length=(s.arrs stencilSitesBank).length ∧
      (∀ x, x ≠ positiveSiteCursor → t.vars x=s.vars x) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  imp_vcgen [installPositiveSites]
  refine wp_for_var L 20
    (fun i u => SegInv (s.arrs stencilSitesBank) (u.arrs stencilSitesBank) 0 i
      (fun k => if (s.arrs nativeFreeBank).getD k 0=0 then 0 else 2*(s.arrs nativeSourceLabelBank).getD k 0+1))
    hL (by simp) ?_ (by imp_frame [positiveSiteBody]) (SegInv.zero _ _ _) ?_ ?_
  · simpa only [vars_setVar,show positiveSiteCount ≠ positiveSiteCursor by decide,if_false] using hCount
  · intro i hi u hSeg hIndex hFrame
    have hSource : u.arrs nativeSourceLabelBank=s.arrs nativeSourceLabelBank := hFrame.arrs _ (by imp_frame [positiveSiteBody])
    have hLength : (u.arrs stencilSitesBank).length=(s.arrs stencilSitesBank).length := hFrame.len _
    have hFlag : u.arrs nativeFreeBank=s.arrs nativeFreeBank := hFrame.arrs _ (by imp_frame [positiveSiteBody])
    have hFlagWord := hFlagWords i hi
    by_cases hz : (s.arrs nativeFreeBank).getD i 0=0
    · imp_vcgen [positiveSiteBody,hIndex,hSource,hFlag,hLength,hz]
      all_goals first
      | (intro h; exact False.elim h)
      | simpa only [Nat.zero_add] using
          (SegInv.step (v:=0) hSeg (by omega) (by simp only [hz,if_true]))
    · have hValue := hLabels i hi hz
      imp_vcgen [positiveSiteBody,hIndex,hSource,hFlag,hLength,hz]
      all_goals first
      | (intro h; exact False.elim h)
      | simpa only [Nat.zero_add] using
          (SegInv.step (v:=2*(s.arrs nativeSourceLabelBank).getD i 0+1) hSeg
            (by omega) (by simp only [hz,if_false]))
  · intro u cost hSeg _ _ hCost
    refine ⟨by omega,fun hFrame => ⟨?_,?_,?_,hFrame.len _,?_,?_,?_⟩⟩
    · simpa only [Nat.zero_add] using hSeg.inside
    · intro k hk
      exact hSeg.outside k (Or.inr (by simpa only [Nat.zero_add] using hk))
    · intro a ha
      exact hFrame.arrs a (by imp_frame [positiveSiteBody])
    · intro x hx
      exact hFrame.vars x (by imp_frame [positiveSiteBody])
    · exact hFrame.inp (by imp_frame [positiveSiteBody])
    · exact hFrame.out (by imp_frame [positiveSiteBody])

#print axioms installPositiveSites_run
end EvenTI.P20Scalar