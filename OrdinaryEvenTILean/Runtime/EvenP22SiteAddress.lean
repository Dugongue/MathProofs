import EvenP22SiteNativeKeys
import EvenP21SiteMode
import EvenP22SiteLookup

namespace EvenTI.P22Site.Address
open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.CellPreparation EvenTI.LiveAlgebra
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

set_option autoImplicit false
set_option maxHeartbeats 350000
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def widths (mode : PreparedMode K) (j : ℕ) : ℕ :=
  if h : j < mode.blocks.length then (mode.blocks.get ⟨j,h⟩).width else 0
noncomputable def multiplicities (mode : PreparedMode K) (j : ℕ) : ℕ :=
  if h : j < mode.blocks.length then (mode.blocks.get ⟨j,h⟩).factor.2 else 0

theorem native_originCount (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) (j : Fin mode.blocks.length) :
    blockOriginCount (mode.blocks.get j) =
      if (mode.blocks.get j).factor.2 = 1 then 1 else (mode.blocks.get j).width := by
  let b := mode.blocks.get j
  have ht := NativeKeys.prepareAnchorPair_tags D budget A B mode h b (List.get_mem _ _)
  have hc : blockOriginCount b = if P21Site.Prepare.isRepeated b then b.width else 1 := by
    unfold blockOriginCount P21Site.Prepare.isRepeated
    cases b.compare <;> rfl
  change blockOriginCount b = if b.factor.2 = 1 then 1 else b.width
  rw [hc,ht]
  by_cases he : b.factor.2 = 1 <;> simp [he]

/-- The already-paid metadata pass can be stopped at a matched block index;
 its global origin prefix is exactly the native semantic block prefix. -/
theorem native_prefix (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) (j : Fin mode.blocks.length) :
    P21Site.Mode.rowPrefix (P21Site.Mode.nativeCount (widths mode) (multiplicities mode)) j.val =
      P21Site.RowOrder.nativeBlockOffset mode j := by
  unfold P21Site.Mode.rowPrefix P21Site.RowOrder.nativeBlockOffset
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k.val < mode.blocks.length := lt_trans k.isLt j.isLt
  simp only [P21Site.Mode.nativeCount,widths,multiplicities,dif_pos hk']
  exact (native_originCount D budget A B mode h ⟨k.val,hk'⟩).symm

/-- No additional address table is needed: finish the checked prefix pass
 with one actual arithmetic assignment. Doubling uses addition, so no literal
 2 needs a separate word-size side condition. -/
def finish : Com := .assign Lookup.answer
  (.add (.add (.var P21Site.globalStart) (.var P21Site.globalStart)) (.lit 1))

theorem finish_run (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) (mode : PreparedMode K)
    (h : prepareAnchorPair D budget A B = some mode) (j : Fin mode.blocks.length)
    {s σ : Env} {W base : ℕ}
    (hMeta : P21Site.Mode.ModePrefix s σ (widths mode) (multiplicities mode) base j.val)
    (hword : 2*(base+P21Site.RowOrder.nativeBlockOffset mode j)+1 < W) :
    ∃ τ, Run W finish σ τ 6 ∧
      τ.vars Lookup.answer = 2*(base+P21Site.RowOrder.nativeBlockOffset mode j)+1 ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧ Frame finish σ τ := by
  have hs : σ.vars P21Site.globalStart = base+P21Site.RowOrder.nativeBlockOffset mode j := by
    rw [← native_prefix D budget A B mode h j]
    exact hMeta.global
  let a := base+P21Site.RowOrder.nativeBlockOffset mode j
  have ha : σ.vars P21Site.globalStart = a := hs
  have hh : a+a+1 = 2*(base+P21Site.RowOrder.nativeBlockOffset mode j)+1 := by dsimp [a]; omega
  have ee : (Expr.add (.add (.var P21Site.globalStart) (.var P21Site.globalStart)) (.lit 1)).evalB W σ =
      some (2*(base+P21Site.RowOrder.nativeBlockOffset mode j)+1) := by
    rw [← hh]
    exact ev_add (ev_add (ev_var ha (by omega)) (ev_var ha (by omega)) (by omega))
      (evalB_lit (by omega)) (by omega)
  let τ := σ.setVar Lookup.answer (2*(base+P21Site.RowOrder.nativeBlockOffset mode j)+1)
  have hr : Run W finish σ τ 6 := Run.assign ee
  exact ⟨τ,hr,by simp [τ],rfl,rfl,rfl,Frame.of_run hr⟩

#print axioms native_originCount
#print axioms native_prefix
#print axioms finish_run
end EvenTI.P22Site.Address


