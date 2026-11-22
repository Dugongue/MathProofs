import EvenP12CompareLiveCRTRow
import EvenP12CompareLiveCRTInstall

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithWeight20261007 (productRowR)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

set_option maxHeartbeats 3000000
set_option maxRecDepth 25000

private def RowPrefix {l : ℕ} (f : Fin l → ℕ) (k : ℕ) (xs : List ℕ) : Prop :=
  xs.length = l ∧ ∀ i : Fin l, i.val < k → xs[i.val]? = some (f i)

private theorem RowPrefix.set {l : ℕ} {f : Fin l → ℕ} {xs : List ℕ}
    (j : Fin l) (h : RowPrefix f j.val xs) : RowPrefix f (j.val+1) (xs.set j.val (f j)) := by
  refine ⟨by simp [h.1],fun i hi => ?_⟩
  by_cases hij : i.val = j.val
  · have hh : i = j := Fin.ext hij
    subst i
    exact List.getElem?_set_self (by rw [h.1]; exact j.isLt)
  · rw [List.getElem?_set_ne (Ne.symm hij)]
    exact h.2 i (by omega)

private theorem RowPrefix.full {l : ℕ} {f : Fin l → ℕ} {xs : List ℕ}
    (h : RowPrefix f l xs) : xs = List.ofFn f := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < l
  · exact (h.2 ⟨j,hj⟩ hj).trans (by simp [hj])
  · rw [List.getElem?_eq_none (by rw [h.1]; omega)]
    simp [hj]

private def storeSmithRow : Com :=
  .seq (.store coefficientBank (.var productRowR) (.var rowCoefficient))
    (.seq (.store targetBank (.var productRowR) (.var rowTarget))
      (.store modulusBank (.var productRowR) (.var rowModulus)))

private def advanceSmithRow : Com := .assign productRowR (.add (.var productRowR) (.lit 1))
private def smithRowStep : Com := .seq loadSmithRow (.seq storeSmithRow advanceSmithRow)
private def smithRowGuard : Cond := .lt (.var productRowR) (.var rowsR)
private def initSmithRows : Com := .seq (.assign productRowR (.lit 0)) (.assign crtRows (.var rowsR))
def populateSmithCRT : Com := .seq initSmithRows (.while smithRowGuard smithRowStep)
def populateSmithCRTCost (M m : ℕ) : ℕ := (loadSmithRowCost M m+28)*(m+1)+12

private def RowTables {l : ℕ} (f : Fin l → UnaryEquation) (k : ℕ) (σ : Env) : Prop :=
  RowPrefix (fun j => (f j).coefficient) k (σ.arrs coefficientBank) ∧
  RowPrefix (fun j => (f j).value) k (σ.arrs targetBank) ∧
  RowPrefix (fun j => (f j).modulus) k (σ.arrs modulusBank)

private theorem storeSmithRow_run {l W : ℕ} {σ : Env} (f : Fin l → UnaryEquation)
    (r : Fin l) (hr : σ.vars productRowR = r.val) (hlW : l < W)
    (ha : σ.vars rowCoefficient = (f r).coefficient) (haW : (f r).coefficient < W)
    (hb : σ.vars rowTarget = (f r).value) (hbW : (f r).value < W)
    (hd : σ.vars rowModulus = (f r).modulus) (hdW : (f r).modulus < W)
    (h : RowTables f r.val σ) :
    ∃ τ, Run W storeSmithRow σ τ 9 ∧ RowTables f (r.val+1) τ ∧ Frame storeSmithRow σ τ := by
  let e := f r
  have hrW := r.isLt.trans hlW
  let σ₁ := σ.setArr coefficientBank r.val e.coefficient
  let σ₂ := σ₁.setArr targetBank r.val e.value
  let τ := σ₂.setArr modulusBank r.val e.modulus
  have r0 : Run W (.store coefficientBank (.var productRowR) (.var rowCoefficient)) σ σ₁ 3 :=
    Run.store (ev_var hr hrW) (ev_var ha haW) (by rw [h.1.1]; exact r.isLt)
  have r1 : Run W (.store targetBank (.var productRowR) (.var rowTarget)) σ₁ σ₂ 3 :=
    Run.store (ev_var hr hrW) (ev_var hb hbW)
      (by simpa [σ₁,arrs_setArr,show targetBank ≠ coefficientBank by decide] using
        (show r.val < (σ.arrs targetBank).length by rw [h.2.1.1]; exact r.isLt))
  have r2 : Run W (.store modulusBank (.var productRowR) (.var rowModulus)) σ₂ τ 3 :=
    Run.store (ev_var hr hrW) (ev_var hd hdW)
      (by simpa [σ₁,σ₂,arrs_setArr,show modulusBank ≠ targetBank by decide,
          show modulusBank ≠ coefficientBank by decide] using (show r.val < (σ.arrs modulusBank).length by rw [h.2.2.1]; exact r.isLt))
  have run : Run W storeSmithRow σ τ 9 := r0.seq (r1.seq r2)
  refine ⟨τ,run,⟨?_,?_,?_⟩,Frame.of_run run⟩
  · simpa [τ,σ₂,σ₁,arrs_setArr,show coefficientBank ≠ modulusBank by decide,
      show coefficientBank ≠ targetBank by decide,e] using RowPrefix.set r h.1
  · simpa [τ,σ₂,σ₁,arrs_setArr,show targetBank ≠ modulusBank by decide,
      show targetBank ≠ coefficientBank by decide,e] using RowPrefix.set r h.2.1
  · simpa [τ,σ₂,σ₁,arrs_setArr,show modulusBank ≠ targetBank by decide,
      show modulusBank ≠ coefficientBank by decide,e] using RowPrefix.set r h.2.2

theorem coordinateEquations_words {M m n : ℕ} [NeZero M]
    (st : ZDiag.State M (m+1) n) (b : Fin m → ZMod M)
    (j : Fin (coordinateEquations st.B st.U b).length) :
    let e := (coordinateEquations st.B st.U b).get j
    e.coefficient ≤ M ∧ e.value ≤ M ∧ 0 < e.modulus ∧ e.modulus ∣ M := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  let i : Fin (m+1) := ⟨j.val,by simpa [coordinateEquations] using j.isLt⟩
  have he : (coordinateEquations st.B st.U b).get j = coordinateEquation st.B st.U b i := by
    exact List.getElem_ofFn (f := coordinateEquation st.B st.U b) j.isLt
  rw [he]
  exact ⟨(ZMod.val_lt _).le,Nat.sub_le ..,Nat.gcd_pos_of_pos_right _ hM,Nat.gcd_dvd_right ..⟩

/-- Materialize all unary equations by reading the live Smith banks and the
retained original right-hand side. The caller reserves three rows-sized arrays. -/
theorem populateSmithCRT_run {M m n W : ℕ} [NeZero M] {σ : Env}
    (st : ZDiag.State M (m+1) n) (b : Fin m → ZMod M)
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+2 < W) (hW : 4*M*M+4*M+10 < W)
    (h : CRTSmithInput st b σ) (hc : ZDiag.Clr (min (m+1) n) st.B)
    (hLen₁ : (σ.arrs coefficientBank).length = m+1)
    (hLen₂ : (σ.arrs targetBank).length = m+1)
    (hLen₃ : (σ.arrs modulusBank).length = m+1) :
    ∃ τ, Run W populateSmithCRT σ τ (populateSmithCRTCost M m) ∧
      CRTInputs (coordinateEquations st.B st.U b) τ ∧
      CRTSmithInput st b τ ∧ Frame populateSmithCRT σ τ := by
  let f := coordinateEquation st.B st.U b
  let I (τ : Env) := CRTSmithInput st b τ ∧ τ.vars crtRows = m+1 ∧
    τ.vars productRowR ≤ m+1 ∧ RowTables f (τ.vars productRowR) τ
  let V (τ : Env) := m+1-τ.vars productRowR
  have hmW : m+1 < W := by omega
  have hMW : M < W := by omega
  have hg (τ : Env) (hτ : I τ) : smithRowGuard.evalB W τ =
      some (decide (τ.vars productRowR < m+1)) := by
    exact evalB_condLt (ev_var rfl (hτ.2.2.1.trans_lt hmW)) (ev_var hτ.1.1 hmW)
  have hs (τ : Env) (hτ : I τ) (hgo : smithRowGuard.evalB W τ = some true) :
      ∃ ξ, Run W smithRowStep τ ξ (loadSmithRowCost M m+24) ∧ I ξ ∧ V ξ < V τ := by
    rw [hg τ hτ] at hgo
    have hi : τ.vars productRowR < m+1 := by simpa using hgo
    let r : Fin (m+1) := ⟨_,hi⟩
    obtain ⟨ρ,r0,hInput,hR,hA,hB,hD,hF⟩ := loadSmithRow_run st b r hL hW hτ.1 rfl hc
    have hData : RowTables f r.val ρ := by
      unfold RowTables
      rw [hF.arrs coefficientBank (by decide),hF.arrs targetBank (by decide),hF.arrs modulusBank (by decide)]
      exact hτ.2.2.2
    have hA' : (f r).coefficient < W := (ZMod.val_lt _).trans hMW
    have hB' : (f r).value < W := (Nat.sub_le ..).trans_lt hMW
    have hD' : (f r).modulus < W :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.gcd_dvd_right _ M)).trans_lt hMW
    obtain ⟨η,r1,hTable,hF1⟩ := storeSmithRow_run f r hR hmW hA hA' hB hB' hD hD' hData
    have hRowη : η.vars productRowR = r.val := (hF1.vars _ (by decide)).trans hR
    let ξ := η.setVar productRowR (r.val+1)
    have hRowW : r.val+1 < W := (Nat.succ_le_of_lt r.isLt).trans_lt hmW
    have r2 : Run W advanceSmithRow η ξ 4 := Run.assign
      (ev_add (ev_var hRowη (r.isLt.trans hmW)) (evalB_lit (n := 1) (by omega)) hRowW)
    have rr : Run W smithRowStep τ ξ (loadSmithRowCost M m+24) :=
      (r0.seq (r1.seq r2)).mono (by omega)
    have ff := Frame.of_run rr
    have hRowξ : ξ.vars productRowR = r.val+1 := by simp [ξ]
    refine ⟨ξ,rr,⟨crtSmithInput_congr hτ.1 (ff.vars _ (by decide)) (ff.vars _ (by decide))
      (ff.vars _ (by decide)) (ff.arrs _ (by decide)) (ff.arrs _ (by decide)),
      (ff.vars _ (by decide)).trans hτ.2.1,by rw [hRowξ]; exact Nat.succ_le_of_lt r.isLt,?_⟩,?_⟩
    · rw [hRowξ]
      exact hTable
    · simp only [V,hRowξ,r]; omega
  let σ₁ := σ.setVar productRowR 0
  let η := σ₁.setVar crtRows (m+1)
  have r0' : Run W (.assign productRowR (.lit 0)) σ σ₁ 2 := Run.assign (evalB_lit (by omega))
  have hr₁ : σ₁.vars rowsR = m+1 := ((Frame.of_run r0').vars _ (by decide)).trans h.1
  have r1' : Run W (.assign crtRows (.var rowsR)) σ₁ η 2 := Run.assign (ev_var hr₁ hmW)
  have r0 : Run W initSmithRows σ η 4 := r0'.seq r1'
  have ff := Frame.of_run r0
  have h0 : η.vars productRowR = 0 := by simp [η,σ₁,vars_setVar,show productRowR ≠ crtRows by decide]
  have hStart : RowTables f 0 η :=
    ⟨⟨by rwa [ff.arrs coefficientBank (by decide)],fun j hj => False.elim (Nat.not_lt_zero j.val hj)⟩,
     ⟨by rwa [ff.arrs targetBank (by decide)],fun j hj => False.elim (Nat.not_lt_zero j.val hj)⟩,
     ⟨by rwa [ff.arrs modulusBank (by decide)],fun j hj => False.elim (Nat.not_lt_zero j.val hj)⟩⟩
  have hI : I η := ⟨crtSmithInput_congr h (ff.vars _ (by decide)) (ff.vars _ (by decide))
    (ff.vars _ (by decide)) (ff.arrs _ (by decide)) (ff.arrs _ (by decide)),
    by simp [η],by simp [h0],by rw [h0]; exact hStart⟩
  obtain ⟨τ,ro,hEnd,hStop⟩ := Run.while_count I V (loadSmithRowCost M m+24)
    (fun ξ hx => ⟨_,hg ξ hx⟩) hs hI
  rw [hg τ hEnd] at hStop
  have hDone : τ.vars productRowR = m+1 := by
    have hl := hEnd.2.2.1
    have hr : ¬ τ.vars productRowR < m+1 := by simpa using hStop
    omega
  have hFinal : RowTables f (m+1) τ := by simpa only [hDone] using hEnd.2.2.2
  have rr : Run W populateSmithCRT σ τ (populateSmithCRTCost M m) :=
    (r0.seq ro).mono (by
      simp [populateSmithCRTCost,smithRowGuard,Cond.size,Expr.size,V,h0,
        show 4+(loadSmithRowCost M m+24) = loadSmithRowCost M m+28 by omega] <;> omega)
  exact ⟨τ,rr,⟨hEnd.2.1.trans (coordinateEquations_length st.B st.U b).symm,
    by simpa only [coordinateEquations,f,List.map_ofFn,Function.comp_def] using hFinal.1.full,
    by simpa only [coordinateEquations,f,List.map_ofFn,Function.comp_def] using hFinal.2.1.full,
    by simpa only [coordinateEquations,f,List.map_ofFn,Function.comp_def] using hFinal.2.2.full⟩,
    hEnd.1,Frame.of_run rr⟩

#print axioms populateSmithCRT_run

end EvenTI.P12Compare
