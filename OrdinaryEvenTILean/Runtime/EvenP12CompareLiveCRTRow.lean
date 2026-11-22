import EvenP12CompareLiveCRTDot
import EvenP12CompareRecoverLinear
import Mathproof.Meta.P15GSSSmithExponent20261007

namespace EvenTI.P12Compare

open scoped BigOperators
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15NetworkDefs20261007
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithWeight20261007
open Mathproof.P15GSSSmithExponent20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_div)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

set_option maxHeartbeats 2000000
set_option maxRecDepth 22000

private def selectDiagonalRow : Com := .assign testRowR (.var productRowR)

private def finishSmithRow : Com :=
  .seq (.assign rowCoefficient (.var productWeightR))
    (.seq (.assign rowTarget (.sub (.var modR) (.var crtDot)))
      (.assign rowModulus (.div (.var modR) (.var testExpR))))

def loadSmithRow : Com := .seq loadSmithDot
  (.seq loadWeightIMP (.seq selectDiagonalRow (.seq testExponentIMP finishSmithRow)))

def loadSmithRowCost (M m : ℕ) : ℕ := 70*m+32*Nat.size M+120

theorem loadSmithRow_run {M m n W : ℕ} [NeZero M] {σ : Env}
    (st : ZDiag.State M (m+1) n) (b : Fin m → ZMod M) (r : Fin (m+1))
    (hL : (m+1)+n+(m+1)*n+(m+1)*(m+1)+2 < W) (hW : 4*M*M+4*M+10 < W)
    (h : CRTSmithInput st b σ) (hR : σ.vars productRowR = r.val)
    (hc : ZDiag.Clr (min (m+1) n) st.B) :
    ∃ τ, Run W loadSmithRow σ τ (loadSmithRowCost M m) ∧
      CRTSmithInput st b τ ∧ τ.vars productRowR = r.val ∧
      τ.vars rowCoefficient = (coordinateEquation st.B st.U b r).coefficient ∧
      τ.vars rowTarget = (coordinateEquation st.B st.U b r).value ∧
      τ.vars rowModulus = (coordinateEquation st.B st.U b r).modulus ∧
      Frame loadSmithRow σ τ := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMW : M < W := by omega
  have hrW : r.val < W := r.isLt.trans (by omega)
  obtain ⟨ρ,r0,hρ,hrρ,hs,hDot,_⟩ := loadSmithDot_run st b r hL hW h hR
  obtain ⟨η,r1,hU,_,f1⟩ := loadWeightIMP_run st r (Fin.last m) hL hMW hρ.2.2.2.1
    hρ.2.2.2.2.1 hρ.1 hρ.2.1 hrρ hs hρ.2.2.2.2.2.1
  have hrη : η.vars productRowR = r.val := (f1.vars _ (by decide)).trans hrρ
  let ζ := η.setVar testRowR r.val
  have r2 : Run W selectDiagonalRow η ζ 2 := Run.assign (ev_var hrη hrW)
  have f2 := Frame.of_run (r1.seq r2)
  have hx : CRTSmithInput st b ζ := crtSmithInput_congr hρ (f2.vars _ (by decide))
    (f2.vars _ (by decide)) (f2.vars _ (by decide)) (f2.arrs _ (by decide)) (f2.arrs _ (by decide))
  have hζrow : ζ.vars testRowR = r.val := by simp [ζ]
  obtain ⟨ω,r3,hE,_,_,f3⟩ := testExponentIMP_run st r (by omega) hMW
    (by have := hx.2.2.2.1; omega) hx.2.2.2.2.1 hx.2.2.1 hx.2.1 hζrow hx.2.2.2.2.2.1 hc
  have f23 := Frame.of_run (r2.seq r3)
  have hw : ω.vars productWeightR = (st.U r (Fin.last m)).val :=
    (f23.vars _ (by decide)).trans hU
  have hd : ω.vars crtDot = (∑ j : Fin m, st.U r j.castSucc*b j : ZMod M).val :=
    (f3.vars _ (by decide)).trans ((f2.vars _ (by decide)).trans hDot)
  have hm : ω.vars modR = M := (f3.vars _ (by decide)).trans hx.2.2.1
  let a := (st.U r (Fin.last m)).val
  let v := (∑ j : Fin m, st.U r j.castSucc*b j : ZMod M).val
  let e := M/Nat.gcd M (rowEntryZ st.B r).val
  let d := Nat.gcd (rowEntryZ st.B r).val M
  have he : M/e = d := by
    dsimp [e,d]
    rw [Nat.div_div_self (Nat.gcd_dvd_left _ _) hM.ne',Nat.gcd_comm]
  let τ₁ := ω.setVar rowCoefficient a
  let τ₂ := τ₁.setVar rowTarget (M-v)
  let τ := τ₂.setVar rowModulus d
  have r4 : Run W (.assign rowCoefficient (.var productWeightR)) ω τ₁ 2 :=
    Run.assign (ev_var hw ((ZMod.val_lt _).trans hMW))
  have hm₁ : τ₁.vars modR = M := ((Frame.of_run r4).vars _ (by decide)).trans hm
  have hd₁ : τ₁.vars crtDot = v := ((Frame.of_run r4).vars _ (by decide)).trans hd
  have r5 : Run W (.assign rowTarget (.sub (.var modR) (.var crtDot))) τ₁ τ₂ 4 :=
    Run.assign (ev_sub (ev_var hm₁ hMW) (ev_var hd₁ ((ZMod.val_lt _).trans hMW))
      ((Nat.sub_le ..).trans_lt hMW))
  have f45 := Frame.of_run (r4.seq r5)
  have hm₂ : τ₂.vars modR = M := (f45.vars _ (by decide)).trans hm
  have hE₂ : τ₂.vars testExpR = e := (f45.vars _ (by decide)).trans hE
  have de : (Expr.div (.var modR) (.var testExpR)).evalB W τ₂ = some d :=
    (ev_div (ev_var hm₂ hMW) (ev_var hE₂ ((Nat.div_le_self ..).trans_lt hMW))
      ((Nat.div_le_self ..).trans_lt hMW)).trans (congrArg some he)
  have r6 : Run W (.assign rowModulus (.div (.var modR) (.var testExpR))) τ₂ τ 4 := Run.assign de
  have run : Run W loadSmithRow σ τ (loadSmithRowCost M m) :=
    (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))))).mono (by
      unfold loadSmithRowCost
      omega)
  have hf := Frame.of_run run
  refine ⟨τ,run,crtSmithInput_congr h (hf.vars _ (by decide)) (hf.vars _ (by decide))
    (hf.vars _ (by decide)) (hf.arrs _ (by decide)) (hf.arrs _ (by decide)),
    ?_,?_,?_,?_,hf⟩
  · exact (hf.vars _ (by decide)).trans hR
  · simp [τ,τ₂,τ₁,vars_setVar,show rowCoefficient ≠ rowModulus by decide,
      show rowCoefficient ≠ rowTarget by decide,coordinateEquation,a]
  · simp [τ,τ₂,vars_setVar,show rowTarget ≠ rowModulus by decide,coordinateEquation,v]
  · simp [τ,coordinateEquation,d]

#print axioms loadSmithRow_run

end EvenTI.P12Compare
