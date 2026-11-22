import EvenP17ReciprocalRecord

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace EvenTI.P17Execution

open EvenTI.P16Execution EvenTI.P17Trial EvenTI.P15Trial EvenTI.P16Trial
open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.P10Scan
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def emitReciprocalTrial (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq resetReciprocalArgs (.seq emitReciprocalHeader (.seq setReciprocalSweepLimit (reciprocalRecordBody D F)))

private theorem transferReciprocalInstalled {l n : ℕ} {L : ReciprocalOffsets} {s t : Env}
    (h : ReciprocalInstalled l n L s)
    (f : ∀ r ∈ reciprocalPermanent, r ≠ reciprocalSweepLimit → t.vars r=s.vars r) :
    ReciprocalInstalled l n L t :=
  ⟨(f _ (by decide) (by decide)).trans h.width,(f _ (by decide) (by decide)).trans h.power,
    (f _ (by decide) (by decide)).trans h.source,(f _ (by decide) (by decide)).trans h.inverse,
    (f _ (by decide) (by decide)).trans h.side,(f _ (by decide) (by decide)).trans h.crossed,
    (f _ (by decide) (by decide)).trans h.squared,(f _ (by decide) (by decide)).trans h.traced,
    (f _ (by decide) (by decide)).trans h.unit,(f _ (by decide) (by decide)).trans h.zero,
    (f _ (by decide) (by decide)).trans h.temp1,(f _ (by decide) (by decide)).trans h.temp2,
    (f _ (by decide) (by decide)).trans h.start,(f _ (by decide) (by decide)).trans h.length,
    (f _ (by decide) (by decide)).trans h.emitWidth⟩

/-- An installed reciprocal cut and its inverse produce a whole serialized
trial record, including tag, framing, and both retained-mode passes. -/
theorem emitReciprocalTrial_run (D : FieldEncoding K) (F : FieldPresentation K) {l n B S : ℕ}
    {σ : Env} (T : Tensor K ((l+1)+(l+1)) n)
    (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K) (L : ReciprocalOffsets)
    (hn : 2 ≤ n) (hN : n+1 < B) (hNN : n*n+1 < B) (hA : (n^l)*(n^l)+1 < B)
    (hLim : l+1 < B) (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hSrc : L.src+(n*n^l)*(n*n^l) ≤ L.out)
    (hInv : L.inv+(n*n^l)*(n*n^l) ≤ L.out)
    (hOut : L.out+n*n ≤ L.cross) (hCross : L.cross+(n*n)*(n*n) ≤ L.square)
    (hSquare : L.square+(n*n)*(n*n) ≤ S)
    (hT : L.tt < L.src ∧ L.tt < L.inv ∧ L.tt < L.out)
    (hU : L.uu < L.src ∧ L.uu < L.inv ∧ L.uu < L.out) (hTU : L.tt≠L.uu)
    (hZ : L.zero < L.out ∧ L.zero≠L.tt ∧ L.zero≠L.uu)
    (hOne : L.one < L.out ∧ L.one≠L.tt ∧ L.one≠L.uu)
    (hS : Slots F canonical qN.WS S B σ) (hRegs : ReciprocalInstalled l n L σ)
    (hZero : val F canonical qN.WS σ L.zero=0) (hUnit : val F canonical qN.WS σ L.one=1)
    (hLoad : InstalledCutMatrix F σ l n L.src (flatten T))
    (hRecip : InstalledCutMatrix F σ l n L.inv N)
    (hCount : σ.vars reciprocalCountWord=(l+1)+(l+1))
    (hCountB : (l+1)+(l+1)<B) (hPayloadB : n*n+2<B)
    (hFrameWord : 1+((l+1)+(l+1))*(n*n+2)<B) :
    ∃ t, Run B (emitReciprocalTrial D F) σ t
      (15+(12+(4+(((reciprocalVisitCost F true l n+12)*(l+1)+8)+
        ((reciprocalVisitCost F false l n+12)*(l+1)+8))))) ∧
      Slots F canonical qN.WS S B t ∧ t.inp=σ.inp ∧
      t.out=σ.out++preparedTrialWords D (PreparedTrial.reciprocal (rawReciprocalAnchor T N)) := by
  have haB : n^l < B :=
    (Nat.le_mul_of_pos_right _ (pow_pos (show 0 < n by omega) l)).trans_lt (by omega)
  have hsB := hS.slots_word
  obtain ⟨ρ,r₀,hρ,hRows,_,_,_,hKeep,hArr,hi,ho⟩ :=
    resetReciprocalArgs_run F hS hRegs.width hRegs.power hRegs.crossed
      (by omega) haB (by omega) (by omega) (by omega)
  let q := (l+1)+(l+1)
  let u : Env := {ρ with out := ρ.out++[0,1+q*(n*n+2),q]}
  let v := u.setVar reciprocalSweepLimit (l+1)
  have r₁ : Run B emitReciprocalHeader ρ u 12 :=
    emitReciprocalHeader_run hFrameWord hPayloadB hRows ((hKeep _ (by decide)).trans hCount)
  have r₂ : Run B setReciprocalSweepLimit u v 4 :=
    setReciprocalSweepLimit_run ((hKeep _ (by decide)).trans hCount) hCountB (by omega)
  have hu : Slots F canonical qN.WS S B u :=
    slots_frame F hρ rfl rfl (fun _ _ => rfl) rfl
  have hv : Slots F canonical qN.WS S B v :=
    Slots.setVar F canonical hu (by decide) (by decide) _
  have hvInstalled : ReciprocalInstalled l n L v := transferReciprocalInstalled hRegs (by
    intro r hr hFresh
    simpa [v,u,hFresh] using hKeep r (by
      have hSafe : ∀ r ∈ reciprocalPermanent,
          r ∉ [Mathproof.P15RecogIMPGrid20261007.gRows,Mathproof.P15RecogIMPGrid20261007.gCols,
            Mathproof.P15RecogIMPDot20261007.dL,Mathproof.P15RecogIMPGrid20261007.gOut] := by decide
      exact hSafe r hr))
  have hvPrefix {k : ℕ} : val F canonical qN.WS v k=val F canonical qN.WS σ k := by
    have he := val_setVar F canonical (by decide : reciprocalSweepLimit≠qN.WS) u (l+1) k
    rw [he]
    change val F canonical qN.WS ρ k = val F canonical qN.WS σ k
    unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
    rw [hKeep _ (by decide),hArr]
  have loadV : InstalledCutMatrix F v l n L.src (flatten T) :=
    fun x y => hvPrefix.trans (hLoad x y)
  have recipV : InstalledCutMatrix F v l n L.inv N :=
    fun x y => hvPrefix.trans (hRecip x y)
  obtain ⟨t,r₃,ht,hti,hto⟩ := reciprocalRecordBody_run D F T N L hn hN hNN hA hLim hQ hP
    hSrc hInv hOut hCross hSquare hT hU hTU hZ hOne hv hvInstalled (by simp [v])
    (hvPrefix.trans hZero) (hvPrefix.trans hUnit) loadV recipV
  let A := rawReciprocalAnchor T N
  let p : PreparedTrial K l n := .reciprocal A
  have hx : t.out =
      v.out++((numberedAnchors p).map (numberedAnchorWords D)).flatMap blockW := by
    change t.out=v.out++(List.ofFn (fun i =>
      blockW (numberedAnchorWords D (numeric (A (reciprocalOrder l i)))))).flatten at hto
    simpa only [p,numberedAnchors,List.map_ofFn,List.flatMap_def,Function.comp_def] using hto
  refine ⟨t,r₀.seq (r₁.seq (r₂.seq r₃)),ht,hti.trans hi,?_⟩
  rw [hx,reciprocalTrialWords_exact]
  change (ρ.out++[0,1+q*(n*n+2),q])++_ = σ.out++([0,1+q*(n*n+2),q]++_)
  rw [ho,List.append_assoc]

#print axioms emitReciprocalTrial_run
end EvenTI.P17Execution
