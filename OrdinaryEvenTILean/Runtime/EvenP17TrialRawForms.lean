import EvenP17TrialFormVisit
import EvenP16TrialRawForm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def basisForm {c d n : ℕ} (D : FieldEncoding K) (xs : Fin c → Coord d n → K)
    (v : Fin (Fintype.card K^c)) : Coord d n → K :=
  fun x => ∑ i : Fin c, coefficients D c v i * xs i x

noncomputable def basisFormWords {c d n : ℕ} (D : FieldEncoding K) (xs : Fin c → Coord d n → K)
    (code : ℕ) : List ℕ :=
  if h : code < Fintype.card K^c then cutFormWords D (basisForm D xs ⟨code,h⟩) else []

noncomputable def rawCutForms (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j)
    (.seq emitFormInit (cappedCutScanWith (Fintype.card K) (encodeOneForm D F) j))

noncomputable def rawCutFormsCost (F : FieldPresentation K) (q c d m n L : ℕ) (j : Fin 4) : ℕ :=
  rawCutSetupBitCost F L j + (emitFormInitCost +
    (30*(m+q)+42+((encodeOneFormCost F c d m+8)*cappedCutChoiceCount q c n+6)))

/-- From the literal tensor pair, compute one physical kernel basis and
serialize the form for every cap-admitted coefficient code using that basis.
The final basis bank is retained and recovers every entry emitted. -/
theorem rawCutForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K (d+d) n) (j : Fin 4) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    let c := cutKernelDimension T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^d
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord d n → K),
      Run B (rawCutForms D F j)
        (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w))
        τ (rawCutFormsCost F (Fintype.card K) c d m n L j) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      (∀ i x, val F canonical qN.WS τ
        ((outputBase j).value m+(i.val*m+(inputCoordOrder n d x).val))=xs i x) ∧
      τ.inp=[] ∧
      τ.out=(List.range (cappedCutChoiceCount (Fintype.card K) c n)).flatMap (basisFormWords D xs) := by
  dsimp only
  let c := cutKernelDimension T S j
  let m := n^d
  let a := augmentedMatrixBase.value m
  let b := (outputBase j).value m
  let o := placedRankSource m
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let B := (cutWordPoly F).eval (bitSize (comparisonInput D T S))
  obtain ⟨ρ,r₀,hW,hCuts,hNull,hBudget,_,hRaw,hIn,hOut,hBig,hChoice⟩ :=
    rawCutSetupProgram_run D F T S j hd hn
  have hRaw' : ρ.arrs rawPairIO.array=(d+d)::n::(tensorWords D T++tensorWords D S) := by
    simpa [comparisonInput,List.append_assoc] using hRaw
  have hdm : d ≤ m := (Nat.lt_two_pow_self (n := d)).le.trans (Nat.pow_le_pow_left hn d)
  have hnm : n ≤ m := (cutInput_side_bounds D T S (by omega : 1 ≤ d) hn).1
  have hWork : o+m ≤ b := hW.frame.layout.output_before
  have hBasisFit : b+m*m ≤ z := hW.frame.layout.basis_before
  have hZ : z+4=Sn := rfl
  have hCutW : Sn+m+m+10 < B := hBig
  obtain ⟨μ,rI,hμ,hMode,hBase,hSrc,hLen,hKeep,hVInit,hArr,hI,hO⟩ :=
    emitFormInit_run F (n::(tensorWords D T++tensorWords D S)) (by omega) (by omega)
      (by omega) (by omega) (show o<B by omega)
      hRaw' hW.frame.slots hBudget hW.frame.form_start hW.frame.side
  have hFrame : CutRecombineInput (B := B) (Sn := Sn) F μ a b o c m z (z+2) (z+3) := by
    exact ⟨hμ,hW.frame.layout,hW.frame.count_word,
      (hKeep _ (by decide)).trans hW.frame.coeff_start,
      (hKeep _ (by decide)).trans hW.frame.basis_start,
      (hKeep _ (by decide)).trans hW.frame.form_start,
      (hKeep _ (by decide)).trans hW.frame.side,
      (hKeep _ (by decide)).trans hW.frame.count,
      (hKeep _ (by decide)).trans hW.frame.zero,
      (hKeep _ (by decide)).trans hW.frame.scratch₁,
      (hKeep _ (by decide)).trans hW.frame.scratch₂,
      (hVInit _).trans hW.frame.zero_value⟩
  have hVisit : CutVisitInput (B := B) (Sn := Sn) F μ a b o c m z (z+2) (z+3) :=
    ⟨hFrame,by rw [hArr];exact hW.coefficient_bank,
      (hKeep _ (by decide)).trans hW.coefficient_count,
      (hKeep _ (by decide)).trans hW.load_base,(hKeep _ (by decide)).trans hW.load_count⟩
  have hBasis := (hCuts j).basis
  rw [hNull] at hBasis
  obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
  have hAtμ (i : Fin c) (x : Coord d n) :
      val F canonical qN.WS μ (b+(i.val*m+(inputCoordOrder n d x).val))=xs i x :=
    (hVInit _).trans (hAt i x)
  have hNullμ : μ.vars (nullityAt j) = c :=
    (hKeep _ (by fin_cases j <;> decide)).trans hNull
  have hStable (ρ : Env) (_ : ρ.arrs=μ.arrs)
      (hf : ∀ r, r ∉ ["left","d","n","i","r",cutChoiceLength] → ρ.vars r=μ.vars r) :
      FormScanReady ρ d n o :=
    ⟨(hf _ (by decide)).trans hMode,(hf _ (by decide)).trans hBase,
      (hf _ (by decide)).trans hSrc,(hf _ (by decide)).trans hLen⟩
  have hSet (ρ : Env) (k : ℕ) (hf : FormScanReady ρ d n o) :
      FormScanReady (ρ.setVar cutChoiceIndex k) d n o := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [show emitFormModes≠cutChoiceIndex by decide] using hf.modes
    · simpa [show reverseDigitBase≠cutChoiceIndex by decide] using hf.base
    · simpa [show fieldVectorStart≠cutChoiceIndex by decide] using hf.start
    · simpa [show fieldVectorLength≠cutChoiceIndex by decide] using hf.length
  have within (i : Fin c) (x : Coord d n) :
      let p := b+(i.val*m+(inputCoordOrder n d x).val)
      p<z ∧ b≤p := by
    dsimp only
    have hi : i.val*m+(inputCoordOrder n d x).val < m*m :=
      outputPoint_lt hW.frame.layout.nullity i (inputCoordOrder n d x)
    exact ⟨(Nat.add_lt_add_left hi b).trans_le hBasisFit,Nat.le_add_right _ _⟩
  obtain ⟨τ,hRun,_,hPres,_,_,hIn',hOut'⟩ :=
    cappedCutBlockScan_run F (encodeOneForm D F) (encodeOneFormCost F c d m) (basisFormWords D xs)
      (fun ρ => FormScanReady ρ d n o) b j hVisit hNullμ
      ((hKeep _ (by decide)).trans hBudget) hnm hChoice hStable hSet (by
        intro σ v hσ hWork hFrame hq hPow hIdx
        obtain ⟨η,r,hNext,hReady,hCode,hCount,hBank,hI₁,hO₁⟩ :=
          encodeOneForm_run D F v (by omega) (by omega) (by omega) hWork hσ hq hPow hIdx
        refine ⟨η,r,hNext,hReady,hCode,hCount,hBank,hI₁,?_⟩
        rw [hO₁,basisFormWords,dif_pos v.isLt]
        congr 2
        funext x
        unfold basisForm
        apply Finset.sum_congr rfl
        intro i _
        have hBounds := within i x
        rw [hFrame _ hBounds.1 hBounds.2,hAtμ i x])
  refine ⟨τ,xs,r₀.seq (rI.seq hRun),hInd,hSpan,?_,(hIn'.trans hI).trans hIn,?_⟩
  · intro i x
    exact (hPres _ (within i x).1 (within i x).2).trans (hAtμ i x)
  · simpa only [hO,hOut,List.nil_append] using hOut'

#print axioms rawCutForms_run
end EvenTI.P17Trial
