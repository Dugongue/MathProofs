import EvenP17TrialRoutedForms
import EvenP17TrialRawFormsBinary

set_option autoImplicit false
set_option maxHeartbeats 2100000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P37Isolation20261004
open Mathproof.Problem18P37HostProgram20261004 (pre pre_ne_host)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem pre_R_ne_L (a b : String) : pre "R" a ≠ pre "L" b := by
  intro h
  have h := congrArg (fun t => t.toList.take 5) h
  simp [pre,String.toList_append] at h

noncomputable def captureTwoCutForms (D : FieldEncoding K) (F : FieldPresentation K) (j k : Fin 4) : Com :=
  .seq (captureCutForms D F j "L") (.seq (.assign formInputCursor (.lit 0)) (captureCutForms D F k "R"))

/-- Replay two selected cuts directly from one retained raw pair tape.
The two independent basis computations append exact fixed-width records to
one host array and retain the original raw tensor pair. -/
theorem captureTwoCutForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n B : ℕ} (T S : Tensor K (d+d) n) (j k : Fin 4) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (σ : Env) (o₀ R : List ℕ) :
    let cl := cutKernelDimension T S j
    let cr := cutKernelDimension T S k
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^d
    let ext := comparisonInitExt F (pairCutSlotCount.value m) w.length (cutChoiceExt L)
    (cutWordPoly F).eval L ≤ B → 0<B →
    (∀ r, σ.vars (pre "L" r)=0 ∧ σ.vars (pre "R" r)=0) →
    (∀ a, σ.arrs (pre "L" a)=List.replicate (ext a) 0 ∧
      σ.arrs (pre "R" a)=List.replicate (ext a) 0) →
    σ.vars formInputCursor=0 →
    (∃ junk, σ.arrs formInputTape=(w.length::w)++junk) →
    (σ.arrs formInputTape).length<B →
    (∀ v∈σ.arrs formInputTape, v<B) →
    σ.vars formOutputCursor=o₀.length →
    (σ.arrs formOutputTape).take o₀.length=o₀ →
    (σ.arrs formOutputTape).length=R.length → R.length<B →
    (σ.arrs formOutputTape).drop o₀.length=R.drop o₀.length →
    o₀.length+2*(n*m)≤R.length →
    ∃ (τ : Env) (xs : Fin cl → Coord d n → K) (ys : Fin cr → Coord d n → K),
      Run B (captureTwoCutForms D F j k) σ τ
        (7*rawCutFormsCost F (Fintype.card K) cl d m n L j+
          (2+7*rawCutFormsCost F (Fintype.card K) cr d m n L k)) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      LinearIndependent K ys ∧
      Submodule.span K (Set.range ys)=selectedKernel (leftOf k) (if targetOf k then S else T) ∧
      τ.vars formOutputCursor=o₀.length+cappedCutChoiceCount (Fintype.card K) cl n*m+
        cappedCutChoiceCount (Fintype.card K) cr n*m ∧
      (τ.arrs formOutputTape).take (τ.vars formOutputCursor)=
        o₀++(List.range (cappedCutChoiceCount (Fintype.card K) cl n)).flatMap (basisFormWords D xs)++
          (List.range (cappedCutChoiceCount (Fintype.card K) cr n)).flatMap (basisFormWords D ys) ∧
      τ.arrs formInputTape=σ.arrs formInputTape ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  dsimp only
  intro hB hPos hv ha hPin hTape hTL hTW hPout hOut hLen hR hRest hCap
  let m := n^d
  let cl := cutKernelDimension T S j
  let q := Fintype.card K
  change o₀.length+2*(n*m)≤R.length at hCap
  have hCap₀ : o₀.length+n*m≤R.length := by omega
  obtain ⟨μ,xs,r₀,hLI,hLS,hLp,hLo,hML,hMR,hMA,hLF⟩ :=
    captureCutForms_run D F T S j "L" hd hn σ o₀ R hB (fun x => (hv x).1) (fun x => (ha x).1)
      hPin hTape hTL hTW hPout hOut hLen hR hRest hCap₀
  let o₁ := o₀++(List.range (cappedCutChoiceCount q cl n)).flatMap (basisFormWords D xs)
  have he : o₁.length=o₀.length+cappedCutChoiceCount q cl n*m := by
    simp only [o₁,List.length_append]
    exact congrArg (o₀.length + ·) (rawFormWords_length D xs n)
  have hMost : cappedCutChoiceCount q cl n*m≤n*m := Nat.mul_le_mul_right m (cappedCutChoiceCount_le q cl n)
  have hCap₁ : o₁.length+n*m≤R.length := by rw [he]; omega
  let η := μ.setVar formInputCursor 0
  have rI : Run B (.assign formInputCursor (.lit 0)) μ η 2 := Run.assign (evalB_lit hPos)
  have hηv (x : String) : η.vars (pre "R" x)=0 := by
    have hvars := hLF.vars (pre "R" x) (pre_R_ne_L x)
      (pre_ne_host "R" x "even.form.input-cursor") (pre_ne_host "R" x "even.form.output-cursor")
    have hpin : pre "R" x ≠ formInputCursor := pre_ne_host "R" x "even.form.input-cursor"
    simpa only [η,vars_setVar,if_neg hpin] using hvars.trans (hv x).2
  have hηa (x : String) :
      η.arrs (pre "R" x)=List.replicate
        (comparisonInitExt F (pairCutSlotCount.value m) (comparisonInput D T S).length
          (cutChoiceExt (bitSize (comparisonInput D T S))) x) 0 :=
    (hLF.arrs (pre "R" x) (pre_R_ne_L x) (pre_ne_host "R" x "even.form.output")).trans (ha x).2
  have hηp : η.vars formOutputCursor=o₁.length := by
    change η.vars formOutputCursor=o₁.length
    simp only [η,vars_setVar,show formOutputCursor≠formInputCursor by decide,if_false]
    exact hLp.trans he.symm
  have hLT : μ.vars formOutputCursor=o₁.length := hLp.trans he.symm
  have hO₁ : (η.arrs formOutputTape).take o₁.length=o₁ := by
    change (μ.arrs formOutputTape).take o₁.length=o₁
    exact hLT ▸ hLo
  have hRem : (η.arrs formOutputTape).drop o₁.length=R.drop o₁.length := by
    change (μ.arrs formOutputTape).drop o₁.length=R.drop o₁.length
    exact hLT ▸ hMR
  have hRawη : η.arrs formInputTape=σ.arrs formInputTape := hMA
  obtain ⟨τ,ys,r₁,hRI,hRS,hP,hO,_,_,hInput,hRF⟩ :=
    captureCutForms_run D F T S k "R" hd hn η o₁ R hB hηv hηa (by simp [η])
      (by rwa [hRawη]) (by rwa [hRawη]) (by rwa [hRawη]) hηp hO₁ hML hR hRem hCap₁
  refine ⟨τ,xs,ys,r₀.seq (rI.seq r₁),hLI,hLS,hRI,hRS,?_,?_,hInput.trans hRawη,?_,?_⟩
  · exact hP.trans (congrArg (·+_) he)
  · simpa only [o₁,List.append_assoc] using hO
  · exact hRF.inp.trans hLF.inp
  · exact (hRF.out rfl).trans (hLF.out rfl)

#print axioms captureTwoCutForms_run
end EvenTI.P17Trial
