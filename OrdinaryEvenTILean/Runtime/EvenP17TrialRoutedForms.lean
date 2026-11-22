import EvenP17TrialRawForms
import EvenP14CutRunLift
import Mathproof.Meta.Problem18P37HostProgram20261004

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P37Isolation20261004
open Mathproof.Problem18P37HostProgram20261004 (pre pre_inj pre_ne_host)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def formInputTape : String := "P37#even.form.raw"
def formInputCursor : String := "P37#even.form.input-cursor"
def formOutputTape : String := "P37#even.form.output"
def formOutputCursor : String := "P37#even.form.output-cursor"

def cutFormIso (tag : String) : Iso :=
  ⟨pre tag,formInputTape,formInputCursor,formOutputTape,formOutputCursor,true⟩

theorem cutFormIso_fresh (tag : String) : Fresh (cutFormIso tag) :=
  ⟨pre_inj tag,fun _ => pre_ne_host tag _ "even.form.raw",
    fun _ => pre_ne_host tag _ "even.form.input-cursor",
    fun _ => pre_ne_host tag _ "even.form.output",
    fun _ => pre_ne_host tag _ "even.form.output-cursor",
    (show formInputCursor≠formOutputCursor by decide),
    (show formInputTape≠formOutputTape by decide)⟩

noncomputable def captureCutForms (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4)
    (tag : String) : Com := iso (cutFormIso tag) (rawCutForms D F j)

private theorem flatMap_width {α β : Type} (xs : List α) (render : α → List β) (w : ℕ)
    (h : ∀ x ∈ xs, (render x).length=w) : (xs.flatMap render).length=xs.length*w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,h _ List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy)),List.length_cons,Nat.add_mul]
    omega

theorem rawFormWords_length (D : FieldEncoding K) {d n c : ℕ}
    (xs : Fin c → Coord d n → K) (budget : ℕ) :
    ((List.range (cappedCutChoiceCount (Fintype.card K) c budget)).flatMap (basisFormWords D xs)).length =
      cappedCutChoiceCount (Fintype.card K) c budget * n^d := by
  let q := Fintype.card K
  let N := cappedCutChoiceCount q c budget
  have hN : N≤q^c := by unfold N cappedCutChoiceCount; split <;> omega
  rw [flatMap_width _ _ (n^d),List.length_range]
  intro i hi
  have hv : i<Fintype.card K^c := (List.mem_range.mp hi).trans_le hN
  simp only [basisFormWords,dif_pos hv,cutFormWords,List.length_ofFn]

/-- Capture the verified raw all-form producer directly into a host array.
Its output can feed subsequent trial pairing, while the raw input bank and
all other controller namespaces are left untouched. -/
theorem captureCutForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n B : ℕ} (T S : Tensor K (d+d) n) (j : Fin 4) (tag : String)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (σ : Env) (o₀ R : List ℕ) :
    let c := cutKernelDimension T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^d
    let ext := comparisonInitExt F (pairCutSlotCount.value m) w.length (cutChoiceExt L)
    (cutWordPoly F).eval L ≤ B →
    (∀ r, σ.vars (pre tag r)=0) →
    (∀ a, σ.arrs (pre tag a)=List.replicate (ext a) 0) →
    σ.vars formInputCursor=0 →
    (∃ junk, σ.arrs formInputTape=(w.length::w)++junk) →
    (σ.arrs formInputTape).length<B →
    (∀ v∈σ.arrs formInputTape, v<B) →
    σ.vars formOutputCursor=o₀.length →
    (σ.arrs formOutputTape).take o₀.length=o₀ →
    (σ.arrs formOutputTape).length=R.length → R.length<B →
    (σ.arrs formOutputTape).drop o₀.length=R.drop o₀.length →
    o₀.length+n*m≤R.length →
    ∃ (τ : Env) (xs : Fin c → Coord d n → K),
      Run B (captureCutForms D F j tag) σ τ (7*rawCutFormsCost F (Fintype.card K) c d m n L j) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.vars formOutputCursor=o₀.length+cappedCutChoiceCount (Fintype.card K) c n*m ∧
      (τ.arrs formOutputTape).take (τ.vars formOutputCursor)=
        o₀++(List.range (cappedCutChoiceCount (Fintype.card K) c n)).flatMap (basisFormWords D xs) ∧
      (τ.arrs formOutputTape).length=R.length ∧
      (τ.arrs formOutputTape).drop (τ.vars formOutputCursor)=R.drop (τ.vars formOutputCursor) ∧
      τ.arrs formInputTape=σ.arrs formInputTape ∧
      Frame (cutFormIso tag) σ τ := by
  dsimp only
  intro hB hv ha hPin hTape hTinLen hTinWord hPout hOut hLen hR hRest hCap
  obtain ⟨ρ,xs,hr,hInd,hSpan,_,_,hResult⟩ := rawCutForms_run D F T S j hd hn
  have hLenOut := rawFormWords_length D xs n
  have hRfit : o₀.length+ρ.out.length ≤ R.length := by
    rw [hResult,hLenOut]
    exact (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (cappedCutChoiceCount_le (Fintype.card K) (cutKernelDimension T S j) n))
      _).trans hCap
  obtain ⟨τ,r,inv,frame⟩ := iso_run (cutFormIso_fresh tag) (cutRunWordLift hB hr) σ o₀ R
    hv ha hPin hTape hTinLen hTinWord (fun h => by cases h)
    (fun _ => hPout) (fun _ => hOut) (fun _ => hLen) (fun _ => hR) (fun _ => hRest)
    (fun _ => hRfit)
  refine ⟨τ,xs,r,hInd,hSpan,?_,?_,inv.outLen rfl,inv.outRest rfl,?_,frame⟩
  · have h := inv.outPtr rfl
    rw [hResult,hLenOut] at h
    exact h
  · exact (inv.outArr rfl).trans (congrArg (o₀ ++ ·) hResult)
  · exact frame.arrs _ (fun y => (pre_ne_host tag y "even.form.raw").symm) (show formInputTape≠formOutputTape by decide)

private theorem flatMap_fixedWindow {α β : Type} (render : α → List β) (w : ℕ)
    (xs : List α) (h : ∀ x ∈ xs, (render x).length=w) (i : ℕ) (hi : i<xs.length) :
    ((xs.flatMap render).drop (i*w)).take w=render xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    cases i with
    | zero =>
      simp only [Nat.zero_mul,List.drop_zero,List.flatMap_cons,List.getElem_cons_zero]
      exact List.take_left' hx
    | succ i =>
      have hι : i<xs.length := by simpa using hi
      have he : (i+1)*w = (render x).length+i*w := by rw [Nat.add_mul,Nat.one_mul,hx,Nat.add_comm]
      rw [he,←List.drop_drop,List.flatMap_cons,List.drop_left]
      exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) i hι

/-- A numeric coefficient index reads its exact installed form from the
contiguous captured output, without reconstructing any preceding forms. -/
theorem capturedCutForm_at (D : FieldEncoding K) {d n c : ℕ} (xs : Fin c → Coord d n → K)
    (budget code : ℕ) (hCode : code<cappedCutChoiceCount (Fintype.card K) c budget)
    (o₀ bank : List ℕ) (pos : ℕ)
    (hBank : bank.take pos =
      o₀++(List.range (cappedCutChoiceCount (Fintype.card K) c budget)).flatMap (basisFormWords D xs)) :
    (((bank.take pos).drop (o₀.length+code*n^d)).take (n^d))=basisFormWords D xs code := by
  let q := Fintype.card K
  let N := cappedCutChoiceCount q c budget
  have hN : N≤q^c := by unfold N cappedCutChoiceCount; split <;> omega
  rw [hBank,←List.drop_drop,List.drop_left]
  have h := flatMap_fixedWindow (basisFormWords D xs) (n^d) (List.range N) (by
    intro i hi
    have hv : i<Fintype.card K^c := (List.mem_range.mp hi).trans_le hN
    simp only [basisFormWords,dif_pos hv,cutFormWords,List.length_ofFn])
    code (by simpa only [List.length_range] using hCode)
  simpa only [List.getElem_range] using h

#print axioms capturedCutForm_at
#print axioms captureCutForms_run
end EvenTI.P17Trial
