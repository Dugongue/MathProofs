import EvenP15TrialCartesian
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P15Trial

open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_arrays)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)

def trialInputFrame (raw : List ℕ) (source target : List (List ℕ)) : List ℕ :=
  pairW raw (pairW (listW source) (listW target))

def openRawTrialFrame : Com :=
  .seq (.assign "cursor" (.lit 0)) (.seq (.assign "end" (.var "length")) pairWindow)

def saveRawFrameBindings : List (String × Expr) :=
  [(rawStart,.var "cursor"),(rawEnd,.var "stop")]

def openPayloadTrialFrame : Com :=
  .seq (commands saveRawFrameBindings) (.seq (.assign "cursor" (.var "stop")) pairWindow)

def trialAxesBindings : List (String × Expr) :=
  [(sourceAxis.scan,.add (.var "cursor") (.lit 1)),(sourceAxis.limit,.var "stop"),
   (targetFirst,.add (.var "stop") (.lit 1)),(targetAxis.limit,.var "end")]

def trialFrameProgram : Com :=
  .seq openRawTrialFrame (.seq openPayloadTrialFrame (commands trialAxesBindings))

private theorem slice_body {z : List ℕ} {p q : ℕ} (hp : p ≤ q) (hq : q ≤ z.length)
    (xs : List (List ℕ)) (h : slice z p q=listW xs) :
    p+1 ≤ q ∧ slice z (p+1) q=xs.flatMap blockW := by
  have hL : (slice z p q).length = (listW xs).length := congrArg List.length h
  rw [slice_length z hq,listW,List.length_cons] at hL
  have hP : p < q := by omega
  rw [slice_cons z hP hq] at h
  exact ⟨by omega,(List.cons.inj h).2⟩

private theorem savedVarsSafe :
    ∀ p ∈ saveRawFrameBindings, ∀ q ∈ saveRawFrameBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [saveRawFrameBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;> simp [NoVar,rawStart,rawEnd]

private theorem installedAxesSafe :
    ∀ p ∈ trialAxesBindings, ∀ q ∈ trialAxesBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [trialAxesBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl <;> simp [NoVar,sourceAxis,targetAxis,sourceStart,sourceEnd,targetStart,targetEnd,targetFirst]

/-- Install the literal intervals from the nested packed pair. The counts
remain at the head of their own payload lists and are skipped exactly once. -/
theorem trialFrameProgram_run (raw : List ℕ) (xs ys : List (List ℕ))
    {B : ℕ} {σ : Env}
    (hLen : (trialInputFrame raw xs ys).length+1 < B) (hB : 2 < B)
    (hWords : ∀ v ∈ trialInputFrame raw xs ys, v < B)
    (hData : σ.arrs "data"=sentinelWords (trialInputFrame raw xs ys))
    (hL : σ.vars "length"=(trialInputFrame raw xs ys).length) :
    let z := trialInputFrame raw xs ys
    ∃ τ a A b C j J, Run B trialFrameProgram σ τ 100 ∧
      τ.arrs "data"=sentinelWords z ∧ τ.inp=σ.inp ∧ τ.out=σ.out ∧
      TrialBankContext z τ a A j J ∧ τ.vars sourceAxis.scan=b ∧ τ.vars sourceAxis.limit=C ∧
      slice z a A=raw ∧ slice z b C=xs.flatMap blockW ∧ slice z j J=ys.flatMap blockW ∧
      (b ≤ C ∧ C ≤ z.length) ∧ (j ≤ J ∧ J ≤ z.length) := by
  let z := trialInputFrame raw xs ys
  let L := z.length
  have hLB : L < B := by change z.length+1 < B at hLen; omega
  let σ₀ := σ.setVar "cursor" 0
  let σ₁ := σ₀.setVar "end" L
  have r₀ : Run B (.assign "cursor" (.lit 0)) σ σ₀ 2 := Run.assign (evalB_lit (by omega))
  have r₁ : Run B (.assign "end" (.var "length")) σ₀ σ₁ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hL.symm,hL ▸ hLB⟩)
  obtain ⟨ρ,a,A,r₂,haa,hA,_,hCur,hStop,hEnd,hBank,hPair,fr⟩ :=
    pairWindow_run z (s := σ₁) (c := 0) (e := L) (by rfl) (by rfl) (by omega)
      (by rfl) hLB hB hWords hData
  have hRawSlice : slice z a A=raw ∧ slice z A L=pairW (listW xs) (listW ys) := by
    have hh : slice z 0 L=z := by simp [slice,L]
    rw [hh] at hPair
    simpa [z,trialInputFrame,Prod.mk.injEq] using hPair.symm
  let ρ₁ := install [(rawStart,a),(rawEnd,A)] ρ
  have r₃ : Run B (commands saveRawFrameBindings) ρ ρ₁ 5 := by
    apply commands_run saveRawFrameBindings [a,A] ρ (by rfl) _ savedVarsSafe
    exact .cons (evalB_var_iff.mpr ⟨hCur.symm,hCur ▸ (haa.trans hA).trans_lt hLB⟩)
      (.cons (evalB_var_iff.mpr ⟨hStop.symm,hStop ▸ hA.trans_lt hLB⟩) .nil)
  let ρ₂ := ρ₁.setVar "cursor" A
  have r₄ : Run B (.assign "cursor" (.var "stop")) ρ₁ ρ₂ 2 :=
    Run.assign (evalB_var_iff.mpr ⟨hStop.symm,hStop ▸ hA.trans_lt hLB⟩)
  obtain ⟨η,b,C,r₅,hbc,hC,_,hBreg,hCreg,hEnd',hBank',hPayload,fr'⟩ :=
    pairWindow_run z (s := ρ₂) (c := A) (e := L) (by rfl) hEnd
      hA (by rfl) hLB hB hWords hBank
  have hSides : slice z b C=listW xs ∧ slice z C L=listW ys := by
    rw [hRawSlice.2] at hPayload
    simpa [Prod.mk.injEq] using hPayload.symm
  obtain ⟨hBNext,hXs⟩ := slice_body hbc hC xs hSides.1
  obtain ⟨hCNext,hYs⟩ := slice_body hC (by rfl) ys hSides.2
  let vals := [(sourceAxis.scan,b+1),(sourceAxis.limit,C),(targetFirst,C+1),(targetAxis.limit,L)]
  let τ := install vals η
  have hE (r : String) (v : ℕ) (h : η.vars r=v) (hv : v < B) :
      (Expr.var r).evalB B η=some v := evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩
  have hEB := hE _ _ hBreg ((hbc.trans hC).trans_lt hLB)
  have hEC := hE _ _ hCreg (hC.trans_lt hLB)
  have hEL := hE _ _ hEnd' hLB
  have hB1 := evalB_bin (op := .add) hEB (evalB_lit (by omega : 1 < B))
    (show b+1 < B from (hBNext.trans hC).trans_lt hLB)
  have hC1 := evalB_bin (op := .add) hEC (evalB_lit (by omega : 1 < B))
    (show C+1 < B from hCNext.trans_lt hLB)
  have hEval : List.Forall₂ (fun (p : String × Expr) (v : ℕ) => p.2.evalB B η=some v)
      trialAxesBindings (vals.map Prod.snd) := .cons hB1 (.cons hEC (.cons hC1 (.cons hEL .nil)))
  have r₆ : Run B (commands trialAxesBindings) η τ 13 :=
    commands_run trialAxesBindings (vals.map Prod.snd) η (by rfl) hEval installedAxesSafe
  have hRaw₁ : τ.vars rawStart=a := by
    change η.vars rawStart=a
    rw [fr'.vars _ (by decide)]
    rfl
  have hRaw₂ : τ.vars rawEnd=A := by
    change η.vars rawEnd=A
    rw [fr'.vars _ (by decide)]
    rfl
  have ho : τ.out=σ.out :=
    (fr'.out (noWrite_of_check (by decide))).trans (fr.out (noWrite_of_check (by decide)))
  have hi : τ.inp=σ.inp := by
    have hNoRead : Mathproof.Problem18IMPFieldLayout20261001.noRead pairWindow := noRead_of_check (by decide)
    exact ((Mathproof.Problem18IMPFieldLayout20261001.run_frame r₅).2.2.2.1 hNoRead).trans
      ((Mathproof.Problem18IMPFieldLayout20261001.run_frame r₂).2.2.2.1 hNoRead)
  have hr : Run B trialFrameProgram σ τ 100 :=
    (r₀.seq (r₁.seq r₂)).seq ((r₃.seq (r₄.seq r₅)).seq r₆) |>.mono (by decide)
  exact ⟨τ,a,A,b+1,C,C+1,L,hr,hBank',hi,ho,⟨⟨hRaw₁,hRaw₂,haa,hA⟩,rfl,rfl⟩,
    rfl,rfl,hRawSlice.1,hXs,hYs,⟨hBNext,hC⟩,⟨hCNext,le_rfl⟩⟩

#print axioms trialFrameProgram_run
end EvenTI.P15Trial
