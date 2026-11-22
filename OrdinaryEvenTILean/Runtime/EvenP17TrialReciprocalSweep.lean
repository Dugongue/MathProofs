import EvenP17ExecutionCells

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.P16Execution EvenTI.P17Execution EvenTI.PrimaryAlignment
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

def reciprocalSweepIndex : String := "even.reciprocal.sweep.index"
def reciprocalSweepLimit : String := "even.reciprocal.sweep.limit"

private def activeStride (n l i : ℕ) : ℕ := if i ≤ l then n^(l-i) else 0

private theorem activeStride_next {n l i : ℕ} (hn : 2 ≤ n) (hi : i<l+1) :
    activeStride n l i/n=activeStride n l (i+1) := by
  have hle : i≤l := by omega
  by_cases h : i<l
  · have h' : i+1≤l := by omega
    simp only [activeStride,if_pos hle,if_pos h']
    rw [show l-i=(l-(i+1))+1 by omega,pow_succ]
    exact Nat.mul_div_cancel _ (by omega)
  · have he : i=l := by omega
    subst i
    have hh : ¬l+1≤l := by omega
    simp [activeStride,hh,Nat.div_eq_of_lt (show 1<n by omega)]

def startReciprocalSweep : Com :=
  .seq (.assign reciprocalSweepIndex (.lit 0)) (.assign crossStride (.var crossA))

def reciprocalSweepGuard : Cond := .lt (.var reciprocalSweepIndex) (.var reciprocalSweepLimit)

def reciprocalSweepStep (visit : Com) : Com :=
  .seq visit (.seq
    (.assign crossStride (.div (.var crossStride) (.var crossN)))
    (.assign reciprocalSweepIndex (.add (.var reciprocalSweepIndex) (.lit 1))))

def reciprocalSweep (visit : Com) : Com :=
  .seq startReciprocalSweep (.while reciprocalSweepGuard (reciprocalSweepStep visit))

def reciprocalTwoSweeps (trueVisit falseVisit : Com) : Com :=
  .seq (reciprocalSweep trueVisit) (reciprocalSweep falseVisit)

private structure SweepInv (ctx : Env → Prop) (render : ℕ → List ℕ) (σ τ : Env) (n l : ℕ) : Prop where
  context : ctx τ
  width : τ.vars crossN=n
  power : τ.vars crossA=n^l
  limit : τ.vars reciprocalSweepLimit=l+1
  cursor : τ.vars reciprocalSweepIndex≤l+1
  stride : τ.vars crossStride=activeStride n l (τ.vars reciprocalSweepIndex)
  input : τ.inp=σ.inp
  output : τ.out=σ.out++(List.range (τ.vars reciprocalSweepIndex)).flatMap render

private theorem sweepWord {B k : ℕ} {τ : Env} {v : String} (hEq : τ.vars v=k) (h : k<B) :
    (Expr.var v).evalB B τ=some k := evalB_var_iff.mpr ⟨hEq.symm,hEq ▸ h⟩

/-- The actual retained-mode clock runs from the installed power n^l down
to 1. Each visit sees both its exact index and its exact mixed-radix stride. -/
theorem reciprocalSweep_run {B n l C : ℕ} (visit : Com) (ctx : Env → Prop) (render : ℕ → List ℕ)
    (hn : 2≤n) (hnB : n<B) (haB : n^l<B) (hlB : l+1<B)
    (hIdx : ∀ τ i, ctx τ → ctx (τ.setVar reciprocalSweepIndex i))
    (hStride : ∀ τ k, ctx τ → ctx (τ.setVar crossStride k))
    (hVisit : ∀ ρ i, ctx ρ → i<l+1 →
      ρ.vars reciprocalSweepIndex=i → ρ.vars crossStride=n^(l-i) → ρ.vars crossN=n →
      ∃ τ, Run B visit ρ τ C ∧ ctx τ ∧ τ.vars reciprocalSweepIndex=i ∧
        τ.vars crossStride=n^(l-i) ∧ τ.vars crossN=ρ.vars crossN ∧ τ.vars crossA=ρ.vars crossA ∧
        τ.vars reciprocalSweepLimit=ρ.vars reciprocalSweepLimit ∧ τ.inp=ρ.inp ∧
        τ.out=ρ.out++render i)
    {σ : Env} (hCtx : ctx σ) (hN : σ.vars crossN=n) (hA : σ.vars crossA=n^l)
    (hL : σ.vars reciprocalSweepLimit=l+1) :
    ∃ τ, Run B (reciprocalSweep visit) σ τ ((C+12)*(l+1)+8) ∧ ctx τ ∧
      τ.vars crossN=n ∧ τ.vars crossA=n^l ∧ τ.vars reciprocalSweepLimit=l+1 ∧
      τ.vars reciprocalSweepIndex=l+1 ∧ τ.vars crossStride=0 ∧
      τ.inp=σ.inp ∧ τ.out=σ.out++(List.range (l+1)).flatMap render := by
  let I := fun τ : Env => SweepInv ctx render σ τ n l
  let V := fun τ : Env => l+1-τ.vars reciprocalSweepIndex
  let α := σ.setVar reciprocalSweepIndex 0
  let β := α.setVar crossStride (n^l)
  have h₀ : Run B (.assign reciprocalSweepIndex (.lit 0)) σ α 2 :=
    Run.assign (evalB_lit (by omega))
  have h₁ : Run B (.assign crossStride (.var crossA)) α β 2 :=
    Run.assign (sweepWord (show α.vars crossA=n^l from hA) haB)
  have hInit : I β := by
    refine ⟨hStride α _ (hIdx σ _ hCtx),hN,hA,hL,?_,?_,rfl,?_⟩
    · simp [β,α,show reciprocalSweepIndex≠crossStride by decide]
    · simp [β,α,show reciprocalSweepIndex≠crossStride by decide,activeStride]
    · simp [β,α,show reciprocalSweepIndex≠crossStride by decide]
  have guard (τ : Env) (h : I τ) :
      reciprocalSweepGuard.evalB B τ=some (decide (τ.vars reciprocalSweepIndex<l+1)) := by
    exact evalB_condLt (evalB_var (h.cursor.trans_lt hlB)) (sweepWord h.limit hlB)
  have step (ρ : Env) (h : I ρ) (hg : reciprocalSweepGuard.evalB B ρ=some true) :
      ∃ τ, Run B (reciprocalSweepStep visit) ρ τ (C+8) ∧ I τ ∧ V τ<V ρ := by
    rw [guard ρ h] at hg
    let i := ρ.vars reciprocalSweepIndex
    have hi : i<l+1 := of_decide_eq_true (Option.some.inj hg)
    have hs : ρ.vars crossStride=n^(l-i) := by
      have hCurrent : ρ.vars crossStride=activeStride n l i := h.stride
      simpa [activeStride,show i≤l by omega] using hCurrent
    obtain ⟨γ,rg,hctx,hcur,hst,hnγ,haγ,hlγ,hin,hout⟩ :=
      hVisit ρ i h.context hi rfl hs h.width
    let η := γ.setVar crossStride (activeStride n l (i+1))
    let τ := η.setVar reciprocalSweepIndex (i+1)
    have hnγ' : γ.vars crossN=n := hnγ.trans h.width
    have hPow : n^(l-i)<B := (Nat.pow_le_pow_right (by omega : 0<n) (Nat.sub_le _ _)).trans_lt haB
    have hDivB : n^(l-i)/n < B := (Nat.div_le_self _ _).trans_lt hPow
    have r₂ : Run B (.assign crossStride (.div (.var crossStride) (.var crossN))) γ
        (γ.setVar crossStride (n^(l-i)/n)) 4 :=
      Run.assign (evalB_bin (op:=.div) (sweepWord hst hPow) (sweepWord hnγ' hnB) hDivB)
    have hNextEq : n^(l-i)/n=activeStride n l (i+1) := by
      rw [←activeStride_next hn hi,activeStride,if_pos (show i≤l by omega)]
    have hAdvance : Run B (.assign crossStride (.div (.var crossStride) (.var crossN))) γ η 4 := by
      simpa only [η,hNextEq] using r₂
    have hCurη : η.vars reciprocalSweepIndex=i := hcur
    have r₃ : Run B (.assign reciprocalSweepIndex (.add (.var reciprocalSweepIndex) (.lit 1))) η τ 4 :=
      Run.assign (evalB_bin (op:=.add) (sweepWord hCurη (hi.trans hlB))
        (evalB_lit (by omega)) (show i+1<B by omega))
    have hτidx : τ.vars reciprocalSweepIndex=i+1 := by simp [τ]
    refine ⟨τ,(rg.seq (hAdvance.seq r₃)).mono (by omega),?_,?_⟩
    · refine ⟨hIdx η _ (hStride γ _ hctx),hnγ.trans h.width,haγ.trans h.power,hlγ.trans h.limit,
        (by rw [hτidx];omega),?_,hin.trans h.input,?_⟩
      · rw [hτidx]
        rfl
      · change γ.out=_
        rw [hout,h.output,hτidx,show ρ.vars reciprocalSweepIndex=i from rfl,List.range_succ,List.flatMap_append]
        simp [List.append_assoc]
    · change l+1-τ.vars reciprocalSweepIndex<l+1-ρ.vars reciprocalSweepIndex
      rw [hτidx,show ρ.vars reciprocalSweepIndex=i from rfl]
      omega
  obtain ⟨τ,r,hT,hG⟩ := Run.while_count I V (C+8)
    (fun τ h => ⟨_,guard τ h⟩) step hInit
  rw [guard τ hT] at hG
  have hDone : τ.vars reciprocalSweepIndex=l+1 :=
    le_antisymm hT.cursor (by have he := of_decide_eq_false (Option.some.inj hG);omega)
  have hZ : τ.vars crossStride=0 := by rw [hT.stride,hDone,activeStride,if_neg (by omega)]
  have hBound : V β=l+1 := by simp [V,β,α,show reciprocalSweepIndex≠crossStride by decide]
  refine ⟨τ,?_,hT.context,hT.width,hT.power,hT.limit,hDone,hZ,hT.input,by simpa only [hDone] using hT.output⟩
  rw [hBound] at r
  change Run B _ β τ ((1+3+(C+8))*(l+1)+1+3) at r
  have hClock : 1+3+(C+8)=C+12 := by omega
  rw [hClock] at r
  have hRun : Run B (reciprocalSweep visit) σ τ (4+((C+12)*(l+1)+1+3)) :=
    (h₀.seq h₁).seq r
  exact hRun.mono (by omega)

def reciprocalPayloadAt {l : ℕ} (payload : HigherModes l → List ℕ) (mirror : Bool) (i : ℕ) : List ℕ :=
  if h : i<l+1 then payload (mirror,⟨i,h⟩) else []

private theorem retainedRange_from_finRange (l : ℕ) :
    (List.finRange (l+1)).map (fun i => i.val)=List.range (l+1) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem reciprocalOrder_payload {l : ℕ} (payload : HigherModes l → List ℕ) :
    (List.ofFn (fun i => payload (reciprocalOrder l i))).flatten =
      (List.range (l+1)).flatMap (reciprocalPayloadAt payload true) ++
      (List.range (l+1)).flatMap (reciprocalPayloadAt payload false) := by
  rw [List.ofFn_add,List.flatten_append,←retainedRange_from_finRange l]
  have hTrue (i : Fin (l+1)) :
      reciprocalOrder l (i.castLE (Nat.le_add_right (l+1) (l+1)))=(true,i) :=
    reciprocalOrder_first i
  have hPayload (b : Bool) (i : Fin (l+1)) :
      reciprocalPayloadAt payload b i.val=payload (b,i) := by
    simp only [reciprocalPayloadAt,dif_pos i.isLt]
  simp only [hTrue,reciprocalOrder_second,List.flatMap_map,
    List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,hPayload]

/-- Execute both visits in their public order. The first loop emits the
right half's anchors and the second loop emits the left half's anchors. -/
theorem reciprocalTwoSweeps_run {B n l : ℕ}
    (visit : Bool → Com) (cost : Bool → ℕ) (ctx : Env → Prop) (payload : HigherModes l → List ℕ)
    (hn : 2≤n) (hnB : n<B) (haB : n^l<B) (hlB : l+1<B)
    (hIdx : ∀ τ i, ctx τ → ctx (τ.setVar reciprocalSweepIndex i))
    (hStride : ∀ τ k, ctx τ → ctx (τ.setVar crossStride k))
    (hVisit : ∀ (mirror : Bool) ρ (i : Fin (l+1)), ctx ρ →
      ρ.vars reciprocalSweepIndex=i.val → ρ.vars crossStride=n^(l-i.val) → ρ.vars crossN=n →
      ∃ τ, Run B (visit mirror) ρ τ (cost mirror) ∧ ctx τ ∧ τ.vars reciprocalSweepIndex=i.val ∧
        τ.vars crossStride=n^(l-i.val) ∧ τ.vars crossN=ρ.vars crossN ∧ τ.vars crossA=ρ.vars crossA ∧
        τ.vars reciprocalSweepLimit=ρ.vars reciprocalSweepLimit ∧ τ.inp=ρ.inp ∧
        τ.out=ρ.out++payload (mirror,i))
    {σ : Env} (hCtx : ctx σ) (hN : σ.vars crossN=n) (hA : σ.vars crossA=n^l)
    (hL : σ.vars reciprocalSweepLimit=l+1) :
    ∃ τ, Run B (reciprocalTwoSweeps (visit true) (visit false)) σ τ
      (((cost true+12)*(l+1)+8)+((cost false+12)*(l+1)+8)) ∧
      ctx τ ∧ τ.inp=σ.inp ∧ τ.out=σ.out++(List.ofFn (fun i => payload (reciprocalOrder l i))).flatten := by
  have runHalf (mirror : Bool) {s : Env} (hctx : ctx s)
      (hN : s.vars crossN=n) (hA : s.vars crossA=n^l) (hL : s.vars reciprocalSweepLimit=l+1) :
      ∃ t, Run B (reciprocalSweep (visit mirror)) s t ((cost mirror+12)*(l+1)+8) ∧
        ctx t ∧ t.vars crossN=n ∧ t.vars crossA=n^l ∧ t.vars reciprocalSweepLimit=l+1 ∧
        t.vars reciprocalSweepIndex=l+1 ∧ t.vars crossStride=0 ∧ t.inp=s.inp ∧
        t.out=s.out++(List.range (l+1)).flatMap (reciprocalPayloadAt payload mirror) :=
    reciprocalSweep_run (visit mirror) ctx (reciprocalPayloadAt payload mirror) hn hnB haB hlB hIdx hStride
      (by
        intro ρ i hρ hi hcur hst hw
        simpa only [reciprocalPayloadAt,dif_pos hi] using hVisit mirror ρ ⟨i,hi⟩ hρ hcur hst hw)
      hctx hN hA hL
  obtain ⟨α,r₁,hα,hNα,hAα,hLα,_,_,hiα,hoα⟩ := runHalf true hCtx hN hA hL
  obtain ⟨τ,r₂,hτ,_,_,_,_,_,hiτ,hoτ⟩ := runHalf false hα hNα hAα hLα
  refine ⟨τ,r₁.seq r₂,hτ,hiτ.trans hiα,?_⟩
  rw [hoτ,hoα,reciprocalOrder_payload,List.append_assoc]

#print axioms reciprocalOrder_payload
#print axioms reciprocalTwoSweeps_run
def setReciprocalSweepLimit : Com :=
  .assign reciprocalSweepLimit (.div (.var reciprocalCountWord) (.lit 2))

/-- The two physical passes obtain their common bound from the count emitted
by the existing reciprocal header. -/
theorem setReciprocalSweepLimit_run {B l : ℕ} {σ : Env}
    (hCount : σ.vars reciprocalCountWord=(l+1)+(l+1))
    (hB : (l+1)+(l+1)<B) (hTwo : 2<B) :
    Run B setReciprocalSweepLimit σ (σ.setVar reciprocalSweepLimit (l+1)) 4 := by
  have h := evalB_bin (op:=.div) (sweepWord hCount hB) (evalB_lit hTwo)
    (show ((l+1)+(l+1))/2<B by omega)
  simpa [setReciprocalSweepLimit,show ((l+1)+(l+1))/2=l+1 by omega] using Run.assign h

#print axioms setReciprocalSweepLimit_run
#print axioms reciprocalSweep_run
end EvenTI.P17Trial
