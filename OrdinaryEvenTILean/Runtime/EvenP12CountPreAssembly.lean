import EvenP12CountPreDispatcher

namespace EvenTI.P12CountPre

open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] {q : Nat}

private theorem getD_eq_headD (p : List Nat) : p.getD 0 0 = p.headD 0 := by
  cases p <;> rfl

private theorem getD_eq_getD_prefix {z p : List Nat} {i : Nat}
    (hp : z.take p.length = p) (hi : i < p.length) : z.getD i 0 = p.getD i 0 := by
  have h := congrArg (fun xs : List Nat => xs[i]?) hp
  rw [List.getElem?_take,if_pos hi] at h
  simpa only [List.getD_eq_getElem?_getD] using congrArg (fun u => Option.getD u (0 : Nat)) h

private theorem encodedBlock_getD (p d n : Nat) (body tail : List Nat)
    (h : body.drop p = d :: n :: tail) :
    (positiveWords (p :: body)).getD (p+1) 0 = d+1 ∧
      (positiveWords (p :: body)).getD (p+2) 0 = n+1 := by
  have hh : (positiveWords (p :: body)).drop (p+1) =
      (d+1) :: (n+1) :: positiveWords tail := by
    change (positiveWords body).drop p = _
    rw [positiveWords,← List.map_drop,h]
    rfl
  have g₀ := congrArg (fun xs : List Nat => xs.getD 0 0) hh
  have g₁ := congrArg (fun xs : List Nat => xs.getD 1 0) hh
  constructor
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_drop,Nat.add_comm] using g₀
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_drop,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using g₁

/-- Header arithmetic performed over offsets in the immutable bank gives the
same query plan as the reference decoder, including malformed inputs. -/
theorem machinePlan_eq_rawPlan (z : List Nat) (hexists : (cut z).1.length < z.length) :
    machinePlan z (cut z).1.length ((cut z).1.length+1)
      ((cut z).1.length+1+(cut (cut z).2).1.length) = rawPlan z := by
  let f := (cut z).1.length
  let a := f+1
  let b := a+(cut (cut z).2).1.length
  let tw := unpositiveWords (cut (cut z).2).1
  have hTwLen : (cut (cut z).2).1.length = tw.length := by simp [tw,unpositiveWords]
  cases hw : unpositiveWords (cut z).1 with
  | nil =>
    have hF : f = 0 := by
      simpa [f,unpositiveWords] using congrArg List.length hw
    simp [machinePlan,rawPlan,hw,f,hF]
  | cons p body =>
    let w := p :: body
    have hPrefix : (cut z).1 = positiveWords w :=
      (positiveWords_cut z).symm.trans (congrArg positiveWords hw)
    have hf : f = body.length+1 := by simp [f,hPrefix,positiveWords,w]
    have hHead : z.headD 0 = p+1 := by
      rw [← getD_eq_headD, getD_eq_getD_prefix (cut_take z) (by omega : 0 < (cut z).1.length),hPrefix]
      rfl
    have hLen (rest : List Nat) (he : body.drop p = rest) :
        rest.length = body.length-p := by rw [← he,List.length_drop]
    have hMarker (hl : 2 ≤ tw.length) : z.getD a 0 = 3 ↔ tw.head? = some 2 := by
      have hh : z.drop a = (cut z).2 := cut_drop z hexists
      have hg : z.getD a 0 = (z.drop a).getD 0 0 := by
        simp [List.getD_eq_getElem?_getD,List.getElem?_drop]
      have hPos : (cut (cut z).2).1 = positiveWords tw := (positiveWords_cut _).symm
      have hL : 0 < (cut (cut z).2).1.length := by omega
      rw [hg,hh,getD_eq_getD_prefix (cut_take (cut z).2) hL,hPos]
      cases h : tw with
      | nil => simp [h] at hl
      | cons v rest => simp [h,positiveWords] <;> omega
    cases hDrop : body.drop p with
    | nil =>
      have hm := hLen [] hDrop
      have hh : ¬ p+1+1 < f := by simp at hm; omega
      change machinePlan z f a b = rawPlan z
      simp only [machinePlan,rawPlan,hw,hDrop,hHead,if_neg hh,Nat.lt_irrefl,false_and,and_false,if_false]
    | cons d rest =>
      cases rest with
      | nil =>
        have hm := hLen [d] hDrop
        have hh : ¬ p+1+1 < f := by simp at hm; omega
        change machinePlan z f a b = rawPlan z
        simp only [machinePlan,rawPlan,hw,hDrop,hHead,if_neg hh,Nat.lt_irrefl,false_and,and_false,if_false]
      | cons n rest =>
        have hm := hLen (d::n::rest) hDrop
        simp only [List.length_cons] at hm
        have hh : p+1+1 < f := by omega
        have hd : z.getD (p+1) 0 = d+1 := by
          rw [getD_eq_getD_prefix (cut_take z) (by omega),hPrefix]
          exact (encodedBlock_getD p d n body rest hDrop).1
        have hn : z.getD (p+1+1) 0 = n+1 := by
          rw [getD_eq_getD_prefix (cut_take z) (by omega),hPrefix]
          exact (encodedBlock_getD p d n body rest hDrop).2
        have hF : 0 < f := by omega
        have hf' : f = (p :: body).length := by simpa using hf
        change machinePlan z f a b = rawPlan z
        simp only [machinePlan,rawPlan,hw,hDrop,hHead,if_pos hh,hd,hn,
          Nat.add_sub_cancel,Nat.zero_lt_succ,true_and,hF]
        by_cases hsz : 2+d*(n*n) ≤ tw.length
        · have hl : a+1 < b := by dsimp [b]; omega
          have hb : a+2+d*(n*n) ≤ b := by dsimp [b]; omega
          have hMarked := hMarker (by omega)
          have hd' : d+1 < f+2 ↔ d ≤ (p :: body).length := by omega
          have hn' : n+1 < f+2 ↔ n ≤ (p :: body).length := by omega
          have he : (a+1 < b ∧ z.getD a 0 = 3 ∧ d+1 < f+2 ∧ n+1 < f+2 ∧
              a+2+d*(n*n) ≤ b) ↔ (tw.head? = some 2 ∧ d ≤ (p :: body).length ∧
                n ≤ (p :: body).length ∧ 2+d*(n*n) ≤ tw.length) := by
            simp only [hl,hMarked,hd',hn',hb,hsz,true_and,and_true]
          have ha' : a+2 = (p :: body).length+3 := by dsimp [a]; omega
          let R := tw.head? = some 2 ∧ d ≤ (p :: body).length ∧
                n ≤ (p :: body).length ∧ 2+d*(n*n) ≤ tw.length
          let L := a+1 < b ∧ z.getD a 0 = 3 ∧ d+1 < f+2 ∧ n+1 < f+2 ∧
              a+2+d*(n*n) ≤ b
          change (if L then some (p+1,d,n,a+2) else none) =
            (if R then some (p+1,d,n,(p::body).length+3) else none)
          by_cases hR : R
          · rw [if_pos (he.mpr hR),if_pos hR,ha']
          · rw [if_neg (fun h => hR (he.mp h)),if_neg hR]
        · have hbad : ¬ a+2+d*(n*n) ≤ b := by dsimp [b]; omega
          simp [hbad,hsz,tw]

def emitLayout : Layout :=
  ⟨["length","i","word","cursor","firstEnd","secondStart","secondEnd",
     "paramEnd","modeStop","dimWord","modeWord","matrixStart","matrixEnd",
     "allEnd","square","stop"],["data"],12⟩

theorem emitProgram_ok (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) :
    Com.Ok emitLayout (emitProgram F enum) := by
  have hTable (r : List (Nat × Nat)) (v : Nat) : Com.Ok emitLayout (digitWrite r v) := by
    induction r with
    | nil => simp [digitWrite,unitPrograms,Com.Ok,Expr.Ok,emitLayout]
    | cons x xs ih =>
      rcases x with ⟨a,b⟩
      simp [digitWrite,Com.Ok,Expr.Ok,Cond.Ok,condExpr,emitLayout,ih] <;> exact ih
  have hUnits (us : List Kˣ) : Com.Ok emitLayout (unitPrograms F us) := by
    induction us with
    | nil => simp [digitWrite,unitPrograms,Com.Ok,Expr.Ok,emitLayout]
    | cons u us ih =>
      simp [unitPrograms,oneQueryProgram,headerProgram,matrixProgram,directWord,bankLoop,bankBody,bankGuard,
        advanceCursor,Com.Ok,Expr.Ok,Cond.Ok,condExpr,emitLayout,hTable,ih] <;> exact ⟨hTable _ _,ih⟩
  have hModes : Com.Ok emitLayout (modesProgram F (List.ofFn enum)) := by
    simp [modesProgram,Com.Ok,Cond.Ok,Expr.Ok,condExpr,advanceMode,emitLayout,hUnits] <;> exact hUnits _
  have hInput : Com.Ok emitLayout inputLoadLoop := by
    change Com.Ok emitLayout (.while (.lt (.var "i") (.var "length"))
      (.seq (.read "word") (.seq (.store "data" (.var "i") (.var "word"))
        (.assign "i" (.add (.var "i") (.lit 1))))))
    simp [Com.Ok,Expr.Ok,Cond.Ok,condExpr,emitLayout]
  have hContext : Com.Ok emitLayout contextProgram := by simp [contextProgram,segmentLoop,segmentCond,segmentBody,advanceCursor,Com.Ok,Expr.Ok,Cond.Ok,condExpr,emitLayout]
  have hSecond : Com.Ok emitLayout secondProgram := by simp [secondProgram,segmentLoop,segmentCond,segmentBody,advanceCursor,Com.Ok,Expr.Ok,Cond.Ok,condExpr,emitLayout]
  simp only [emitProgram,liveQueryProgram,livePayloadProgram,headerGuards,guardAll,Com.Ok,hInput,hContext,hSecond,hModes]
  simp [payloadGuard,
    querySizeGuard,payloadStart,addLiteral,predecessorExpr,dataAt,Com.Ok,Expr.Ok,Cond.Ok,condExpr,
    emitLayout,hInput,hContext,hSecond,hModes]

theorem emitProgram_run (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (z : List Nat) (B : Nat)
    (hLim : z.length+3+(z.length+1)^3 < B) (hCard : Fintype.card K + 1 < B)
    (hWord : ∀ v ∈ z, v+1 < B) :
    ∃ τ, Run B (emitProgram F enum)
      (initEnv (fun _ => z.length+1) (z.length::z)) τ
      (emitLoopBudget q (Fintype.card K) z.length+50*z.length+45) ∧
      τ.out = emitQueries F enum z := by
  let L := z.length
  have hLen : L < B := by omega
  have hOne : 1 < B := by omega
  let σ := initEnv (fun _ => L+1) (L::z)
  let σ₀ := {σ.setVar "length" L with inp := z}
  have r₀ : Run B (.read "length") σ σ₀ 1 := Run.read rfl
  have hInitial : σ₀.arrs "data" = inputBuffer z 0 := by simp [σ₀,σ,initEnv,L,inputBuffer_zero]
  have hWords : ∀ v ∈ z, v < B := fun v h => by have := hWord v h; omega
  obtain ⟨t,rt,hLength,hBank,hOut,hIn⟩ := inputLoad_run z
    (σ := σ₀) (by simp [σ₀,L]) (by simp [σ₀,σ,initEnv]) rfl hInitial hLen hOne hWords
  have ht : t.arrs "data" = sentinelWords z := hBank.trans (inputBuffer_full z)
  have hCursor : t.vars "cursor" = 0 := by
    have hv : varUntouched "cursor" inputLoadLoop := by
      change "cursor" ≠ "word" ∧ True ∧ "cursor" ≠ "i"
      decide
    rw [vars_eq_of_untouched rt (x := "cursor") hv]
    simp [σ₀,σ,initEnv]
  obtain ⟨u,ru,hFirst,hArr,hUOut,hUInp⟩ := contextProgram_run z hCursor ht hLen hWords
  have hLu := (vars_eq_of_untouched ru (x := "length") (by simp [varUntouched,contextProgram,segmentLoop,segmentBody,advanceCursor])).trans hLength
  have hCutL := cut_length_le z
  have hEFirst : (Expr.var "firstEnd").evalB B u = some (cut z).1.length := by
    simp [hFirst,hCutL.trans_lt hLen]
  have hELen : (Expr.var "length").evalB B u = some L := by rw [evalB_var_iff,show u.vars "length" = L from hLu]; exact ⟨rfl,hLen⟩
  have hEval := evalB_condLt hEFirst hELen
  rw [← emitProgramOutput_eq_emitQueries F enum z]
  by_cases h : (cut z).1.length < L
  · have hTrue : (Cond.lt (.var "firstEnd") (.var "length")).evalB B u = some true := by simpa [h] using hEval
    obtain ⟨v,rv,hf,ha,hb,hArr',hout',hin'⟩ := secondProgram_run z hFirst h
      ((congrFun hArr "data").trans ht) hLen hWords
    have haLe : (cut z).1.length+1 ≤ z.length := by omega
    have hbLe : (cut z).1.length+1+(cut (cut z).2).1.length ≤ z.length := by
      have hg := cut_length_le ((cut z).2)
      have hh := congrArg List.length (cut_drop z h)
      simp only [List.length_drop] at hh
      omega
    obtain ⟨τ,rτ,ho⟩ := liveQueryProgram_run F enum z hf ha hb hCutL haLe hbLe
      ((congrFun hArr' "data").trans ((congrFun hArr "data").trans ht)) hLim hCard hWord
    have r := r₀.seq (rt.seq (ru.seq (Run.ite_true (d := .skip) hTrue (rv.seq rτ))))
    refine ⟨τ,r.mono ?_,?_⟩
    · change _ ≤ _
      simp only [Cond.size,Expr.size]
      omega
    · rw [ho,machinePlan_eq_rawPlan z h,hout',hUOut,hOut]
      simp [σ₀,σ,initEnv,emitProgramOutput,List.append_assoc]
  · have hFalse : (Cond.lt (.var "firstEnd") (.var "length")).evalB B u = some false := by simpa [h] using hEval
    have r := r₀.seq (rt.seq (ru.seq (Run.ite_false (c := .seq secondProgram (liveQueryProgram F enum)) hFalse Run.skip)))
    refine ⟨u,r.mono ?_,?_⟩
    · simp only [Cond.size,Expr.size]
      omega
    · have hs := cut_snd_eq_nil_at_end z (by dsimp [L] at h; omega)
      have hnone : rawPlan z = none := by
        unfold rawPlan
        simp only [hs,cut,unpositiveWords,List.map_nil]
        split <;> try rfl
        split <;> simp
      rw [hUOut,hOut,emitProgramOutput,hnone]
      simp [σ₀,σ,initEnv]

noncomputable def emitCostPoly (q card : Nat) : Polynomial Nat :=
  (Polynomial.C q *
      (13 * Polynomial.X + Polynomial.C (4*(card+1)+13) * (Polynomial.X*Polynomial.X)+26)+15) *
    Polynomial.X + 50 * Polynomial.X + 175

theorem emitQueries_turingPolytime (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) :
    TuringPolytime (emitQueries F enum) := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  let card := Fintype.card K
  let P : Polynomial Nat := (Polynomial.X+1)^3 + Polynomial.X + Polynomial.C (card+12)
  apply ramPolytime_of_bounded_imp emitLayout (emitProgram F enum) (emitQueries F enum)
    P (emitCostPoly q card) (emitProgram_ok F enum)
  intro z
  let s := bitSize z
  let B := 2^(P.eval s+s+1)
  have hLen : z.length ≤ s := Lax51Proofs.Encoding.length_le_bitSize z
  have hLim : z.length+3+(z.length+1)^3 < B := by
    have hPow : (z.length+1)^3 ≤ (s+1)^3 := Nat.pow_le_pow_left (by omega) _
    apply (Nat.lt_two_pow_self (n := z.length+3+(z.length+1)^3)).trans_le
    apply Nat.pow_le_pow_right (by omega)
    simp [P]
    omega
  have hCard : card+1 < B := by
    apply (Nat.lt_two_pow_self (n := card+1)).trans_le
    apply Nat.pow_le_pow_right (by omega)
    simp [P]
    omega
  have hWord : ∀ v ∈ z, v+1 < B := by
    intro v hv
    have ht := Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hv
    exact (Nat.succ_le_of_lt ht).trans_lt (Nat.pow_lt_pow_right (by omega)
      (by change s+1 < P.eval s+s+1; simp [P] <;> omega))
  obtain ⟨τ,hr,ho⟩ := emitProgram_run F enum z B hLim hCard hWord
  refine ⟨fun _ => z.length+1,τ,hr.mono ?_,ho⟩
  have hc : emitLoopBudget q card z.length ≤ emitLoopBudget q card s := by
    unfold emitLoopBudget
    gcongr
  have hEval : (emitCostPoly q card).eval s = emitLoopBudget q card s + 50*s + 45 := by
    simp [emitCostPoly,emitLoopBudget] <;> omega
  change emitLoopBudget q card z.length + 50*z.length + 45 ≤ (emitCostPoly q card).eval s
  exact (Nat.add_le_add_right (Nat.add_le_add hc (Nat.mul_le_mul_left 50 hLen)) 45).trans_eq hEval.symm

theorem countPreZ_turingPolytime_checked (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) [DecidableEq K]
    (hCompare : TuringPolytime (EvenTI.Contract.compareWords F P)) :
    TuringPolytime (countPreZ F P enum) :=
  countPreZ_turingPolytime_of_emitQueries F enum P hCompare (emitQueries_turingPolytime F enum)

#print axioms emitProgram_run
#print axioms emitQueries_turingPolytime
#print axioms countPreZ_turingPolytime_checked
#print axioms machinePlan_eq_rawPlan
end EvenTI.P12CountPre
