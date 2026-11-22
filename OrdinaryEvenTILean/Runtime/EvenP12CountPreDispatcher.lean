import EvenP12CountPreTape
import EvenP12CountPrePayload

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle

set_option autoImplicit false
variable {K : Type} [Field K] [Fintype K] {q : Nat}

def guardAll : List Cond → Com → Com
  | [], body => body
  | g :: gs, body => .ite g (guardAll gs body) .skip

def guardCost (cs : List Cond) : Nat := (cs.map (fun c => 1+c.size)).sum

theorem guardAll_run_true {B N : Nat} {σ τ : Env} (cs : List Cond) (body : Com)
    (hs : ∀ c ∈ cs, c.evalB B σ = some true) (hr : Run B body σ τ N) :
    Run B (guardAll cs body) σ τ (guardCost cs + N) := by
  induction cs with
  | nil => simpa [guardAll,guardCost] using hr
  | cons c cs ih =>
    have hc := hs c List.mem_cons_self
    have hcs : ∀ g ∈ cs, g.evalB B σ = some true :=
      fun g hg => hs g (List.mem_cons_of_mem c hg)
    exact (Run.ite_true (d := .skip) hc (ih hcs)).mono (by simp [guardCost] <;> omega)

theorem guardAll_run_false {B : Nat} {σ : Env} (cs : List Cond) (body : Com)
    (hs : ∀ c ∈ cs, ∃ b, c.evalB B σ = some b)
    (hn : ¬ ∀ c ∈ cs, c.evalB B σ = some true) :
    Run B (guardAll cs body) σ σ (guardCost cs + 1) := by
  induction cs with
  | nil => exact False.elim (hn (by simp))
  | cons c cs ih =>
    obtain ⟨b,hb⟩ := hs c List.mem_cons_self
    have hcs : ∀ g ∈ cs, ∃ b, g.evalB B σ = some b :=
      fun g hg => hs g (List.mem_cons_of_mem c hg)
    cases b with
    | false =>
      exact (Run.ite_false (c := guardAll cs body) hb Run.skip).mono (by simp [guardCost] <;> omega)
    | true =>
      have hf : ¬ ∀ g ∈ cs, g.evalB B σ = some true := by simpa [hb] using hn
      exact (Run.ite_true (d := .skip) hb (ih hcs hf)).mono (by simp [guardCost] <;> omega)

def headerGuards : List Cond :=
  [.lt (.lit 0) (.var "modeStop"),
    .lt (.lit 0) (.var "dimWord"),
    .lt (addLiteral (.var "secondStart") 1) (.var "secondEnd"),
    .eq (dataAt (.var "secondStart")) (.lit 3),
    .lt (.var "modeStop") (addLiteral (.var "firstEnd") 2),
    .lt (.var "dimWord") (addLiteral (.var "firstEnd") 2)]

def payloadGuard : Cond := .lt (.var "allEnd") (addLiteral (.var "secondEnd") 1)

def livePayloadProgram (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) : Com :=
  .seq payloadStart (.ite payloadGuard (modesProgram F (List.ofFn enum)) .skip)

def liveQueryProgram (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) : Com :=
  .ite (.lt (.lit 0) (.var "firstEnd"))
    (.seq querySizeGuard (guardAll headerGuards (livePayloadProgram F enum)))
    .skip
def emitProgram (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) : Com :=
  .seq (.read "length") (.seq inputLoadLoop (.seq contextProgram
    (.ite (.lt (.var "firstEnd") (.var "length"))
      (.seq secondProgram (liveQueryProgram F enum))
      .skip)))

/-- A raw plan has the exact dimensions and physical locations used by
the live query loop. The guards inspect the actual decoded segment lengths. -/
def rawPlan (z : List Nat) : Option (Nat × Nat × Nat × Nat) :=
  let w := unpositiveWords (cut z).1
  let tw := unpositiveWords (cut (cut z).2).1
  match w with
  | p :: body =>
    match body.drop p with
    | d :: n :: _ =>
      if tw.head? = some 2 ∧ d ≤ w.length ∧ n ≤ w.length ∧ 2+d*(n*n) ≤ tw.length
      then some (p+1,d,n,w.length+3)
      else none
    | _ => none
  | _ => none

def emitProgramOutput (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (z : List Nat) : List Nat :=
  (cut z).1 ++ [0] ++
    match rawPlan z with
    | none => []
    | some (p,d,n,a) => queryTape F enum z p d n a

/-- The final address guard is checked on the live packed tape before the
serializer is allowed to read any matrix entry. -/
theorem livePayloadProgram_run (F : FieldEncoding K) (enum : Fin q ≃ Kˣ)
    (z : List Nat) {B e d n a b : Nat} {σ : Env}
    (he : σ.vars "paramEnd" = e) (hd : σ.vars "modeStop" = d+1)
    (hn : σ.vars "dimWord" = n+1) (ha : σ.vars "secondStart" = a)
    (hb : σ.vars "secondEnd" = b) (he1 : 1 ≤ e) (hez : e ≤ z.length)
    (hbz : b ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length + n*n + 1 < B) (hCard : Fintype.card K + 1 < B)
    (hD : d+1 < B) (hN : n+1 < B)
    (hm : a+2+n*n < B) (hAll : a+2+d*(n*n) < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (livePayloadProgram F enum) σ τ
        ((q*(13 * e + (4 * (Fintype.card K + 1) + 13)*(n*n)+26)+15)*d+42) ∧
      τ.out = σ.out ++ (if a+2+d*(n*n) ≤ b then queryTape F enum z e d n (a+2) else []) := by
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  have hB : 1 < B := by omega
  obtain ⟨t,hr,hStart,hSq,hEnd,hAllEnd,hMode,hv,hArr,hOut⟩ :=
    payloadStart_run ha hd hn hB hD hN hm hAll
  have hb' := (hv "secondEnd" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
  have haEval : (Expr.var "allEnd").evalB B t = some (a+2+d*(n*n)) := by simp [hAllEnd,hAll]
  have hbEval : (Expr.var "secondEnd").evalB B t = some b := by simp [hb',show b < B by omega]
  have hEndEval : (addLiteral (.var "secondEnd") 1).evalB B t = some (b+1) :=
    evalB_bin (op := .add) hbEval (evalB_lit hB) (show b+1 < B by omega)
  have hGuard := evalB_condLt haEval hEndEval
  by_cases h : a+2+d*(n*n) ≤ b
  · have hTrue : payloadGuard.evalB B t = some true := by
      unfold payloadGuard
      rw [hGuard]
      exact congrArg some (decide_eq_true (by omega))
    have hPar := (hv "paramEnd" (by decide) (by decide) (by decide) (by decide) (by decide)).trans he
    have hDim := (hv "dimWord" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn
    have hStop := (hv "modeStop" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd
    obtain ⟨τ,rt,hout⟩ := modesProgram_run F (List.ofFn enum) z hPar hDim hMode hStop
      hStart hEnd hSq he1 hez (h.trans hbz) ((congrFun hArr "data").trans hBank) (by omega) hCard hD hN hWords
    have rr := hr.seq (Run.ite_true (d := .skip) hTrue rt)
    refine ⟨τ,rr.mono ?_,?_⟩
    · simp only [List.length_ofFn,payloadGuard,addLiteral,Cond.size,Expr.size]
      omega
    · simp [h,hout,hOut,queryTape]
  · have hFalse : payloadGuard.evalB B t = some false := by
      unfold payloadGuard
      rw [hGuard]
      exact congrArg some (decide_eq_false (by omega))
    have r := hr.seq (Run.ite_false (c := modesProgram F (List.ofFn enum)) hFalse Run.skip)
    exact ⟨t,r.mono (by simp [payloadGuard,addLiteral,Cond.size,Expr.size] <;> omega),by simp [h,hOut]⟩

def emitLoopBudget (q card L : Nat) : Nat :=
  (q*(13 * L + (4 * (card + 1) + 13)*(L*L)+26)+15)*L+130

def machinePlan (z : List Nat) (f a b : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let e := z.headD 0
  let m := if e+1 < f then z.getD e 0 else 0
  let n := if e+1 < f then z.getD (e+1) 0 else 0
  if 0 < f ∧ 0 < m ∧ 0 < n ∧ a+1 < b ∧ z.getD a 0 = 3 ∧ m < f+2 ∧ n < f+2 ∧
      a+2+(m-1)*((n-1)*(n-1)) ≤ b then some (e,m-1,n-1,a+2)
  else none

private theorem getDataTotal {z : List Nat} {B a : Nat} {σ : Env}
    (ha : σ.vars "secondStart" = a) (haz : a ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hWords : ∀ v ∈ z, v+1 < B) :
    (dataAt (.var "secondStart")).evalB B σ = some (z.getD a 0) := by
  have he : (Expr.var "secondStart").evalB B σ = some a := by simp [ha,haz.trans_lt hLen]
  by_cases h : a < z.length
  · have hget : z.getD a 0 = z[a] := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
    rw [hget]
    exact eval_dataAt he h hBank (fun v hv => by have := hWords v hv; omega)
  · have ha' : a = z.length := by omega
    rw [ha'] at he ⊢
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : z.length ≤ z.length),Option.getD_none]
    exact evalB_get he (by rw [hBank]; simp [sentinelWords]) (show 0 < B by omega)

theorem liveQueryProgram_run (F : FieldEncoding K) (enum : Fin q ≃ Kˣ)
    (z : List Nat) {B f a b : Nat} {σ : Env}
    (hf : σ.vars "firstEnd" = f) (ha : σ.vars "secondStart" = a) (hb : σ.vars "secondEnd" = b)
    (hfz : f ≤ z.length) (haz : a ≤ z.length) (hbz : b ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hLim : z.length+3+(z.length+1)^3 < B) (hCard : Fintype.card K + 1 < B)
    (hWords : ∀ v ∈ z, v+1 < B) :
    ∃ τ, Run B (liveQueryProgram F enum) σ τ (emitLoopBudget q (Fintype.card K) z.length) ∧
      τ.out = σ.out ++
        match machinePlan z f a b with
        | none => []
        | some (e,d,n,a) => queryTape F enum z e d n a := by
  let L := z.length
  change L+3+(L+1)^3 < B at hLim
  have hLen : L < B := by omega
  have h3 : 3 < B := by omega
  have evF : (Expr.var "firstEnd").evalB B σ = some f := by simp [hf,hfz.trans_lt hLen]
  have hg := evalB_condLt (evalB_lit (B := B) (σ := σ) (n := 0) (by omega)) evF
  by_cases hF : 0 < f
  · have hgT : (Cond.lt (.lit 0) (.var "firstEnd")).evalB B σ = some true := by simpa [hF] using hg
    let e := z.headD 0
    let m := if e+1 < f then z.getD e 0 else 0
    let n := if e+1 < f then z.getD (e+1) 0 else 0
    obtain ⟨t,rt,he,hm,hn,hf',hArr,hOut⟩ :=
      querySizeGuard_run z hf hF hfz hBank hLen hWords
    have ha' := (vars_eq_of_untouched rt (x := "secondStart") (by simp [varUntouched,querySizeGuard])).trans ha
    have hb' := (vars_eq_of_untouched rt (x := "secondEnd") (by simp [varUntouched,querySizeGuard])).trans hb
    have hW (i : Nat) : z.getD i 0 < B := by
      by_cases hi : i < z.length
      · have hh := hWords _ (List.getElem_mem hi)
        simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using Nat.lt_of_succ_lt hh
      · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : z.length ≤ i)]
        omega
    have hM : m < B := by dsimp [m]; split <;> first | exact hW _ | omega
    have hN : n < B := by dsimp [n]; split <;> first | exact hW _ | omega
    have evM : (Expr.var "modeStop").evalB B t = some m := by rw [evalB_var_iff, show t.vars "modeStop" = m from hm]; exact ⟨rfl,hM⟩
    have evN : (Expr.var "dimWord").evalB B t = some n := by rw [evalB_var_iff, show t.vars "dimWord" = n from hn]; exact ⟨rfl,hN⟩
    have evA : (Expr.var "secondStart").evalB B t = some a := by simp [ha',haz.trans_lt hLen]
    have evB : (Expr.var "secondEnd").evalB B t = some b := by simp [hb',hbz.trans_lt hLen]
    have evF' : (Expr.var "firstEnd").evalB B t = some f := by simp [hf',hfz.trans_lt hLen]
    have evOne := evalB_lit (B := B) (σ := t) (n := 1) (by omega)
    have evTwo := evalB_lit (B := B) (σ := t) (n := 2) (by omega)
    have evZero := evalB_lit (B := B) (σ := t) (n := 0) (by omega)
    have evA' : (addLiteral (.var "secondStart") 1).evalB B t = some (a+1) :=
      evalB_bin (op := .add) evA evOne (show a+1 < B by omega)
    have evF'' : (addLiteral (.var "firstEnd") 2).evalB B t = some (f+2) :=
      evalB_bin (op := .add) evF' evTwo (show f+2 < B by omega)
    have e₁ := evalB_condLt evZero evM
    have e₂ := evalB_condLt evZero evN
    have e₃ := evalB_condLt evA' evB
    have e₄ := evalB_condEq (getDataTotal ha' haz ((congrFun hArr "data").trans hBank) hLen hWords) (evalB_lit h3)
    have e₅ := evalB_condLt evM evF''
    have e₆ := evalB_condLt evN evF''
    let pass := 0 < m ∧ 0 < n ∧ a+1 < b ∧ z.getD a 0 = 3 ∧ m < f+2 ∧ n < f+2
    have hEval : (∀ g ∈ headerGuards, g.evalB B t = some true) ↔ pass := by
      simp [headerGuards,pass,e₁,e₂,e₃,e₄,e₅,e₆]
    have hAllEval : ∀ g ∈ headerGuards, ∃ v, g.evalB B t = some v := by
      intro g hg
      simp only [headerGuards,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,e₁⟩
      · exact ⟨_,e₂⟩
      · exact ⟨_,e₃⟩
      · exact ⟨_,e₄⟩
      · exact ⟨_,e₅⟩
      · exact ⟨_,e₆⟩
    by_cases hP : pass
    · have hpEF : e+1 < f := by
        by_contra! h
        have hh := hP.1
        simp [m,if_neg (by omega : ¬ e+1 < f)] at hh
      have he1 : 1 ≤ e := by
        by_contra! h
        have hs : z.getD 0 0 = e := by cases z <;> rfl
        have he : e = 0 := by omega
        have hm' := hP.1
        have heq : m = e := by
          change (if e+1 < f then z.getD e 0 else 0) = e
          rw [if_pos hpEF,he,hs,he]
        omega
      have hez : e ≤ L := by omega
      have hDl : m-1 ≤ L := by have := hP.2.2.2.2.1; omega
      have hNl : n-1 ≤ L := by have := hP.2.2.2.2.2; omega
      have mEq : m-1+1 = m := by have := hP.1; omega
      have nEq : n-1+1 = n := by have := hP.2.1; omega
      have hsq := Nat.mul_le_mul hNl hNl
      have hSmall := Nat.mul_le_mul (Nat.le_refl (L+1)) hsq
      have hCube : (L+1)*(L*L) ≤ (L+1)^3 := by
        calc
          (L+1)*(L*L) ≤ (L+1)*((L+1)*(L+1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))
          _ = (L+1)^3 := by ring
      have hAll := (Nat.mul_le_mul hDl hsq).trans
        ((Nat.mul_le_mul_right _ (Nat.le_succ L)).trans hCube)
      have hSle : (n-1)*(n-1) ≤ (L+1)*((n-1)*(n-1)) := by
        exact (one_mul ((n-1)*(n-1))).symm.le.trans
          (Nat.mul_le_mul_right _ (by omega))
      have hSq := hSle.trans (hSmall.trans hCube)
      have hm' : t.vars "modeStop" = (m-1)+1 := hm.trans mEq.symm
      have hn' : t.vars "dimWord" = (n-1)+1 := hn.trans nEq.symm
      have hL : z.length = L := rfl
      rw [hL] at haz hbz
      obtain ⟨τ,rτ,ho⟩ := livePayloadProgram_run F enum z he hm' hn' ha' hb' he1 hez hbz
        ((congrFun hArr "data").trans hBank) (by rw [hL]; omega) hCard (by rw [mEq]; exact hM) (by rw [nEq]; exact hN)
        (by omega) (by omega) (fun v hv => by have := hWords v hv; omega)
      have rr := Run.ite_true (d := .skip) hgT (rt.seq (guardAll_run_true headerGuards _ (hEval.mpr hP) rτ))
      refine ⟨τ,rr.mono ?_,?_⟩
      · have hcost : guardCost headerGuards ≤ 50 := by decide
        have hBase :
          13 * e + (4 * (Fintype.card K + 1) + 13) * ((n-1)*(n-1))+26 ≤
            13 * L + (4 * (Fintype.card K + 1) + 13)*(L*L)+26 := by gcongr
        have hmul :
          (q*(13 * e + (4 * (Fintype.card K + 1) + 13)*((n-1)*(n-1))+26)+15)*(m-1) ≤
            (q*(13 * L + (4 * (Fintype.card K + 1) + 13)*(L*L)+26)+15)*L := by gcongr
        change 4+(18+(guardCost headerGuards+
            ((q*(13*e+(4*(Fintype.card K+1)+13)*((n-1)*(n-1))+26)+15)*(m-1)+42))) ≤
          (q*(13*L+(4*(Fintype.card K+1)+13)*(L*L)+26)+15)*L+130
        omega
      · by_cases hh : a+2+(m-1)*((n-1)*(n-1)) ≤ b
        · have hmPlan : machinePlan z f a b = some (e,m-1,n-1,a+2) := by
            exact if_pos ⟨hF,hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,hP.2.2.2.2.1,hP.2.2.2.2.2,hh⟩
          rw [hmPlan,ho,hOut,if_pos hh]
        · have hmPlan : machinePlan z f a b = none := by
            exact if_neg (fun c => hh c.2.2.2.2.2.2.2)
          rw [hmPlan,ho,hOut,if_neg hh]
    · have hr : Run B (guardAll headerGuards (livePayloadProgram F enum)) t t
          (guardCost headerGuards+1) :=
        guardAll_run_false headerGuards _ hAllEval (fun h => hP (hEval.mp h))
      have rr := Run.ite_true (d := .skip) hgT (rt.seq hr)
      refine ⟨t,rr.mono ?_,?_⟩
      · have hcost : guardCost headerGuards ≤ 50 := by decide
        simp only [emitLoopBudget,Cond.size,Expr.size]
        omega
      · have hmPlan : machinePlan z f a b = none := by
          exact if_neg (fun c => hP ⟨c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,c.2.2.2.2.2.2.1⟩)
        simp [hmPlan,hOut]
  · have hgF : (Cond.lt (.lit 0) (.var "firstEnd")).evalB B σ = some false := by simpa [hF] using hg
    have rr := Run.ite_false (c := .seq querySizeGuard (guardAll headerGuards (livePayloadProgram F enum))) hgF Run.skip
    exact ⟨σ,rr.mono (by simp [emitLoopBudget,Cond.size,Expr.size] <;> omega),
      by simp [machinePlan,hF]⟩

#print axioms liveQueryProgram_run
theorem cut_snd_eq_nil_at_end (z : List Nat)
    (h : z.length ≤ (cut z).1.length) : (cut z).2 = [] := by
  have hh := congrArg List.length (cut_drop_poss z)
  simp only [List.length_append] at hh
  exact List.length_eq_zero_iff.mp (by omega)

theorem emitProgramOutput_eq_emitQueries (F : FieldEncoding K) (enum : Fin q ≃ Kˣ)
    (z : List Nat) : emitProgramOutput F enum z = emitQueries F enum z := by
  unfold emitProgramOutput emitQueries
  rw [List.append_assoc]
  apply congrArg (fun v => (cut z).1 ++ 0 :: v)
  cases hw : unpositiveWords (cut z).1 with
  | nil => simp [rawPlan, guardedQueries, hw, comparisonInputOf, packSegments]
  | cons p body =>
    cases hh : body.drop p with
    | nil => simp [rawPlan, guardedQueries, hw, comparisonInputOf, hh, packSegments]
    | cons d rest =>
      cases rest with
      | nil => simp [rawPlan, guardedQueries, hw, comparisonInputOf, hh, packSegments]
      | cons n rest =>
        let tw := unpositiveWords (cut (cut z).2).1
        have hq : comparisonInputOf (p :: body) = d :: n :: rest := hh
        by_cases h :
          d ≤ (p :: body).length ∧ n ≤ (p :: body).length ∧ 2+d*(n*n) ≤ tw.length
        · by_cases htw : tw.head? = some 2
          · have hs : (cut z).1.length < z.length := by
              by_contra! he
              have hnil := cut_snd_eq_nil_at_end z he
              simp [tw,hnil,cut,unpositiveWords] at htw
            have hs₁ := cut_drop_poss z
            have hs₂ := cut_drop_poss (cut z).2
            have hprefix : (cut z).1 = positiveWords (p :: body) := by
              rw [← hw,positiveWords_cut]
            have htw' : (cut (cut z).2).1 = positiveWords tw := by
              exact (positiveWords_cut (cut z).2).symm
            let tail :=
              (if (cut (cut z).2).1.length < (cut z).2.length then [0] else []) ++ (cut (cut z).2).2
            have hz : z = positiveWords (p :: body) ++ 0 :: (positiveWords tw ++ tail) := by
              rw [List.append_assoc] at hs₂
              change (cut (cut z).2).1 ++ tail = (cut z).2 at hs₂
              rw [htw'] at hs₂
              rw [if_pos hs,List.append_assoc] at hs₁
              have hd :
                  positiveWords (p::body) ++ 0 :: (cut z).2 = z := by
                simpa only [hprefix,List.singleton_append] using hs₁
              exact hd.symm.trans (congrArg (fun x => positiveWords (p::body) ++ 0 :: x) hs₂.symm)
            have hr : rawPlan z = some (p+1,d,n,(p :: body).length+3) := by
              simp only [rawPlan,hw,hh,show unpositiveWords (cut (cut z).2).1 = tw from rfl,
                if_pos (show tw.head? = some 2 ∧ d ≤ (p :: body).length ∧
                  n ≤ (p :: body).length ∧ 2+d*(n*n) ≤ tw.length from ⟨htw,h.1,h.2.1,h.2.2⟩)]
            have he : guardedQueries F enum (p::body) tw = preK F enum (p::body) tw := by
              simp only [guardedQueries,hq,if_pos h]
            change (match rawPlan z with
              | none => []
              | some (p,d,n,a) => queryTape F enum z p d n a) =
                packSegments (guardedQueries F enum (p::body) tw)
            rw [hr,he]
            conv_lhs => rw [hz]
            exact queryTape_eq_packSegments F enum p body tw tail rest d n hh htw h.2.2
          · have hr : rawPlan z = none := by
              simp only [rawPlan,hw,hh]
              exact if_neg (fun hb => htw hb.1)
            have hg : guardedQueries F enum (p::body) tw = [] := by
              simp only [guardedQueries,hq,if_pos h,preK,hh,if_neg htw]
            change (match rawPlan z with
              | none => []
              | some (p,d,n,a) => queryTape F enum z p d n a) =
                packSegments (guardedQueries F enum (p::body) tw)
            rw [hr,hg]
            rfl
        · have hn : ¬ ((unpositiveWords (cut (cut z).2).1).head? = some 2 ∧
              d ≤ (p :: body).length ∧ n ≤ (p :: body).length ∧
                2+d*(n*n) ≤ (unpositiveWords (cut (cut z).2).1).length) :=
              fun hb => h hb.2
          have hr : rawPlan z = none := by simp only [rawPlan,hw,hh,if_neg hn]
          have hg : guardedQueries F enum (p::body) tw = [] := by
            simp only [guardedQueries,hq,if_neg h]
          change (match rawPlan z with
            | none => []
            | some (p,d,n,a) => queryTape F enum z p d n a) =
              packSegments (guardedQueries F enum (p::body) tw)
          rw [hr,hg]
          rfl

#print axioms emitProgramOutput_eq_emitQueries
#print axioms livePayloadProgram_run
#print axioms rawPlan
end EvenTI.P12CountPre
