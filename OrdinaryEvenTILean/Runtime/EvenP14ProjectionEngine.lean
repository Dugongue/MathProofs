import EvenP14ProjectionWindow
import EvenP14ProjectionReplay




set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace EvenTI.P14Projection

open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

def packBlockWord : Com := .write (.add (.var "word") (.lit 1))
def popBlock : Com := .assign "blocks" (.sub (.var "blocks") (.lit 1))
def nonzeroBlocks : Cond := .lt (.lit 0) (.var "blocks")
def skipWindow : Com := .assign "cursor" (.var "end")
def emitBlock : Com :=
  .seq openWindow (.seq (bankLoop packBlockWord)
    (.seq (.write (.lit 0)) popBlock))
def blockBody : Com := .ite nonzeroBlocks emitBlock skipWindow
def blockLoop : Com := .while inside blockBody

def slice (z : List Nat) (c e : Nat) : List Nat := (z.take e).drop c

theorem slice_length (z : List Nat) {c e : Nat} (he : e ≤ z.length) :
    (slice z c e).length = e-c := by simp [slice,Nat.min_eq_left he]

theorem slice_cons (z : List Nat) {c e : Nat} (h : c < e) (he : e ≤ z.length) :
    slice z c e = (z[c]'(h.trans_le he)) :: slice z (c+1) e := by
  have hc : c < (z.take e).length := by simp [Nat.min_eq_left he,h]
  unfold slice
  rw [List.drop_eq_getElem_cons hc,List.getElem_take]

theorem slice_pair (z : List Nat) {c e : Nat} (hc : c ≤ e) (he : e ≤ z.length) (a : Nat) :
    let j := c+min a (e-c)
    (slice z c e).take a = slice z c j ∧ (slice z c e).drop a = slice z j e := by
  dsimp only
  have hj : c+min a (e-c) ≤ e := by have := Nat.min_le_right a (e-c); omega
  have hMin : min (c+a) e = c+min a (e-c) := by
    by_cases hh : a ≤ e-c
    · rw [Nat.min_eq_left hh,Nat.min_eq_left (by omega)]
    · rw [Nat.min_eq_right (by omega : e-c ≤ a),Nat.min_eq_right (by omega)]
      omega
  constructor
  · simp only [slice,List.take_drop,List.take_take,hMin]
  · simp only [slice,List.drop_drop]
    by_cases h : a ≤ e-c
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right (by omega : e-c ≤ a)]
      have h₁ : e ≤ c+a := by omega
      have hd : (z.take e).length = e := by simp [Nat.min_eq_left he]
      rw [List.drop_eq_nil_of_le (by omega : (z.take e).length ≤ c+a),
        List.drop_eq_nil_of_le (by omega : (z.take e).length ≤ c+(e-c))]

theorem packBlockWord_run {B : Nat} {t : Env} (hB : 1 < B)
    (hw : t.vars "word"+1 < B) :
    Run B packBlockWord t {t with out := t.out ++ [t.vars "word"+1]} 4 :=
  Run.write (evalB_bin (op := .add) (evalB_var (by omega)) (evalB_lit hB) hw)

theorem emitBlock_run (z : List Nat) {c e k B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e) (hk : s.vars "blocks"=k+1)
    (hce : c<e) (hez : e≤z.length) (hz : z.length<B) (hB : 2<B)
    (hkB : k+1<B) (hv : ∀ a ∈ z, a+1<B)
    (hd : s.arrs "data"=sentinelWords z) :
    ∃ t j, Run B emitBlock s t (15*z.length+38) ∧ c<j ∧ j≤e ∧
      t.vars "cursor"=j ∧ t.vars "end"=e ∧ t.vars "blocks"=k ∧
      t.arrs "data"=sentinelWords z ∧
      t.out ++ packSegments (unlistAux k (slice z j e)) =
        s.out ++ packSegments (unlistAux (k+1) (slice z c e)) := by
  let a := z[c]'(hce.trans_le hez)
  let j := c+1+min a (e-(c+1))
  have hj : j≤e := by
    have h := Nat.min_le_right a (e-(c+1))
    dsimp [j]; omega
  have hcl : c+1≤j := Nat.le_add_right _ _
  obtain ⟨u,ru,hu,hstop,hend,fu⟩ := openWindow_run z hc he hce hez hz (by omega)
    (fun a ha => (Nat.lt_succ_self a).trans (hv a ha)) hd
  have hblocks : u.vars "blocks"=k+1 := (fu.vars _ (by decide)).trans hk
  have hbank : u.arrs "data"=sentinelWords z := (fu.arrs _ (by decide)).trans hd
  have hOut : u.out=s.out := fu.out (by apply noWrite_of_check; rfl)
  obtain ⟨v,rv,hPresv,hArrv,_,hCurv,hOutv⟩ := bankLoop_run_of_mem z packBlockWord Nat.succ
    (c:=4) (fun t hm => packBlockWord_run (by omega) (hv _ hm))
    hcl (hj.trans hez) hu hstop hbank hz (by omega)
    (fun a ha => (Nat.lt_succ_self a).trans (hv a ha))
  let w := {v with out := v.out ++ [0]}
  have rw₀ : Run B (.write (.lit 0)) v w 2 := Run.write (evalB_lit (by omega))
  have hwCount : w.vars "blocks"=k+1 := (hPresv _ (by decide) (by decide)).trans hblocks
  have ev : (Expr.sub (.var "blocks") (.lit 1)).evalB B w = some k := by
    have r := evalB_bin (B := B) (σ := w) (op := .sub)
      (evalB_var_iff.mpr ⟨hwCount.symm,hwCount ▸ hkB⟩) (evalB_lit (by omega : 1<B))
      (by simp [Bop.apply]; omega)
    simpa using r
  let t := w.setVar "blocks" k
  have rt : Run B popBlock w t 4 := Run.assign ev
  have cost : 21 + (15*(j-(c+1))+4 + (2+4)) ≤ 15*z.length+38 := by
    have := hj.trans hez
    omega
  refine ⟨t,j,(ru.seq (rv.seq (rw₀.seq rt))).mono cost,by omega,hj,?_,?_,?_,?_,?_⟩
  · simpa [t,w] using hCurv
  · simpa [t,w] using (hPresv "end" (by decide) (by decide)).trans hend
  · simp [t]
  · simpa [t,w] using congrFun hArrv "data" |>.trans hbank
  · have hs := slice_pair z (show c+1≤e by omega) hez a
    rw [slice_cons z hce hez,unlistAux]
    change t.out ++ packSegments (unlistAux k (slice z j e)) =
      s.out ++ packSegments (((slice z (c+1) e).take a) :: unlistAux k ((slice z (c+1) e).drop a))
    rw [hs.1,hs.2]
    simp [t,w,hOutv,hOut,packSegments,positiveWords,slice,j,List.append_assoc]

#print axioms emitBlock_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace EvenTI.P14Projection

open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

theorem inside_eval {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e) (hcb : c<B) (heb : e<B) :
    inside.evalB B s = some (decide (c<e)) :=
  evalB_condLt (evalB_var_iff.mpr ⟨hc.symm,hc ▸ hcb⟩)
    (evalB_var_iff.mpr ⟨he.symm,he ▸ heb⟩)

structure PackInv (z : List Nat) (e B : Nat) (target : List Nat) (t : Env) : Prop where
  address : t.vars "cursor" ≤ e
  endpoint : t.vars "end" = e
  count : t.vars "blocks" < B
  bank : t.arrs "data" = sentinelWords z
  exactOut : t.out ++ packSegments (unlistAux (t.vars "blocks") (slice z (t.vars "cursor") e)) = target

theorem blockLoop_run (z : List Nat) {c e k B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e) (hk : s.vars "blocks"=k)
    (hce : c≤e) (hez : e≤z.length) (hz : z.length<B) (hB : 2<B)
    (hkB : k<B) (hv : ∀ a ∈ z, a+1<B) (hd : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B blockLoop s t ((15*z.length+50)*z.length+4) ∧
      t.out = s.out ++ packSegments (unlistAux k (slice z c e)) := by
  let output := s.out ++ packSegments (unlistAux k (slice z c e))
  let I := PackInv z e B output
  let V (t : Env) := e-t.vars "cursor"
  have eb : e<B := hez.trans_lt hz
  have ev (t : Env) (ht : I t) :
      inside.evalB B t = some (decide (t.vars "cursor"<e)) :=
    inside_eval rfl ht.endpoint (ht.address.trans_lt eb) eb
  have hStep (t : Env) (ht : I t) (hg : inside.evalB B t = some true) :
      ∃ u, Run B blockBody t u (15*z.length+46) ∧ I u ∧ V u < V t := by
    rw [ev t ht] at hg
    have hcur : t.vars "cursor" < e := of_decide_eq_true (Option.some.inj hg)
    have hG : nonzeroBlocks.evalB B t = some (decide (0<t.vars "blocks")) :=
      evalB_condLt (evalB_lit (by omega)) (evalB_var ht.count)
    cases hk' : t.vars "blocks" with
    | zero =>
      have falseG : nonzeroBlocks.evalB B t = some false := by rw [hG,hk']; rfl
      let u := t.setVar "cursor" e
      have r : Run B skipWindow t u 2 :=
        Run.assign (evalB_var_iff.mpr ⟨ht.endpoint.symm,ht.endpoint ▸ eb⟩)
      refine ⟨u,(Run.ite_false (c := emitBlock) falseG r).mono ?_,?_,?_⟩
      · change 6 ≤ 15*z.length+46
        omega
      · refine ⟨by simp [u],by simpa [u] using ht.endpoint,by simpa [u] using ht.count,ht.bank,?_⟩
        simpa [u,hk',unlistAux,packSegments] using ht.exactOut
      · simp [V,u]; omega
    | succ k' =>
      have trueG : nonzeroBlocks.evalB B t = some true := by rw [hG,hk']; rfl
      obtain ⟨u,j,hr,hj,hje,hcu,heu,hku,hbu,hOut⟩ :=
        emitBlock_run z rfl ht.endpoint hk' hcur hez hz hB (by simpa only [hk'] using ht.count) hv ht.bank
      refine ⟨u,(Run.ite_true (d := skipWindow) trueG hr).mono ?_,?_,?_⟩
      · change 4+(15*z.length+38) ≤ 15*z.length+46
        omega
      · refine ⟨by rw [hcu]; exact hje,heu,by rw [hku]; exact (Nat.lt_succ_self k').trans (by simpa only [hk'] using ht.count),hbu,?_⟩
        rw [hcu,hku,hOut]
        simpa only [hk'] using ht.exactOut
      · dsimp [V]; rw [hcu]; omega
  have hStart : I s :=
    ⟨hc ▸ hce,he,hk ▸ hkB,hd,by simp [output,hc,hk]⟩
  obtain ⟨t,hr,ht,hf⟩ := Run.while_count I V (15*z.length+46)
    (fun t ht => ⟨_,ev t ht⟩) hStep hStart
  have hNo : ¬ t.vars "cursor"<e := by
    rw [ev t ht] at hf
    exact of_decide_eq_false (Option.some.inj hf)
  have hEnd : t.vars "cursor"=e := Nat.le_antisymm ht.address (Nat.le_of_not_gt hNo)
  have hEmpty : slice z (t.vars "cursor") e = [] := by rw [hEnd]; simp [slice]
  refine ⟨t,hr.mono ?_,?_⟩
  · change (4+(15*z.length+46))*(e-s.vars "cursor")+4 ≤ (15*z.length+50)*z.length+4
    rw [show 4+(15*z.length+46)=15*z.length+50 by omega,hc]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 4
  · have hNil : ∀ n, unlistAux n [] = [] := by intro n; cases n <;> rfl
    simpa only [hEmpty,hNil,output,packSegments,List.flatMap_nil,List.append_nil] using ht.exactOut

def packBlockHeader : Com :=
  .seq (.assign "blocks" (.get "data" (.var "cursor"))) (.seq advanceCursor blockLoop)
def packWindow : Com := .ite inside packBlockHeader .skip

theorem packWindow_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e)
    (hce : c≤e) (hez : e≤z.length) (hz : z.length<B) (hB : 2<B)
    (hv : ∀ a ∈ z, a+1<B) (hd : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B packWindow s t ((15*z.length+50)*z.length+20) ∧
      t.out = s.out ++ packSegments (unlistW (slice z c e)) := by
  have eb : e<B := hez.trans_lt hz
  have hGuard := inside_eval hc he (hce.trans_lt eb) eb
  by_cases h : c<e
  · let a := z[c]'(h.trans_le hez)
    have hab : a<B := (Nat.lt_succ_self a).trans (hv a (List.getElem_mem (h.trans_le hez)))
    let r := s.setVar "blocks" a
    have er : (Expr.get "data" (.var "cursor")).evalB B s = some a := by
      apply evalB_get (evalB_var_iff.mpr ⟨hc.symm,hc ▸ hce.trans_lt eb⟩) _ hab
      rw [hd,sentinelWords,List.getElem?_append_left (h.trans_le hez),List.getElem?_eq_getElem]
    have hRun : Run B (.assign "blocks" (.get "data" (.var "cursor"))) s r 3 := Run.assign er
    let u := r.setVar "cursor" (c+1)
    have er' : (Expr.add (.var "cursor") (.lit 1)).evalB B r = some (c+1) :=
      evalB_bin (op := .add) (evalB_var_iff.mpr ⟨by simp [r,hc],by simp [r,hc]; omega⟩)
        (evalB_lit (by omega : 1<B)) (by simp only [Bop.apply]; omega)
    have hRun' : Run B advanceCursor r u 4 := Run.assign er'
    obtain ⟨t,ht,hOut⟩ := blockLoop_run z (s := u)
      (by simp [u]) (by simp [u,r,he]) (by simp [u,r]) (show c+1≤e by omega)
      hez hz hB hab hv hd
    have hYes : inside.evalB B s = some true := by simpa [h] using hGuard
    refine ⟨t,(Run.ite_true (d := .skip) hYes (hRun.seq (hRun'.seq ht))).mono ?_,?_⟩
    · change 4+(3+(4+((15*z.length+50)*z.length+4))) ≤ (15*z.length+50)*z.length+20
      omega
    · rw [hOut,slice_cons z h hez]
      rfl
  · have hNo : inside.evalB B s = some false := by simpa [h] using hGuard
    have hempty : slice z c e = [] := by rw [Nat.le_antisymm hce (Nat.le_of_not_gt h)]; simp [slice]
    refine ⟨s,(Run.ite_false (c := packBlockHeader) hNo Run.skip).mono ?_,?_⟩
    · change 5≤(15*z.length+50)*z.length+20
      omega
    · simp [hempty,unlistW,packSegments]

#print axioms packWindow_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace EvenTI.P14Projection

open EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

def pairWindow : Com := .ite inside openWindow (.assign "stop" (.var "cursor"))

/-- A literal length-prefixed pair becomes two adjacent windows in the same
bank. Clamping implements the exact codec even on truncated input. -/
theorem pairWindow_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e)
    (hce : c≤e) (hez : e≤z.length) (hz : z.length<B) (hB : 2<B)
    (hv : ∀ a ∈ z, a < B) (hd : s.arrs "data"=sentinelWords z) :
    ∃ (t : Env) (i j : Nat), Run B pairWindow s t 25 ∧ (i ≤ j) ∧ (j ≤ e) ∧ (c ≤ i) ∧
      t.vars "cursor"=i ∧ t.vars "stop"=j ∧ t.vars "end"=e ∧
      t.arrs "data"=sentinelWords z ∧
      unpairW (slice z c e)=(slice z i j,slice z j e) ∧ Frame pairWindow s t := by
  have ec := inside_eval hc he (hce.trans_lt (hez.trans_lt hz)) (hez.trans_lt hz)
  by_cases H : c<e
  · let a := z[c]'(H.trans_le hez)
    let j := c+1+min a (e-(c+1))
    have hclamp := Nat.min_le_right a (e-(c+1))
    obtain ⟨t,hr,hi,hj,he',f⟩ := openWindow_run z hc he H hez hz (by omega) hv hd
    have et : inside.evalB B s = some true := by simpa [H] using ec
    have rr : Run B pairWindow s t 25 := Run.ite_true (d := .assign "stop" (.var "cursor")) et hr
    have hle : j ≤ e := by dsimp [j]; omega
    have hs := slice_pair z (show c+1≤e by omega) hez a
    refine ⟨t,c+1,j,rr,Nat.le_add_right _ _,hle,by omega,hi,hj,he',
      (f.arrs _ (by decide)).trans hd,?_,Frame.of_run rr⟩
    rw [slice_cons z H hez,unpairW]
    exact Prod.ext hs.1 hs.2
  · have hEq : c=e := Nat.le_antisymm hce (Nat.le_of_not_gt H)
    let t := s.setVar "stop" c
    have et : inside.evalB B s = some false := by simpa [H] using ec
    have eC : (Expr.var "cursor").evalB B s = some c :=
      evalB_var_iff.mpr ⟨hc.symm,hc ▸ hce.trans_lt (hez.trans_lt hz)⟩
    have r₂ : Run B (.assign "stop" (.var "cursor")) s t 2 := Run.assign eC
    have rr : Run B pairWindow s t 25 :=
      (Run.ite_false (c := openWindow) et r₂).mono (by decide)
    refine ⟨t,c,c,rr,le_rfl,hce,le_rfl,by simpa [t] using hc,by simp [t],
      by simpa [t] using he,hd,?_,Frame.of_run rr⟩
    rw [hEq]
    simp [slice,unpairW]

def skipKind : Com := .ite inside advanceCursor .skip

theorem skipKind_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e) (hce : c≤e)
    (hez : e≤z.length) (hz : z.length<B) (hB : 1<B) :
    ∃ t i, Run B skipKind s t 8 ∧ t.vars "cursor" = i ∧ i≤e ∧
      (slice z c e).tail = slice z i e ∧ Frame skipKind s t := by
  have ec := inside_eval hc he (hce.trans_lt (hez.trans_lt hz)) (hez.trans_lt hz)
  by_cases H : c<e
  · let t := s.setVar "cursor" (c+1)
    have r : Run B advanceCursor s t 4 := Run.assign (evalB_bin (op := .add)
      (evalB_var_iff.mpr ⟨hc.symm,hc ▸ hce.trans_lt (hez.trans_lt hz)⟩) (evalB_lit hB) (by simp only [Bop.apply]; omega))
    have et : inside.evalB B s = some true := by simpa [H] using ec
    have rr : Run B skipKind s t 8 := Run.ite_true (d := .skip) et r
    refine ⟨t,c+1,rr,by simp [t],by omega,?_,Frame.of_run rr⟩
    rw [slice_cons z H hez]
    rfl
  · have hEq : c=e := Nat.le_antisymm hce (Nat.le_of_not_gt H)
    have et : inside.evalB B s = some false := by simpa [H] using ec
    have rr : Run B skipKind s s 8 := (Run.ite_false (c := advanceCursor) et Run.skip).mono (by decide)
    exact ⟨s,c,rr,hc,hce,by rw [hEq]; simp [slice],Frame.of_run rr⟩

#print axioms pairWindow_run
#print axioms skipKind_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace EvenTI.P14Projection

open EvenTI.Comparison EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

def routeHeader (raw : List Nat) : Option Nat :=
  let l := cutHalf (raw.headD 0)
  let n := (raw.drop 1).headD 0
  let a := (raw.drop 2).length/2
  if (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n) then some (if l=1 then min n a else a) else none

def emitCap : Com :=
  .seq (.write (.add (.var "cap") (.lit 1)))
    (.seq (.write (.lit 0)) (.assign "project" (.lit 1)))

def emitNormalCap : Com := .seq (.assign "cap" (.var "available")) emitCap

def emitSmallCap : Com :=
  .seq (.assign "cap" (.sub (.var "dim") (.sub (.var "dim") (.var "available")))) emitCap

def goodFour : Cond := .lt (.lit 4) (.var "dim")
def goodHigher : Cond := .lt (.lit 0) (.var "dim")
def hasHigher : Cond := .lt (.lit 1) (.var "half")
def isFour : Cond := .eq (.var "half") (.lit 1)
def selectCap : Com :=
  .ite isFour (.ite goodFour emitSmallCap .skip)
    (.ite hasHigher (.ite goodHigher emitNormalCap .skip) .skip)

def payloadLength : Cond := .lt (.lit 1) remaining
def readHalf : Expr := .sub (.div (.get "data" (.var "cursor")) (.lit 2)) (.lit 1)
def readDim : Expr := .get "data" (.add (.var "cursor") (.lit 1))
def readAvailable : Expr := .div (.sub remaining (.lit 2)) (.lit 2)

def headerBody : Com :=
  .seq (.assign "half" readHalf)
    (.seq (.assign "dim" readDim) (.seq (.assign "available" readAvailable) selectCap))

def headerProgram : Com :=
  .seq (.assign "project" (.lit 0)) (.ite payloadLength headerBody .skip)

theorem liveVar {x : String} {v B : Nat} {s : Env} (h : s.vars x=v) (hv : v<B) :
    (Expr.var x).evalB B s = some v :=
  evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩

theorem emitCap_run {B c : Nat} {s : Env} (hB : 2<B) (hc : s.vars "cap"=c)
    (hcB : c+1<B) :
    ∃ t, Run B emitCap s t 8 ∧ t.out=s.out++packSegments [[c]] ∧ t.vars "project"=1 := by
  let a := {s with out := s.out++[c+1]}
  let b := {a with out := a.out++[0]}
  let t := b.setVar "project" 1
  have r₁ : Run B (.write (.add (.var "cap") (.lit 1))) s a 4 :=
    Run.write (evalB_bin (op:=.add) (liveVar hc (by omega)) (evalB_lit (by omega : 1<B)) hcB)
  have r₂ : Run B (.write (.lit 0)) a b 2 := Run.write (evalB_lit (by omega))
  have r₃ : Run B (.assign "project" (.lit 1)) b t 2 := Run.assign (evalB_lit (by omega))
  exact ⟨t,r₁.seq (r₂.seq r₃),by simp [t,b,a,packSegments,positiveWords,List.append_assoc],by simp [t]⟩

theorem selectedCap_run {B l n a : Nat} {s : Env}
    (hB : 4<B) (hl : s.vars "half"=l) (hn : s.vars "dim"=n) (ha : s.vars "available"=a)
    (hz : s.vars "project"=0) (hlB : l<B) (hnB : n<B) (haB : a+1<B) :
    let shape := (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n)
    ∃ t, Run B selectCap s t 40 ∧
      t.vars "project"=(if shape then 1 else 0) ∧
      t.out=s.out++(if shape then packSegments [[if l=1 then min n a else a]] else []) := by
  have e₁ : isFour.evalB B s = some (decide (l=1)) :=
    evalB_condEq (liveVar hl hlB) (evalB_lit (by omega))
  have e₂ : hasHigher.evalB B s = some (decide (1<l)) :=
    evalB_condLt (evalB_lit (by omega)) (liveVar hl hlB)
  have e₃ : goodFour.evalB B s = some (decide (4<n)) :=
    evalB_condLt (evalB_lit hB) (liveVar hn hnB)
  have e₄ : goodHigher.evalB B s = some (decide (0<n)) :=
    evalB_condLt (evalB_lit (by omega)) (liveVar hn hnB)
  by_cases h₁ : l=1
  · have e₁' : isFour.evalB B s = some true := by rw [e₁]; simp [h₁]
    by_cases h₃ : 4<n
    · have e₃' : goodFour.evalB B s = some true := by rw [e₃]; simp [h₃]
      have hsmall : n-(n-a) = min n a := by
        by_cases h : n≤a
        · rw [Nat.min_eq_left h]; omega
        · rw [Nat.min_eq_right (by omega)]; omega
      let u := s.setVar "cap" (min n a)
      have ee : (Expr.sub (.var "dim") (.sub (.var "dim") (.var "available"))).evalB B s = some (min n a) := by
        rw [← hsmall]
        apply evalB_bin (op:=.sub) (liveVar hn hnB)
        · exact evalB_bin (op:=.sub) (liveVar hn hnB) (liveVar ha (by omega)) (by simp only [Bop.apply]; omega)
        · simp only [Bop.apply]
          omega
      have rr : Run B (.assign "cap" (.sub (.var "dim") (.sub (.var "dim") (.var "available")))) s u 6 :=
        Run.assign ee
      have hmin := Nat.min_le_right n a
      obtain ⟨t,rt,hout,hproj⟩ := emitCap_run (B:=B) (by omega) (s:=u) (c:=min n a) (by simp [u]) (by omega)
      have shape : (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n) := Or.inl ⟨h₁,h₃⟩
      exact ⟨t,(Run.ite_true e₁' (Run.ite_true e₃' (rr.seq rt))).mono (by decide),
        by simpa only [if_pos shape] using hproj,by simpa only [if_pos shape,if_pos h₁,u,out_setVar] using hout⟩
    · have e₃' : goodFour.evalB B s = some false := by rw [e₃]; simp [h₃]
      have bad : ¬ ((l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n)) := by omega
      exact ⟨s,(Run.ite_true e₁' (Run.ite_false (c:=emitSmallCap) e₃' Run.skip)).mono (by decide),
        by simpa [bad] using hz,by simp [bad]⟩
  · have e₁' : isFour.evalB B s = some false := by rw [e₁]; simp [h₁]
    by_cases h₂ : 1<l
    · have e₂' : hasHigher.evalB B s = some true := by rw [e₂]; simp [h₂]
      by_cases h₄ : 0<n
      · have e₄' : goodHigher.evalB B s = some true := by rw [e₄]; simp [h₄]
        let u := s.setVar "cap" a
        have rr : Run B (.assign "cap" (.var "available")) s u 2 := Run.assign (liveVar ha (by omega))
        obtain ⟨t,rt,hout,hproj⟩ := emitCap_run (B:=B) (by omega) (s:=u) (c:=a) (by simp [u]) haB
        have shape : (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n) := Or.inr ⟨h₂,h₄⟩
        exact ⟨t,(Run.ite_false e₁' (Run.ite_true e₂' (Run.ite_true e₄' (rr.seq rt)))).mono (by decide),
          by simpa only [if_pos shape] using hproj,by simpa only [if_pos shape,if_neg h₁,u,out_setVar] using hout⟩
      · have e₄' : goodHigher.evalB B s = some false := by rw [e₄]; simp [h₄]
        have bad : ¬ ((l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n)) := by omega
        exact ⟨s,(Run.ite_false e₁' (Run.ite_true e₂' (Run.ite_false (c:=emitNormalCap) e₄' Run.skip))).mono
          (by decide),by simpa [bad] using hz,by simp [bad]⟩
    · have e₂' : hasHigher.evalB B s = some false := by rw [e₂]; simp [h₂]
      have bad : ¬ ((l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n)) := by omega
      exact ⟨s,(Run.ite_false e₁' (Run.ite_false (c:=.ite goodHigher emitNormalCap .skip) e₂' Run.skip)).mono
        (by decide),by simpa [bad] using hz,by simp [bad]⟩

#print axioms selectedCap_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace EvenTI.P14Projection

open EvenTI.Comparison EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

theorem headerProgram_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e)
    (hce : c≤e) (hez : e≤z.length) (hz : z.length<B) (hB : 4<B)
    (hv : ∀ a ∈ z, a<B) (hd : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B headerProgram s t 90 ∧
      t.vars "project" = (if (routeHeader (slice z c e)).isSome then 1 else 0) ∧
      t.out = s.out ++ ((routeHeader (slice z c e)).map fun a => packSegments [[a]]).getD [] ∧
      Frame headerProgram s t := by
  let a₀ := s.setVar "project" 0
  have r₀ : Run B (.assign "project" (.lit 0)) s a₀ 2 := Run.assign (evalB_lit (by omega))
  have eRaw : remaining.evalB B a₀ = some (e-c) := by
    apply evalB_bin (op:=.sub) (liveVar (s:=a₀) (x:="end") (by simp [a₀,he]) (by omega))
      (liveVar (s:=a₀) (x:="cursor") (by simp [a₀,hc]) (by omega))
    change e-c<B
    omega
  have eG : payloadLength.evalB B a₀ = some (decide (1<e-c)) := evalB_condLt (evalB_lit (by omega)) eRaw
  by_cases good : 1<e-c
  · have hc₁ : c<e := by omega
    have hc₂ : c+1<e := by omega
    let d := z[c]'(hc₁.trans_le hez)
    let n := z[c+1]'(hc₂.trans_le hez)
    let l := cutHalf d
    let b := (e-c-2)/2
    have hdB : d<B := hv d (List.getElem_mem (hc₁.trans_le hez))
    have hnB : n<B := hv n (List.getElem_mem (hc₂.trans_le hez))
    have dl : d/2≤d := Nat.div_le_self _ _
    have lb : l<B := by unfold l cutHalf; omega
    have bb : b+1<B := by
      have h := Nat.div_le_self (e-c-2) 2
      dsimp [b]; omega
    have e₀ : (Expr.get "data" (.var "cursor")).evalB B a₀ = some d := by
      apply evalB_get (liveVar (x:="cursor") (s:=a₀) (v:=c) (by simp [a₀,hc]) (by omega)) _ hdB
      change (s.arrs "data")[c]? = some d
      rw [hd,sentinelWords,List.getElem?_append_left (hc₁.trans_le hez),List.getElem?_eq_getElem]
    have eHalf : readHalf.evalB B a₀ = some l := by
      apply evalB_bin (op:=.sub)
      · exact evalB_bin (op:=.div) e₀ (evalB_lit (by omega : 2<B)) (by simp only [Bop.apply]; omega)
      · exact evalB_lit (by omega : 1<B)
      · exact lb
    let a₁ := a₀.setVar "half" l
    have r₁ : Run B (.assign "half" readHalf) a₀ a₁ 7 := Run.assign eHalf
    have ei : (Expr.add (.var "cursor") (.lit 1)).evalB B a₁ = some (c+1) := by
      apply evalB_bin (op:=.add) (liveVar (x:="cursor") (s:=a₁) (by simp [a₁,a₀,hc]) (by omega))
        (evalB_lit (by omega : 1<B))
      change c+1<B
      omega
    have en : readDim.evalB B a₁ = some n := by
      apply evalB_get ei _ hnB
      change (s.arrs "data")[c+1]? = some n
      rw [hd,sentinelWords,List.getElem?_append_left (hc₂.trans_le hez),List.getElem?_eq_getElem]
    let a₂ := a₁.setVar "dim" n
    have r₂ : Run B (.assign "dim" readDim) a₁ a₂ 5 := Run.assign en
    have eR₂ : remaining.evalB B a₂ = some (e-c) := by
      apply evalB_bin (op:=.sub) (liveVar (s:=a₂) (x:="end") (by simp [a₂,a₁,a₀,he]) (by omega))
        (liveVar (s:=a₂) (x:="cursor") (by simp [a₂,a₁,a₀,hc]) (by omega))
      change e-c<B
      omega
    have eb : readAvailable.evalB B a₂ = some b :=
      evalB_bin (op:=.div)
        (evalB_bin (op:=.sub) eR₂ (evalB_lit (by omega : 2<B)) (by simp only [Bop.apply]; omega))
        (evalB_lit (by omega : 2<B)) (by simp only [Bop.apply]; omega)
    let a₃ := a₂.setVar "available" b
    have r₃ : Run B (.assign "available" readAvailable) a₂ a₃ 8 := Run.assign eb
    obtain ⟨t,rt,hproj,hout⟩ := selectedCap_run (s:=a₃) hB
      (l:=l) (n:=n) (a:=b) (by simp [a₃,a₂,a₁]) (by simp [a₃,a₂]) (by simp [a₃])
      (by simp [a₃,a₂,a₁,a₀]) lb hnB bb
    have ht : payloadLength.evalB B a₀ = some true := by simpa [good] using eG
    have rr : Run B headerProgram s t 90 :=
      (r₀.seq (Run.ite_true (d:=.skip) ht (r₁.seq (r₂.seq (r₃.seq rt))))).mono (by decide)
    have hh : slice z c e = d :: n :: slice z (c+1+1) e := by rw [slice_cons z hc₁ hez,slice_cons z hc₂ hez]
    have hTail := slice_length z (c:=c+1+1) hez
    have hR : routeHeader (slice z c e) =
        if (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n) then some (if l=1 then min n b else b) else none := by
      rw [hh]
      simp only [routeHeader,List.headD_cons,List.tail_cons,List.drop_succ_cons,List.drop_zero,hTail]
      rw [show e-(c+1+1)=e-c-2 by omega] <;> rfl
    refine ⟨t,rr,?_,?_,Frame.of_run rr⟩
    · rw [hR]
      split <;> simp_all
    · rw [hR]
      split <;> simp_all [a₃,a₂,a₁,a₀]
  · have hf : payloadLength.evalB B a₀ = some false := by simpa [good] using eG
    have hR : routeHeader (slice z c e)=none := by
      by_cases h : c<e
      · rw [slice_cons z h hez]
        have hRest : slice z (c+1) e = [] := by
          rw [show c+1=e by omega]; simp [slice]
        simp [routeHeader,hRest]
      · rw [show c=e by omega]
        simp [routeHeader,slice,cutHalf]
    have rr : Run B headerProgram s a₀ 90 :=
      (r₀.seq (Run.ite_false (c:=headerBody) hf Run.skip)).mono (by decide)
    exact ⟨a₀,rr,by simp [hR,a₀],by simp [hR,a₀],Frame.of_run rr⟩

#print axioms headerProgram_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace EvenTI.P14Projection

open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

def closeRight : Com := .assign "end" (.var "stop")
def takeFirstWindow : Com := .seq pairWindow closeRight
def nestedProjection : Com :=
  .seq takeFirstWindow (.seq skipKind (.seq takeFirstWindow packWindow))

theorem takeFirstWindow_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e)
    (hce : c≤e) (hz : e≤z.length) (hBz : z.length<B) (hB : 2<B)
    (hv : ∀ a ∈ z, a < B) (ha : s.arrs "data"=sentinelWords z) :
    ∃ t i j, Run B takeFirstWindow s t 27 ∧
      (i ≤ j) ∧ (j ≤ e) ∧ t.vars "cursor"=i ∧ t.vars "end"=j ∧
      t.arrs "data"=sentinelWords z ∧ t.out=s.out ∧
      (unpairW (slice z c e)).1 = slice z i j := by
  obtain ⟨r,i,j,hr,hij,hje,_,hi,hj,_,hb,hs,fr⟩ :=
    pairWindow_run z hc he hce hz hBz hB hv ha
  let t := r.setVar "end" j
  have rt : Run B closeRight r t 2 := Run.assign (liveVar hj (hje.trans_lt (hz.trans_lt hBz)))
  exact ⟨t,i,j,hr.seq rt,hij,hje,by simpa [t] using hi,by simp [t],hb,
    fr.out (by apply noWrite_of_check; rfl),congrArg Prod.fst hs⟩

theorem nestedProjection_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor"=c) (he : s.vars "end"=e)
    (hce : c≤e) (hz : e≤z.length) (hBz : z.length<B) (hB : 2<B)
    (hv : ∀ a ∈ z, a+1 < B) (ha : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B nestedProjection s t ((15*z.length+50)*z.length+82) ∧
      t.out=s.out++packSegments (preparedAnchorBlocks (unpairW (slice z c e)).1) := by
  have hv' : ∀ a ∈ z,a<B := fun a hm => (Nat.lt_succ_self a).trans (hv a hm)
  obtain ⟨r,i,j,hr,hij,hje,hi,hj,hrb,hro,hrs⟩ :=
    takeFirstWindow_run z hc he hce hz hBz hB hv' ha
  obtain ⟨u,k,hu,hk,hkj,ht,fu⟩ := skipKind_run z hi hj hij (hje.trans hz) hBz (by omega)
  have hju : u.vars "end"=j := (fu.vars _ (by decide)).trans hj
  have hbu : u.arrs "data"=sentinelWords z := (fu.arrs _ (by decide)).trans hrb
  have hou : u.out=s.out := (fu.out (by apply noWrite_of_check; rfl)).trans hro
  obtain ⟨v,a,b,rv,hab,hbj,ha',hb',hbv,hov,hvs⟩ :=
    takeFirstWindow_run z hk hju hkj (hje.trans hz) hBz hB hv' hbu
  obtain ⟨t,rt,hot⟩ := packWindow_run z ha' hb' hab (hbj.trans (hje.trans hz)) hBz hB hv hbv
  refine ⟨t,(hr.seq (hu.seq (rv.seq rt))).mono (by omega),?_⟩
  rw [hot,hov,hou,preparedAnchorBlocks,hrs,ht,hvs]

theorem spectralPairRequest_header (w : List Nat) :
    spectralPairRequest w =
      match routeHeader (unpairW w).1 with
      | none => []
      | some a => packSegments [[a]] ++
        packSegments (preparedAnchorBlocks (unpairW (unpairW w).2).1) := by
  let raw := (unpairW w).1
  let l := EvenTI.Comparison.cutHalf (raw.headD 0)
  let n := (raw.drop 1).headD 0
  let a := (raw.drop 2).length/2
  let cap := if l=1 then min n a else a
  let shape := (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n)
  let anchors := preparedAnchorBlocks (unpairW (unpairW w).2).1
  change (if shape then packSegments ([cap]::anchors) else []) =
    (match (if shape then some cap else none) with
      | none => []
      | some u => packSegments [[u]] ++ packSegments anchors)
  by_cases h : shape
  · simp only [if_pos h,packSegments,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  · simp only [if_neg h]

def resumePair : Com :=
  .seq (.assign "cursor" (.var "end")) (.assign "end" (.var "length"))
def projectGuard : Cond := .eq (.var "project") (.lit 1)

def projectionBody : Com :=
  .seq pairWindow (.seq closeRight (.seq headerProgram
    (.ite projectGuard (.seq resumePair nestedProjection) .skip)))

theorem projectionBody_run (z : List Nat) {B : Nat} {s : Env}
    (hc : s.vars "cursor"=0) (he : s.vars "end"=z.length)
    (hl : s.vars "length"=z.length) (hBz : z.length<B) (hB : 4<B)
    (hv : ∀ a ∈ z, a+1 < B) (ha : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B projectionBody s t ((15*z.length+50)*z.length+215) ∧
      t.out=s.out++spectralPairRequest z := by
  have hv' : ∀ a ∈ z,a<B := fun a hm => (Nat.lt_succ_self a).trans (hv a hm)
  obtain ⟨r,i,j,hr,hij,hjz,_,hi,hj,he',hb,hs,fr⟩ :=
    pairWindow_run z hc he (Nat.zero_le _) le_rfl hBz (by omega) hv' ha
  have hs' : unpairW z=(slice z i j,slice z j z.length) := by simpa [slice] using hs
  let u := r.setVar "end" j
  have ru : Run B closeRight r u 2 := Run.assign (liveVar hj (hjz.trans_lt hBz))
  obtain ⟨v,rv,hp,ho,fv⟩ :=
    headerProgram_run z (s:=u) (by simpa [u] using hi) (by simp [u]) hij hjz hBz hB hv' hb
  have huOut : u.out=s.out := fr.out (by apply noWrite_of_check; rfl)
  have hLen : v.vars "length"=z.length := by
    rw [fv.vars _ (by decide)]
    exact (fr.vars _ (by decide)).trans hl
  have hEnd : v.vars "end"=j := by rw [fv.vars _ (by decide)]; simp [u]
  have hBank : v.arrs "data"=sentinelWords z := (fv.arrs _ (by decide)).trans hb
  have hvp : v.vars "project"<B := by rw [hp]; split <;> omega
  have eg : projectGuard.evalB B v = some (decide (v.vars "project"=1)) :=
    evalB_condEq (evalB_var hvp) (evalB_lit (by omega))
  rw [spectralPairRequest_header,hs']
  cases hHead : routeHeader (slice z i j) with
  | none =>
    have hf : projectGuard.evalB B v = some false := by rw [eg,hp,hHead]; rfl
    refine ⟨v,(hr.seq (ru.seq (rv.seq (Run.ite_false (c:=.seq resumePair nestedProjection) hf Run.skip)))).mono ?_,?_⟩
    · norm_num [projectGuard,Cond.size,Expr.size] <;> omega
    · simpa [hHead,huOut] using ho
  | some a =>
    have ht : projectGuard.evalB B v = some true := by rw [eg,hp,hHead]; rfl
    let x := v.setVar "cursor" j
    let y := x.setVar "end" z.length
    have rx : Run B (.assign "cursor" (.var "end")) v x 2 := Run.assign (liveVar hEnd (hjz.trans_lt hBz))
    have ry : Run B (.assign "end" (.var "length")) x y 2 :=
      Run.assign (liveVar (x:="length") (s:=x) (by simpa [x] using hLen) hBz)
    obtain ⟨t,rt,hot⟩ := nestedProjection_run z (s:=y)
      (by simp [x,y]) (by simp [y]) hjz le_rfl hBz (by omega) hv hBank
    have rxy : Run B resumePair v y 4 := rx.seq ry
    refine ⟨t,(hr.seq (ru.seq (rv.seq (Run.ite_true (d:=.skip) ht (rxy.seq rt))))).mono ?_,?_⟩
    · change 25+(2+(90+(4+(4+((15*z.length+50)*z.length+82))))) ≤ _
      omega
    · simpa [y,x,ho,hHead,huOut,List.append_assoc] using hot

#print axioms nestedProjection_run
#print axioms projectionBody_run
end EvenTI.P14Projection



set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace EvenTI.P14Projection

open EvenTI.P12CountPre EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Mathproof.Problem18P34Machine20261002Layout (layout layout_ok)

def spectralProjectionProgram : Com :=
  .seq (.read "length") <| .seq inputLoadLoop <|
  .seq (.assign "cursor" (.lit 0)) <|
  .seq (.assign "end" (.var "length")) projectionBody

theorem spectralProjectionProgram_run (z : List Nat) {B : Nat}
    (hB : 4<B) (hz : z.length<B) (hv : ∀ a ∈ z, a+1<B) :
    ∃ t, Run B spectralProjectionProgram (initEnv (fun _ => z.length+1) (z.length::z)) t
      ((15*z.length+63)*z.length+225) ∧ t.out=spectralPairRequest z := by
  let s := initEnv (fun _ => z.length+1) (z.length::z)
  let u := {s.setVar "length" z.length with inp := z}
  have r₁ : Run B (.read "length") s u 1 := Run.read rfl
  have hv' : ∀ a ∈ z,a<B := fun a h => (Nat.lt_succ_self a).trans (hv a h)
  obtain ⟨v,r₂,hl,hBank,hout,_⟩ := inputLoad_run z (σ:=u)
    (by simp [u]) (by simp [u,s,initEnv]) rfl
    (by simp [u,s,initEnv,inputBuffer_zero]) hz (by omega) hv'
  let x := v.setVar "cursor" 0
  let y := x.setVar "end" z.length
  have r₃ : Run B (.assign "cursor" (.lit 0)) v x 2 := Run.assign (evalB_lit (by omega))
  have r₄ : Run B (.assign "end" (.var "length")) x y 2 := Run.assign
    (liveVar (s:=x) (x:="length") (by simpa [x] using hl) hz)
  obtain ⟨t,rt,ht⟩ := projectionBody_run z (s:=y) (by simp [y,x]) (by simp [y])
    (by simpa [y,x] using hl) hz hB hv (hBank.trans (inputBuffer_full z))
  refine ⟨t,(r₁.seq (r₂.seq (r₃.seq (r₄.seq rt)))).mono ?_,?_⟩
  · simp only [Nat.add_mul]
    omega
  · simpa [y,x,hout,u,s,initEnv] using ht

/-- Exact binary time bound on all serialized callback words, including
incomplete length headers and truncated nested lists. -/
theorem spectralPairRequest_turingPolytime : TuringPolytime spectralPairRequest := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp (layout spectralProjectionProgram) spectralProjectionProgram
    spectralPairRequest (Polynomial.C 4) ((15*Polynomial.X+63)*Polynomial.X+225) (layout_ok _)
  intro z
  let L := bitSize z
  let B := 2^(4+L+1)
  have hbase : 2^(L+1)<B := Nat.pow_lt_pow_right (by decide) (by omega)
  have hB : 4<B := (show 4<2^5 by decide).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hf : z.length≤L := Lax51Proofs.Encoding.length_le_bitSize z
  have hLen : z.length<B := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one z).trans hbase
  have hWords (a : Nat) (ha : a ∈ z) : a+1<B :=
    (Nat.succ_le_of_lt (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one ha)).trans_lt hbase
  obtain ⟨t,r,ho⟩ := spectralProjectionProgram_run z hB hLen hWords
  refine ⟨fun _ => z.length+1,t,?_,ho⟩
  simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  exact r.mono (Nat.add_le_add_right (Nat.mul_le_mul
    (by omega : 15*z.length+63 ≤ 15*L+63) hf) 225)

#print axioms spectralProjectionProgram_run
#print axioms spectralPairRequest_turingPolytime
end EvenTI.P14Projection

