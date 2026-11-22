import EvenP15RecoverConstantTable
import EvenP15ScalarPrefixProbe

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 25000

namespace EvenTI.P15Scalar

open EvenTI.Contract EvenTI.Part8 EvenTI.P15Recover
open EvenTI.P12Compare (coordinateBank)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

local notation "M" => (Fintype.card K - 1)

private local instance baseUnitsOrder : NeZero M :=
  ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

def baseUnitBank : String := "even.scalar.base.units"
def baseUnitCursor : String := "even.scalar.base.unit.cursor"
def baseUnitArgument : String := "even.scalar.base.unit.argument"
def baseUnitDigit : String := "even.scalar.base.unit.digit"

def baseUnitDigitTable (D : FieldEncoding K) (L : BaseUnitLog K) : List ℕ :=
  List.ofFn (fun j : Fin M => (D (L.decode (j.val : ZMod M) : K)).val)

private def readBaseUnitExponent : Com :=
  .assign baseUnitArgument (.get coordinateBank (.var baseUnitCursor))

private def storeBaseUnitDigit : Com :=
  .store baseUnitBank (.var baseUnitCursor) (.var baseUnitDigit)

private def baseUnitNext : Com :=
  .assign baseUnitCursor (.add (.var baseUnitCursor) (.lit 1))

private def baseUnitGuard : Cond :=
  .lt (.var baseUnitCursor) (.var inputColsR)

private def baseUnitVisit (D : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq readBaseUnitExponent
    (.seq (constantWordTable baseUnitArgument baseUnitDigit 0 (baseUnitDigitTable D L))
      (.seq storeBaseUnitDigit baseUnitNext))

def decodeBaseUnitBank (D : FieldEncoding K) (L : BaseUnitLog K) : Com :=
  .seq (.assign baseUnitCursor (.lit 0)) (.while baseUnitGuard (baseUnitVisit D L))

def decodeBaseUnitBankCost (K : Type) [Fintype K] (n : ℕ) : ℕ :=
  (6*(Fintype.card K-1)+16)*n+6

private theorem baseUnitDigitTable_getD (D : FieldEncoding K) (L : BaseUnitLog K) (a : ZMod M) :
    (baseUnitDigitTable D L).getD a.val 0 = (D (L.decode a : K)).val := by
  unfold baseUnitDigitTable
  have h : a.val < (List.ofFn (fun j : Fin M => (D (L.decode (j.val : ZMod M) : K)).val)).length := by
    simpa only [List.length_ofFn] using ZMod.val_lt a
  rw [List.getD_eq_getElem _ _ h,List.getElem_ofFn]
  change (D (L.decode (a.val : ZMod M) : K)).val = _
  rw [ZMod.natCast_zmod_val]

/-- Convert the actual CRT output coordinates into exact fixed-field unit
digits. The live source coordinates, auxiliary field roots, and tapes are
preserved. The same routine serves comparison correction and scalar probes. -/
theorem decodeBaseUnitBank_run (D : FieldEncoding K) (L : BaseUnitLog K)
    {n W : ℕ} {s : Env} (z : Fin n → ZMod M)
    (hQ : Fintype.card K ≤ W) (hN : n < W) (hOne : 1 < W)
    (hCount : s.vars inputColsR = n)
    (hLen : n ≤ (s.arrs coordinateBank).length) (hOut : n ≤ (s.arrs baseUnitBank).length)
    (hWords : ∀ i, (s.arrs coordinateBank).getD i.val 0 = (z i).val) :
    ∃ t, Run W (decodeBaseUnitBank D L) s t (decodeBaseUnitBankCost K n) ∧
      Frame (decodeBaseUnitBank D L) s t ∧
      (∀ k, k ≠ baseUnitBank → t.arrs k=s.arrs k) ∧
      ∀ i, (t.arrs baseUnitBank).getD i.val 0 = (D (L.decode (z i) : K)).val := by
  have hCard : 1 < Fintype.card K := Fintype.one_lt_card
  have hm : M < W := by omega
  have htLen : (baseUnitDigitTable D L).length = M := by simp [baseUnitDigitTable]
  have htWord : ∀ v ∈ baseUnitDigitTable D L, v < W := by
    intro v hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact (D _).isLt.trans_le hQ
  let I (t : Env) := t.vars baseUnitCursor ≤ n ∧ t.vars inputColsR=n ∧
    (∀ k, k ≠ baseUnitBank → t.arrs k=s.arrs k) ∧
    (t.arrs baseUnitBank).length = (s.arrs baseUnitBank).length ∧
    ∀ i : Fin n, i.val < t.vars baseUnitCursor →
      (t.arrs baseUnitBank).getD i.val 0 = (D (L.decode (z i) : K)).val
  let G (t : Env) := n-t.vars baseUnitCursor
  let u := s.setVar baseUnitCursor 0
  have r0 : Run W (.assign baseUnitCursor (.lit 0)) s u 2 := Run.assign (evalB_lit (by omega))
  have hInit : I u := ⟨by simp [u],by simpa [u,show inputColsR ≠ baseUnitCursor by decide] using hCount,
    fun _ _ => rfl,rfl,fun i hi => False.elim (Nat.not_lt_zero i.val (by simpa [u] using hi))⟩
  have hguard (t : Env) (ht : I t) : baseUnitGuard.evalB W t =
      some (decide (t.vars baseUnitCursor < n)) :=
    evalB_condLt (evalB_var (ht.1.trans_lt hN)) (ev_var ht.2.1 hN)
  have step (t : Env) (ht : I t) (hh : baseUnitGuard.evalB W t = some true) :
      ∃ v, Run W (baseUnitVisit D L) t v (6*M+12) ∧ I v ∧ G v < G t := by
    rw [hguard t ht] at hh
    have hi : t.vars baseUnitCursor < n := by simpa using hh
    let i : Fin n := ⟨_,hi⟩
    let a := z i
    have readLim : i.val < (t.arrs coordinateBank).length := by
      rw [ht.2.2.1 coordinateBank (by decide)]
      exact hi.trans_le hLen
    have hLookup : (t.arrs coordinateBank).getD i.val 0 = a.val :=
      (congrArg (fun L : List ℕ => L.getD i.val 0) (ht.2.2.1 coordinateBank (by decide))).trans (hWords i)
    have hAt : (t.arrs coordinateBank)[i.val]? = some a.val := by
      rw [List.getD_eq_getElem _ _ readLim] at hLookup
      rw [List.getElem?_eq_getElem readLim,hLookup]
    have ei : (Expr.var baseUnitCursor).evalB W t = some i.val := evalB_var (hi.trans hN)
    let p := t.setVar baseUnitArgument a.val
    have rp : Run W readBaseUnitExponent t p 3 :=
      Run.assign (evalB_get ei hAt ((ZMod.val_lt a).trans hm))
    have hk : p.vars baseUnitArgument=a.val := by simp [p]
    obtain ⟨q,rq,hq,fq⟩ := constantWordTable_run baseUnitArgument baseUnitDigit (baseUnitDigitTable D L)
      (i:=0) ((ZMod.val_lt a).trans hm) hk (by simpa [htLen] using hm) htWord
    have hdigit : q.vars baseUnitDigit = (D (L.decode a : K)).val := by
      simpa only [Nat.zero_le,if_true,Nat.sub_zero,baseUnitDigitTable_getD] using hq
    have hQidx : q.vars baseUnitCursor=i.val := by
      rw [fq.vars _ (constantWordTable_preserves _ _ _ _ _ (by decide))]
      simp [p,show baseUnitCursor ≠ baseUnitArgument by decide,i]
    have hQout : q.arrs baseUnitBank=t.arrs baseUnitBank :=
      fq.arrs _ (constantWordTable_arrayFrame _ _ _ _ _)
    have eQ : (Expr.var baseUnitCursor).evalB W q = some i.val := ev_var hQidx (hi.trans hN)
    have eV : (Expr.var baseUnitDigit).evalB W q = some (D (L.decode a : K)).val :=
      ev_var hdigit ((D _).isLt.trans_le hQ)
    let w := q.setArr baseUnitBank i.val (D (L.decode a : K)).val
    have rw₁ : Run W storeBaseUnitDigit q w 3 :=
      Run.store eQ eV (by rw [hQout,ht.2.2.2.1]; exact hi.trans_le hOut)
    let v := w.setVar baseUnitCursor (i.val+1)
    have ew : (Expr.var baseUnitCursor).evalB W w = some i.val := eQ
    have rv : Run W baseUnitNext w v 4 := Run.assign
      (ev_add ew (evalB_lit hOne) ((Nat.succ_le_of_lt hi).trans_lt hN))
    have r : Run W (baseUnitVisit D L) t v (6*M+12) := by
      exact (rp.seq (rq.seq (rw₁.seq rv))).mono (by rw [htLen]; omega)
    have hvIndex : v.vars baseUnitCursor=i.val+1 := by simp [v]
    have hvCols : v.vars inputColsR=n := by
      simp only [v,w,vars_setVar,vars_setArr,if_neg (show inputColsR ≠ baseUnitCursor by decide)]
      rw [fq.vars _ (constantWordTable_preserves _ _ _ _ _ (by decide))]
      simpa [p,show inputColsR ≠ baseUnitArgument by decide] using ht.2.1
    have hvArr : v.arrs baseUnitBank=(t.arrs baseUnitBank).set i.val (D (L.decode a : K)).val := by
      change (q.arrs baseUnitBank).set _ _=_
      rw [hQout]
    refine ⟨v,r,⟨by rw [hvIndex]; exact Nat.succ_le_of_lt hi,hvCols,?_,?_,?_⟩,?_⟩
    · intro k hk
      simp only [v,w,arrs_setVar,arrs_setArr,if_neg hk]
      rw [fq.arrs _ (constantWordTable_arrayFrame _ _ _ _ _)]
      exact ht.2.2.1 k hk
    · rw [hvArr,List.length_set]
      exact ht.2.2.2.1
    · intro j hj
      rw [hvIndex] at hj
      rw [hvArr]
      by_cases he : j=i
      · subst j
        rw [getD_set_self' (hi.trans_le (by rw [ht.2.2.2.1]; exact hOut))]
      · have hne : i.val ≠ j.val := fun h => he (Fin.ext h.symm)
        rw [getD_set_ne' hne]
        have hjlt : j.val < i.val := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hne.symm
        exact ht.2.2.2.2 j hjlt
    · simp only [G,hvIndex]
      change n-(i.val+1) < n-i.val
      omega
  obtain ⟨t,r1,ht,hStop⟩ := Run.while_count I G (6*M+12)
    (fun t h => ⟨_,hguard t h⟩) step hInit
  have hd : t.vars baseUnitCursor=n := by
    rw [hguard t ht] at hStop
    exact le_antisymm ht.1 (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hStop)))
  have rr : Run W (decodeBaseUnitBank D L) s t (decodeBaseUnitBankCost K n) :=
    (r0.seq r1).mono (by simp [decodeBaseUnitBankCost,G,u,baseUnitGuard,Cond.size,Expr.size,
      show 4+(6*M+12)=6*M+16 by omega] <;> omega)
  exact ⟨t,rr,Frame.of_run rr,ht.2.2.1,fun i => ht.2.2.2.2 i (by rw [hd]; exact i.isLt)⟩

#print axioms decodeBaseUnitBank_run
end EvenTI.P15Scalar