import EvenP17ScalarActiveRead
import EvenP17ScalarActiveLoop
import EvenP12CompareLiveCRTInstall

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 15000

namespace EvenTI.P19Scalar.PrefixScan


open EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

def activeSlotBank : String := "even.scalar.active.slots"
def activeWordCursor : String := "even.scalar.active.cursor"
def activeWordLimit : String := "even.scalar.active.limit"
def activeReferenceSlot : String := "even.scalar.active.reference.slot"
def activeReferenceWord : String := "even.scalar.active.reference.word"
def activeWordAnswer : String := "even.scalar.active.answer"

private def activeWordGuard : Cond := .lt (.var activeWordCursor) (.var activeWordLimit)
private def activeWordEqual : Cond :=
  .eq (.get coordinateBank (.get activeSlotBank (.var activeWordCursor))) (.var activeReferenceWord)
private def activeWordKeep : Com := .ite activeWordEqual .skip (.assign activeWordAnswer (.lit 0))
private def activeWordBody : Com :=
  .seq activeWordKeep (.assign activeWordCursor (.add (.var activeWordCursor) (.lit 1)))

def checkActiveResidueWords : Com :=
  .seq (.assign activeWordCursor (.lit 0))
    (.seq (.assign activeReferenceWord (.get coordinateBank (.var activeReferenceSlot)))
      (.seq (.assign activeWordAnswer (.lit 1)) (.while activeWordGuard activeWordBody)))

/-- Prefix-capacity variant: the active array may have arbitrary unused tail storage.
Read actual recovered residue words through the installed ordered slot
list and compare all of them with the actual reference coordinate. All arrays
and the real input/output tapes remain unchanged. -/
theorem checkActiveResidueWords_run
    {W reference : ℕ} {s : Env} (coords slots : List ℕ)
    (hOne : 1 < W) (hCoordsWord : coords.length < W) (hSlotsWord : slots.length < W)
    (hValues : ∀ a ∈ coords, a < W)
    (hIndices : ∀ a ∈ slots, a < coords.length)
    (hReference : reference < coords.length)
    (hCoords : s.arrs coordinateBank=coords)
    (hSlots : ∀ k < slots.length, (s.arrs activeSlotBank)[k]? = some (slots.getD k 0))
    (hLimit : s.vars activeWordLimit=slots.length)
    (hRefSlot : s.vars activeReferenceSlot=reference) :
    ∃ t, Run W checkActiveResidueWords s t (30*slots.length+30) ∧
      t.vars activeWordAnswer ≤ 1 ∧
      (t.vars activeWordAnswer=1 ↔
        ∀ j < slots.length, coords.getD (slots.getD j 0) 0 = coords.getD reference 0) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  let value := coords.getD reference 0
  have hRefValue : value < W := by
    rw [show value = coords[reference] from List.getD_eq_getElem _ _ hReference]
    exact hValues _ (List.getElem_mem hReference)
  let a := s.setVar activeWordCursor 0
  let b := a.setVar activeReferenceWord value
  let z := b.setVar activeWordAnswer 1
  have r0 : Run W (.assign activeWordCursor (.lit 0)) s a 2 :=
    Run.assign (evalB_lit (by omega))
  have haReference : a.vars activeReferenceSlot=reference := by
    simpa only [a,vars_setVar,show activeReferenceSlot ≠ activeWordCursor by decide,if_false] using hRefSlot
  have er : (Expr.var activeReferenceSlot).evalB W a = some reference :=
    evalB_var_iff.mpr ⟨haReference.symm,by rw [haReference]; exact hReference.trans hCoordsWord⟩
  have r1 : Run W (.assign activeReferenceWord (.get coordinateBank (.var activeReferenceSlot))) a b 3 := by
    apply Run.assign
    refine evalB_get er ?_ hRefValue
    change (s.arrs coordinateBank)[reference]?=some value
    rw [hCoords,List.getElem?_eq_getElem hReference]
    rw [show value=coords[reference] from List.getD_eq_getElem _ _ hReference]
  have r2 : Run W (.assign activeWordAnswer (.lit 1)) b z 2 :=
    Run.assign (evalB_lit hOne)
  let I (u : Env) : Prop :=
    u.vars activeWordCursor ≤ slots.length ∧ u.vars activeWordLimit=slots.length ∧
    u.vars activeReferenceWord=value ∧ u.vars activeWordAnswer ≤ 1 ∧
    (u.vars activeWordAnswer=1 ↔ ∀ j < u.vars activeWordCursor,
      coords.getD (slots.getD j 0) 0=value) ∧
    u.arrs=s.arrs ∧ u.inp=s.inp ∧ u.out=s.out
  let potential (u : Env) := slots.length-u.vars activeWordCursor
  have hZeroCursor : z.vars activeWordCursor=0 := by
    simp [z,b,a,activeWordCursor,activeReferenceWord,activeWordAnswer]
  have iz : I z := by
    refine ⟨by rw [hZeroCursor]; omega,?_,?_,?_,?_,rfl,rfl,rfl⟩
    · simpa [z,b,a,activeWordCursor,activeWordLimit,activeReferenceWord,activeWordAnswer] using hLimit
    · simp [z,b,a,activeWordCursor,activeReferenceWord,activeWordAnswer]
    · simp [z,activeWordAnswer]
    · rw [hZeroCursor]
      simp [z]
  have guard (u : Env) (hu : I u) :
      activeWordGuard.evalB W u=some (decide (u.vars activeWordCursor < slots.length)) := by
    have e := evalB_condLt (evalB_var (hu.1.trans_lt hSlotsWord))
      (evalB_var (x:=activeWordLimit) (hu.2.1 ▸ hSlotsWord))
    simpa only [activeWordGuard,hu.2.1] using e
  have step (u : Env) (hu : I u) (hg : activeWordGuard.evalB W u=some true) :
      ∃ v, Run W activeWordBody u v 16 ∧ I v ∧ potential v < potential u := by
    rw [guard u hu] at hg
    have hk : u.vars activeWordCursor < slots.length := by simpa using hg
    let k := u.vars activeWordCursor
    let slot := slots[k]
    have hSlot : slot < coords.length := hIndices slot (List.getElem_mem hk)
    have hVal : coords.getD slot 0 < W := by
      rw [List.getD_eq_getElem _ _ hSlot]
      exact hValues _ (List.getElem_mem hSlot)
    have hSlotRead : (u.arrs activeSlotBank)[k]?=some slot := by
      rw [hu.2.2.2.2.2.1]
      have hAt : slots.getD k 0 = slot := List.getD_eq_getElem _ _ hk
      exact (hSlots k hk).trans (congrArg some hAt)
    have hValueRead : (u.arrs coordinateBank)[slot]?=some (coords.getD slot 0) := by
      rw [hu.2.2.2.2.2.1,hCoords,List.getElem?_eq_getElem hSlot,
        List.getD_eq_getElem _ _ hSlot]
    obtain ⟨w,rk,hwAnswer,hwVars,hwArrays,hwInp,hwOut⟩ :=
      EvenTI.P17Scalar.ActiveRead.keepResidueBit_run coordinateBank activeSlotBank activeWordCursor
        activeReferenceWord activeWordAnswer rfl (hk.trans hSlotsWord)
        hSlotRead (hSlot.trans hCoordsWord) hValueRead hVal
        hu.2.2.1 hRefValue (show 0 < W by omega)
    have hwCursor : w.vars activeWordCursor=k :=
      hwVars _ (by decide)
    let v := w.setVar activeWordCursor (k+1)
    have rn : Run W (.assign activeWordCursor (.add (.var activeWordCursor) (.lit 1))) w v 4 :=
      Run.assign (evalB_bin (op:=.add)
        (evalB_var_iff.mpr ⟨hwCursor.symm,by rw [hwCursor]; exact hk.trans hSlotsWord⟩)
        (evalB_lit hOne) ((Nat.succ_le_of_lt hk).trans_lt hSlotsWord))
    have hPred :
        (if coords.getD slot 0=value then u.vars activeWordAnswer else 0)=1 ↔
        ∀ j < k+1, coords.getD (slots.getD j 0) 0=value := by
      have old := hu.2.2.2.2.1
      have hAt : slots.getD k 0=slot := List.getD_eq_getElem _ _ hk
      by_cases he : coords.getD slot 0=value
      · simp only [he,if_true]
        constructor
        · intro h j hj
          by_cases hlt : j < k
          · exact old.mp h j hlt
          · have hjk : j=k := by omega
            simpa only [hjk,hAt] using he
        · intro h
          exact old.mpr (fun j hj => h j (by omega))
      · simp only [he,if_false]
        constructor
        · omega
        · intro hall
          exact False.elim (he (hAt ▸ hall k (by omega)))
    have hvCursor : v.vars activeWordCursor=k+1 := by simp [v]
    have hvAnswer : v.vars activeWordAnswer =
        if coords.getD slot 0=value then u.vars activeWordAnswer else 0 := by
      simpa only [v,vars_setVar,show activeWordAnswer ≠ activeWordCursor by decide,if_false]
        using hwAnswer
    refine ⟨v,(rk.seq rn).mono (by omega),?_,?_⟩
    · refine ⟨by rw [hvCursor]; omega,?_,?_,?_,?_,?_,?_,?_⟩
      · have hh := (hwVars activeWordLimit (by decide)).trans hu.2.1
        simpa only [v,vars_setVar,show activeWordLimit ≠ activeWordCursor by decide,if_false] using hh
      · have hh := (hwVars activeReferenceWord (by decide)).trans hu.2.2.1
        simpa only [v,vars_setVar,show activeReferenceWord ≠ activeWordCursor by decide,if_false] using hh
      · rw [hvAnswer]
        split <;> first | exact hu.2.2.2.1 | omega
      · rw [hvAnswer,hvCursor]
        exact hPred
      · exact hwArrays.trans hu.2.2.2.2.2.1
      · exact hwInp.trans hu.2.2.2.2.2.2.1
      · exact hwOut.trans hu.2.2.2.2.2.2.2
    · change slots.length-(k+1) < slots.length-k
      omega

  obtain ⟨t,rt,ht,hEnd⟩ := Run.while_count I potential 16
    (fun u hu => ⟨_,guard u hu⟩) step iz
  rw [guard t ht] at hEnd
  have hDone : t.vars activeWordCursor=slots.length := by
    have hh := of_decide_eq_false (Option.some.inj hEnd)
    exact le_antisymm ht.1 (Nat.le_of_not_gt hh)
  have hPotential : potential z=slots.length := by
    change slots.length-z.vars activeWordCursor=slots.length
    rw [hZeroCursor,Nat.sub_zero]
  have hGuardSize : activeWordGuard.size=3 := rfl
  refine ⟨t,(r0.seq (r1.seq (r2.seq rt))).mono ?_,ht.2.2.2.1,?_,
    ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2⟩
  · change 2+(3+(2+((1+activeWordGuard.size+16)*potential z+1+activeWordGuard.size))) ≤ _
    rw [hGuardSize,hPotential]
    omega
  · simpa only [hDone] using ht.2.2.2.2.1

theorem checkActiveResidueWords_eq : checkActiveResidueWords =
    EvenTI.P17Scalar.checkActiveResidueWords := rfl

#print axioms checkActiveResidueWords_run
end EvenTI.P19Scalar.PrefixScan
