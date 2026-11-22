import EvenP15RequestHeader

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P17Recover

open EvenTI.P15Execution EvenTI.P14Projection EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands commands_run install)

def leftRecordStart : String := "even.recover.left.record.start"
def rightRecordStart : String := "even.recover.right.record.start"
def rightRecordEnd : String := "even.recover.right.record.end"

def anchorListStart (right : Bool) : String :=
  if right then "even.recover.right.anchors" else "even.recover.left.anchors"
def formStart (right : Bool) : String :=
  if right then "even.recover.right.forms" else "even.recover.left.forms"
def formEnd (right : Bool) : String :=
  if right then "even.recover.right.forms.end" else "even.recover.left.forms.end"

private def originalBindings : List (String × Expr) :=
  [(leftRecordStart,.var "cursor"),(rightRecordStart,.var "stop"),(rightRecordEnd,.var "end")]

private def readBindings (right : Bool) : List (String × Expr) :=
  [("cursor",.var (if right then rightRecordStart else leftRecordStart)),
   ("end",.var (if right then rightRecordEnd else rightRecordStart))]

private def saveBindings (right : Bool) : List (String × Expr) :=
  [(anchorListStart right,.var "cursor"),(formStart right,.var "stop"),(formEnd right,.var "end")]

def openTrialSections (right : Bool) : Com :=
  .seq (commands (readBindings right))
    (.seq skipKind (.seq pairWindow (commands (saveBindings right))))

def openPairedTrialSections : Com :=
  .seq (commands originalBindings) (.seq (openTrialSections false) (openTrialSections true))

/-- Locations for the literal length-prefixed anchors and trailing field forms.
The anchor and form sections may be empty. -/
structure OperandSections (z : List ℕ) (right : Bool) (a f : List ℕ) (s : Env) : Prop where
  ordered : s.vars (anchorListStart right) ≤ s.vars (formStart right) ∧
    s.vars (formStart right) ≤ s.vars (formEnd right) ∧ s.vars (formEnd right) ≤ z.length
  anchors : slice z (s.vars (anchorListStart right)) (s.vars (formStart right)) = a
  forms : slice z (s.vars (formStart right)) (s.vars (formEnd right)) = f

private theorem originalSafe :
    ∀ p ∈ originalBindings, ∀ q ∈ originalBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [originalBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;>
    simp [NoVar,leftRecordStart,rightRecordStart,rightRecordEnd]

private theorem readSafe (right : Bool) :
    ∀ p ∈ readBindings right, ∀ q ∈ readBindings right, NoVar p.1 q.2 := by
  cases right <;> intro p hp q hq <;>
    simp only [readBindings,List.mem_cons,List.not_mem_nil,or_false,Bool.false_eq_true,
      if_false,if_true] at hp hq <;>
    rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;> simp [NoVar,leftRecordStart,rightRecordStart,rightRecordEnd]

private theorem saveSafe (right : Bool) :
    ∀ p ∈ saveBindings right, ∀ q ∈ saveBindings right, NoVar p.1 q.2 := by
  cases right <;> intro p hp q hq <;>
    simp only [saveBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq <;>
    rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> simp [NoVar,anchorListStart,formStart,formEnd]

private theorem readVar {B v : ℕ} {s : Env} {r : String} (h : s.vars r=v) (hb : v < B) :
    (Expr.var r).evalB B s=some v := evalB_var_iff.mpr ⟨h.symm,h ▸ hb⟩

theorem openTrialSections_run (z a f : List ℕ) (right : Bool) {B c e k : ℕ} {s : Env}
    (hc : s.vars (if right then rightRecordStart else leftRecordStart)=c)
    (he : s.vars (if right then rightRecordEnd else rightRecordStart)=e)
    (hce : c ≤ e) (hez : e ≤ z.length) (hB : 2 < B) (hZ : z.length < B)
    (hW : ∀ x ∈ z, x < B) (hBank : s.arrs "data"=sentinelWords z)
    (hSlice : slice z c e = k::pairW a f) :
    ∃ t, Run B (openTrialSections right) s t 45 ∧ OperandSections z right a f t ∧
      Frame (openTrialSections right) s t := by
  let s₀ := install [("cursor",c),("end",e)] s
  have r₀ : Run B (commands (readBindings right)) s s₀ 5 :=
    commands_run (readBindings right) [c,e] s (by cases right <;> rfl)
      (.cons (readVar hc ((hce.trans hez).trans_lt hZ)) (.cons (readVar he (hez.trans_lt hZ)) .nil))
      (readSafe right)
  obtain ⟨s₁,b,r₁,hb,hbe,hTail,hFrame⟩ := skipKind_run z (s:=s₀)
    (show s₀.vars "cursor"=c by simp [s₀,install]) (show s₀.vars "end"=e by simp [s₀,install])
    hce hez hZ (by omega)
  have hE : s₁.vars "end" = e := by
    rw [hFrame.vars _ (by decide)]
    simp [s₀,install]
  have hD : s₁.arrs "data"=sentinelWords z := (hFrame.arrs _ (by decide)).trans hBank
  obtain ⟨s₂,i,j,r₂,hij,hje,_,hi,hj,he₂,_,hp,_⟩ := pairWindow_run z hb hE hbe hez hZ hB hW hD
  have hValues : slice z i j = a ∧ slice z j e = f := by
    rw [hSlice,List.tail_cons] at hTail
    rw [← hTail,unpairW_pairW] at hp
    exact Prod.mk.inj hp.symm
  let vals := [i,j,e]
  let t := install [(anchorListStart right,i),(formStart right,j),(formEnd right,e)] s₂
  have r₃ : Run B (commands (saveBindings right)) s₂ t 7 :=
    commands_run (saveBindings right) vals s₂ (by cases right <;> rfl)
      (.cons (readVar hi ((hij.trans (hje.trans hez)).trans_lt hZ))
        (.cons (readVar hj ((hje.trans hez).trans_lt hZ)) (.cons (readVar he₂ (hez.trans_lt hZ)) .nil)))
      (saveSafe right)
  have hr : Run B (openTrialSections right) s t 45 := r₀.seq (r₁.seq (r₂.seq r₃))
  have hI : t.vars (anchorListStart right)=i := by cases right <;> simp [t,install,anchorListStart,formStart,formEnd]
  have hJ : t.vars (formStart right)=j := by cases right <;> simp [t,install,anchorListStart,formStart,formEnd]
  have hE' : t.vars (formEnd right)=e := by cases right <;> simp [t,install,anchorListStart,formStart,formEnd]
  refine ⟨t,hr,⟨?_,?_,?_⟩,Frame.of_run hr⟩
  · rw [hI,hJ,hE']; exact ⟨hij,hje,hez⟩
  · simpa only [hI,hJ] using hValues.1
  · simpa only [hJ,hE'] using hValues.2

/-- Open both nested trial payloads in the immutable original request bank. -/
theorem openPairedTrialSections_run (w la lf ra rf : List ℕ) (kl kr : ℕ)
    {B : ℕ} {s : Env}
    (h : LoadedRequest w (kl::pairW la lf) (kr::pairW ra rf) s) (hB : 2 < B)
    (hZ : (pairW w (pairW (kl::pairW la lf) (kr::pairW ra rf))).length < B)
    (hW : ∀ x ∈ pairW w (pairW (kl::pairW la lf) (kr::pairW ra rf)), x < B) :
    let z := pairW w (pairW (kl::pairW la lf) (kr::pairW ra rf))
    ∃ t, Run B openPairedTrialSections s t 97 ∧
      OperandSections z false la lf t ∧ OperandSections z true ra rf t ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out ∧
      t.vars requestRawStart=s.vars requestRawStart ∧ t.vars requestRawEnd=s.vars requestRawEnd := by
  let z := pairW w (pairW (kl::pairW la lf) (kr::pairW ra rf))
  let c := s.vars "cursor"
  let j := s.vars "stop"
  let e := s.vars "end"
  let s₀ := install [(leftRecordStart,c),(rightRecordStart,j),(rightRecordEnd,e)] s
  obtain ⟨_,_,hcj,hje,he⟩ := h.ordered
  have heb : e < B := by change s.vars "end" < B; rw [he]; exact hZ
  have r₀ : Run B (commands originalBindings) s s₀ 7 :=
    commands_run originalBindings [c,j,e] s (by rfl)
      (.cons (readVar rfl ((hcj.trans hje).trans_lt heb))
        (.cons (readVar rfl (hje.trans_lt heb)) (.cons (readVar rfl heb) .nil))) originalSafe
  have s₀c : s₀.vars leftRecordStart=c := by simp [s₀,install,leftRecordStart,rightRecordStart,rightRecordEnd]
  have s₀j : s₀.vars rightRecordStart=j := by simp [s₀,install,leftRecordStart,rightRecordStart,rightRecordEnd]
  have s₀e : s₀.vars rightRecordEnd=e := by simp [s₀,install,leftRecordStart,rightRecordStart,rightRecordEnd]
  obtain ⟨s₁,r₁,hLeft,hFrame⟩ := openTrialSections_run z la lf false s₀c s₀j hcj (hje.trans he.le) hB hZ hW h.stored h.leftTrial
  have hJ : s₁.vars rightRecordStart=j := (hFrame.vars _ (by decide)).trans s₀j
  have hE : s₁.vars rightRecordEnd=e := (hFrame.vars _ (by decide)).trans s₀e
  have hData : s₁.arrs "data"=sentinelWords z := (hFrame.arrs _ (by decide)).trans h.stored
  obtain ⟨t,r₂,hRight,tf⟩ := openTrialSections_run z ra rf true hJ hE hje he.le hB hZ hW hData h.rightTrial
  have hL : OperandSections z false la lf t := by
    have hs := tf.vars (anchorListStart false) (by decide)
    have hf := tf.vars (formStart false) (by decide)
    have he' := tf.vars (formEnd false) (by decide)
    exact ⟨by rw [hs,hf,he']; exact hLeft.ordered,
      by rw [hs,hf]; exact hLeft.anchors,by rw [hf,he']; exact hLeft.forms⟩
  have hr : Run B openPairedTrialSections s t 97 := r₀.seq (r₁.seq r₂)
  have hrFrame := Frame.of_run hr
  have hWrites : arrayWrites openPairedTrialSections = ∅ := by decide
  refine ⟨t,hr,hL,hRight,funext (fun a => hrFrame.arrs a (by simp [hWrites])),?_,?_,?_,?_⟩
  · exact hrFrame.inp (by apply noRead_of_check; rfl)
  · exact hrFrame.out (by apply noWrite_of_check; rfl)
  · exact hrFrame.vars _ (by decide)
  · exact hrFrame.vars _ (by decide)

#print axioms openTrialSections_run
#print axioms openPairedTrialSections_run

end EvenTI.P17Recover
