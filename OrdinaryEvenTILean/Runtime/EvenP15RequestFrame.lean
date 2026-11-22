import EvenP14ProjectionEngine
import EvenP10TrialPayload
import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P10Scan EvenTI.P12CountPre EvenTI.P14Projection
open Mathproof.Problem18IMPFieldLayout20261001 (noRead run_frame)

/-- The original pair words are retained for both comparison and scalar
controllers while the two numeric trial windows are opened. -/
def requestRawStart : String := "even.request.raw.start"
def requestRawEnd : String := "even.request.raw.end"

private def initialFrame : Com := .seq (.assign "cursor" (.lit 0)) (.assign "end" (.var "length"))
private def saveRawBounds : Com := .seq (.assign requestRawStart (.var "cursor"))
  (.seq (.assign requestRawEnd (.var "stop")) (.assign "cursor" (.var "stop")))

def requestWindows : Com := .seq initialFrame (.seq pairWindow (.seq saveRawBounds pairWindow))

def requestLoadProgram : Com := .seq (.read "length") (.seq inputLoadLoop requestWindows)

structure LoadedRequest (w left right : List ℕ) (s : Env) : Prop where
  stored : s.arrs "data" = sentinelWords (pairW w (pairW left right))
  raw : slice (pairW w (pairW left right)) (s.vars requestRawStart) (s.vars requestRawEnd) = w
  leftTrial : slice (pairW w (pairW left right)) (s.vars "cursor") (s.vars "stop") = left
  rightTrial : slice (pairW w (pairW left right)) (s.vars "stop") (s.vars "end") = right
  ordered : s.vars requestRawStart ≤ s.vars requestRawEnd ∧ s.vars requestRawEnd ≤ s.vars "cursor" ∧
    s.vars "cursor" ≤ s.vars "stop" ∧ s.vars "stop" ≤ s.vars "end" ∧
    s.vars "end" = (pairW w (pairW left right)).length

/-- The verified pair-window parser is replayed on the actual nested payload;
all positions refer to one bank and the original words stay in place. -/
theorem requestWindows_run (w left right : List ℕ) {B : ℕ} {s : Env}
    (hB : 4 < B) (hn : (pairW w (pairW left right)).length < B)
    (hWords : ∀ a ∈ pairW w (pairW left right), a < B)
    (hL : s.vars "length" = (pairW w (pairW left right)).length)
    (hData : s.arrs "data" = sentinelWords (pairW w (pairW left right))) :
    ∃ t, Run B requestWindows s t 80 ∧ LoadedRequest w left right t ∧ t.inp=s.inp ∧ t.out=s.out := by
  let z := pairW w (pairW left right)
  let x := s.setVar "cursor" 0
  let y := x.setVar "end" z.length
  have r₀ : Run B (.assign "cursor" (.lit 0)) s x 2 := Run.assign (evalB_lit (by omega))
  have r₁ : Run B (.assign "end" (.var "length")) x y 2 := Run.assign
    (liveVar (by simpa [x] using hL) hn)
  obtain ⟨u,a,b,ru,hab,hb,_,hCur,hStop,hEnd,hBank,hPair,fu⟩ :=
    pairWindow_run z (s:=y) (c:=0) (e:=z.length) (by rfl) (by rfl) (by omega)
      (by rfl) hn (by omega) hWords hData
  have hTop : slice z a b=w ∧ slice z b z.length=pairW left right := by
    have hz : slice z 0 z.length=z := by simp [slice]
    rw [hz] at hPair
    simpa [z,Prod.mk.injEq] using hPair.symm
  let u₁ := u.setVar requestRawStart a
  let u₂ := u₁.setVar requestRawEnd b
  let u₃ := u₂.setVar "cursor" b
  have r₂ : Run B (.assign requestRawStart (.var "cursor")) u u₁ 2 :=
    Run.assign (liveVar hCur ((hab.trans hb).trans_lt hn))
  have r₃ : Run B (.assign requestRawEnd (.var "stop")) u₁ u₂ 2 :=
    Run.assign (liveVar (by simpa [u₁,requestRawStart] using hStop) (hb.trans_lt hn))
  have r₄ : Run B (.assign "cursor" (.var "stop")) u₂ u₃ 2 :=
    Run.assign (liveVar (by simpa [u₂,u₁,requestRawStart,requestRawEnd] using hStop) (hb.trans_lt hn))
  obtain ⟨t,c,d,rt,hcd,hd,hbc,hC,hD,hE,htBank,hSub,ft⟩ :=
    pairWindow_run z (s:=u₃) (c:=b) (e:=z.length) (by rfl)
      (by simpa [u₃,u₂,u₁,requestRawStart,requestRawEnd] using hEnd)
      hb (by rfl) hn (by omega) hWords hBank
  have hTrails : slice z c d=left ∧ slice z d z.length=right := by
    rw [hTop.2] at hSub
    simpa [Prod.mk.injEq] using hSub.symm
  have hRA : t.vars requestRawStart=a := by
    rw [ft.vars _ (by decide)]
    simp [u₃,u₂,u₁,requestRawStart,requestRawEnd]
  have hRB : t.vars requestRawEnd=b := by
    rw [ft.vars _ (by decide)]
    simp [u₃,u₂,u₁,requestRawStart,requestRawEnd]
  have hRead : noRead pairWindow := noRead_of_check (by decide)
  have hInp : t.inp=s.inp :=
    ((run_frame rt).2.2.2.1 hRead).trans ((run_frame ru).2.2.2.1 hRead)
  have hOut : t.out=s.out := (ft.out (noWrite_of_check (by decide))).trans (fu.out (noWrite_of_check (by decide)))
  refine ⟨t,((r₀.seq r₁).seq (ru.seq ((r₂.seq (r₃.seq r₄)).seq rt))).mono (by decide),?_,hInp,hOut⟩
  exact ⟨htBank,by rw [hRA,hRB]; exact hTop.1,
    by rw [hC,hD]; exact hTrails.1,by rw [hD,hE]; exact hTrails.2,
    by rw [hRA,hRB,hC,hD,hE]; exact ⟨hab,hbc,hcd,hd,rfl⟩⟩

theorem requestLoadProgram_run (w left right : List ℕ) {B : ℕ}
    (hB : 4 < B) (hn : (pairW w (pairW left right)).length < B)
    (hWords : ∀ a ∈ pairW w (pairW left right), a < B) :
    let z := pairW w (pairW left right)
    ∃ t, Run B requestLoadProgram (initEnv (fun _ => z.length+1) (z.length::z)) t
      (13*z.length+90) ∧ LoadedRequest w left right t ∧ t.inp=[] ∧ t.out=[] := by
  let z := pairW w (pairW left right)
  let s := initEnv (fun _ => z.length+1) (z.length::z)
  let u := {s.setVar "length" z.length with inp := z}
  have r₀ : Run B (.read "length") s u 1 := Run.read rfl
  obtain ⟨v,r₁,hl,hData,hOut,hIn⟩ := inputLoad_run z (σ:=u) (by simp [u])
    (by simp [u,s,initEnv]) rfl (by simp [u,s,initEnv,inputBuffer_zero]) hn (by omega) hWords
  obtain ⟨t,rt,hLoad,hi,ho⟩ := requestWindows_run w left right hB hn hWords hl
    (hData.trans (inputBuffer_full z))
  exact ⟨t,(r₀.seq (r₁.seq rt)).mono (by dsimp [z]; omega),hLoad,hi.trans hIn, by simpa [u,s,initEnv] using ho.trans hOut⟩

#print axioms requestLoadProgram_run
end EvenTI.P15Execution