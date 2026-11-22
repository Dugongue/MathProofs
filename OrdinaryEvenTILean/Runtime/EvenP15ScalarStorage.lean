import EvenP15RequestFrame

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P15Execution EvenTI.P10Scan EvenTI.P12CountPre EvenTI.P14Projection
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites)

/-- The literal prepared-request parser works on an independently sized
workspace. Each untouched bank retains its full initialized contents,
so native chart, CRT, and scalar-scratch extents can be chosen separately. -/
theorem requestLoadWithStorage_run (w left right : List ℕ) (alloc : String → ℕ) {B : ℕ}
    (hB : 4 < B) (hn : (pairW w (pairW left right)).length < B)
    (hWords : ∀ a ∈ pairW w (pairW left right), a < B)
    (hSize : alloc "data" = (pairW w (pairW left right)).length+1) :
    let z := pairW w (pairW left right)
    ∃ t, Run B requestLoadProgram (initEnv alloc (z.length::z)) t (13*z.length+90) ∧
      LoadedRequest w left right t ∧ t.inp=[] ∧ t.out=[] ∧
      ∀ bank, bank ≠ "data" → t.arrs bank=List.replicate (alloc bank) 0 := by
  let z := pairW w (pairW left right)
  let s := initEnv alloc (z.length::z)
  let u := {s.setVar "length" z.length with inp := z}
  have r₀ : Run B (.read "length") s u 1 := Run.read rfl
  obtain ⟨v,r₁,hl,hData,hOut,hIn⟩ := inputLoad_run z (σ:=u) (by simp [u])
    (by simp [u,s,initEnv]) rfl (by simp [u,s,initEnv,inputBuffer_zero,hSize,z]) hn (by omega) hWords
  obtain ⟨t,rt,hLoad,hi,ho⟩ := requestWindows_run w left right hB hn hWords hl
    (hData.trans (inputBuffer_full z))
  have rr : Run B requestLoadProgram s t (13*z.length+90) :=
    (r₀.seq (r₁.seq rt)).mono (by dsimp [z]; omega)
  have hWrites : arrayWrites requestLoadProgram = ({"data"} : Finset String) := by decide
  refine ⟨t,rr,hLoad,hi.trans hIn,by simpa [u,s,initEnv] using ho.trans hOut,?_⟩
  intro bank hb
  have save := (Frame.of_run rr).arrs bank (by rw [hWrites,Finset.mem_singleton]; exact hb)
  exact save

#print axioms requestLoadWithStorage_run
end EvenTI.P15Scalar