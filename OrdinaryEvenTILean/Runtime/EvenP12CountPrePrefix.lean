import EvenP12CountPreInput

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.P10Oracle

set_option autoImplicit false

/-- The variables which a fixed command can change. -/
def varUntouched (x : String) : Com → Prop
  | .skip | .write _ | .store _ _ _ => True
  | .assign y _ | .read y => x ≠ y
  | .seq c d | .ite _ c d => varUntouched x c ∧ varUntouched x d
  | .while _ c => varUntouched x c

theorem vars_eq_of_untouched {B N : Nat} {c : Com} {σ τ : Env} {x : String}
    (r : Run B c σ τ N) (h : varUntouched x c) : τ.vars x = σ.vars x := by
  obtain ⟨j,-,hr⟩ := r
  revert h
  induction hr with
  | skip | store | write | while_false => intro _; rfl
  | assign | read =>
    intro hv
    simp only [varUntouched] at hv
    exact if_neg hv
  | seq _ _ ih ih' =>
    intro hc
    exact (ih' hc.2).trans (ih hc.1)
  | ite_true _ _ ih => exact fun h => ih h.1
  | ite_false _ _ ih => exact fun h => ih h.2
  | while_true _ _ _ ih ih' =>
    intro hc
    exact (ih' hc).trans (ih hc)

theorem segment_untouched (copy : Bool) {x : String} (hx : x ≠ "cursor") :
    varUntouched x (segmentLoop copy) := by
  cases copy <;> simp [varUntouched,segmentLoop,segmentBody,advanceCursor,hx]

theorem cut_length_le (z : List Nat) : (cut z).1.length ≤ z.length := by
  have hh := congrArg List.length (cut_drop_poss z)
  simp only [List.length_append] at hh
  omega

theorem cut_take (z : List Nat) : z.take (cut z).1.length = (cut z).1 := by
  let k := (cut z).1.length
  have h := congrArg (List.take k) (cut_drop_poss z)
  rw [List.append_assoc] at h
  exact h.symm.trans List.take_append_length

theorem cut_drop (z : List Nat) (h : (cut z).1.length < z.length) :
    z.drop ((cut z).1.length + 1) = (cut z).2 := by
  have h' : (cut z).1 ++ 0 :: (cut z).2 = z := by
    simpa [h,List.append_assoc] using cut_drop_poss z
  calc
    z.drop ((cut z).1.length + 1) =
        ((cut z).1 ++ 0 :: (cut z).2).drop ((cut z).1.length + 1) :=
      congrArg (List.drop ((cut z).1.length + 1)) h'.symm
    _ = _ := by rw [List.drop_length_add_append]; rfl

def contextProgram : Com :=
  .seq (segmentLoop true) (.seq (.write (.lit 0)) (.assign "firstEnd" (.var "cursor")))

theorem contextProgram_run (z : List Nat) {B : Nat} {σ : Env}
    (hc : σ.vars "cursor" = 0) (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length < B) (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B contextProgram σ τ (17*z.length+12) ∧
      τ.vars "firstEnd" = (cut z).1.length ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out ++ (cut z).1 ++ [0] ∧ τ.inp = σ.inp := by
  obtain ⟨u,hu,hc',h0,ha,hi,ho⟩ :=
    segmentLoop_run true z (Nat.zero_le _) hc hBank hLen hWords
  simp only [Nat.zero_add,List.drop_zero,if_true] at hc' ho
  let v := {u with out := u.out ++ [0]}
  let τ := v.setVar "firstEnd" (cut z).1.length
  have r₁ : Run B (.write (.lit 0)) u v 2 := Run.write (evalB_lit (by omega))
  have r₂ : Run B (.assign "firstEnd" (.var "cursor")) v τ 2 := Run.assign
    (by simp [v,hc', (cut_length_le z).trans_lt hLen])
  exact ⟨τ,(hu.seq (r₁.seq r₂)).mono (by omega),by simp [τ],
    by simpa [τ,v] using ha,by simp [τ,v,ho],by simpa [τ,v] using hi⟩

def secondProgram : Com :=
  .seq (.assign "secondStart" (.add (.var "firstEnd") (.lit 1)))
    (.seq (.assign "cursor" (.var "secondStart"))
      (.seq (segmentLoop false) (.assign "secondEnd" (.var "cursor"))))

theorem secondProgram_run (z : List Nat) {B : Nat} {σ : Env}
    (hf : σ.vars "firstEnd" = (cut z).1.length) (hexists : (cut z).1.length < z.length)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length < B) (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B secondProgram σ τ (17*z.length+16) ∧
      τ.vars "firstEnd" = (cut z).1.length ∧
      τ.vars "secondStart" = (cut z).1.length+1 ∧
      τ.vars "secondEnd" = (cut z).1.length+1+(cut (cut z).2).1.length ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out ∧ τ.inp = σ.inp := by
  let a := (cut z).1.length+1
  let t := σ.setVar "secondStart" a
  let u := t.setVar "cursor" a
  have hb : a < B := by dsimp [a]; omega
  have h₁ : Run B (.assign "secondStart" (.add (.var "firstEnd") (.lit 1))) σ t 4 := by
    apply Run.assign
    exact evalB_bin (op := .add) (by simp [hf]; omega) (evalB_lit (by omega)) hb
  have h₂ : Run B (.assign "cursor" (.var "secondStart")) t u 2 := Run.assign (by simp [t,hb])
  have hl : a ≤ z.length := by dsimp [a]; omega
  obtain ⟨v,h₃,hc',h0,ha,hi,ho⟩ := segmentLoop_run false z (σ := u) hl (by simp [u])
    (by simpa [u,t] using hBank) hLen hWords
  have hcursor : v.vars "cursor" = a+(cut (cut z).2).1.length := by
    rw [hc',show z.drop a = (cut z).2 from cut_drop z hexists]
  have hvl : v.vars "cursor" ≤ z.length := by
    have hd := cut_length_le (z.drop a)
    simp only [List.length_drop] at hd
    omega
  let τ := v.setVar "secondEnd" (a+(cut (cut z).2).1.length)
  have h₄ : Run B (.assign "secondEnd" (.var "cursor")) v τ 2 :=
    Run.assign (by rw [evalB_var_iff,← hcursor]; exact ⟨rfl,hvl.trans_lt hLen⟩)
  refine ⟨τ,(h₁.seq (h₂.seq (h₃.seq h₄))).mono (by omega),?_,?_,?_,?_,?_,?_⟩
  · have h := vars_eq_of_untouched h₃ (segment_untouched false (x := "firstEnd") (by decide))
    simp [τ,h,u,t,hf]
  · have h := vars_eq_of_untouched h₃ (segment_untouched false (x := "secondStart") (by decide))
    simp [τ,h,u,t,a]
  · simp [τ,a]
  · simpa [τ,t,u] using ha
  · simpa [τ,t,u] using ho
  · simpa [τ,t,u] using hi

#print axioms vars_eq_of_untouched
#print axioms contextProgram_run
#print axioms secondProgram_run
end EvenTI.P12CountPre
